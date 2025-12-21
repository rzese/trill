/** <module> wrapper_parser

This module implements the ontology_parser interface using Java's OWL API
through JPL (Java-Prolog bidirectional interface).

## Overview

The wrapper_parser module provides a hybrid Java-Prolog approach to parsing
OWL ontologies. It leverages the powerful and standards-compliant Java OWL API
for parsing while maintaining the axioms in Prolog format for reasoning.

## Architecture

1. **Java Side**: Uses the prob-owlapi library (it.unife.ml.probowlapi) to:
   - Parse OWL/RDF files
   - Extract axioms in a standardized format
   - Handle namespace resolution

2. **Prolog Side**: 
   - Receives axioms from Java
   - Asserts them as `adb/1` facts
   - Provides the ontology_parser interface predicates

## Requirements

- **Java 11+**: Required for the OWL API
- **JPL 7.6.1+**: Java-Prolog interface
- **prob-owlapi-2.0.8.jar**: Contains the TrillKBParserWrapper class

## Key Features

1. **Full OWL Support**: Leverages Java OWL API for complete OWL parsing
2. **Streaming Loading**: Parses and asserts axioms incrementally
3. **Prefix Management**: Handles namespace prefixes via Java
4. **Concurrent Operations**: Uses concurrent_maplist for batch operations

## Main Predicates

### Axiom Management
- axiom/1: Query axioms (via adb/1 facts)
- add_axiom/1: Add single axiom
- add_axioms/1: Add list of axioms (concurrent)
- remove_axiom/1: Remove single axiom
- remove_axioms/1: Remove list of axioms (concurrent)
- is_axiom/1: Validate axiom format

### KB Loading
- load_kb/1: Load KB from Prolog file
- load_owl_kb/1: Load KB from OWL file (via Java)
- load_owl_kb_from_string/1: Load KB from OWL string

### Prefix Management
- kb_prefixes/1: Get registered prefixes
- add_kb_prefix/2: Register namespace prefix
- remove_kb_prefix/1, remove_kb_prefix/2: Remove prefix

## Axiom Types Supported

The module recognizes all standard OWL axiom types:
- Class axioms: subClassOf, equivalentClasses, disjointClasses
- Property axioms: subPropertyOf, propertyDomain, propertyRange
- Property characteristics: transitiveProperty, symmetricProperty, etc.
- Individual axioms: classAssertion, propertyAssertion
- Identity: sameIndividual, differentIndividuals
- Annotations: annotationAssertion

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

%:- module(wrapper_parser,[]).


:- use_module(library(lists)).
:- use_module(library(jpl)).             % JPL 7.x
:- use_module(library(error)).
:- use_module(library(apply)).
:- use_module(library(readutil)).
:- use_module(library(ordsets)).
:- use_module(library(thread)).
:- use_module(library(assoc)).

:- use_module(library(trill_utility)).

jar_file('prob-owlapi-2.0.8.jar').
wrapper_class('it.unife.ml.probowlapi.trill.TrillKBParserWrapper').

expand_atomic_default_operation(reduce). %expand or reduce

/*****************************/

/************************************
 * 
 * ABSTRACT PREDICATES FROM
 * ontology_parser
 * 
 * In the following there is the
 * implementation of the abstract
 * predicates of the ontology_parser
 * interface.
 * 
 ************************************/

/******************************/

/********************************
  AXIOMS MANAGEMENT
*********************************/
%% axiom(:Axiom)
% -------- Recognized TRILL axiom functors --------------------------
% This is used by add_axiom/1 to quickly validate shape.  Keep in sync with
% TRILL syntax: subClassOf, equivalentClasses, subPropertyOf, propertyDomain,
% propertyRange, transitiveProperty, inverseProperties, symmetricProperty,
% sameIndividual, differentIndividuals, classAssertion, propertyAssertion,
% annotationAssertion, functionalProeprty, plus concept descriptions used inside axioms. 
:- multifile trill:axiom/1.
trill:axiom(M:A) :- M:adb(A).


:- multifile trill:add_axiom/1.
trill:add_axiom(M:Axiom) :-
  add_axiom(M,Axiom),
  trill:update_tabs(M,Axiom).

add_axiom(M,Axiom) :-
  must_be(nonvar, Axiom),
  trill:is_axiom(Axiom),
  trill:kb_prefixes(M:NSList),
  ns_expand_term(M,NSList, Axiom, TRILLAxiomExpanded),
  add_axiom_no_check(M,TRILLAxiomExpanded).

add_axiom_no_check(M,Axiom) :-
  M:adb(Axiom),!.

add_axiom_no_check(M,Axiom) :-
  assertz(M:adb(Axiom)),
  add_kb_atom(M,Axiom).

add_kb_atom(M,Axiom) :-
  ensure_kb_atom_dict(M,KBA0),
  collect_axiom_entities(Axiom,KBA0,KBA),
  ( KBA0 == KBA -> true
  ; retractall(M:kb_atom(_)),
    assertz(M:kb_atom(KBA))
  ).

ensure_kb_atom_dict(M,KBA) :-
  ( M:kb_atom(KBA) -> true
  ; empty_kba(Empty),
    assertz(M:kb_atom(Empty)),
    KBA = Empty
  ).

empty_kba(kbatoms{annotationProperty:[],
                  class:[],
                  dataProperty:[],
                  datatype:[],
                  individual:[],
                  objectProperty:[]}).

collect_axiom_entities(subClassOf(Sub,Super),KBA0,KBA) :-
  collect_class_expr(Sub,KBA0,KBA1),
  collect_class_expr(Super,KBA1,KBA).
collect_axiom_entities(equivalentClasses(List),KBA0,KBA) :-
  collect_class_list(List,KBA0,KBA).
collect_axiom_entities(disjointClasses(List),KBA0,KBA) :-
  collect_class_list(List,KBA0,KBA).
collect_axiom_entities(disjointUnion(Class,List),KBA0,KBA) :-
  collect_class_expr(Class,KBA0,KBA1),
  collect_class_list(List,KBA1,KBA).
collect_axiom_entities(subPropertyOf(Sub,Super),KBA0,KBA) :-
  collect_property_expr(Sub,any,KBA0,KBA1),
  collect_property_expr(Super,any,KBA1,KBA).
collect_axiom_entities(equivalentProperties(List),KBA0,KBA) :-
  collect_property_list(List,any,KBA0,KBA).
collect_axiom_entities(propertyDomain(Prop,Domain),KBA0,KBA) :-
  collect_property_expr(Prop,any,KBA0,KBA1),
  collect_class_expr(Domain,KBA1,KBA).
collect_axiom_entities(propertyRange(Prop,Range),KBA0,KBA) :-
  range_property_kind(Prop,Range,KBA0,Kind),
  collect_property_expr(Prop,Kind,KBA0,KBA1),
  collect_range_target(Range,Kind,KBA1,KBA).
collect_axiom_entities(transitiveProperty(Prop),KBA0,KBA) :-
  collect_property_expr(Prop,object,KBA0,KBA).
collect_axiom_entities(functionalProperty(Prop),KBA0,KBA) :-
  collect_property_expr(Prop,object,KBA0,KBA).
collect_axiom_entities(symmetricProperty(Prop),KBA0,KBA) :-
  collect_property_expr(Prop,object,KBA0,KBA).
collect_axiom_entities(inverseProperties(P,S),KBA0,KBA) :-
  collect_property_expr(P,object,KBA0,KBA1),
  collect_property_expr(S,object,KBA1,KBA).
collect_axiom_entities(sameIndividual(List),KBA0,KBA) :-
  collect_individual_list(List,KBA0,KBA).
collect_axiom_entities(differentIndividuals(List),KBA0,KBA) :-
  collect_individual_list(List,KBA0,KBA).
collect_axiom_entities(classAssertion(Class,Ind),KBA0,KBA) :-
  collect_class_expr(Class,KBA0,KBA1),
  collect_individual(Ind,KBA1,KBA).
collect_axiom_entities(propertyAssertion(Prop,Subj,Obj),KBA0,KBA) :-
  assertion_property_kind(Prop,Obj,KBA0,Kind),
  collect_property_expr(Prop,Kind,KBA0,KBA1),
  collect_individual(Subj,KBA1,KBA2),
  collect_assertion_object(Obj,Kind,KBA2,KBA).
collect_axiom_entities(annotationAssertion(Prop,Target,Value),KBA0,KBA) :-
  collect_property_expr(Prop,annotation,KBA0,KBA1),
  collect_annotation_target(Target,KBA1,KBA2),
  collect_annotation_value(Value,KBA2,KBA).
collect_axiom_entities(Term,KBA0,KBA) :-
  compound(Term),
  Term =.. [_|Args],
  collect_axiom_terms(Args,KBA0,KBA).
collect_axiom_entities(_,KBA,KBA).

collect_axiom_terms([],KBA,KBA).
collect_axiom_terms([H|T],KBA0,KBA) :-
  collect_axiom_entities(H,KBA0,KBA1),
  collect_axiom_terms(T,KBA1,KBA).

collect_class_list(List,KBA0,KBA) :-
  ( is_list(List) -> collect_class_list_items(List,KBA0,KBA)
  ; collect_class_expr(List,KBA0,KBA)
  ).

collect_class_list_items([],KBA,KBA).
collect_class_list_items([H|T],KBA0,KBA) :-
  collect_class_expr(H,KBA0,KBA1),
  collect_class_list_items(T,KBA1,KBA).

collect_property_list(List,Kind,KBA0,KBA) :-
  ( is_list(List) -> collect_property_list_items(List,Kind,KBA0,KBA)
  ; collect_property_expr(List,Kind,KBA0,KBA)
  ).

collect_property_list_items([],_,KBA,KBA).
collect_property_list_items([H|T],Kind,KBA0,KBA) :-
  collect_property_expr(H,Kind,KBA0,KBA1),
  collect_property_list_items(T,Kind,KBA1,KBA).

collect_individual_list(List,KBA0,KBA) :-
  ( is_list(List) -> collect_individual_list_items(List,KBA0,KBA)
  ; collect_individual(List,KBA0,KBA)
  ).

collect_individual_list_items([],KBA,KBA).
collect_individual_list_items([H|T],KBA0,KBA) :-
  collect_individual(H,KBA0,KBA1),
  collect_individual_list_items(T,KBA1,KBA).

collect_class_expr(Expr,KBA,KBA) :- var(Expr), !.
collect_class_expr(Expr,KBA,KBA) :- number(Expr), !.
collect_class_expr('',KBA,KBA) :- !.
collect_class_expr(Expr,KBA,KBA) :- is_literal_term(Expr), !.
collect_class_expr(Expr,KBA0,KBA) :-
  is_list(Expr), !,
  collect_class_list_items(Expr,KBA0,KBA).
collect_class_expr(Expr,KBA0,KBA) :-
  atom(Expr), !,
  add_entity(class,Expr,KBA0,KBA).
collect_class_expr(intersectionOf(List),KBA0,KBA) :-
  collect_class_list(List,KBA0,KBA).
collect_class_expr(unionOf(List),KBA0,KBA) :-
  collect_class_list(List,KBA0,KBA).
collect_class_expr(complementOf(C),KBA0,KBA) :-
  collect_class_expr(C,KBA0,KBA).
collect_class_expr(oneOf(List),KBA0,KBA) :-
  collect_individual_list(List,KBA0,KBA).
collect_class_expr(someValuesFrom(Prop,Filler),KBA0,KBA) :-
  restriction_kind(Filler,Kind),
  collect_property_expr(Prop,Kind,KBA0,KBA1),
  collect_restriction_filler(Filler,Kind,KBA1,KBA).
collect_class_expr(allValuesFrom(Prop,Filler),KBA0,KBA) :-
  restriction_kind(Filler,Kind),
  collect_property_expr(Prop,Kind,KBA0,KBA1),
  collect_restriction_filler(Filler,Kind,KBA1,KBA).
collect_class_expr(hasValue(Prop,Val),KBA0,KBA) :-
  value_kind(Val,Kind),
  collect_property_expr(Prop,Kind,KBA0,KBA1),
  ( Kind = data -> collect_assertion_object(Val,data,KBA1,KBA)
  ; collect_individual(Val,KBA1,KBA)
  ).
collect_class_expr(hasSelf(Prop),KBA0,KBA) :-
  collect_property_expr(Prop,object,KBA0,KBA).
collect_class_expr(minCardinality(_,Prop),KBA0,KBA) :-
  collect_property_expr(Prop,object,KBA0,KBA).
collect_class_expr(minCardinality(_,Prop,Filler),KBA0,KBA) :-
  restriction_kind(Filler,Kind),
  collect_property_expr(Prop,Kind,KBA0,KBA1),
  collect_restriction_filler(Filler,Kind,KBA1,KBA).
collect_class_expr(maxCardinality(_,Prop),KBA0,KBA) :-
  collect_property_expr(Prop,object,KBA0,KBA).
collect_class_expr(maxCardinality(_,Prop,Filler),KBA0,KBA) :-
  restriction_kind(Filler,Kind),
  collect_property_expr(Prop,Kind,KBA0,KBA1),
  collect_restriction_filler(Filler,Kind,KBA1,KBA).
collect_class_expr(exactCardinality(_,Prop),KBA0,KBA) :-
  collect_property_expr(Prop,object,KBA0,KBA).
collect_class_expr(exactCardinality(_,Prop,Filler),KBA0,KBA) :-
  restriction_kind(Filler,Kind),
  collect_property_expr(Prop,Kind,KBA0,KBA1),
  collect_restriction_filler(Filler,Kind,KBA1,KBA).
collect_class_expr(Expr,KBA0,KBA) :-
  Expr =.. [_|Args],
  collect_class_args(Args,KBA0,KBA).

collect_class_args([],KBA,KBA).
collect_class_args([H|T],KBA0,KBA) :-
  collect_class_expr(H,KBA0,KBA1),
  collect_class_args(T,KBA1,KBA).

collect_property_expr(Expr,_Kind,KBA,KBA) :- var(Expr), !.
collect_property_expr(Expr,_,KBA,KBA) :- number(Expr), !.
collect_property_expr('',_,KBA,KBA) :- !.
collect_property_expr(Expr,Kind,KBA0,KBA) :-
  is_list(Expr), !,
  collect_property_list_items(Expr,Kind,KBA0,KBA).
collect_property_expr(inverseOf(P),Kind,KBA0,KBA) :-
  collect_property_expr(P,Kind,KBA0,KBA).
collect_property_expr(propertyChain(List),Kind,KBA0,KBA) :-
  collect_property_list(List,Kind,KBA0,KBA).
collect_property_expr(annotationProperty(Prop),_,KBA0,KBA) :-
  add_property_entity(annotation,Prop,KBA0,KBA).
collect_property_expr(Expr,Kind,KBA0,KBA) :-
  atom(Expr), !,
  select_property_kind(Kind,Expr,KBA0,FinalKind),
  add_property_entity(FinalKind,Expr,KBA0,KBA).
collect_property_expr(Expr,Kind,KBA0,KBA) :-
  Expr =.. [_|Args],
  collect_property_args(Args,Kind,KBA0,KBA).

collect_property_args([],_,KBA,KBA).
collect_property_args([H|T],Kind,KBA0,KBA) :-
  collect_property_expr(H,Kind,KBA0,KBA1),
  collect_property_args(T,Kind,KBA1,KBA).

select_property_kind(any,Expr,KBA,Kind) :-
  known_property_kind(Expr,KBA,Kind), !.
select_property_kind(any,_Expr,_KBA,object) :- !.
select_property_kind(Kind,_Expr,_KBA,Kind).

known_property_kind(Expr,KBA,annotation) :-
  atom(Expr),
  memberchk(Expr,KBA.annotationProperty).
known_property_kind(Expr,KBA,data) :-
  atom(Expr),
  memberchk(Expr,KBA.dataProperty).
known_property_kind(Expr,KBA,object) :-
  atom(Expr),
  memberchk(Expr,KBA.objectProperty).

collect_individual(Ind,KBA,KBA) :- var(Ind), !.
collect_individual(Ind,KBA,KBA) :- is_literal_term(Ind), !.
collect_individual(Ind,KBA,KBA) :- number(Ind), !.
collect_individual('',KBA,KBA) :- !.
collect_individual(Ind,KBA0,KBA) :-
  atom(Ind), !,
  add_entity(individual,Ind,KBA0,KBA).
collect_individual(Ind,KBA0,KBA) :-
  Ind =.. [_|Args],
  collect_individual_args(Args,KBA0,KBA).

collect_individual_args([],KBA,KBA).
collect_individual_args([H|T],KBA0,KBA) :-
  collect_individual(H,KBA0,KBA1),
  collect_individual_args(T,KBA1,KBA).

collect_assertion_object(Value,data,KBA0,KBA) :-
  ( Value = literal(type(DT,_)) -> add_entity(datatype,DT,KBA0,KBA)
  ; Value = literal(type(_,DT)) -> add_entity(datatype,DT,KBA0,KBA)
  ; Value = literal(lang(_,_)) -> KBA = KBA0
  ; Value = literal(_) -> KBA = KBA0
  ; Value = literal(_,_ ) -> KBA = KBA0
  ; Value = literal(_,_,_) -> KBA = KBA0
  ; maybe_datatype_iri(Value) -> add_entity(datatype,Value,KBA0,KBA)
  ; number(Value) -> KBA = KBA0
  ; add_entity(datatype,Value,KBA0,KBA)
  ).
collect_assertion_object(Value,_Kind,KBA0,KBA) :-
  collect_individual(Value,KBA0,KBA).

collect_annotation_target(Target,KBA0,KBA) :-
  ( compound(Target) -> collect_axiom_entities(Target,KBA0,KBA)
  ; annotation_target_type(Target,KBA0,Type),
    add_annotation_target(Type,Target,KBA0,KBA)
  ).

annotation_target_type(Target,KBA,property(Kind)) :-
  known_property_kind(Target,KBA,Kind), !.
annotation_target_type(Target,KBA,individual) :-
  atom(Target),
  memberchk(Target,KBA.individual), !.
annotation_target_type(_,_,class).

add_annotation_target(property(Kind),Target,KBA0,KBA) :-
  add_property_entity(Kind,Target,KBA0,KBA).
add_annotation_target(Type,Target,KBA0,KBA) :-
  add_entity(Type,Target,KBA0,KBA).

collect_annotation_value(Value,KBA0,KBA) :-
  ( compound(Value) -> collect_axiom_entities(Value,KBA0,KBA)
  ; KBA = KBA0
  ).

collect_range_target(Range,data,KBA0,KBA) :-
  ( Range = datatypeRestriction(DT,_) -> add_entity(datatype,DT,KBA0,KBA)
  ; atom(Range) -> add_entity(datatype,Range,KBA0,KBA)
  ; KBA = KBA0
  ).
collect_range_target(Range,_Kind,KBA0,KBA) :-
  collect_class_expr(Range,KBA0,KBA).

range_property_kind(Prop,Range,KBA,Kind) :-
  ( known_property_kind(Prop,KBA,data) -> Kind = data
  ; is_datatype_term(Range) -> Kind = data
  ; Kind = object
  ).

assertion_property_kind(Prop,Obj,KBA,Kind) :-
  ( known_property_kind(Prop,KBA,data) -> Kind = data
  ; is_datatype_term(Obj) -> Kind = data
  ; Kind = object
  ).

restriction_kind(Filler,data) :-
  is_datatype_term(Filler), !.
restriction_kind(_,object).

value_kind(Value,data) :-
  is_datatype_term(Value), !.
value_kind(_,object).

collect_restriction_filler(Filler,data,KBA0,KBA) :-
  collect_range_target(Filler,data,KBA0,KBA).
collect_restriction_filler(Filler,object,KBA0,KBA) :-
  collect_class_expr(Filler,KBA0,KBA).

add_property_entity(annotation,Value,KBA0,KBA) :-
  add_entity(annotationProperty,Value,KBA0,KBA).
add_property_entity(data,Value,KBA0,KBA) :-
  add_entity(dataProperty,Value,KBA0,KBA).
add_property_entity(object,Value,KBA0,KBA) :-
  add_entity(objectProperty,Value,KBA0,KBA).

add_entity(_Type,Value,KBA,KBA) :- var(Value), !.
add_entity(_Type,Value,KBA,KBA) :- Value == '', !.
add_entity(_Type,Value,KBA,KBA) :- number(Value), !.
add_entity(Type,Value,KBA0,KBA) :-
  atom(Value),
  get_dict(Type,KBA0,List),
  ( memberchk(Value,List) -> KBA = KBA0
  ; KBA = KBA0.put(Type,[Value|List])
  ).
add_entity(_Type,_Value,KBA,KBA).

maybe_datatype_iri(Value) :-
  atom(Value),
  ( sub_atom(Value,_,_,_,'XMLSchema#')
  ; sub_atom(Value,0,_,_,'xsd:')
  ; sub_atom(Value,_,_,_,'Datatype')
  ; sub_atom(Value,_,_,_,'Literal')
  ).

is_literal_term(literal(_)).
is_literal_term(literal(_,_)).
is_literal_term(literal(_,_,_)).

is_datatype_term(Term) :-
  is_literal_term(Term), !.
is_datatype_term(Term) :-
  number(Term), !.
is_datatype_term(datatypeRestriction(_,_)) :- !.
is_datatype_term(Term) :-
  atom(Term),
  maybe_datatype_iri(Term).


:- multifile trill:add_axioms/1.
trill:add_axioms(M:Axioms) :-
    must_be(list, Axioms),
    concurrent_maplist(add_axiom(M), Axioms).


:- multifile trill:remove_axiom/1.
trill:remove_axiom(M:Axiom) :-
    retractall(M:adb(Axiom)).

remove_axiom(M,Axiom) :- trill:remove_axiom(M:Axiom).


:- multifile trill:remove_axioms/1.
trill:remove_axioms(M:Axioms) :-
    must_be(list, Axioms),
    concurrent_maplist(remove_axiom(M), Axioms).


:- multifile trill:is_axiom/1.
/**
 * is_axiom(?Axiom:string) is det
 *
 * This predicate unifies Axiom with one of the possible type of axioms managed by TRILL.
 */
trill:is_axiom(subClassOf(_,_)).
trill:is_axiom(equivalentClasses(_)).
trill:is_axiom(disjointClasses(_)).
trill:is_axiom(subPropertyOf(_,_)).
trill:is_axiom(equivalentProperties(_)).
trill:is_axiom(propertyDomain(_,_)).
trill:is_axiom(propertyRange(_,_)).
trill:is_axiom(transitiveProperty(_)).
trill:is_axiom(functionalProperty(_)).
trill:is_axiom(inverseProperties(_,_)).
trill:is_axiom(symmetricProperty(_)).
trill:is_axiom(sameIndividual(_)).
trill:is_axiom(differentIndividuals(_)).
trill:is_axiom(classAssertion(_,_)).
trill:is_axiom(propertyAssertion(_,_,_)).
trill:is_axiom(annotationAssertion(_,_,_)).


/********************************
  AXIOMS SEARCH
*********************************/

:- multifile ontology_parser:get_axiom_subClassOf/3,
             ontology_parser:get_axiom_subPropertyOf/3,
             ontology_parser:get_axiom_equivalentClasses/2, ontology_parser:get_axiom_differentIndividuals/2,
             ontology_parser:get_axiom_sameIndividual/2, ontology_parser:get_axiom_propertyAssertion/4,
             ontology_parser:get_axiom_classAssertion/3, ontology_parser:get_axiom_propertyRange/3,
             ontology_parser:get_axiom_propertyDomain/3, ontology_parser:get_axiom_disjointClasses/2,
             ontology_parser:get_axiom_disjointUnion/3, ontology_parser:get_axiom_transitiveProperty/2,
             ontology_parser:get_axiom_symmetricProperty/2, ontology_parser:get_axiom_inverseProperties/3,
             ontology_parser:get_axiom_equivalentProperties/2, ontology_parser:get_axiom_annotationAssertion/4.

ontology_parser:get_axiom_subClassOf(M,A,B):-
  M:adb(subClassOf(A,B)).

ontology_parser:get_axiom_subPropertyOf(M,R,S):-
  M:adb(subPropertyOf(R,S)).

ontology_parser:get_axiom_equivalentClasses(M,L):-
  M:adb(equivalentClasses(L)).

ontology_parser:get_axiom_differentIndividuals(M,SI):-
  M:adb(differentIndividuals(SI)).

ontology_parser:get_axiom_sameIndividual(M,SI):-
  M:adb(sameIndividual(SI)).

ontology_parser:get_axiom_propertyAssertion(M,P,S,O):-
  M:adb(propertyAssertion(P,S,O)).

ontology_parser:get_axiom_classAssertion(M,C,I):-
  M:adb(classAssertion(C,I)).

ontology_parser:get_axiom_propertyRange(M,P,D):-
  M:adb(propertyRange(P,D)).

ontology_parser:get_axiom_propertyDomain(M,P,D):-
  M:adb(propertyDomain(P,D)).

ontology_parser:get_axiom_disjointClasses(M,L):-
  M:adb(disjointClasses(L)).

ontology_parser:get_axiom_disjointUnion(M,C,L):-
  M:adb(disjointUnion(C,L)).

ontology_parser:get_axiom_transitiveProperty(M,P):-
  M:adb(transitiveProperty(P)).

ontology_parser:get_axiom_functionalProperty(M,P):-
  M:adb(functionalProperty(P)).

ontology_parser:get_axiom_symmetricProperty(M,P):-
  M:adb(symmetricProperty(P)).

ontology_parser:get_axiom_inverseProperties(M,P,S):-
  M:adb(inverseProperties(P,S)).

ontology_parser:get_axiom_equivalentProperties(M,L):-
  M:adb(equivalentProperties(L)).

ontology_parser:get_axiom_annotationAssertion(M,AnnIRI,Ax,AnnVal):-
  M:adb(annotationAssertion(AnnIRI,Ax,AnnVal)).


/********************************
  CLASSES, PREDICATES AND
  INDIVIDUALS MANAGEMENT
*********************************/
%:- multifile ontology_parser:get_classes_list/2.
%ontology_parser:get_classes_list(M,Classes):-
%  M:kb_atom(KBA),
%  Classes=KBA.class.


/********************************
  PREFIXES MANAGEMENT
*********************************/

% Get the KB's prefixes contained into ns4query
% We store prefixes as kb_prefix/2 and expose them through kb_prefixes/1
:- multifile trill:kb_prefixes/1.
trill:kb_prefixes(M:Pairs) :-
  findall(S=IRI, M:kb_prefix(S, IRI), Pairs).


:- multifile trill:add_kb_prefix/2.
trill:add_kb_prefix(M:Short, Long) :-
  must_be(atom, Short), must_be(atom, Long),
  retractall(M:kb_prefix(Short, _)),
  assertz(M:kb_prefix(Short, Long)).


% Adds a list of kb prefixes into ns4query
:- multifile trill:add_kb_prefixes/1.
trill:add_kb_prefixes(M:Pairs) :-
  must_be(list, Pairs),
  add_kb_prefix_pairs(M, Pairs).

add_kb_prefix_pairs(_, []).
add_kb_prefix_pairs(M, [Short=Long|Rest]) :-
  trill:add_kb_prefix(M:Short, Long),
  add_kb_prefix_pairs(M, Rest).


/********************************
  CONNECTED INDIVIDUALS (PARALLEL BFS)
*********************************/

:- multifile scan_connected_individuals/3.
scan_connected_individuals(M, Seeds, Connected) :-
  must_be(list, Seeds),
  maplist(must_be(atom), Seeds),
  include(valid_individual_atom, Seeds, AtomSeeds),
  list_to_ord_set(AtomSeeds, SeedSet),
  ( SeedSet == [] ->
      Connected = []
  ; bfs_connected_component(M, SeedSet, SeedSet, Connected)
  ).


bfs_connected_component(_M, Visited, [], Visited) :- !.
bfs_connected_component(M, Visited, Frontier, Connected) :-
  parallel_frontier_neighbors(M, Frontier, Visited, FreshNeighbors),
  ( FreshNeighbors == [] ->
      Connected = Visited
  ; ord_union(Visited, FreshNeighbors, UpdatedVisited),
    bfs_connected_component(M, UpdatedVisited, FreshNeighbors, Connected)
  ).

parallel_frontier_neighbors(_M, [], _Visited, []) :- !.
parallel_frontier_neighbors(M, Frontier, Visited, FreshNeighbors) :-
  concurrent_maplist(frontier_neighbors(M, Visited), Frontier, Nested),
  append(Nested, FlatNeighbors),
  list_to_ord_set(FlatNeighbors, NeighborSet),
  ord_subtract(NeighborSet, Visited, FreshNeighbors).

frontier_neighbors(M, Visited, Node, FreshNeighbors) :-
  parallel_collect_neighbors(M, Node, RawNeighbors),
  exclude({Visited}/[Candidate]>>ord_memberchk(Candidate, Visited), RawNeighbors, Filtered),
  sort(Filtered, FreshNeighbors).

parallel_collect_neighbors(M, Node, AllNeighbors) :-
  concurrent(2,
            [collect_subject_neighbors(M, Node, SubjectNeighbors),
             collect_object_neighbors(M, Node, ObjectNeighbors)],
            []),
  append(SubjectNeighbors, ObjectNeighbors, AllNeighbors).

collect_subject_neighbors(M, Node, Neighbors) :-
  findall(Neighbor,
          neighbor_from_subject(M, Node, Neighbor),
          Neighbors).

collect_object_neighbors(M, Node, Neighbors) :-
  findall(Neighbor,
          neighbor_from_object(M, Node, Neighbor),
          Neighbors).

neighbor_from_subject(M, Node, Neighbor) :-
  kb_property_assertion(M, _P, Node, Object),
  normalize_neighbor(Object, Neighbor),
  Neighbor \== Node.

neighbor_from_object(M, Node, Neighbor) :-
  kb_property_assertion(M, _P, Subject, Node),
  normalize_neighbor(Subject, Neighbor),
  Neighbor \== Node.

kb_property_assertion(M, P, S, O) :-
  M:adb(propertyAssertion(P,S,O)).
kb_property_assertion(M, P, S, O) :-
  predicate_property(M:propertyAssertion(_,_,_), defined),
  M:propertyAssertion(P,S,O).

normalize_neighbor(Value, Value) :-
  valid_individual_atom(Value).

valid_individual_atom(Value) :-
  atom(Value),
  Value \== ''.



%=======================================
:- multifile trill:remove_kb_prefix/2.
trill:remove_kb_prefix(M:Short, Long) :-
  retractall(M:kb_prefix(Short, Long)).

:- multifile trill:remove_kb_prefix/1.
trill:remove_kb_prefix(M:NameOrIRI) :-
  (   retractall(M:kb_prefix(NameOrIRI, _))
  ;   retractall(M:kb_prefix(_, NameOrIRI))
  ), !.



% -------- namespace expansion helpers ---

/**
 * expand_all_ns(++Module:string,++Args:list,++NSList:list,--ExpandedArgs:list) is det
 *
 * The predicate takes as input a list containing strings and expands these strings
 * using the list of prefixes. Finally, it returns the list of expanded strings.
 * It adds names in Args to the list of known elements.
 */
expand_all_ns(M, Args, NSList, Expanded) :-
  % NSList is a list of Short=IRI pairs (atoms)
  must_be(list, Args),
  must_be(list, NSList),
  maplist(ns_expand_term(M,NSList), Args, Expanded).

ns_expand_term(M,NSList, TermIn, TermOut) :-
  ( atomic(TermIn)
    ->  ns_expand_atomic(NSList, TermIn, TermOut)
    ;   
    ( is_list(TermIn) -> 
        maplist(ns_expand_term(M,NSList), TermIn, TermOut)
        ;
        ns_expand_functor(M,NSList, TermIn, TermOut)
    )      
  ).

ns_expand_functor(M,NSList, TermIn, TermOut) :-
  TermIn =.. [F|As],
  add_rule_from_functor(M,F),
  ( (cardinality_functor(F)) ->
    ( As = [C|Entities],
      number(C), % Otherwise fail
      maplist(ns_expand_term(M,NSList), Entities, AsE),
      TermOut =.. [F,C|AsE]
    )
    ;
    ( TermIn=literal(_) -> 
      TermOut=TermIn
      ;
      ( maplist(ns_expand_term(M,NSList), As, AsE),
        TermOut =.. [F|AsE]
      )
    )
  ),!.

ns_expand_atomic(NSList, A, Out) :-
  expand_atomic_default_operation(Op),
  ns_expand_atomic(NSList, A, Out,Op).

%%       uri_split(+URI,-Namespace,-Term,+Split_Char) is det
%
%       Splits a URI into the Namespace and the Term parts
%       separated by the Split_Char character.
%       It supposes URI = concat(Namespace,Split_Char,Term)

uri_split(URI,Namespace,Term,Split_Char) :-
	sub_atom(URI,Start,_,After,Split_Char),
	sub_atom(URI,0,Start,_,Namespace),
	Start1 is Start + 1,
	sub_atom(URI,Start1,After,_,Term),!.

ns_expand_atomic(NSList,NS_URL,Full_URL,reduce):-
  atomic(NS_URL),
  NS_URL \= literal(_),
  uri_split(NS_URL,Long_NS_T,Term, '#'),!, % full URI or entity with #
  atomic_list_concat([Long_NS_T, '#'], Long_NS),
  ( member(Short_NS=Long_NS,NSList) -> % prefix found
    ( dif([],Short_NS) -> 
      concat_atom([Short_NS,':',Term],Full_URL) % specific prefix
      ;
      concat_atom([':',Term],Full_URL) % default prefix
    )
    ;
    ( sub_atom(Long_NS_T,_,_,_,':') -> % entity is full URI
        Full_URL=NS_URL % impossible to reduce
        ;
        concat_atom([':',Term],Full_URL) % not full URI, add ':'
    )
  ),!.

ns_expand_atomic(_NSList,NS_URL,IRIOut,reduce):- 
  atomic(NS_URL),
  NS_URL \= literal(_),
  \+ sub_atom(NS_URL,_,_,_,':'),!, % entity without ':'
  atomic_list_concat([':', NS_URL], IRIOut). % Add ':'

ns_expand_atomic(NSList,NS_URL,Full_URL,reduce):- 
  atomic(NS_URL),
  (
    (member(''=Long_NS,NSList), sub_string(NS_URL,_,Start,Length,Long_NS))
    ->
    (sub_atom(NS_URL,Start,Length,_,Term),concat_atom([':',Term],Full_URL))
    ;
    Full_URL=NS_URL
  ),!. % entity with ':' -> do nothing

ns_expand_atomic(NSList,NS_URL,Full_URL,expand):-
  atomic(NS_URL),
  NS_URL \= literal(_),
  uri_split(NS_URL,Short_NS,Term, ':'),!, % prefix:term, :term or full URI
  ( dif(Short_NS,'') ->
    ( member(Short_NS=Long_NS,NSList) -> % prefix:term
      concat_atom([Long_NS,Term],Full_URL)
      ;
      Full_URL = NS_URL % full URI or unknowkn prefix
    )
    ;
    ( member(''=Long_NS,NSList) -> % default prefix or unexpandable
      concat_atom([Long_NS,NS_URL],Full_URL) % default prefix
      ;
      Full_URL = NS_URL % unexpandable
    )
  ),!.

ns_expand_atomic(_NSList,IRI,IRIOut,expand):- % without :
  atomic(IRI),
  atomic_list_concat([':', IRI], IRIOut).


/********************************
  LOAD KNOWLEDGE BASE
*********************************/
:- multifile trill:load_kb/1, trill:load_owl_kb/1, trill:load_owl_kb_from_string/1.
/**
 * load_kb(++FileName:atom) is det
 *
 * Parse ontology from a file using Java OWL API and assert axioms/prefixes. 
 * 
 */
trill:load_kb(File) :-
  get_module(M),
  must_be(atom, File),
  %retractall(M:adb(_)),
  %retractall(M:kb_prefix(_, _)),
  parse_file(File,JRes),
  bridge_assert_result(M,JRes).


/**
 * load_owl_kb(++FileName:atom) is det
 *
 * The predicate performs the same operations as load_kb.
 * Maintained for compatibility with internal_parser.
 */
trill:load_owl_kb(FileName):-
  trill:load_kb(FileName).


/**
 * load_owl_kb_from_string(++KB:atom) is det
 *
 * Parse ontology from a string (RDF/XML, Turtle, OWL Functional, …) via OWL API. 
 * The knowledge base can be defined in every OWL format known by Java OWL API.
 */
trill:load_owl_kb_from_string(String):-
  get_module(M),
  must_be(atom, String),
  %retractall(M:adb(_)),
  %retractall(M:kb_prefix(_, _)),
  parse_string(String,JRes),
  bridge_assert_result(M, JRes).


% -------- bridge result decoding -----------------------------------

% JRes is an instance of it.unife.ml.probowlapi.trill.TrillTest1$Result
% with public fields: axioms (String[]), prefixes (String[] of "short=IRI")
bridge_assert_result(M,JRes) :-
    % prefixes
    jpl_get(JRes, prefixes, JPrefArray),
    jpl_array_to_list(JPrefArray, PrefListJava),
    maplist(assert_prefix_from_java(M), PrefListJava),
    % axioms
    jpl_get(JRes, axioms, JAxiomArray),
    jpl_array_to_list(JAxiomArray, AxiomStrings),
    maplist(assert_axiom_from_string(M), AxiomStrings),
    % entity
    jpl_get(JRes, classes, JClassArray),
    jpl_array_to_list(JClassArray, ClassStrings),
    concurrent_maplist(atom_to_term,ClassStrings,ClassStringsT,_),
    jpl_get(JRes, properties, JPropArray),
    jpl_array_to_list(JPropArray, PropStrings),
    concurrent_maplist(atom_to_term,PropStrings,PropStringsT,_),
    jpl_get(JRes, individuals, JIndArray),
    jpl_array_to_list(JIndArray, IndStrings),
    concurrent_maplist(atom_to_term,IndStrings,IndStringsT,_),
    jpl_get(JRes, annotationProperty, JAnPropArray),
    jpl_array_to_list(JAnPropArray, AnPropStrings),
    concurrent_maplist(atom_to_term,AnPropStrings,AnPropStringsT,_),
    jpl_get(JRes, dataProperty, JDataPropArray),
    jpl_array_to_list(JDataPropArray, DataPropStrings),
    concurrent_maplist(atom_to_term,DataPropStrings,DataPropStringsT,_),
    jpl_get(JRes, datatype, JDTArray),
    jpl_array_to_list(JDTArray, DTStrings),
    concurrent_maplist(atom_to_term,DTStrings,DTStringsT,_),
    assert(M:kb_atom(kbatoms{annotationProperty:AnPropStringsT,class:ClassStringsT,dataProperty:DataPropStringsT,datatype:DTStringsT,individual:IndStringsT,objectProperty:PropStringsT})).

assert_prefix_from_java(M,JStr) :-
    %jpl_call(JStr, 'toString', [], S), % ensure an atom/string
    atom_string(A, JStr),
    (   sub_atom(A, B, 1, _, '=')
    ->  sub_atom(A, 0, B, _, Short),
        succ(B, C0), sub_atom(A, C0, _, 0, IRI),
        trill:add_kb_prefix(M:Short, IRI)
    ;   true
    ).

assert_axiom_from_string(M,JStr) :-
    %jpl_call(JStr, 'toString', [], S),
    atom_string(A, JStr),
    % turn the textual TRILL term into a real Prolog term and assert it
    atom_to_term(A, Term, _Bindings),
    trill:add_axiom(M:Term).


/********************************
  CHECK QUERY ARGS
*********************************/ 

:- multifile ontology_parser:check_query_args_1/5.
ontology_parser:check_query_args_1(_,_,[],[],[]).

ontology_parser:check_query_args_1(M,[ATH|ATT],[H|T],[HEx|TEx],NotEx):-
  check_query_args_2(M,[ATH],[H],[HEx]),!,
  ontology_parser:check_query_args_1(M,ATT,T,TEx,NotEx).

ontology_parser:check_query_args_1(M,[_|ATT],[H|T],TEx,[H|NotEx]):-
  ontology_parser:check_query_args_1(M,ATT,T,TEx,NotEx).

% expands query arguments using prefixes and checks their existence in the kb
check_query_args_2(M,AT,L,LEx) :-
  trill:kb_prefixes(M:NSList),
  expand_all_ns(M,L,NSList,LEx), %from internal_parser module
  check_query_args_presence(M,AT,LEx).

check_query_args_presence(_M,_AT,[]):-!.

check_query_args_presence(M,[class|ATT],['http://www.w3.org/2002/07/owl#Thing'|T]) :-
  check_query_args_presence(M,ATT,T).

check_query_args_presence(M,[AT|ATT],[H|T]) :-
  nonvar(H),
  atomic(H),!,
  find_atom_in_axioms(M,AT,H),%!,
  check_query_args_presence(M,ATT,T).

check_query_args_presence(M,[AT|ATT],[H|T]) :-
  nonvar(H),
  \+ atomic(H),!,
  H =.. [CE|L],
  flatten(L,L1),
  from_expression_to_args_type(CE,AT,L1,ATs),
  check_query_args_presence(M,ATs,L1),
  check_query_args_presence(M,ATT,T).

/*
check_query_args_presence(M,[_|T]):-
  check_query_args_presence(M,T).
*/

% looks for presence of atoms in kb's axioms
find_atom_in_axioms(M,class,H):-
  M:kb_atom(L1),
  ( member(H,L1.class) ),!.

find_atom_in_axioms(M,ind,H):-
  M:kb_atom(L1),
  ( member(H,L1.individual) ; member(H,L1.datatype) ),!.

find_atom_in_axioms(M,prop,H):-
  M:kb_atom(L1),
  ( member(H,L1.objectProperty) ; member(H,L1.dataProperty) ; member(H,L1.annotationProperty) ),!.

find_atom_in_axioms(_,num,H):-
  integer(H),!.

from_expression_to_args_type(complementOf,class,_,[class]) :- !.
from_expression_to_args_type(someValuesFrom,class,_,[prop,class]) :- !.
from_expression_to_args_type(allValuesFrom,class,_,[prop,class]) :- !.
from_expression_to_args_type(hasValue,class,_,[prop,ind]) :- !.
from_expression_to_args_type(hasSelf,class,_,[prop]) :- !.
from_expression_to_args_type(minCardinality,class,[_,_,_],[num,prop,class]) :- !.
from_expression_to_args_type(minCardinality,class,[_,_],[num,prop]) :- !.
from_expression_to_args_type(maxCardinality,class,[_,_,_],[num,prop,class]) :- !.
from_expression_to_args_type(maxCardinality,class,[_,_],[num,prop]) :- !.
from_expression_to_args_type(exactCardinality,class,[_,_,_],[num,prop,class]) :- !.
from_expression_to_args_type(exactCardinality,class,[_,_],[num,prop]) :- !.
from_expression_to_args_type(inverseOf,prop,_,[prop]) :- !.
from_expression_to_args_type(ExprList,AT,L1,ATs):-
  is_expr_list(ExprList,AT,ListType),!,
  create_list(ListType,L1,ATs).

is_expr_list(intersectionOf,class,class).
is_expr_list(unionOf,class,class).
is_expr_list(oneOf,class,ind).
is_expr_list(propertyChain,prop,prop).

create_list([],_,[]).

create_list([_|T],AT,[AT|ATT]):-
  create_list(T,AT,ATT).


% ========================================

/********************************
  PARSER MANAGEMENT
*********************************/ 

:- multifile ontology_parser:clean_up_parser/1.
ontology_parser:clean_up_parser(M):-
  M:(dynamic adb/1, kb_atom/1, kb_prefix/2,rule/1),
  forall(trill:axiom(M:A),retractall(M:adb(A))),
  retractall(M:kb_atom(_)).

:- multifile ontology_parser:set_up_parser/1.
ontology_parser:set_up_parser(M):-
  M:(dynamic adb/1, kb_atom/1, kb_prefix/2,rule/1),
  init_java_bridge,
  trill:add_kb_prefixes(M:[('disponte'='http://ai.unife.it/disponte#'),('owl'='http://www.w3.org/2002/07/owl#')]).


/* ************************************** */



/*****************************/

/************************************
 * 
 * INTERNAL PARSER IMPLEMENTATION
 * 
 * In the following there is the
 * implementation of the actual 
 * parser, based on Thea2 lib.
 * 
 ************************************/

/******************************/


/****************************************
  UTILITY
  ****************************************/
init_java_bridge:-
    jpl_get_actual_jvm_opts(_),!.
init_java_bridge :-
  % Point to your assembled JAR (jar-with-dependencies)
  jar_file(JarFile),
  absolute_file_name(library(JarFile), NewFolder, [access(read)]),
  
  % Get existing CLASSPATH env var (not the JVM one, but often aligns)
  (   getenv('CLASSPATH', ExistingCP)
  ->  true
  ;   ExistingCP = ''
  ),

  % On Windows, use ; separator
  atomic_list_concat([ExistingCP, NewFolder], ';', FullCP),
  atomic_list_concat(['-Djava.class.path=', FullCP], JVMOpt),

  % Set JVM options
  jpl_set_default_jvm_opts(['-Xms128m','-Xmx1g', JVMOpt]).


close_java_vm:-
  jpl_call('java.lang.System', exit, [0], _).


parse_file(File,JRes):-
  wrapper_class(WrapperClass),
  jpl_call(WrapperClass,
          'parseOntologyFile',
          [File],
          JRes).

parse_string(String,JRes):-
  wrapper_class(WrapperClass),
  jpl_call(WrapperClass,
          'parseOntologyString',
          [String],
          JRes).

/****************************************
  AXIOMS
  ****************************************/

% concept descriptions (accepted as subterms inside axioms)
is_concept(T) :-
    (   atomic(T)
    ;   T = someValuesFrom(_,_)
    ;   T = allValuesFrom(_,_)
    ;   T = unionOf(_)
    ;   T = intersectionOf(_)
    ;   T = exactCardinality(_, _)
    ;   T = exactCardinality(_, _, _)
    ;   T = maxCardinality(_, _)
    ;   T = maxCardinality(_, _, _)
    ;   T = minCardinality(_, _)
    ;   T = minCardinality(_, _, _)
    ;   T = complementOf(_)
    ;   T = oneOf(_)
    ), !.

% ----------------------------


/* ************************************** */


/*****************************/

/************************************
 * 
 * TERM EXPANSION
 * 
 * 
 ************************************/

/******************************/

user:term_expansion(owl_rdf(String),[]):-
  trill:load_owl_kb_from_string(String),!.

user:term_expansion(TRILLAxiom,[]):-
  get_module(M),
  add_axiom(M,TRILLAxiom).

