/** <module> ontology_parser_test1

TRILL translation utilities backed by OWL API (via JPL).

## Overview

This module is an alternative implementation of the ontology_parser interface
that uses the Java OWL API via JPL. It is similar to wrapper_parser but provides
a slightly different API structure.

## Purpose

This module serves as a test/alternative implementation for the parser system.
It demonstrates how to integrate the Java OWL API with TRILL's axiom storage
format.

## Features

- Parses OWL ontologies using Java OWL API
- Stores axioms as `adb/1` facts (same as wrapper_parser)
- Provides full prefix management
- Supports both file and string-based ontology loading
- Exports getter predicates for all axiom types

## Requirements

- Java 11+
- JPL 7.6.1+
- prob-owlapi-2.0.8.jar with TrillTest1 class

## Main Predicates

### Loading
- load_kb/1: Load from Prolog file
- load_owl_kb/1: Load from OWL file
- load_owl_kb_from_string/1: Load from string

### Prefix Management
- kb_prefixes/1: Get all registered prefixes
- add_kb_prefix/2: Register a prefix
- remove_kb_prefix/1, remove_kb_prefix/2: Remove prefix

### Axiom Management
- axiom/1: Query axioms
- add_axiom/1, add_axioms/1: Add axiom(s)
- remove_axiom/1, remove_axioms/1: Remove axiom(s)

### Query Validation
- check_query_args/4: Validate and expand query arguments

### Axiom Getters
- get_axiom_subClassOf/3
- get_axiom_equivalentClasses/2
- get_axiom_classAssertion/3
- get_axiom_propertyAssertion/4
- (and many more...)

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(ontology_parser_test1,
          [ load_kb/1,
            load_owl_kb/1,
            load_owl_kb_from_string/1,
            % ====
            % expand_all_ns/4,
            % expand_all_ns/5,
            % ====
            axiom/1,
            % multifile API used by trill.pl
            kb_prefixes/1,
            add_kb_prefix/2,
            add_kb_prefixes/1,
            remove_kb_prefix/1,
            remove_kb_prefix/2,
            add_axiom/1,
            add_axioms/1,
            remove_axiom/1,
            remove_axioms/1,
            %---------
            check_query_args/4,
            set_up_parser/1, clean_up_parser/1,
            get_axiom_subClassOf/3, get_axiom_equivalentClasses/2,
            get_axiom_disjointClasses/2, get_axiom_disjointUnion/3,
            get_axiom_subPropertyOf/3, get_axiom_equivalentProperties/2,
            get_axiom_differentIndividuals/2, get_axiom_sameIndividual/2,
            get_axiom_classAssertion/3, get_axiom_propertyAssertion/4,
            get_axiom_propertyRange/3, get_axiom_propertyDomain/3, 
            get_axiom_transitiveProperty/2,
            get_axiom_symmetricProperty/2, get_axiom_inverseProperties/3,
            get_axiom_annotationAssertion/4,
            %---------
            get_classes_list/2
          ]).

:- use_module(library(lists)).
:- use_module(library(jpl)).             % JPL 7.x
:- use_module(library(error)).
:- use_module(library(apply)).
:- use_module(library(readutil)).

:- use_module(library(trill_utility)).


:- meta_predicate axiom(:).
:- meta_predicate kb_prefixes(:).
:- meta_predicate add_kb_prefix(:,+).
:- meta_predicate add_kb_prefixes(:).
:- meta_predicate add_axiom(:).
:- meta_predicate add_axioms(:).
:- meta_predicate remove_kb_prefix(:,+).
:- meta_predicate remove_kb_prefix(:).
:- meta_predicate remove_axiom(:).
:- meta_predicate remove_axioms(:).
:- meta_predicate load_kb(+).
:- meta_predicate load_owl_kb(+).
:- meta_predicate load_owl_kb_from_string(+).
:- meta_predicate check_query_args(+,+,+,-).
:- meta_predicate get_axiom_subClassOf(+,-,-).
:- meta_predicate get_axiom_subPropertyOf(+,-,-).
:- meta_predicate get_axiom_equivalentClasses(+,-).
:- meta_predicate get_axiom_differentIndividuals(+,-).
:- meta_predicate get_axiom_sameIndividual(+,-). 
:- meta_predicate get_axiom_propertyAssertion(+,-,-,-).
:- meta_predicate get_axiom_classAssertion(+,-,-). 
:- meta_predicate get_axiom_propertyRange(+,-,-).
:- meta_predicate get_axiom_propertyDomain(+,-,-). 
:- meta_predicate get_axiom_disjointClasses(+,-).
:- meta_predicate get_axiom_disjointUnion(+,-,-). 
:- meta_predicate get_axiom_transitiveProperty(+,-).
:- meta_predicate get_axiom_symmetricProperty(+,-). 
:- meta_predicate get_axiom_inverseProperties(+,-,-).
:- meta_predicate get_axiom_equivalentProperties(+,-). 
:- meta_predicate get_axiom_annotationAssertion(+,-,-,-).

init_java_bridge :-
    % Point to your assembled JAR (jar-with-dependencies)
    absolute_file_name(library('prob-owlapi-2.0.8.jar'), NewFolder, [access(read)]),
    
    % Get existing CLASSPATH env var (not the JVM one, but often aligns)
    (   getenv('CLASSPATH', ExistingCP)
    ->  true
    ;   ExistingCP = ''
    ),

    % On Windows, use ; separator
    atomic_list_concat([ExistingCP, NewFolder], ';', FullCP),
    atomic_list_concat(['-Djava.class.path=', FullCP], JVMOpt),

    % Set JVM options
    jpl_set_default_jvm_opts([JVMOpt]).


% -------- dynamic/multifile datastore (per module) -----------------

% We store prefixes as kb_prefix/2 and expose them through kb_prefixes/1
:- multifile  kb_prefixes/1.

% -------- public API expected by trill.pl --------------------------
% trill.pl declares these as multifile; we define them here to keep the same API
% See the header of trill.pl for the corresponding meta_predicates. 

kb_prefixes(M:Pairs) :-
    findall(S=IRI, M:kb_prefix(S, IRI), Pairs).

add_kb_prefix(M:Short, Long) :-
    must_be(atom, Short), must_be(atom, Long),
    retractall(M:kb_prefix(Short, _)),
    assertz(M:kb_prefix(Short, Long)).

add_kb_prefixes(M:Pairs) :-
    must_be(list, Pairs),
    maplist(add_kb_prefix_pair(M), Pairs).

add_kb_prefix_pair(M, Short=Long) :- add_kb_prefix(M:Short, Long).

remove_kb_prefix(M:Short, Long) :-
    retractall(M:kb_prefix(Short, Long)).

remove_kb_prefix(M:NameOrIRI) :-
    (   retractall(M:kb_prefix(NameOrIRI, _))
    ;   retractall(M:kb_prefix(_, NameOrIRI))
    ), !.

add_axiom(M:Axiom) :-
    M:adb(Axiom),!.

add_axiom(M:Axiom) :-
    is_axiom(Axiom),
    assertz(M:adb(Axiom)),
    trill:update_tabs(M,Axiom).

add_axiom(M,Axiom) :-
  is_axiom(Axiom),
  assertz(M:adb(Axiom)).

add_axioms(M:Axioms) :-
    must_be(list, Axioms),
    concurrent_maplist(add_axiom(M), Axioms).

remove_axiom(M:Axiom) :-
    retractall(M:adb(Axiom)).

remove_axiom(M,Axiom) :- remove_axiom(M:Axiom).

remove_axioms(M:Axioms) :-
    must_be(list, Axioms),
    concurrent_maplist(remove_axiom(M), Axioms).

% -------- namespace expansion helpers (used by manual and trill) ---
% These keep the interface provided previously by the Translation Utilities
% (used to expand prefixes inside atoms/lists in queries / axioms). 

expand_all_ns(M, Args, NSList, Expanded) :-
    expand_all_ns(M, Args, NSList, true, Expanded).

expand_all_ns(_M, Args, NSList, _AddName, Expanded) :-
    % NSList is a list of Short=IRI pairs (atoms)
    must_be(list, Args),
    must_be(list, NSList),
    maplist(ns_expand_term(NSList), Args, Expanded).

ns_expand_term(NSList, TermIn, TermOut) :-
    (   atomic(TermIn)
    ->  ns_expand_atomic(NSList, TermIn, TermOut)
    ;   TermIn =.. [F|As],
        maplist(ns_expand_term(NSList), As, AsE),
        % ns_expand_atomic(NSList, F, FE), % Expansion of the predicate
        % TermOut =.. [FE|AsE]
        TermOut =.. [F|AsE]
    ).

ns_expand_atomic(NSList, A, Out) :-
    (   atom(A),
        sub_atom(A, B, _, C, ':') 
        -> (  B>0, C>=0
            ->  sub_atom(A, 0, B, _, Pref),
            sub_atom(A, _, C, 0, Local),
            (   memberchk(Pref=IRI, NSList)
            ->  atomic_list_concat([IRI, Local], Out)
            ;   Out = A
            )
        ; Out = A
        )
    ;   atomic_list_concat([':', A], Out)
    ).

% -------- OWL loader entry points (Java -> Prolog) -----------------

%% load_owl(+FileName:atom) is det.
%  Parse ontology from a file using Java OWL API and assert axioms/prefixes.
load_kb(File) :-
    get_module(M),
    must_be(atom, File),
    %retractall(M:adb(_)),
    %retractall(M:kb_prefix(_, _)),
    jpl_call('it.unife.ml.probowlapi.trill.TrillTest1',
             'parseOntologyFile',
             [File],
             JRes),
    bridge_assert_result(M,JRes).

load_owl_kb(FileName):-
  load_kb(FileName).

%% load_owl_kb_from_string(+RDFOrFunctional:atom) is det.
%  Parse ontology from a string (RDF/XML, Turtle, OWL Functional, …) via OWL API.
load_owl_kb_from_string(String) :-
    get_module(M),
    must_be(atom, String),
    %retractall(M:adb(_)),
    %retractall(M:kb_prefix(_, _)),
    jpl_call('it.unife.ml.probowlapi.trill.TrillTest1',
             'parseOntologyString',
             [String],
             JRes),
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
        add_kb_prefix(M:Short, IRI)
    ;   true
    ).

assert_axiom_from_string(M,JStr) :-
    %jpl_call(JStr, 'toString', [], S),
    atom_string(A, JStr),
    % turn the textual TRILL term into a real Prolog term and assert it
    atom_to_term(A, Term, _Bindings),
    add_axiom(M:Term).

% -------- Recognized TRILL axiom functors --------------------------
% This is used by add_axiom/1 to quickly validate shape.  Keep in sync with
% TRILL syntax: subClassOf, equivalentClasses, subPropertyOf, propertyDomain,
% propertyRange, transitiveProperty, inverseProperties, symmetricProperty,
% sameIndividual, differentIndividuals, classAssertion, propertyAssertion,
% annotationAssertion, plus concept descriptions used inside axioms. 

axiom(M:A) :- M:adb(A).

is_axiom(subClassOf(_,_)).
is_axiom(equivalentClasses(_)).
is_axiom(disjointClasses(_)).
is_axiom(subPropertyOf(_,_)).
is_axiom(equivalentProperties(_)).
is_axiom(propertyDomain(_,_)).
is_axiom(propertyRange(_,_)).
is_axiom(transitiveProperty(_)).
is_axiom(inverseProperties(_,_)).
is_axiom(symmetricProperty(_)).
is_axiom(sameIndividual(_)).
is_axiom(differentIndividuals(_)).
is_axiom(classAssertion(_,_)).
is_axiom(propertyAssertion(_,_,_)).
is_axiom(annotationAssertion(_,_,_)).

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
check_query_args(M,QT,QA,QAEx):-
  from_query_type_to_args_type(QT,AT),
  check_query_args_1(M,AT,QA,QAExT,NotEx),!,
  check_query_not_existent_args(QA,QAExT,NotEx,QAEx),!.

check_query_not_existent_args(QA,QAExT,[],QAEx) :- !,
  ( length(QA,1) -> 
    QAEx = ['unsat'|QAExT]
    ;
    ( length(QA,0) -> QAEx = ['inconsistent','kb'] ; QAEx = QAExT)
  ).
check_query_not_existent_args(_QA,_QAExT,NotEx,_QAEx) :-
  print_message(warning,iri_not_exists(NotEx)),!,fail.

from_query_type_to_args_type(io,[class,ind]):- !.
from_query_type_to_args_type(pv,[prop,ind,ind]):- !.
from_query_type_to_args_type(sc,[class,class]):- !.
from_query_type_to_args_type(un,[class]):- !.
from_query_type_to_args_type(it,[]):- !.

check_query_args_1(_,_,[],[],[]).

check_query_args_1(M,[ATH|ATT],[H|T],[HEx|TEx],NotEx):-
  check_query_args_2(M,[ATH],[H],[HEx]),!,
  check_query_args_1(M,ATT,T,TEx,NotEx).

check_query_args_1(M,[_|ATT],[H|T],TEx,[H|NotEx]):-
  check_query_args_1(M,ATT,T,TEx,NotEx).

% expands query arguments using prefixes and checks their existence in the kb
check_query_args_2(M,AT,L,LEx) :-
  kb_prefixes(NSList),
  expand_all_ns(M,L,NSList,false,LEx), %from internal_parser module
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


get_classes_list(M,Classes):-
  M:kb_atom(KBA),
  Classes=KBA.class.

set_up_parser(M):-
  M:(dynamic adb/1, kb_atom/1, kb_prefix/2),
  init_java_bridge.

clean_up_parser(M):-
  M:(dynamic adb/1, kb_atom/1, kb_prefix/2),
  retractall(M:kb_atom(_)).

get_axiom_subClassOf(M,A,B):-
  M:adb(subClassOf(A,B)).

get_axiom_subPropertyOf(M,R,S):-
  M:adb(subPropertyOf(R,S)).

get_axiom_equivalentClasses(M,L):-
  M:adb(equivalentClasses(L)).

get_axiom_differentIndividuals(M,SI):-
  M:adb(differentIndividuals(SI)).

get_axiom_sameIndividual(M,SI):-
  M:adb(sameIndividual(SI)).

get_axiom_propertyAssertion(M,P,S,O):-
  M:adb(propertyAssertion(P,S,O)).

get_axiom_classAssertion(M,C,I):-
  M:adb(classAssertion(C,I)).

get_axiom_propertyRange(M,P,D):-
  M:adb(propertyRange(P,D)).

get_axiom_propertyDomain(M,P,D):-
  M:adb(propertyDomain(P,D)).

get_axiom_disjointClasses(M,L):-
  M:adb(disjointClasses(L)).

get_axiom_disjointUnion(M,C,L):-
  M:adb(disjointUnion(C,L)).

get_axiom_transitiveProperty(M,P):-
  M:adb(transitiveProperty(P)).

get_axiom_symmetricProperty(M,P):-
  M:adb(symmetricProperty(P)).

get_axiom_inverseProperties(M,P,S):-
  M:adb(inverseProperties(P,S)).

get_axiom_equivalentProperties(M,L):-
  M:adb(equivalentProperties(L)).

get_axiom_annotationAssertion(M,AnnIRI,Ax,AnnVal):-
  M:adb(annotationAssertion(AnnIRI,Ax,AnnVal)).

user:term_expansion(owl_rdf(String),[]):-
  load_owl_kb_from_string(String),!.

user:term_expansion(TRILLAxiom,[]):-
  is_axiom(TRILLAxiom),
  get_module(M),
  kb_prefixes(NSList),
  ns_expand_term(NSList, TRILLAxiom, TRILLAxiomExpanded),
  assertz(M:adb(TRILLAxiomExpanded)).

