/** <module> javaOWLAPI_parser

This module implements the ontology_parser interface using Java's OWL API
through JPL (Java-Prolog bidirectional interface).

## Overview

The javaOWLAPI_parser module provides a Java-based approach to parsing and
managing OWL ontologies. Unlike the wrapper_parser which stores axioms in
Prolog format, this parser maintains a tighter integration with the Java
OWL API for certain operations.

## Architecture

This module uses the ontology_parser multifile predicates, allowing TRILL
to switch between different parser backends. The Java side handles:
- Ontology parsing and loading
- Axiom management
- Namespace resolution

## Main Components

### Axiom Management
- axiom/1: Query axioms via classAxiom, propertyAxiom, fact, declarationAxiom
- add_axiom/1: Add axiom through Java bridge
- remove_axiom/1: Remove axiom from the KB

### Axiom Categories
- classAxiom: Class hierarchy axioms (subClassOf, equivalentClasses, etc.)
- propertyAxiom: Property axioms (subPropertyOf, propertyDomain, etc.)
- fact: ABox assertions (classAssertion, propertyAssertion)
- declarationAxiom: Entity declarations

## Notes

This parser is an alternative to the wrapper_parser and internal_parser.
It provides deeper Java integration but requires the JPL library and
prob-owlapi JAR to be properly configured.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(javaOWLAPI_parser, []).

:- use_module(library(trill_utility)).

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
% The main component of an OWL 2 ontology is a set of axioms - statements that say what is true in the domain being modeled.
% @see classAxiom/1, propertyAxiom/1, fact/1
:- multifile ontology_parser:axiom/1.

ontology_parser:axiom(M:A) :- classAxiom(M:A).
ontology_parser:axiom(M:A) :- propertyAxiom(M:A).
ontology_parser:axiom(M:hasKey(A,B)) :- M:hasKey(A,B).
ontology_parser:axiom(M:A) :- fact(M:A).
ontology_parser:axiom(M:A) :- declarationAxiom(M:A).
%axiom(annotation(A,B,C)) :-
%	annotation(A,B,C). % CJM-treat annotations as axioms

:- multifile ontology_parser:add_axiom/1.
ontology_parser:add_axiom(M:Ax):-
  assert(M:addKBName),
  %init_kb_atom(M),
  create_and_assert_axioms(M,Ax),!,
  retractall(M:addKBName),
  ontology_parser:update_tabs(M,Ax),!.

prolog:message(axiom_not_added(Ax,M)) -->
  [ 'Problems in adding axiom ~w ~w' -[Ax,M] ].

ontology_parser:add_axiom(M:Ax):-
  print_message(warning,axiom_not_added(Ax,M)).

:- multifile ontology_parser:add_axioms/1.
ontology_parser:add_axioms(_:[]).

ontology_parser:add_axioms(M:[H|T]) :-
  ontology_parser:add_axiom(M:H),
  ontology_parser:add_axioms(M:T).

:- multifile ontology_parser:remove_axiom/1.
ontology_parser:remove_axiom(M:Ax):-
  %print_message(warning,under_development),
  ( M:ns4query(NSList) -> true; NSList = []),
  expand_axiom(M,Ax,NSList,ExpAx),
  retract_axiom(M,ExpAx),
  retractall(M:owl(ExpAx,'ont')),!,
  trill:reset_query.


/*
ontology_parser:remove_axiom(M:subClassOf(C,D)):-
  print_message(warning,under_development),
  ( M:ns4query(NSList) -> true; NSList = []),
  expand_axiom(M,subClassOf(C,D),NSList,subClassOf(ExpC,ExpD)),
  remove_subClassOf(M,ExpC,ExpD),
  retract_axiom(M,subClassOf(ExpC,ExpD)),
  retractall(M:owl(subClassOf(ExpC,ExpD),'ont')),!.

ontology_parser:remove_axiom(M:Ax):-
  print_message(warning,under_development),
  ( M:ns4query(NSList) *-> true; NSList = []),
  Ax =.. [P|Args],
  ( (length(Args,1), Args = [IntArgs], is_list(IntArgs)) -> 
       ( expand_all_ns(M,IntArgs,NSList,false,ArgsExp),
         AxEx =.. [P,ArgsExp]
       )
     ;
       ( expand_all_ns(M,Args,NSList,false,ArgsExp),
         AxEx =.. [P|ArgsExp]
       )
  ),
  retract_axiom(M,AxEx),
  retractall(M:owl(AxEx,'ont')),!.
*/

:- multifile ontology_parser:remove_axioms/1.
ontology_parser:remove_axioms(_:[]):-!.

ontology_parser:remove_axioms(M:[H|T]) :-
  ontology_parser:remove_axiom(M:H),
  ontology_parser:remove_axioms(M:T).

test_and_assert(M,Ax,O):-
  (\+ M:owl(Ax,O) ->
    (assert_axiom(M,Ax,O), assert(M:owl(Ax,O)))
   ;
    true
  ).

/*
create_and_assert_axioms(M,Axiom) :-
  Axiom=..[P|Args],
  ( M:ns4query(NSList) -> true; NSList = []),
  ( (length(Args,1), Args = [IntArgs], is_list(IntArgs)) -> 
       ( expand_all_ns(M,IntArgs,NSList,ArgsExp),
         ExpAxiom =.. [P,ArgsExp]
       )
     ;
       ( expand_axiom(M,Axiom,NSList,ExpAxiom)
         %NewTRILLAxiom =.. [P|ArgsExp]
       )
  ),
  test_and_assert(M,ExpAxiom,'ont').
*/

create_and_assert_axioms(M,Axiom) :-
  ( M:ns4query(NSList) -> true; NSList = []),
  expand_axiom(M,Axiom,NSList,ExpAxiom),
  test_and_assert(M,ExpAxiom,'ont').


:- multifile ontology_parser:is_axiom/1.
/**
 * is_axiom(?Axiom:string) is det
 *
 * This predicate unifies Pred with one of the possible type of axioms managed by TRILL and 
 * by the translation module.
 */
ontology_parser:is_axiom(Axiom) :-
	functor(Axiom,Pred,Arity),
	axiompred(Pred/Arity),!.

/********************************
  AXIOMS SEARCH
*********************************/

:- multifile ontology_parser:get_axiom_subClassOf/3, ontology_parser:get_axiom_subPropertyOf/3,
             ontology_parser:get_axiom_equivalentClasses/2, ontology_parser:get_axiom_differentIndividuals/2,
             ontology_parser:get_axiom_sameIndividual/2, ontology_parser:get_axiom_propertyAssertion/4,
             ontology_parser:get_axiom_classAssertion/3, ontology_parser:get_axiom_propertyRange/3,
             ontology_parser:get_axiom_propertyDomain/3, ontology_parser:get_axiom_disjointClasses/2,
             ontology_parser:get_axiom_disjointUnion/3, ontology_parser:get_axiom_transitiveProperty/2,
             ontology_parser:get_axiom_symmetricProperty/2, ontology_parser:get_axiom_inverseProperties/3,
             ontology_parser:get_axiom_equivalentProperties/2, ontology_parser:get_axiom_annotationAssertion/4.


ontology_parser:get_axiom_subClassOf(M,A,B):-
  get_parser(M,Parser),
  jpl_call(Parser, 'getAxiomSubClassOf', [A], JavaArray),
  jpl_array_to_list(JavaArray, Strings),
  maplist(atom_string, Classes, Strings),
  member(Classes,B).

ontology_parser:get_axiom_subPropertyOf(M,R,S):-
  get_parser(M,Parser),
  jpl_call(Parser, 'getAxiomSubObjectPropertyOf', [R], JavaArray),
  jpl_array_to_list(JavaArray, Strings),
  maplist(atom_string, Properties, Strings),
  member(Properties,B).

ontology_parser:get_axiom_equivalentClasses(M,L):- % TODO needs of C (search here)
  get_parser(M,Parser),
  jpl_call(Parser, 'getAxiomEquivalentClassOf', [], JavaArray),
  jpl_array_to_list(JavaArray, Strings),
  maplist(atom_string, Properties, Strings),
  M:equivalentClasses(L).

ontology_parser:get_axiom_differentIndividuals(M,SI):-
  M:differentIndividuals(SI).

ontology_parser:get_axiom_sameIndividual(M,SI):-
  M:sameIndividual(SI).

ontology_parser:get_axiom_propertyAssertion(M,P,S,O):-
  M:propertyAssertion(P,S,O).

ontology_parser:get_axiom_classAssertion(M,C,I):-
  M:classAssertion(C,I).

ontology_parser:get_axiom_propertyRange(M,P,D):-
  M:propertyRange(P,D).

ontology_parser:get_axiom_propertyDomain(M,P,D):-
  M:propertyDomain(P,D).

ontology_parser:get_axiom_disjointClasses(M,L):-
  M:disjointClasses(L).

ontology_parser:get_axiom_disjointUnion(M,C,L):-
  M:disjointUnion(C,L).

ontology_parser:get_axiom_transitiveProperty(M,P):-
  M:transitiveProperty(P).

ontology_parser:get_axiom_symmetricProperty(M,P):-
  M:symmetricProperty(P).

ontology_parser:get_axiom_inverseProperties(M,P,S):-
  M:inverseProperties(P,S).

ontology_parser:get_axiom_equivalentProperties(M,L):-
  M:equivalentProperties(L).

ontology_parser:get_axiom_annotationAssertion(M,AnnIRI,Ax,AnnVal):-
  M:annotationAssertion(AnnIRI,Ax,AnnVal).

/********************************
  CLASSES, PREDICATES AND
  INDIVIDUALS MANAGEMENT
*********************************/


:- multifile ontology_parser:get_classes_list/2.

ontology_parser:get_classes_list(M,Classes):-
  get_parser(M,Parser),
  jpl_call(Parser, 'getClassesList', [], A),
  jpl_array_to_list(A, Strings),
  maplist(atom_string, Classes, Strings).
  
/********************************
  PREFIXES MANAGEMENT
*********************************/

% Get the KB's prefixes contained into ns4query
:- multifile ontology_parser:kb_prefixes/1.

ontology_parser:kb_prefixes(M:Prefixes):-
  get_parser(M,Parser),
  jpl_call(Parser, 'getPrefixesList', [], JavaArray),
  jpl_array_to_list(JavaArray, Strings),
  maplist(atom_string, Prefixes, Strings),!.

% Adds a list of kb prefixes into ns4query
:- multifile ontology_parser:add_kb_prefixes/1.

ontology_parser:add_kb_prefixes(_:[]):-!.

ontology_parser:add_kb_prefixes(M:[(H=H1)|T]):-
  ontology_parser:add_kb_prefix(M:H,H1),
  ontology_parser:add_kb_prefixes(M:T).

% Adds a prefix into ns4query
:- multifile ontology_parser:add_kb_prefix/2.

%% add_prefix(+ShortPrefix, +IriPrefix)
%% Aggiunge un prefisso all'ontologia tramite Java.
ontology_parser:add_kb_prefix(M:ShortPrefix,IriPrefix):-
  get_parser(M,Parser),
  % Converte gli atomi Prolog in stringhe Java
    atom_string(ShortPrefix, SP0),
    atom_string(IriPrefix,   IRI),

    % Caso prefisso vuoto: ""
    (   SP0 == ""
    ->  SP = ""                   % lo mandiamo come stringa Java ""
    ;   % altrimenti assicuriamo che finisca con :
        ( sub_atom(SP0, _, 1, 0, ":")
        -> SP = SP0
        ;  string_concat(SP0, ":", SP)
        )
    ),

    % Chiama il metodo Java
    jpl_call(Parser, 'addPrefix', [SP, IRI], Result),

      ( Result == @(true)
    -> true
    ;  format("WARNING: formato ontologia non supporta prefissi.~n"),
       fail
    ).
   

% Removes a prefix from ns4query
:- multifile ontology_parser:remove_kb_prefix/2.

ontology_parser:remove_kb_prefix(M:ShortPrefix,_LongPrefix) :- % TODO check if remove
  ontology_parser:remove_kb_prefix(M:ShortPrefix).

:- multifile ontology_parser:remove_kb_prefix/1.
ontology_parser:remove_kb_prefix(M:A):-
 get_parser(M,Parser),
    atom_string(ShortPrefix, SP0),

    % Caso prefisso vuoto → default prefix
    (   SP0 == ""
    ->  SP = ""
    ;   % Normalizzazione: deve finire con ":"
        (   sub_atom(SP0, _, 1, 0, ":")
        ->  SP = SP0
        ;   string_concat(SP0, ":", SP)
        )
    ),

    jpl_call(Parser, 'removePrefix', [SP], Result),

      ( Result == @(true)
    -> true
    ;  fail).


/********************************
  LOAD KNOWLEDGE BASE
*********************************/
:- multifile ontology_parser:load_kb/1, ontology_parser:load_owl_kb/1, ontology_parser:load_owl_kb_from_string/1.
/**
 * load_kb(++FileName:kb_file_name) is det
 *
 * The predicate loads the knowledge base contained in the given file. 
 * 
 */
ontology_parser:load_kb(FileName):-
  get_module(M),
  get_parser(M,Parser),
  jpl_call(Parser, 'loadOntology', [URI], Ret),
  ( dif(Ret,@(false)) -> 
    assert(M:javaOWLAPI_ontology_wrapper(Parser))
    ;
    (print_message(warning,kb_loading_error), fail)
  ).

/**
 * load_owl_kb(++FileName:kb_file_name) is det
 *
 * The predicate performs the same operations as load_kb.
 * Maintained for compatibility with internal_parser.
 */
ontology_parser:load_owl_kb(FileName):-
  ontology_parser:load_kb(FileName).

/**
 * load_owl_kb_from_string(++KB:string) is det
 *
 * The predicate loads the knowledge base contained in the given string. 
 * The knowledge base can be defined in every OWL format.
 */
ontology_parser:load_owl_kb_from_string(String):-
  get_module(M),
  get_parser(M,Parser),
  jpl_call(Parser, 'loadOntologyFromString', [String], Ret),
  ( dif(Ret,@(false)) -> 
    assert(M:javaOWLAPI_ontology_wrapper(Parser))
    ;
    (print_message(warning,kb_loading_error), fail)
  ).


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

%% iri_exists_for_entity(+AT, +L, -LEx)
%  AT  : atom (entity)
%  L   : atom (input IRI label)
%  LEx : atom (string form of the resolved IRI)
%
%  Succeeds iff OntologyUtils.iriExistsInOntologyGivenEntity(resolveIRI(L), AT)
%  returns true. Fails otherwise.
check_query_args_2(M,AT,L,LEx) :-
  get_parser(M,Parser),
  expand_IRI(Parser,L,LRef,LRefStr),
  jpl_call(Parser, 'iriExistsInOntologyGivenEntity', [LRef,AT], @(true)).


/********************************
  PARSER MANAGEMENT
*********************************/ 

:- multifile ontology_parser:set_up_kb_loading/1.

% Do nothing at the moment
ontology_parser:set_up_kb_loading(_M).

:- multifile ontology_parser:clean_up_parser/1.

ontology_parser:clean_up_parser(M):-
  jpl_call(Parser, 'resetParser', [], @(void)),
  retractall(M:javaOWLAPI_ontology_wrapper(_)).  


:- multifile ontology_parser:set_up_parser/1.

ontology_parser:set_up_parser(M):-
  internal_parser_init(M).


/* ************************************** */




/*****************************/

/************************************
 * 
 * INTERNAL PARSER IMPLEMENTATION
 * 
 * In the following there is the
 * implementation of the actual 
 * parser, exploiting Java ProbOWLAPI.
 * 
 ************************************/

/******************************/

/*****************************
  MESSAGES
******************************/
:- multifile prolog:message/1.

prolog:message(kb_loading_error) -->
  [ 'Error in loading the given file. Please, check the path.' ].


/*****************************
  PARSER INITIALIZATION
******************************/

get_parser(M,Parser):-
  M:javaOWLAPI_ontology_wrapper(Parser),!.

get_parser(M,Parser):-
  internal_parser_init(M),
  M:javaOWLAPI_ontology_wrapper(Parser),!.

internal_parser_init(M) :-
  retractall(M:javaOWLAPI_ontology_wrapper(_)),
  jpl_new('it.unife.ml.probowlapi.trill.TRILLOWLAPIOntologyWrapper',[],JRef),
  assert(M:javaOWLAPI_ontology_wrapper(JRef)).

expand_IRI(Parser,L,LRef,LRefStr):-
  jpl_call(Parser, 'resolveIRI', [L], LRef),
  jpl_call(LRef, 'toString', [], LRefStr),
  atom_string(LEx, LRefStr).
