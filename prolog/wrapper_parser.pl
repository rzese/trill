/** <module> wrapper_parser

This module implements the ontology_parser interface.
It uses Java OWL API and JPL to parse an OWL ontology.
It translates OWL axioms into TRILL's Prolog syntax and asserts them as
`adb/1` facts, preserving the public predicates used by `trill.pl`.

Requires:
  - Java 11+
  - JPL 7.6.1
  - A JAR on the JVM classpath containing it.unife.ml.probowlapi.trill.TrillTest1

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(wrapper_parser,[]).


:- use_module(library(lists)).
:- use_module(library(jpl)).             % JPL 7.x
:- use_module(library(error)).
:- use_module(library(apply)).
:- use_module(library(readutil)).

:- use_module(library(trill_utility)).

jar_file('prob-owlapi-2.0.8.jar').
wrapper_class('it.unife.ml.probowlapi.trill.TrillKBParserWrapper').

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
% annotationAssertion, plus concept descriptions used inside axioms. 
:- multifile trill:axiom/1.
trill:axiom(M:A) :- M:adb(A).


:- multifile trill:add_axiom/1.
trill:add_axiom(M:Axiom) :-
    M:adb(Axiom),!.

trill:add_axiom(M:Axiom) :-
    add_axiom(M,Axiom),
    trill:update_tabs(M,Axiom).

add_axiom(M,Axiom) :-
  trill:is_axiom(Axiom),
  assertz(M:adb(Axiom)).


:- multifile trill:add_axioms/1.
trill:add_axioms(M:Axioms) :-
    must_be(list, Axioms),
    concurrent_maplist(wrapper_parser:add_axiom(M), Axioms).


:- multifile trill:remove_axiom/1.
trill:remove_axiom(M:Axiom) :-
    retractall(M:adb(Axiom)).

remove_axiom(M,Axiom) :- trill:remove_axiom(M:Axiom).


:- multifile trill:remove_axioms/1.
trill:remove_axioms(M:Axioms) :-
    must_be(list, Axioms),
    concurrent_maplist(wrapper_parser:remove_axiom(M), Axioms).


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

:- multifile ontology_parser:get_axiom_subClassOf/3, ontology_parser:get_axiom_subPropertyOf/3,
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
:- multifile ontology_parser:get_classes_list/2.
ontology_parser:get_classes_list(M,Classes):-
  M:kb_atom(KBA),
  Classes=KBA.class.


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
  maplist(wrapper_parser:add_kb_prefix_pair(M), Pairs).

add_kb_prefix_pair(M, Short=Long) :- trill:add_kb_prefix(M:Short, Long).


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
expand_all_ns(_M, Args, NSList, Expanded) :-
  % NSList is a list of Short=IRI pairs (atoms)
  must_be(list, Args),
  must_be(list, NSList),
  maplist(wrapper_parser:ns_expand_term(NSList), Args, Expanded).

ns_expand_term(NSList, TermIn, TermOut) :-
  (   atomic(TermIn)
  ->  ns_expand_atomic(NSList, TermIn, TermOut)
  ;   TermIn =.. [F|As],
      maplist(wrapper_parser:ns_expand_term(NSList), As, AsE),
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
    maplist(wrapper_parser:assert_prefix_from_java(M), PrefListJava),
    % axioms
    jpl_get(JRes, axioms, JAxiomArray),
    jpl_array_to_list(JAxiomArray, AxiomStrings),
    maplist(wrapper_parser:assert_axiom_from_string(M), AxiomStrings),
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
  ontology_parser:kb_prefixes(NSList),
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
  M:(dynamic adb/1, kb_atom/1, kb_prefix/2),
  forall(ontology_parser:axiom(M:A),retractall(M:adb(A))),
  retractall(M:kb_atom(_)).

:- multifile ontology_parser:set_up_parser/1.
ontology_parser:set_up_parser(M):-
  M:(dynamic adb/1, kb_atom/1, kb_prefix/2),
  init_java_bridge.


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



parse_file(File,JRes):-
  wrapper_class(WrapperClass),
  jpl_call(WrapperClass,
          'parseOntologyFile',
          [File],
          JRes).

parse_string(String,Jres):-
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
  trill:is_axiom(TRILLAxiom),
  get_module(M),
  trill:kb_prefixes(NSList),
  ns_expand_term(NSList, TRILLAxiom, TRILLAxiomExpanded),
  assertz(M:adb(TRILLAxiomExpanded)).

