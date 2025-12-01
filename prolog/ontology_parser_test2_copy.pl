/** <module> java_parser

This module implements the ontology_parser interface.
It uses Java OWL API and JPL to parse an OWL ontology.
This module is for TRILL translation & on-demand OWLAPI backend (via JPL).
Ontology stays in Java. axioms are retrieved on demand by functor and
optionally cached per functor.

Requires:
  - Java 11+
  - JPL 7.6.1
  - A JAR on the JVM classpath containing it.unife.ml.probowlapi.trill.TrillTest1

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(java_parser_2,
    [ set_trill_cache_policy/1     % none | functor | all (all behaves like old “assert everything”)
    ]).


:- use_module(library(lists)).
:- use_module(library(jpl)).             % JPL 7.x
:- use_module(library(error)).
:- use_module(library(apply)).
:- use_module(library(readutil)).

:- use_module(library(trill_utility)).

jar_file('prob-owlapi-2.0.8.jar').
wrapper_class('it.unife.ml.probowlapi.trill.TrillTest2').

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

% --- on-demand bridge: *this* is what TRILL calls repeatedly --------

% Enumerate axioms by *functor*; unify in Prolog (fast after 1st fetch).
:- multifile trill:axiom/1.
trill:axiom(M:Term) :-
  nonvar(Term), functor(Term, F, _),
  % 1) local session facts added via add_axiom/1
  M:cache_axiom(F, Term).

trill:axiom(M:Term) :-
  nonvar(Term), functor(Term, F, _),
  % 2) functor bucket (from Java), according to cache policy
  fetch_if_needed_(M,F),
  M:cache_axiom(F, Term).

% --- write-through for ad-hoc axioms in the current session --------
% We keep these only in the local cache so they are visible immediately
% to TRILL (without round-tripping to Java). That satisfies the “ontology
% lives in Java” requirement while still letting you inject temporary axioms.
:- multifile trill:add_axiom/1.
trill:add_axiom(M:Ax) :- 
  add_axiom(M,Ax),
  trill:update_tabs(M,Ax).

add_axiom(M,Ax) :-
  must_be(nonvar, Ax),
  trill:is_axiom(M:Ax),
  functor(Ax,F,_),
  assertz(M:cache_axiom(F, Ax)).


:- multifile trill:add_axioms/1.
trill:add_axioms(M:Axs) :- 
  must_be(list, Axs),
  forall(member(A, Axs), java_parser:add_axiom(M,A)).


:- multifile trill:remove_axiom/1.
trill:remove_axiom(M:Ax) :-
  functor(Ax,F,_),
  retractall(M:cache_axiom(F, Ax)).

remove_axiom(M,Axiom) :- trill:remove_axiom(M:Axiom).


:- multifile trill:remove_axioms/1.
trill:remove_axioms(M:Axs) :-
  must_be(list, Axs),
  forall(member(A, Axs), java_parser:remove_axiom(M,A)).


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
  trill:axiom(subClassOf(A,B)).

ontology_parser:get_axiom_subPropertyOf(M,R,S):-
  trill:axiom(subPropertyOf(R,S)).

ontology_parser:get_axiom_equivalentClasses(M,L):-
  trill:axiom(equivalentClasses(L)).

ontology_parser:get_axiom_differentIndividuals(M,SI):-
  trill:axiom(differentIndividuals(SI)).

ontology_parser:get_axiom_sameIndividual(M,SI):-
  trill:axiom(sameIndividual(SI)).

ontology_parser:get_axiom_propertyAssertion(M,P,S,O):-
  trill:axiom(propertyAssertion(P,S,O)).

ontology_parser:get_axiom_classAssertion(M,C,I):-
  trill:axiom(classAssertion(C,I)).

ontology_parser:get_axiom_propertyRange(M,P,D):-
  trill:axiom(propertyRange(P,D)).

ontology_parser:get_axiom_propertyDomain(M,P,D):-
  trill:axiom(propertyDomain(P,D)).

ontology_parser:get_axiom_disjointClasses(M,L):-
  trill:axiom(disjointClasses(L)).

ontology_parser:get_axiom_disjointUnion(M,C,L):-
  trill:axiom(disjointUnion(C,L)).

ontology_parser:get_axiom_transitiveProperty(M,P):-
  trill:axiom(transitiveProperty(P)).

ontology_parser:get_axiom_symmetricProperty(M,P):-
  trill:axiom(symmetricProperty(P)).

ontology_parser:get_axiom_inverseProperties(M,P,S):-
  trill:axiom(inverseProperties(P,S)).

ontology_parser:get_axiom_equivalentProperties(M,L):-
  trill:axiom(equivalentProperties(L)).

ontology_parser:get_axiom_annotationAssertion(M,AnnIRI,Ax,AnnVal):-
  trill:axiom(annotationAssertion(AnnIRI,Ax,AnnVal)).


/********************************
  CLASSES, PREDICATES AND
  INDIVIDUALS MANAGEMENT
*********************************/











/********************************
  PREFIXES MANAGEMENT
*********************************/

% Get the KB's prefixes contained into ns4query
% We store prefixes as kb_prefix/2 and expose them through kb_prefixes/1
:- multifile trill:kb_prefixes/1.
/*
trill:kb_prefixes(Pairs) :-
  findall(S=L, M:ns(S,L), Pairs).
*/
% Prefixes are kept on Java side; expose as list of 'Alias=IRI' pairs.
trill:kb_prefixes(M:Pairs) :-
  ( kb_prefix_cache(M,Pairs) -> true
  ; java_class(JCls),
    jpl_call(JCls, 'prefixes', [M], Arr),
    % Arr is a Java String[] with entries like "ex=http://example.org#"
    jpl_array_to_list(Arr, L0),
    maplist(string_pair_to_eq, L0, Pairs),
    assertz(kb_prefix_cache(M,Pairs))
  ).

string_pair_to_eq(S, A=B) :-
  sub_atom(S,Before,1,After,'='),
  sub_atom(S,0,Before,_,Alias),
  sub_atom(S,_,After,0,IRI),
  atom_string(A,Alias),
  atom_string(B,IRI).


:- multifile trill:add_kb_prefix/2.
/*
trill:add_kb_prefix(M:Short, Long) :-
  must_be(atom, Short), must_be(atom, Long),
  retractall(M:ns(Short,_)), assertz(M:ns(Short,Long)).
*/
% Manual add/remove of prefixes:
trill:add_kb_prefix(M:Alias, IRI) :-
  must_be(atom, Alias), must_be(atom, IRI),
  java_class(JCls),
  % we forward to Java; also drop cached prefixes
  jpl_call(JCls, 'addPrefix', [M, Alias, IRI], _),
  retractall(kb_prefix_cache(M,_)).

add_kb_prefix(M, Short, Long) :- trill:add_kb_prefix(M:Short, Long).

% Adds a list of kb prefixes into ns4query
:- multifile trill:add_kb_prefixes/1.
/*
trill:add_kb_prefixes(M:Pairs) :-
  must_be(list, Pairs), forall(member(S=L, Pairs), java_parser:add_kb_prefix(M,S,L)).
*/
trill:add_kb_prefixes(M:List) :-
  must_be(list, List),
  maplist(wrapper_parser:add_kb_prefix_pair(M), List).

add_kb_prefix_pair(M, Short=Long) :- trill:add_kb_prefix(M:Short, Long).

:- multifile trill:remove_kb_prefix/2.
/*
trill:remove_kb_prefix(M:Short, Long) :- retractall(M:ns(Short,Long)).
*/
trill:remove_kb_prefix(Alias) :-
  must_be(atom, Alias),
  get_current_module(M),
  java_class(JCls),
  jpl_call(JCls, 'removePrefix', [M, Alias], _),
  retractall(kb_prefix_cache(M,_)).

:- multifile trill:remove_kb_prefix/1.
/*
trill:remove_kb_prefix(M:Name) :- ( retractall(M:ns(Name,_)) ; retractall(M:ns(_,Name)) ), !.
*/
trill:remove_kb_prefix(M:Alias, IRI) :-
  must_be(atom, Alias), must_be(atom, IRI),
  get_current_module(M),
  java_class(JCls),
  jpl_call(JCls, 'removePrefixExact', [M, Alias, IRI], _),
  retractall(kb_prefix_cache(M,_)).


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
  maplist(java_parser:ns_expand_term(NSList), Args, Expanded).

ns_expand_term(NS, TermIn, TermOut) :-
  ( var(TermIn) -> TermOut = TermIn
  ; atomic(TermIn) -> ns_expand_atomic(NS, TermIn, TermOut)
  ; TermIn = (Pfx:Local) -> ns_expand_atomic(NS, Pfx:Local, TermOut)
  ; TermIn =.. [F|As],
    maplist(java_parser:ns_expand_term(NS), As, AsE),
    ns_expand_atomic(NS, F, FE),
    TermOut =.. [FE|AsE]
  ).

ns_expand_atomic(NS, A, Out) :-
  ( A = (Pfx:Local) ->
      ( memberchk(Pfx=IRI, NS) -> atom_concat(IRI, Local, Out) ; Out = A )
  ; Out = A ).

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
  must_be(atom, File),
  get_module(M),
  ensure_kb_predicates(M),
  clear_caches_(M),
  store_id_(M, StoreId),
  % load ontology into Java store, get prefixes
  parse_file(File,StoreId).
  %pull_prefixes_(M,StoreId).


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
trill:load_owl_kb_from_string(String) :-
  must_be(atom, String),
  get_module(M),
  ensure_kb_predicates(M),
  clear_caches_(M),
  store_id_(M, StoreId),
  parse_string(String,StoreId).
  %pull_prefixes_(M,StoreId).


/*****************************/

/********************************
  PARSER MANAGEMENT
*********************************/ 

:- multifile ontology_parser:clean_up_parser/1.
ontology_parser:clean_up_parser(M):-
  ensure_kb_predicates(M),
  clear_caches_(M),
  retractall(M:kb_atom(_)).

:- multifile ontology_parser:set_up_parser/1.
ontology_parser:set_up_parser(M):-
  ensure_kb_predicates(M),
  ensure_cache_policy(M),
  init_java_bridge,
  ensure_jvm_started.


/* ************************************** */

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

% ---------------- configuration & state -----------------------------
% Where prefixes and ad-hoc axioms (added at runtime) are cached:
:- create_prolog_flag(trill_kb_module, user, [type(atom)]).
target_module(M) :- current_prolog_flag(trill_kb_module, M).

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


% ---------------- cache management ----------------------------------

% Cache policy:
%   none     -> never keep Java results in Prolog (always call Java, slowest but smallest).
%   functor  -> cache per functor (default). First call to a functor fills its bucket.
%   all      -> fetch all functors once (effectively “old behavior” but still pulled from Java).
default_cache_policy(functor).

set_trill_cache_policy(M:Policy) :-
  must_be(oneof([none, functor, all]), Policy),
  retractall(M:cache_policy(_)),
  asserta(M:cache_policy(Policy)).

ensure_cache_policy(M):-
  (M:cache_policy(_) -> true ; 
    ( default_cache_policy(Policy),
      set_trill_cache_policy(Policy)
    )
  ).

% Java store id (per process; if you want multiple KBs simultaneously, set trill_kb_module and reload)
%:- dynamic kb_store_id/1.
%:- dynamic fetched_functor/1.      % marks that we cached a functor already
%:- dynamic cache_axiom/2.          % cache_axiom(Functor, Term)
%:- dynamic ns/2.                   % prefixes cache for kb_prefixes/1 not used
%etc.

ensure_kb_predicates(M) :-
  ( predicate_property(M:kb_store_id(_), dynamic) -> true ; dynamic(M:kb_store_id12) ),
  ( predicate_property(M:fetched_functor(_), dynamic) -> true ; dynamic(M:fetched_functor/1) ),
  ( predicate_property(M:cache_axiom(_,_), dynamic) -> true ; dynamic(M:cache_axiom/2) ),
  ( predicate_property(M:cache_policy(_), dynamic) -> true ; dynamic(M:cache_policy/1) ).

clear_caches_(M) :-
  retractall(M:fetched_functor(_)),
  retractall(M:cache_axiom(_,_)).
  %retractall(M:ns(_,_)).

% Utility to make sure JVM is up before first call; we assume classpath is
% properly set (see README below).
ensure_jvm_started :-
  ( jpl_get_actual_jvm_opts(_)
  -> true
  ;  true % TODO you might jpl_set_default_jvm_opts/1 here programmatically if needed
  ).

% ---------------- parsing -------------------------------------------

parse_file(File,StoreId):-
  wrapper_class(WrapperClass),
  jpl_call(WrapperClass, 'loadFromFile', [StoreId, File], _).

parse_string(String,StoreId):-
  wrapper_class(WrapperClass),
  jpl_call(WrapperClass, 'loadFromString', [StoreId, String], _).


% ---------------- internal helpers ----------------------------------

store_id_(M, StoreId) :-
  ( M:kb_store_id(Id) -> StoreId = Id
  ; atom_string(M, S), string_concat("trill:", S, StoreIdS),
    assertz(M:kb_store_id(StoreIdS)), StoreId = StoreIdS).

/*
pull_prefixes_(M,StoreId) :-
  wrapper_class(WrapperClass),
  % fetch small list of prefixes into the cheap Prolog cache
  jpl_call(WrapperClass, 'prefixPairs', [StoreId], JPairs),
  jpl_array_to_list(JPairs, PairArrayList),
  forall(member(Arr, PairArrayList),
         ( jpl_array_to_list(Arr, [AliasJ, IriJ]),
           jpl_get(AliasJ, toString, AliasS),
           jpl_get(IriJ,   toString, IriS),
           atom_string(Alias, AliasS),
           atom_string(Iri,   IriS),
           ( Alias == '' -> true ; java_parser:add_kb_prefix(M, Alias, Iri) ))).
*/

fetch_if_needed_(M,F) :-
  cache_policy(none), !,
  % no caching: call Java now and stream results once
  fetch_functor_now_(M,F, false).
fetch_if_needed_(M,F) :-
  cache_policy(functor),
  ( M:fetched_functor(F) -> true
  ; fetch_functor_now_(M,F, true), assertz(M:fetched_functor(F)) ).
fetch_if_needed_(M,F) :-
  cache_policy(all),
  ( M:fetched_functor(all) -> true
  ; % fetch all supported functors once
    forall(member(FF, [ subClassOf, equivalentClasses, disjointClasses,
                        subPropertyOf, equivalentProperties, propertyDomain, propertyRange,
                        transitiveProperty, inverseProperties, symmetricProperty,
                        sameIndividual, differentIndividuals,
                        classAssertion, propertyAssertion, annotationAssertion ]),
           fetch_functor_now_(M,FF, true)),
    assertz(M:fetched_functor(all)),
    true ).

fetch_functor_now_(M,F, Cache) :-
  M:kb_store_id(StoreId),
  atom_string(F, FS),
  wrapper_class(WrapperClass),
  jpl_call(WrapperClass, 'queryFunctor', [StoreId, FS], JAxs),
  jpl_array_to_list(JAxs, AxStrs),
  forall(member(JStr, AxStrs),
         ( jpl_get(JStr, toString, SS),
           atom_string(A, SS),
           read_term_from_atom(A, Term, [syntax_errors(error)]),
           ( Cache -> assertz(M:cache_axiom(F, Term)) ; true ),
           % If not caching, still succeed via unification on backtracking:
           ( Cache -> true ; ( Term = _ ) ) )).  % no-op: just allow enumeration in caller
