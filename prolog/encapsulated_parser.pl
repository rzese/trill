/** <module> encapsulated_parser

Parser backend that keeps the ontology inside a dedicated Java object
and serves axioms to TRILL on demand.  It merges the historical
encapsulated_parser API with the newer GPT implementation so one
backend satisfies every caller.
*/

%:- module(encapsulated_parser,
%                    [ set_cache_policy/1
%                    ]).

%:- meta_predicate set_cache_policy(:).

:- use_module(library(lists)).
:- use_module(library(jpl)).
:- use_module(library(error)).
:- use_module(library(apply)).
:- use_module(library(trill_utility)).
:- use_module(library(ordsets)).

jar_file('prob-owlapi-2.0.8.jar').
parser_class('it.unife.ml.probowlapi.trill.TrillEncapsulated').

prolog:message(no_jvm) -->
    [ 'JVM not available! Error in initialization of the Java Virtual Machine.' ].

prolog:message(no_ontology_loaded) -->
    [ 'No ontology loaded. Call load_kb/1 or load_owl_kb/1 first.' ].

/* ------------------------------------------------------------------
 *  Public configuration API
 * ------------------------------------------------------------------ */

/* Cache policies:
    none: no caching, forward every axiom request to Java
    lazy: cache functors on first request
    eager: cache all functors after loading
    selective(List): cache only functors in List after loading
    matching: delegate partially instantiated queries to Java so only
                 matching axioms are materialised
*/
default_cache_policy(lazy).

normalize_policy(none, none).
normalize_policy(lazy, lazy).
normalize_policy(eager, eager).
normalize_policy(matching, matching).
normalize_policy(selective(List0), selective(List)) :-
    must_be(list, List0),
    maplist(must_be(atom), List0),
    sort(List0, List).


set_cache_policy(M:PolicyIn) :-
    normalize_policy(PolicyIn, Policy),
    ensure_module_state(M),
    retractall(M:cache_policy(_)),
    assertz(M:cache_policy(Policy)),
    clear_axiom_cache_state(M),
    maybe_prime_cache(M).

maybe_prime_cache(M) :-
    ( M:ontology_ready -> prime_cache_after_load(M) ; true ).


/* ------------------------------------------------------------------
 *  AXIOM MANAGEMENT
 * ------------------------------------------------------------------ */

:- multifile trill:axiom/1.
trill:axiom(M:Pattern) :-
    var(Pattern), !,
    ensure_module_state(M),
    ensure_cache_policy(M),
    supported_functor_list(M, Functors),
    member(Functor, Functors),
    enumerate_axioms(M, Functor, Pattern).

trill:axiom(M:Pattern) :-
    nonvar(Pattern),
    ensure_module_state(M),
    ensure_cache_policy(M),
    functor(Pattern, Functor, _),
    enumerate_axioms(M, Functor, Pattern).

enumerate_axioms(M, Functor, Term) :-
    (   M:cache_policy(none)
    ->  ( fetch_functor_terms(M, Functor, Terms),
          member(Term, Terms)
        )
    ;   ( M:cache_policy(matching),
            nonvar(Term)
        ->  fetch_matching_axioms(M, Functor, Term)
        ;   ( ensure_functor_cached(M, Functor), % Other cache policies
              M:cache_axiom(Functor, Term)
            )
        )
    ).

:- multifile trill:add_axiom/1.
trill:add_axiom(M:Axiom) :-
    add_axiom(M, Axiom),
    trill:update_tabs(M,Axiom).

add_axiom(M, Axiom) :-
    must_be(nonvar, Axiom),
    trill:is_axiom(Axiom),
    ns_expand_term(M, Axiom, Expanded),
    add_axiom_no_check(M, Expanded).

add_axiom_no_check(M, Axiom) :-
    term_to_atom(Axiom, Atom),
    ensure_instance(M, JRef),
    jpl_call(JRef, 'addAxiom', [Atom], _),
    functor(Axiom, Functor, _),
    invalidate_functor_cache(M, Functor).

:- multifile trill:add_axioms/1.
trill:add_axioms(M:Axioms) :-
    must_be(list, Axioms),
    maplist(encapsulated_parser:add_axiom(M), Axioms).

:- multifile trill:remove_axiom/1.
trill:remove_axiom(M:Axiom) :-
    term_to_trill_atom(Axiom, Atom),
    ensure_instance(M, JRef),
    jpl_call(JRef, 'removeAxiom', [Atom], _),
    functor(Axiom, Functor, _),
    invalidate_functor_cache(M, Functor).

remove_axiom(M, Ax) :- trill:remove_axiom(M:Ax).

:- multifile trill:remove_axioms/1.
trill:remove_axioms(M:Axioms) :-
    must_be(list, Axioms),
    maplist(encapsulated_parser:remove_axiom(M), Axioms).

:- multifile trill:is_axiom/1.
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

/* ------------------------------------------------------------------
 *  AXIOM SEARCH
 * ------------------------------------------------------------------ */

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
  trill:axiom(M:subClassOf(A,B)).

ontology_parser:get_axiom_subPropertyOf(M,R,S):-
  trill:axiom(M:subPropertyOf(R,S)).

ontology_parser:get_axiom_equivalentClasses(M,L):-
  trill:axiom(M:equivalentClasses(L)).

ontology_parser:get_axiom_differentIndividuals(M,L):-
  trill:axiom(M:differentIndividuals(L)).

ontology_parser:get_axiom_sameIndividual(M,L):-
  trill:axiom(M:sameIndividual(L)).

ontology_parser:get_axiom_propertyAssertion(M,P,S,O):-
  trill:axiom(M:propertyAssertion(P,S,O)).

ontology_parser:get_axiom_classAssertion(M,C,I):-
  trill:axiom(M:classAssertion(C,I)).

ontology_parser:get_axiom_propertyRange(M,P,R):-
  trill:axiom(M:propertyRange(P,R)).

ontology_parser:get_axiom_propertyDomain(M,P,D):-
  trill:axiom(M:propertyDomain(P,D)).

ontology_parser:get_axiom_disjointClasses(M,L):-
  trill:axiom(M:disjointClasses(L)).

ontology_parser:get_axiom_disjointUnion(M,C,L):-
  trill:axiom(M:disjointUnion(C,L)).

ontology_parser:get_axiom_transitiveProperty(M,P):-
  trill:axiom(M:transitiveProperty(P)).

ontology_parser:get_axiom_symmetricProperty(M,P):-
  trill:axiom(M:symmetricProperty(P)).

ontology_parser:get_axiom_inverseProperties(M,P,S):-
  trill:axiom(M:inverseProperties(P,S)).

ontology_parser:get_axiom_equivalentProperties(M,L):-
  trill:axiom(M:equivalentProperties(L)).

ontology_parser:get_axiom_annotationAssertion(M,Ann,Ax,Val):-
  trill:axiom(M:annotationAssertion(Ann,Ax,Val)).


/********************************
    CONNECTED INDIVIDUALS (JAVA-ASSISTED)
*********************************/

:- multifile scan_connected_individuals/5.

scan_connected_individuals(_, [], _, IndividualsSet0, IndividualsSet) :-
    !,
    sort(IndividualsSet0, IndividualsSet).

scan_connected_individuals(M, IndividualsToCheck, _Checked, IndividualsSet0, IndividualsSet) :-
    append(IndividualsToCheck, IndividualsSet0, RawSeeds),
    sort(RawSeeds, Seeds),
    ( Seeds == []
    -> sort(IndividualsSet0, IndividualsSet)
    ;   java_connected_component(M, Seeds, IndividualsSet)
    ).

scan_connected_individuals_parallel(M, Seeds, Connected) :-
    sort(Seeds, DedupSeeds),
    ( DedupSeeds == []
    -> Connected = []
    ;   java_connected_component(M, DedupSeeds, Connected)
    ).

java_connected_component(M, Seeds, Connected) :-
    java_fetch_connected(M, Seeds, RawConnected),
    sort(RawConnected, Connected).

java_fetch_connected(M, Seeds, ConnectedAtoms) :-
    ensure_instance(M, JRef),
    maplist(term_string_for_java, Seeds, SeedStrings),
    jpl_list_to_array(SeedStrings, SeedArray),
    jpl_call(JRef, 'getConnectedIndividuals', [SeedArray], Arr),
    jpl_array_to_list(Arr, RawStrings),
    maplist(atom_string, ConnectedAtoms, RawStrings).

term_string_for_java(Term, String) :-
    must_be(nonvar, Term),
    ( atom(Term) ->
        atom_string(Term, String)
    ; number(Term) ->
        number_string(Term, String)
    ; term_to_atom(Term, Atom),
      atom_string(Atom, String)
    ).


/********************************
  CLASSES, PREDICATES AND
  INDIVIDUALS MANAGEMENT
*********************************/
%:- multifile ontology_parser:get_classes_list/2.
%ontology_parser:get_classes_list(M, Classes) :-
%    ( M:ontology_ready ->
%        ensure_instance(M, JRef),
%        jpl_call(JRef, 'getClassIRIs', [], Arr),
%        array_to_atoms(Arr, Classes)
%    ;   Classes = []
%    ).

/********************************
  PREFIXES MANAGEMENT
*********************************/

:- multifile trill:kb_prefixes/1.
trill:kb_prefixes(M:Pairs) :-
    ensure_instance(M, JRef),
    jpl_call(JRef, 'getPrefixPairs', [], Arr),
    jpl_array_to_list(Arr, Raw),
    maplist(prefix_string_pair, Raw, Pairs).

prefix_string_pair(Str, Alias=IRI) :-
    atom_string(Atom, Str),
    sub_atom(Atom,Before,1,After,'='),
    sub_atom(Atom,0,Before,_,Alias),
    sub_atom(Atom,_,After,0,IRI).

:- multifile trill:add_kb_prefix/2.
trill:add_kb_prefix(M:Alias, IRI) :-
    must_be(atom, Alias), must_be(atom, IRI),
    ensure_instance(M, JRef),
    jpl_call(JRef, 'addPrefix', [Alias, IRI], _).

:- multifile trill:add_kb_prefixes/1.
trill:add_kb_prefixes(M:Pairs) :-
    must_be(list, Pairs),
    maplist(encapsulated_parser:add_kb_prefix_pair(M), Pairs).

add_kb_prefix_pair(M, Alias=IRI) :-
    trill:add_kb_prefix(M:Alias, IRI).

:- multifile trill:remove_kb_prefix/1.
trill:remove_kb_prefix(M:Alias) :-
    must_be(atom, Alias),
    ensure_instance(M, JRef),
    jpl_call(JRef, 'removePrefix', [Alias], _).

:- multifile trill:remove_kb_prefix/2.
trill:remove_kb_prefix(M:Alias, IRI) :-
    must_be(atom, Alias), must_be(atom, IRI),
    ensure_instance(M, JRef),
    jpl_call(JRef, 'removePrefixExact', [Alias, IRI], _).

expand_all_ns(_M, [], []).
expand_all_ns(M, [H|T], [EH|ET]) :-
    ns_expand_term(M, H, EH),
    expand_all_ns(M, T, ET).

ns_expand_term(_M, Var, Var) :- var(Var), !.
ns_expand_term(_M, Num, Num) :- number(Num), !.
ns_expand_term(_M, literal(Lit), literal(Lit)) :- !.
ns_expand_term(M, Prefix:Local, Expanded) :- !,
    atomics_to_string([Prefix, ':', Local], Raw),
    expand_atomic_term(M, Raw, Expanded).
ns_expand_term(M, List, ExpandedArgs) :- is_list(List), !,
    maplist(ns_expand_term(M), List, ExpandedArgs).
ns_expand_term(M, Atom, Expanded) :- atomic(Atom), !,
    expand_atomic_term(M, Atom, Expanded).
ns_expand_term(M, Compound, Expanded) :-
    Compound =.. [F|Args],
    add_rule_from_functor(M,F),
    maplist(ns_expand_term(M), Args, ExpandedArgs),
    Expanded =.. [F|ExpandedArgs].

expand_atomic_term(M, Atom, Expanded) :-
    ensure_instance(M, JRef),
    %atom_string(Atom, Str),
    jpl_call(JRef, 'compressIRI', [Atom], Out),
    ( Out == @(null)
    -> Expanded = Atom
    ;  Expanded = Out
    ).

/* ------------------------------------------------------------------
 *  LOAD KNOWLEDGE BASE
 * ------------------------------------------------------------------ */

:- multifile trill:load_kb/1, trill:load_owl_kb/1, trill:load_owl_kb_from_string/1.

trill:load_kb(File) :-
    must_be(atom, File),
    get_module(M),
    ensure_runtime_ready(M),
    ensure_instance(M, JRef),
    clear_axiom_cache_state(M),
    jpl_call(JRef, 'loadFromFile', [File], _),
    post_load_refresh(M).

trill:load_owl_kb(File) :-
    trill:load_kb(File).

trill:load_owl_kb_from_string(String) :-
    must_be(atom, String),
    get_module(M),
    ensure_runtime_ready(M),
    ensure_instance(M, JRef),
    clear_axiom_cache_state(M),
    jpl_call(JRef, 'loadFromString', [String], _),
    post_load_refresh(M).

post_load_refresh(M) :-
    retractall(M:ontology_ready),
    assertz(M:ontology_ready),
    prime_cache_after_load(M).

prime_cache_after_load(M) :-
    M:cache_policy(Policy),
    ( Policy == eager ->
        ( fetch_all_functors(M),
          retractall(M:fetched_functor(all)),
          assertz(M:fetched_functor(all))
        )
    ; Policy = selective(List), List \= [] ->
        fetch_functor_list(M, List)
    ; true
    ).

/* ------------------------------------------------------------------
 *  CHECK QUERY ARGS
 * ------------------------------------------------------------------ */

:- multifile ontology_parser:check_query_args_1/5.
ontology_parser:check_query_args_1(_M, _, [], [], []) :- !.
ontology_parser:check_query_args_1(M, Types, Args, Expanded, Missing) :-
    ensure_instance(M, JRef),
    %maplist(atom_string, Types, TypeStrings),
    %maplist(term_to_arg_string, Args, ArgStrings),
    jpl_list_to_array(Types, TypeArray),
    jpl_list_to_array(Args, ArgArray),
    jpl_call(JRef, 'checkAndExpandArgs', [TypeArray, ArgArray], ResultArray),
    jpl_array_to_list(ResultArray, ResultStrings),
    parse_check_results(Args, ResultStrings, Expanded, Missing).

term_to_arg_string(Term, String) :-
    ( Term = Prefix:Local ->
        atomics_to_string([Prefix, ':', Local], String)
    ; number(Term) ->
        number_string(Term, String)
    ; atom(Term) ->
        atom_string(Term, String)
    ; term_to_atom(Term, Atom),
      atom_string(Atom, String)
    ).

parse_check_results([], [], [], []).
parse_check_results([_Orig|OT], [Result|RT], [Exp|ET], Missing) :-
    atom_string(ResultAtom, Result),
    sub_atom(ResultAtom, 0, 3, _, 'ok:'), !,
    sub_atom(ResultAtom, 3, _, 0, ExpandedPart),
    atom_string(Exp, ExpandedPart),
    parse_check_results(OT, RT, ET, Missing).
parse_check_results([Orig|OT], [Result|RT], Exp, [Orig|MissingTail]) :-
    atom_string(ResultAtom, Result),
    ( sub_atom(ResultAtom, 0, _, _, 'missing:') -> true ; true ),
    parse_check_results(OT, RT, Exp, MissingTail).

/* ------------------------------------------------------------------
 *  PARSER MANAGEMENT
 * ------------------------------------------------------------------ */

:- multifile ontology_parser:set_up_parser/1.
ontology_parser:set_up_parser(M) :-
    ensure_runtime_ready(M).

:- multifile ontology_parser:clean_up_parser/1.
ontology_parser:clean_up_parser(M) :-
    ensure_module_state(M),
    clear_axiom_cache_state(M),
    ( M:java_class(JRef) ->
        jpl_call(JRef, 'dispose', [], _),
        retractall(M:java_class(_))
    ; true ),
    retractall(M:ontology_ready).

ensure_runtime_ready(M) :-
    ensure_module_state(M),
    init_java_bridge(M),
    init_java_class(M),
    ensure_cache_policy(M).

ensure_cache_policy(M) :-
    ( M:cache_policy(_) -> true
    ; default_cache_policy(Policy),
      assertz(M:cache_policy(Policy))
    ).

ensure_module_state(M) :-
    ( predicate_property(M:cache_axiom(_,_), dynamic) -> true ; dynamic(M:cache_axiom/2) ),
    ( predicate_property(M:fetched_functor(_), dynamic) -> true ; dynamic(M:fetched_functor/1) ),
    ( predicate_property(M:cache_policy(_), dynamic) -> true ; dynamic(M:cache_policy/1) ),
    ( predicate_property(M:java_class(_), dynamic) -> true ; dynamic(M:java_class/1) ),
    ( predicate_property(M:supported_functors(_), dynamic) -> true ; dynamic(M:supported_functors/1) ),
    ( predicate_property(M:ontology_ready, dynamic) -> true ; dynamic(M:ontology_ready/0) ),
    ( predicate_property(M:java_bridge_initialized, dynamic) -> true ; dynamic(M:java_bridge_initialized/0) ),
    ( predicate_property(M:rule(_), dynamic) -> true ; dynamic(M:rule/1) ).

init_java_bridge(M) :-
    M:java_bridge_initialized, !.
init_java_bridge(_M) :-
    jpl_get_actual_jvm_opts(_),!.
init_java_bridge(M) :-
    jar_file(Jar),
    absolute_file_name(library(Jar), JarPath, [access(read)]),
    (   getenv('CLASSPATH', Existing) -> true ; Existing = '' ),
    atomic_list_concat([Existing, JarPath], ';', CP),
    atomic_list_concat(['-Djava.class.path=', CP], JVMOpt),
    jpl_set_default_jvm_opts(['-Xms128m','-Xmx1g', JVMOpt]),
    assertz(M:java_bridge_initialized).

init_java_class(M) :-
    ( M:java_class(_) -> true
    ; parser_class(Class),
      jpl_new(Class, [], JRef),
      assertz(M:java_class(JRef))
    ).

ensure_instance(M, JRef) :-
    init_java_class(M),
    M:java_class(JRef).

/* ------------------------------------------------------------------
 *  INTERNAL HELPERS
 * ------------------------------------------------------------------ */

clear_axiom_cache_state(M) :-
    retractall(M:cache_axiom(_,_)),
    retractall(M:fetched_functor(_)),
    retractall(M:supported_functors(_)),
    retractall(M:ontology_ready),
    ( M:java_class(JRef) -> jpl_call(JRef, 'clearAllCaches', [], _) ; true ).

fetch_functor_terms(M, Functor, Terms) :-
    ensure_instance(M, JRef),
    jpl_call(JRef, 'fetchAxioms', [Functor], Arr),
    jpl_array_to_list(Arr, Raw),
    %maplist(atom_string, AtomStrs, Raw),
    maplist(read_term_safely, Raw, Terms),
    update_rule_lists(M,Terms).

fetch_matching_axioms(M, Functor, Pattern) :-
    ensure_instance(M, JRef),
    pattern_filters(Pattern, Filters),
    jpl_list_to_array(Filters, FilterArray),
    jpl_call(JRef, 'fetchMatchingAxioms', [Functor, FilterArray], Arr),
    jpl_array_to_list(Arr, Raw),
    maplist(read_term_safely, Raw, Terms),
    member(Term, Terms),
    Pattern = Term,
    update_rule_lists(M,Terms).

read_term_safely(Atom, Term) :-
    read_term_from_atom(Atom, Term, [syntax_errors(error)]).

ensure_functor_cached(M, Functor) :-
    ( M:fetched_functor(all) -> true
    ; M:fetched_functor(Functor) -> true
    ; fetch_functor_and_store(M, Functor)
    ).

fetch_functor_and_store(M, Functor) :-
    fetch_functor_terms(M, Functor, Terms),
    retractall(M:cache_axiom(Functor,_)),
    forall(member(T, Terms), assertz(M:cache_axiom(Functor, T))),
    ( M:fetched_functor(all) -> true ; assertz(M:fetched_functor(Functor)) ),
    update_rule_lists(M,Terms).

fetch_all_functors(M) :-
    supported_functor_list(M, Functors),
    forall(member(F, Functors), fetch_functor_and_store(M, F)).

fetch_functor_list(M, Functors) :-
    forall(member(F, Functors), fetch_functor_and_store(M, F)).

supported_functor_list(M, Functors) :-
    ( M:supported_functors(Fs) -> Functors = Fs
    ; ensure_instance(M, JRef),
      jpl_call(JRef, 'supportedFunctors', [], Arr),
      jpl_array_to_list(Arr, Raw),
      maplist(atom_string, Functors, Raw),
      assertz(M:supported_functors(Functors))
    ).

pattern_filters(Term, Filters) :-
    Term =.. [_|Args],
    maplist(arg_filter_value, Args, Filters).

filter_wildcard('<<ANY>>').

arg_filter_value(Arg, Value) :-
    (   ground(Arg)
    ->  with_output_to(atom(Value), write_term(Arg, [quoted(true), numbervars(true)]))
    ;   filter_wildcard(Value)
    ).

invalidate_functor_cache(M, Functor) :-
    retractall(M:cache_axiom(Functor,_)),
    retractall(M:fetched_functor(Functor)),
    ( M:java_class(JRef) ->
                jpl_call(JRef, 'clearFunctorCache', [Functor], _)
    ; true ),
    retractall(M:fetched_functor(all)).

term_to_trill_atom(Term, Atom) :-
    %with_output_to(atom(Atom), write_term(Term, [quoted(true), numbervars(true)])).
    term_to_atom(Term, Atom).

array_to_atoms(Array, Atoms) :-
    jpl_array_to_list(Array, Raw),
    maplist(atom_string, Atoms, Raw).


update_rule_lists(_M,[]):-!.

update_rule_lists(M,_T):-
    ensure_instance(M, JRef),
    jpl_call(JRef, 'getRequiredRules', [], Arr),
    jpl_array_to_list(Arr, Raw),
    forall(member(Rule,Raw),add_rule(M,Rule)),
    trill:prune_tableau_rules(M).

:- multifile sandbox:safe_meta/2.

%sandbox:safe_meta(encapsulated_parser:set_cache_policy(_), []).

user:term_expansion(owl_rdf(String), []) :-
    trill:load_owl_kb_from_string(String), !.

user:term_expansion(Axiom, []) :-
    get_module(M),
    add_axiom(M,Axiom).
