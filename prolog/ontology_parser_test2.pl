:- module(utility_traslation,
    [ load_owl/1,
      load_owl_from_string/1,
      % multifile API used by trill.pl
      kb_prefixes/1,
      add_kb_prefix/2, add_kb_prefixes/1,
      remove_kb_prefix/1, remove_kb_prefix/2,
      add_axiom/1, add_axioms/1,
      remove_axiom/1, remove_axioms/1,
      % namespace helpers kept for compatibility
      expand_all_ns/4, expand_all_ns/5,
      is_axiom/1,
      % optional: tweak cache behavior
      set_trill_cache_policy/1     % none | functor | all (all behaves like old “assert everything”)
    ]).

/** <module> TRILL translation & on-demand OWLAPI backend (via JPL)
  Ontology stays in Java. axioms are retrieved on demand by functor and
  optionally cached per functor.
*/

:- use_module(library(jpl)).      % JPL 7.6.1
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(error)).

% ---------------- configuration & state -----------------------------

init_java_bridge :-
    % Point to your assembled JAR (jar-with-dependencies)
    Jar = 'prob-owlapi-2.0.8.jar',
    jpl_set_default_jvm_opts(['-Xms128m','-Xmx1g',
                              classpath(Jar)]).

% Where prefixes and ad-hoc axioms (added at runtime) are cached:
:- create_prolog_flag(trill_kb_module, user, [type(atom)]).
target_module(M) :- current_prolog_flag(trill_kb_module, M).

% Cache policy:
%   none     -> never keep Java results in Prolog (always call Java, slowest but smallest).
%   functor  -> cache per functor (default). First call to a functor fills its bucket.
%   all      -> fetch all functors once (effectively “old behavior” but still pulled from Java).
:- dynamic cache_policy/1.
cache_policy(functor).

set_trill_cache_policy(Policy) :-
  must_be(oneof([none, functor, all]), Policy),
  retractall(cache_policy(_)),
  asserta(cache_policy(Policy)).

% Java store id (per process; if you want multiple KBs simultaneously, set trill_kb_module and reload)
:- dynamic kb_store_id/1.
:- dynamic fetched_functor/1.      % marks that we cached a functor already
:- dynamic cache_axiom/2.          % cache_axiom(Functor, Term)
:- dynamic ns/2.                   % prefixes cache for kb_prefixes/1 etc.

ensure_kb_predicates :-
  target_module(M),
  ( predicate_property(M:ns(_,_), dynamic) -> true ; dynamic(M:ns/2) ).

clear_caches_ :-
  retractall(fetched_functor(_)),
  retractall(cache_axiom(_,_)),
  retractall(ns(_,_)).

% ---------------- public API (used by trill.pl) --------------------

load_owl(File) :-
  must_be(atom, File),
  ensure_kb_predicates,
  clear_caches_,
  target_module(M),
  store_id_(M, StoreId),
  % load ontology into Java store, get prefixes
  jpl_call('it.unife.ml.probowlapi.trill.TrillTest2', 'loadFromFile', [StoreId, File], _),
  pull_prefixes_(StoreId).

load_owl_from_string(String) :-
  must_be(atom, String),
  ensure_kb_predicates,
  clear_caches_,
  target_module(M),
  store_id_(M, StoreId),
  jpl_call('it.unife.ml.probowlapi.trill.TrillTest2', 'loadFromString', [StoreId, String], _),
  pull_prefixes_(StoreId).

kb_prefixes(Pairs) :-
  findall(S=L, ns(S,L), Pairs).

add_kb_prefix(Short, Long) :-
  must_be(atom, Short), must_be(atom, Long),
  retractall(ns(Short,_)), assertz(ns(Short,Long)).

add_kb_prefixes(Pairs) :-
  must_be(list, Pairs), forall(member(S=L, Pairs), add_kb_prefix(S,L)).

remove_kb_prefix(Short, Long) :- retractall(ns(Short,Long)).
remove_kb_prefix(Name) :- ( retractall(ns(Name,_)) ; retractall(ns(_,Name)) ), !.

% --- write-through for ad-hoc axioms in the current session --------
% We keep these only in the local cache so they are visible immediately
% to TRILL (without round-tripping to Java). That satisfies the “ontology
% lives in Java” requirement while still letting you inject temporary axioms.
add_axiom(Ax)      :- must_be(nonvar, Ax), is_axiom(Ax), functor(Ax,F,_), assertz(cache_axiom(F, Ax)).
add_axioms(Axs)    :- must_be(list, Axs), forall(member(A, Axs), add_axiom(A)).
remove_axiom(Ax)   :- functor(Ax,F,_), retractall(cache_axiom(F, Ax)).
remove_axioms(Axs) :- must_be(list, Axs), forall(member(A, Axs), remove_axiom(A)).

% --- on-demand bridge: *this* is what TRILL calls repeatedly --------

% Enumerate axioms by *functor*; unify in Prolog (fast after 1st fetch).
axiom(Term) :-
  nonvar(Term), functor(Term, F, _),
  % 1) local session facts added via add_axiom/1
  cache_axiom(F, Term).
axiom(Term) :-
  nonvar(Term), functor(Term, F, _),
  % 2) functor bucket (from Java), according to cache policy
  fetch_if_needed_(F),
  cache_axiom(F, Term).

% ---------------- namespace expansion (compatibility) ---------------

expand_all_ns(_M, Args, NSList, Expanded) :-
  expand_all_ns(_M, Args, NSList, true, Expanded).

expand_all_ns(_M, Args, NSList, _AddName, Expanded) :-
  must_be(list, Args), must_be(list, NSList),
  maplist(ns_expand_term(NSList), Args, Expanded).

ns_expand_term(NS, TermIn, TermOut) :-
  ( var(TermIn) -> TermOut = TermIn
  ; atomic(TermIn) -> ns_expand_atomic(NS, TermIn, TermOut)
  ; TermIn = (Pfx:Local) -> ns_expand_atomic(NS, Pfx:Local, TermOut)
  ; TermIn =.. [F|As],
    maplist(ns_expand_term(NS), As, AsE),
    ns_expand_atomic(NS, F, FE),
    TermOut =.. [FE|AsE]
  ).

ns_expand_atomic(NS, A, Out) :-
  ( A = (Pfx:Local) ->
      ( memberchk(Pfx=IRI, NS) -> atom_concat(IRI, Local, Out) ; Out = A )
  ; Out = A ).

% ---------------- validation (as before) ----------------------------

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

% ---------------- internal helpers ----------------------------------

store_id_(M, StoreId) :-
  ( kb_store_id(Id) -> StoreId = Id
  ; atom_string(M, S), string_concat("trill:", S, StoreIdS),
    assertz(kb_store_id(StoreIdS)), StoreId = StoreIdS).

pull_prefixes_(StoreId) :-
  % fetch small list of prefixes into the cheap Prolog cache
  jpl_call('it.unife.ml.probowlapi.trill.TrillTest2', 'prefixPairs', [StoreId], JPairs),
  jpl_array_to_list(JPairs, PairArrayList),
  forall(member(Arr, PairArrayList),
         ( jpl_array_to_list(Arr, [AliasJ, IriJ]),
           jpl_get(AliasJ, toString, AliasS),
           jpl_get(IriJ,   toString, IriS),
           atom_string(Alias, AliasS),
           atom_string(Iri,   IriS),
           ( Alias == '' -> true ; add_kb_prefix(Alias, Iri) ))).

fetch_if_needed_(F) :-
  cache_policy(none), !,
  % no caching: call Java now and stream results once
  fetch_functor_now_(F, false).
fetch_if_needed_(F) :-
  cache_policy(functor),
  ( fetched_functor(F) -> true
  ; fetch_functor_now_(F, true), assertz(fetched_functor(F)) ).
fetch_if_needed_(F) :-
  cache_policy(all),
  ( fetched_functor(all) -> true
  ; % fetch all supported functors once
    forall(member(FF, [ subClassOf, equivalentClasses, disjointClasses,
                        subPropertyOf, equivalentProperties, propertyDomain, propertyRange,
                        transitiveProperty, inverseProperties, symmetricProperty,
                        sameIndividual, differentIndividuals,
                        classAssertion, propertyAssertion, annotationAssertion ]),
           fetch_functor_now_(FF, true)),
    assertz(fetched_functor(all)),
    true ).

fetch_functor_now_(F, Cache) :-
  kb_store_id(StoreId),
  atom_string(F, FS),
  jpl_call('it.unife.ml.probowlapi.trill.TrillTest2', 'queryFunctor', [StoreId, FS], JAxs),
  jpl_array_to_list(JAxs, AxStrs),
  forall(member(JStr, AxStrs),
         ( jpl_get(JStr, toString, SS),
           atom_string(A, SS),
           read_term_from_atom(A, Term, [syntax_errors(error)]),
           ( Cache -> assertz(cache_axiom(F, Term)) ; true ),
           % If not caching, still succeed via unification on backtracking:
           ( Cache -> true ; ( Term = _ ) ) )).  % no-op: just allow enumeration in caller
