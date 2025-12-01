% -*- mode: prolog; coding: utf-8 -*-
/** <module> TRILL <-> OWLAPI bridge (via JPL)

This module replaces the old RDF/Prolog parser with a Java OWL API bridge.
The ontology is stored only in Java.  Prolog queries for axioms are
forwarded to Java on demand.  A tiny per-kind cache is provided on the
Prolog side for hot queries.

Java side: it.unife.ml.probowlapi.trill.TrillTest3 (see java/ below).
JPL version: 7.6.1  |  Java: 11

*/

:- module(java_parser_3, []).

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

% TRILL declares: :- meta_predicate axiom(:).
% We implement axiom(M:Pattern) by:
%  1) generating overlay axioms,
%  2) asking Java for the axiom KIND and enumerating,
%  3) letting Prolog unification handle Pattern (variables are okay).

:- multifile trill:axiom/1.
trill:axiom(M:Pattern) :-
    module_atom(M, MAtom),
    % 1) enumerate overlay first
    kb_overlay_axiom(MAtom, Ax),
    Ax = Pattern.

trill:axiom(M:Pattern) :-
    module_atom(M, MAtom),
    functor(Pattern, Kind, _Arity),
    % fetch cached list or ask Java
    ( kb_axiom_cache(MAtom, Kind, List)
    -> true
    ;  ask_java_for_axioms(MAtom, Kind, List),
       assertz(kb_axiom_cache(MAtom, Kind, List))
    ),
    member(P, List),
    P = Pattern.

ask_java_for_axioms(M, Kind, Terms) :-
    java_class(JCls),
    % returns a Java array of org.jpl7.Term representing *ground* TRILL axioms
    jpl_call(JCls, 'axiomsFor', [M, Kind], JavaArray),
    % Turn array of Terms into a Prolog list of terms
    jpl_array_to_terms(JavaArray, Terms).


:- multifile trill:add_axiom/1.
trill:add_axiom(M:Axiom) :-
    module_atom(M, MAtom),
    assertz(kb_overlay_axiom(MAtom, Axiom)),
    retractall(kb_axiom_cache(MAtom,_,_)).

trill:add_axioms(M:Axioms) :-
    module_atom(M, MAtom),
    must_be(list, Axioms),
    forall(member(Ax,Axioms), assertz(kb_overlay_axiom(MAtom, Ax))),
    retractall(kb_axiom_cache(MAtom,_,_)).

trill:remove_axiom(M:Axiom) :-
    module_atom(M, MAtom),
    retractall(kb_overlay_axiom(MAtom, Axiom)),
    retractall(kb_axiom_cache(MAtom,_,_)).

trill:remove_axioms(M:Axioms) :-
    module_atom(M, MAtom),
    must_be(list, Axioms),
    forall(member(Ax,Axioms), retractall(kb_overlay_axiom(MAtom, Ax))),
    retractall(kb_axiom_cache(MAtom,_,_)).














init_java_bridge :-
    % Point to your assembled JAR (jar-with-dependencies)
    Jar = 'prob-owlapi-2.0.8.jar',
    jpl_set_default_jvm_opts(['-Xms128m','-Xmx1g',
                              classpath(Jar)]).

% === State ===================================================================

:- dynamic kb_current_module/1.            % last module which called set_up/1
:- dynamic kb_java_ready/1.                % module whose Java store is ready
:- dynamic kb_axiom_cache/3.               % kb_axiom_cache(M,Kind,ListOfTerms)
:- dynamic kb_overlay_axiom/2.             % additional axioms in Prolog overlay: kb_overlay_axiom(M, Axiom)
:- dynamic kb_prefix_cache/2.              % kb_prefix_cache(M,Pairs)

% === TRILL multifile hooks ===================================================
% All these predicates belong to module 'trill' but are defined here.
% This matches TRILL's public interface (see trill.pl multifile declarations).

:- multifile trill:axiom/1.
:- multifile trill:add_axiom/1.
:- multifile trill:add_axioms/1.
:- multifile trill:remove_axiom/1.
:- multifile trill:remove_axioms/1.
:- multifile trill:add_kb_prefix/2.
:- multifile trill:add_kb_prefixes/1.
:- multifile trill:remove_kb_prefix/1.
:- multifile trill:remove_kb_prefix/2.
:- multifile trill:kb_prefixes/1.
:- multifile trill:load_owl/1.
:- multifile trill:load_owl_from_string/1.

% === Config ==================================================================

java_class('it.unife.ml.probowlapi.trill.TrillTest3').

% Utility to make sure JVM is up before first call; we assume classpath is
% properly set (see README below).
ensure_jvm_started :-
    ( jpl_get_actual_jvm_opts(_)
    -> true
    ;  true % you might jpl_set_default_jvm_opts/1 here programmatically if needed
    ).

% Get a stable atom for module M (strip M if it is a module-qualified goal)
module_atom(M0, MAtom) :-
    ( var(M0) -> throw(error(instantiation_error, module_atom/2)) ; true ),
    ( atom(M0) -> MAtom = M0
    ; M0 = _:_
    -> strip_module(M0, MAtom, _)
    ; throw(error(type_error(atom,M0), module_atom/2))
    ).

% Remember last set_up module to be used by non-meta loaders
set_current_module(M) :-
    retractall(kb_current_module(_)),
    assertz(kb_current_module(M)).

get_current_module(M) :-
    ( kb_current_module(M) -> true
    ; M = trill                % sensible default
    ).

% === Public: lifecycle =======================================================

set_up(M) :-
    module_atom(M, MAtom),
    ensure_jvm_started,
    java_class(JCls),
    % initialise per-module book-keeping on Java side
    jpl_call(JCls, 'initModule', [MAtom], _),
    retractall(kb_axiom_cache(MAtom,_,_)),
    retractall(kb_prefix_cache(MAtom,_)),
    retractall(kb_overlay_axiom(MAtom,_)),
    ( kb_java_ready(MAtom) -> true ; assertz(kb_java_ready(MAtom)) ),
    set_current_module(MAtom).

clean_up(M) :-
    module_atom(M, MAtom),
    java_class(JCls),
    ( kb_java_ready(MAtom)
    -> jpl_call(JCls, 'clear', [MAtom], _)
    ;  true
    ),
    retractall(kb_axiom_cache(MAtom,_,_)),
    retractall(kb_prefix_cache(MAtom,_)),
    retractall(kb_overlay_axiom(MAtom,_)),
    retractall(kb_java_ready(MAtom)).

% === Loading & prefixes ======================================================

% Non-meta on TRILL side; we use the last module which called set_up/1.
trill:load_owl(File) :-
    must_be(atom, File),
    get_current_module(M),
    java_class(JCls),
    jpl_call(JCls, 'loadOntologyFromFile', [M, File], _),
    retractall(kb_axiom_cache(M,_,_)),
    retractall(kb_prefix_cache(M,_)).

trill:load_owl_from_string(String) :-
    must_be(atom, String),
    get_current_module(M),
    java_class(JCls),
    jpl_call(JCls, 'loadOntologyFromString', [M, String], _),
    retractall(kb_axiom_cache(M,_,_)),
    retractall(kb_prefix_cache(M,_)).

% Prefixes are kept on Java side; expose as list of 'Alias=IRI' pairs.
trill:kb_prefixes(Pairs) :-
    get_current_module(M),
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

% Manual add/remove of prefixes:
trill:add_kb_prefix(Alias, IRI) :-
    must_be(atom, Alias), must_be(atom, IRI),
    get_current_module(M),
    java_class(JCls),
    % we forward to Java; also drop cached prefixes
    jpl_call(JCls, 'addPrefix', [M, Alias, IRI], _),
    retractall(kb_prefix_cache(M,_)).

trill:add_kb_prefixes(List) :-
    must_be(list, List),
    forall(member(A=I, List), trill:add_kb_prefix(A,I)).

trill:remove_kb_prefix(Alias) :-
    must_be(atom, Alias),
    get_current_module(M),
    java_class(JCls),
    jpl_call(JCls, 'removePrefix', [M, Alias], _),
    retractall(kb_prefix_cache(M,_)).

trill:remove_kb_prefix(Alias, IRI) :-
    must_be(atom, Alias), must_be(atom, IRI),
    get_current_module(M),
    java_class(JCls),
    jpl_call(JCls, 'removePrefixExact', [M, Alias, IRI], _),
    retractall(kb_prefix_cache(M,_)).

% === Prolog overlay for axioms ==============================================



% === The heart: axiom/1 ======================================================


