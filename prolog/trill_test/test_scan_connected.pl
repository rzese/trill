/** <module> test_scan_connected

Lightweight PLUnit tests for the parallel connected-individuals search.
This file is isolated from the heavier TRILL ontology fixtures to keep
startup and debugging simple.
*/

:- module(test_scan_connected, [test_scan_connected/0]).
:- use_module(library(plunit)).
:- ensure_loaded('../internal_parser.pl').

:- dynamic propertyAssertion/3.

% Minimal axiom accessor used by the connectivity search in this test module
get_axiom_propertyAssertion(_M, P, S, O) :-
  propertyAssertion(P,S,O).

%% test_scan_connected is det
%  Runs only the scan_connected test group.
test_scan_connected :-
  run_tests([scan_connected]).

setup_scan_connected :-
  retractall(test_scan_connected:propertyAssertion(_,_,_)),
  assertz(test_scan_connected:propertyAssertion(r,a,b)),
  assertz(test_scan_connected:propertyAssertion(r,b,c)),
  assertz(test_scan_connected:propertyAssertion(r,c,d)),
  assertz(test_scan_connected:propertyAssertion(r,e,f)).

cleanup_scan_connected :-
  retractall(test_scan_connected:propertyAssertion(_,_,_)).

:- begin_tests(scan_connected, []).

% Basic reachability from a single seed
test(parallel_bfs_reaches_all, [setup(test_scan_connected:setup_scan_connected), cleanup(test_scan_connected:cleanup_scan_connected), nondet]) :-
  test_scan_connected:scan_connected_individuals_parallel(user, [a], Connected),
  assertion(Connected == [a,b,c,d]).

% Isolated component should stay isolated
test(parallel_bfs_handles_isolated, [setup(test_scan_connected:setup_scan_connected), cleanup(test_scan_connected:cleanup_scan_connected), nondet]) :-
  test_scan_connected:scan_connected_individuals_parallel(user, [e], Connected),
  assertion(Connected == [e,f]).

% Merged frontier should avoid duplicates
test(parallel_bfs_merges_frontier, [setup(test_scan_connected:setup_scan_connected), cleanup(test_scan_connected:cleanup_scan_connected), nondet]) :-
  test_scan_connected:scan_connected_individuals_parallel(user, [a,c], Connected),
  assertion(Connected == [a,b,c,d]).

:- end_tests(scan_connected).
