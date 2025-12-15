/** <module> test_trill

Test suite for the standard TRILL algorithm.

## Overview

This module contains PLUnit tests for the TRILL (Tableau Reasoner for
descrIption Logics in Prolog) algorithm. It tests various types of
queries across multiple knowledge bases.

## Test Categories

### trill_biopax
Tests subsumption queries on the BioPAX metabolic pathways ontology.
- Probabilistic subsumption queries
- Explanation extraction
- All explanations collection

### trill_dbpedia
Tests on the DBPedia Wikipedia extract ontology.

### trill_brca
Tests on the breast cancer risk factor ontology.
- Instance checking with probabilities
- Subsumption queries

### trill_peoplePets
Tests probabilistic instance checking with property chains.

### trill_vicodi
Tests on the VICODI European history ontology.

### trill_pizza
Tests unsatisfiability detection and inconsistency checking.

### non_det
Tests non-deterministic rule application (or_rule).

### local_cons
Tests local consistency vs global inconsistency.

## Running Tests

```prolog
?- test_trill.
```

Or run individual test groups:
```prolog
?- run_tests([trill_brca]).
```

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(test_trill,
  [test_trill/0]).
:- use_module(library(plunit)).

/**
 * test_trill is det
 *
 * Runs all TRILL algorithm tests.
 * Sets the algorithm to 'trill' and executes all test groups.
 */
test_trill_prob:-
    trill:set_algorithm(trill),
    run_tests([trill_biopax,
    %trill_biopax_rdf,
    trill_dbpedia,
    trill_brca,
    trill_peoplePets,
    trill_vicodi,
    trill_pizza,
    non_det,
    local_cons
    ]).

:- use_module(library(trill_test/trill_test)).

% =============================================================================
% BRCA Tests - Breast Cancer Risk Factor Ontology
% =============================================================================
:- begin_tests(trill_brca, []).

:- consult(library('examples/BRCA.pl')).

test(p_wlbrcr_h):-
  run((prob_instanceOf('WomanUnderLifetimeBRCRisk','Helen',Prob),close_to(Prob,0.123))).
test(p_wa_wulbrcr):-
  run((prob_sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',Prob),close_to(Prob,0.123))).

:- end_tests(trill_brca).

% =============================================================================
% VICODI Tests - European History Ontology
% =============================================================================
:- begin_tests(trill_vicodi, []).

:- consult(library(examples/vicodi)).

test(p_r_avdpf):-
  run((prob_instanceOf('vicodi:Role','vicodi:Anthony-van-Dyck-is-Painter-in-Flanders',Prob),close_to(Prob,0.27540000000000003))).
test(p_p_r):-
  run((prob_sub_class('vicodi:Painter','vicodi:Role',Prob),close_to(Prob,0.30600000000000005))).

:- end_tests(trill_vicodi).

% =============================================================================
% PeoplePets Tests - Probabilistic Reasoning
% =============================================================================
:- begin_tests(trill_peoplePets, []).

:- consult(library(examples/peoplePets)).

test(p_nl_k):-
  run((prob_instanceOf('natureLover','Kevin',Prob),close_to(Prob,0.8696))).

:- end_tests(trill_peoplePets).

% =============================================================================
% BioPAX Tests - Metabolic Pathways
% =============================================================================
:- begin_tests(trill_biopax, []).

:- consult(library(examples/biopaxLevel3)).

test(p_twbr_e):-
  run((prob_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Prob),close_to(Prob,0.98))).

:- end_tests(trill_biopax).

:- begin_tests(trill_biopax_rdf, []).

:- ensure_loaded(library(trill)).

test(p_twbr_e):-
  run((init_trill(trill),load_owl_kb('../examples/biopaxLevel3_rdf.owl'),prob_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Prob),close_to(Prob,0.98))).


:- end_tests(trill_biopax_rdf).


:- begin_tests(trill_dbpedia, []).

:- consult(library('examples/DBPedia.pl')).

test(p_p_pp):-
  run((prob_sub_class('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/PopulatedPlace',Prob),close_to(Prob,0.8273765902816))).


:- end_tests(trill_dbpedia).


% =============================================================================

:- begin_tests(trill_pizza, []).

:- consult(library(examples/pizza)).

test(p_uns_tof):-
  run((prob_unsat('tofu',Prob),close_to(Prob,1.0))).

:- end_tests(trill_pizza).

:- begin_tests(non_det, []).

:- consult(library(examples/example_or_rule)).

test(p_u_a):-
  run((prob_unsat(a,Prob),close_to(Prob,0.03393568))).



:- end_tests(non_det).

:- begin_tests(non_det_max, []).

:- begin_tests(local_cons, []).

:- consult(library(examples/local_inconsistent_kb)).


%test(p_in):-
%  run((prob_inconsistent_theory(Prob),close_to(Prob,1.0))).

%test(e_in):-
%  run((all_inconsistent_theory(Expl),
%       same_expl(Expl,[[classAssertion(a, ind1),classAssertion(complementOf(x), ind2),subClassOf(a, allValuesFrom(r, x)),propertyAssertion(r, ind1, ind2)]])
%  )).

test(p_pv_3_4):-
  run((prob_property_value(t,ind3,ind4,Prob),close_to(Prob,1.0))).

test(p_i_x_4):-
  run((prob_instanceOf(x,ind4,Prob),close_to(Prob,1.0))).

:- end_tests(local_cons).
