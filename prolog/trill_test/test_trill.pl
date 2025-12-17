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

### trill_commander
Tests universal restrictions (allValuesFrom) and equivalent classes.

### trill_johnEmployee
Tests basic instance checking and class membership.

### trill_peoplePets
Tests probabilistic instance checking with property chains.

### trill_pizza
Tests unsatisfiability detection and inconsistency checking.

### non_det
Tests non-deterministic rule application (or_rule).

### non_det_max
Tests maximum cardinality restrictions (max_rule).

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
test_trill:-
    trill:set_algorithm(trill),
    run_tests([trill_biopax,
    %trill_biopax_rdf,
    trill_dbpedia,
    trill_brca,
    trill_commander,
    trill_johnEmployee,
    trill_peoplePets,
    trill_pizza,
    non_det,
    non_det_max,
    local_cons
    ]).

:- use_module(library(trill_test/trill_test)).

% =============================================================================
% BRCA Tests - Breast Cancer Risk Factor Ontology
% =============================================================================
:- begin_tests(trill_brca, []).

:- consult(library('examples/BRCA.pl')).

test(ne_wlbrcr_h):-
  run((aggregate_all(count, (instanceOf('WomanUnderLifetimeBRCRisk','Helen',_ListExpl)), Count), Count = 5)).
test(ne_wa_wulbrcr):-
  run((aggregate_all(count, (sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',_ListExpl)), Count), Count = 2)).

:- end_tests(trill_brca).

% =============================================================================
% Commander Tests - Universal Restrictions
% =============================================================================
:- begin_tests(trill_commander, []).

:- consult(library(examples/commander)).

test(abc):-run((aggregate_all(count, axiom(_), Count), Count=6)).

test(e_c_j):-
  run((instanceOf(commander,john,Expl),
       one_of(Expl,[[equivalentClasses([':guard', ':soldier']), classAssertion(allValuesFrom(':commands', ':guard'), ':john'), subClassOf(allValuesFrom(':commands', ':soldier'), ':commander')]])
  )).

:- end_tests(trill_commander).

% =============================================================================
% PeoplePets Tests - Probabilistic Reasoning
% =============================================================================
:- begin_tests(trill_peoplePets, []).

:- consult(library(examples/peoplePets)).

test(ne_nl_k):-
  run((aggregate_all(count, (instanceOf('natureLover','Kevin',_ListExpl)), Count),Count = 3)).

:- end_tests(trill_peoplePets).

% =============================================================================
% BioPAX Tests - Metabolic Pathways
% =============================================================================
:- begin_tests(trill_biopax, []).

:- consult(library(examples/biopaxLevel3)).

test(e_twbr_e):-
  run((sub_class(':TransportWithBiochemicalReaction',':Entity',ListExpl),
       one_of(ListExpl,[[subClassOf(':BiochemicalReaction',':Conversion'),subClassOf(':Conversion',':Interaction'),subClassOf(':Interaction',':Entity'),subClassOf(':TransportWithBiochemicalReaction',':BiochemicalReaction')],
[subClassOf(':Conversion',':Interaction'),subClassOf(':Interaction',':Entity'),subClassOf(':Transport',':Conversion'),subClassOf(':TransportWithBiochemicalReaction',':Transport')]])
  )).
test(ae_twbr_e):-
  run((all_sub_class(':TransportWithBiochemicalReaction',':Entity',Expl),
       same_expl(Expl,[[subClassOf(':BiochemicalReaction', ':Conversion'),
       subClassOf(':Conversion', ':Interaction'),
       subClassOf(':Interaction', ':Entity'),
       subClassOf(':TransportWithBiochemicalReaction', ':BiochemicalReaction')],
       [subClassOf(':Conversion', ':Interaction'),
       subClassOf(':Interaction', ':Entity'),
       subClassOf(':Transport', ':Conversion'),
       subClassOf(':TransportWithBiochemicalReaction', ':Transport')]])
  )).

:- end_tests(trill_biopax).

:- begin_tests(trill_biopax_rdf, []).

:- ensure_loaded(library(trill)).

test(p_twbr_e):-
  run((init_trill(trill),load_owl_kb('../examples/biopaxLevel3_rdf.owl'),
  sub_class(':TransportWithBiochemicalReaction',':Entity',ListExpl),
       one_of(ListExpl,[[subClassOf(':BiochemicalReaction',':Conversion'),subClassOf(':Conversion',':Interaction'),subClassOf(':Interaction',':Entity'),subClassOf(':TransportWithBiochemicalReaction',':BiochemicalReaction')],
[subClassOf(':Conversion',':Interaction'),subClassOf(':Interaction',':Entity'),subClassOf(':Transport',':Conversion'),subClassOf(':TransportWithBiochemicalReaction',':Transport')]])
  )).

:- end_tests(trill_biopax_rdf).


:- begin_tests(trill_dbpedia, []).

:- consult(library('examples/DBPedia.pl')).

test(ae_p_pp):-
  run((all_sub_class('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/PopulatedPlace',Expl),
       ( same_expl(Expl,[[equivalentClasses(['http://dbpedia.org/ontology/A73_A0_',intersectionOf(['http://dbpedia.org/ontology/PopulatedPlace','http://dbpedia.org/ontology/Settlement'])]),subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/A73_A0_')],[subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/PopulatedPlace')],[equivalentClasses(['http://dbpedia.org/ontology/A0_144_',intersectionOf(['http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/PopulatedPlace'])]),subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/Settlement'),subClassOf('http://dbpedia.org/ontology/Settlement','http://dbpedia.org/ontology/A0_144_')],[subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/Settlement'),subClassOf('http://dbpedia.org/ontology/Settlement','http://dbpedia.org/ontology/PopulatedPlace')]])
       ;
       same_expl(Expl,[[equivalentClasses([':A73_A0_',intersectionOf([':PopulatedPlace',':Settlement'])]),subClassOf(':Place',':A73_A0_')],[subClassOf(':Place',':PopulatedPlace')],[equivalentClasses([':A0_144_',intersectionOf([':Place',':PopulatedPlace'])]),subClassOf(':Place',':Settlement'),subClassOf(':Settlement',':A0_144_')],[subClassOf(':Place',':Settlement'),subClassOf(':Settlement',':PopulatedPlace')]])
      ),!
  )).

:- end_tests(trill_dbpedia).


:- begin_tests(trill_johnEmployee, []).

:- consult(library(examples/johnEmployee)).

test(e_p_j):-
  run((instanceOf('johnEmployee:person','johnEmployee:john',Expl),
       same_expl([Expl],[[classAssertion('johnEmployee:employee', 'johnEmployee:john'), subClassOf('johnEmployee:employee', 'johnEmployee:worker'), subClassOf('johnEmployee:worker', 'johnEmployee:person')]])
  )).
  
:- end_tests(trill_johnEmployee).


:- begin_tests(trill_pizza, []).

:- consult(library(examples/pizza)).

test(e_uns_tof):-
  run((unsat('tofu',Expl),
       same_expl([Expl],[[disjointClasses([':cheeseTopping', ':vegetableTopping']), subClassOf(':soyCheeseTopping', ':cheeseTopping'), subClassOf(':soyCheeseTopping', ':vegetableTopping'), subClassOf(':tofu', ':soyCheeseTopping')]])
  )).

:- end_tests(trill_pizza).

:- begin_tests(non_det, []).

:- consult(library(examples/example_or_rule)).

test(e_u_a):-
  run((all_unsat(a,Expl),
  same_expl(Expl,[
      [subClassOf(':a',intersectionOf([':b',someValuesFrom(':r',':e')])),
      subClassOf(':a',unionOf([complementOf(':c'),complementOf(':d')])),
      subClassOf(':b',intersectionOf([':c',':d']))],
      [subClassOf(':a',intersectionOf([':b',someValuesFrom(':r',':e')])),
      subClassOf(':a',unionOf([':f',allValuesFrom(':r',':b')])),
      subClassOf(':a',unionOf([complementOf(':c'),complementOf(':f')])),
      subClassOf(':b',complementOf(':e')),
      subClassOf(':b',intersectionOf([':c',':d']))],
      [subClassOf(':a',intersectionOf([':b',someValuesFrom(':r',':e')])),
      subClassOf(':a',unionOf([':f',allValuesFrom(':r',':b')])),
      subClassOf(':a',unionOf([intersectionOf([':c',complementOf(':c')]),complementOf(':f')])),
      subClassOf(':b',complementOf(':e'))],
      [subClassOf(':a',intersectionOf([':b',someValuesFrom(':r',':e')])),
      subClassOf(':a',unionOf([':f',allValuesFrom(':r',':b')])),
      subClassOf(':b',complementOf(':e')),
      subClassOf(':b',complementOf(':f'))],
      [subClassOf(':a',intersectionOf([':b',someValuesFrom(':r',':e')])),
    subClassOf(':b',complementOf(':e')),
  subClassOf(':b',intersectionOf([':c',':d'])),
subClassOf(':c',intersectionOf([minCardinality(1,':r'),':e']))]
      ])
  )).

:- end_tests(non_det).

:- begin_tests(non_det_max, []).

:- consult(library(examples/example_max_rule)).

test(e_i):-
  run((all_inconsistent_theory(Expl),
  same_expl(Expl,[[disjointClasses([':b',':e',':f']),classAssertion(':a',':1'),classAssertion(':c',':3'),classAssertion(':c',':4'),classAssertion(':e',':3'),classAssertion(':f',':4'),subClassOf(':a',maxCardinality(1,':s',':c')),propertyAssertion(':s',':1',':3'),propertyAssertion(':s',':1',':4')],
                  [disjointClasses([':b',':e',':f']),classAssertion(':a',':1'),classAssertion(':b',':2'),classAssertion(':c',':2'),classAssertion(':c',':4'),classAssertion(':f',':4'),subClassOf(':a',maxCardinality(1,':s',':c')),propertyAssertion(':s',':1',':2'),propertyAssertion(':s',':1',':4')],
                  [disjointClasses([':b',':e',':f']),classAssertion(':a',':1'),classAssertion(':b',':2'),classAssertion(':c',':2'),classAssertion(':c',':3'),classAssertion(':e',':3'),subClassOf(':a',maxCardinality(1,':s',':c')),propertyAssertion(':s',':1',':2'),propertyAssertion(':s',':1',':3')]
                ])
  )).

:- end_tests(non_det_max).


:- begin_tests(local_cons, []).

:- consult(library(examples/local_inconsistent_kb)).


%test(p_in):-
%  run((prob_inconsistent_theory(Prob),close_to(Prob,1.0))).

%test(e_in):-
%  run((all_inconsistent_theory(Expl),
%       same_expl(Expl,[[classAssertion(a, ind1),classAssertion(complementOf(x), ind2),subClassOf(a, allValuesFrom(r, x)),propertyAssertion(r, ind1, ind2)]])
%  )).

test(e_pv_3_4):-
  run((all_property_value(r,ind3,ind4,Expl),
       same_expl(Expl,[[subPropertyOf(':s', ':t'), subPropertyOf(':t', ':r'), subPropertyOf(':u', ':s'), propertyAssertion(':u', ':ind3', ':ind4')]])
  )).

test(e_i_x_4):-
  run((all_instanceOf(':x',':ind4',Expl),
       same_expl(Expl,[[classAssertion(':a', ':ind3'), subClassOf(':a', allValuesFrom(':r', ':x')), subPropertyOf(':s', ':t'), subPropertyOf(':t', ':r'), subPropertyOf(':u', ':s'), propertyAssertion(':u', ':ind3', ':ind4')]])
  )).

:- end_tests(local_cons).
