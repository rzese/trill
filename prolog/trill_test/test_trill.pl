:- module(test_trill,
  [test_trill/0]).
:- use_module(library(plunit)).

test_trill:-
    trill:set_algorithm(trill),
    run_tests([trill_biopax,
    trill_dbpedia,
    trill_brca,
    trill_commander,
    trill_johnEmployee,
    trill_peoplePets,
    trill_vicodi,
    trill_pizza]).

:- use_module(library(trill_test/trill_test)).

:- begin_tests(trill_brca, []).

:- ensure_loaded(library('examples/BRCA.pl')).

test(rkb_brca):-
  run((reload_kb(false),true)).
test(p_wlbrcr_h):-
  run((prob_instanceOf('WomanUnderLifetimeBRCRisk','Helen',Prob),close_to(Prob,0.123))).
test(ne_wlbrcr_h):-
  run((aggregate_all(count, (instanceOf('WomanUnderLifetimeBRCRisk','Helen',_ListExpl)), Count), Count = 5)).
test(p_wa_wulbrcr):-
  run((prob_sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',Prob),close_to(Prob,0.123))).
test(ne_wa_wulbrcr):-
  run((aggregate_all(count, (sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',_ListExpl)), Count), Count = 2)).

:- end_tests(trill_brca).


:- begin_tests(trill_vicodi, []).

:-ensure_loaded(library(examples/vicodi)).

test(rkb_v):-
  run((reload_kb(false),true)).
test(p_r_avdpf):-
  run((prob_instanceOf('vicodi:Role','vicodi:Anthony-van-Dyck-is-Painter-in-Flanders',Prob),close_to(Prob,0.27540000000000003))).
test(p_p_r):-
  run((prob_sub_class('vicodi:Painter','vicodi:Role',Prob),close_to(Prob,0.30600000000000005))).

:- end_tests(trill_vicodi).


:- begin_tests(trill_commander, []).

:-ensure_loaded(library(examples/commander)).

test(rkb_c):-
  run((reload_kb(false),true)).
test(e_c_j):-
  run((instanceOf(commander,john,Expl),
       one_of(Expl,[[equivalentClasses([guard, soldier]), classAssertion(allValuesFrom(commands, guard), john), subClassOf(allValuesFrom(commands, soldier), commander)]])
  )).

:- end_tests(trill_commander).


:- begin_tests(trill_peoplePets, []).

:-ensure_loaded(library(examples/peoplePets)).

test(rkb_pp):-
  run((reload_kb(false),true)).
test(p_nl_k):-
  run((prob_instanceOf('natureLover','Kevin',Prob),close_to(Prob,0.348))).
test(ne_nl_k):-
  run((aggregate_all(count, (instanceOf('natureLover','Kevin',_ListExpl)), Count),Count = 2)).

:- end_tests(trill_peoplePets).


:- begin_tests(trill_biopax, []).

:-ensure_loaded(library(examples/biopaxLevel3)).

test(rkb_bp):-
  run((reload_kb(false),true)).
test(p_twbr_e):-
  run((prob_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Prob),close_to(Prob,0.98))).
test(e_twbr_e):-
  run((sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',ListExpl),
       one_of(ListExpl,[[subClassOf('http://www.biopax.org/release/biopax-level3.owl#BiochemicalReaction','http://www.biopax.org/release/biopax-level3.owl#Conversion'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#Conversion','http://www.biopax.org/release/biopax-level3.owl#Interaction'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#Interaction','http://www.biopax.org/release/biopax-level3.owl#Entity'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#TransportWithBiochemicalReaction','http://www.biopax.org/release/biopax-level3.owl#BiochemicalReaction')],
[subClassOf('http://www.biopax.org/release/biopax-level3.owl#Conversion','http://www.biopax.org/release/biopax-level3.owl#Interaction'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#Interaction','http://www.biopax.org/release/biopax-level3.owl#Entity'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#Transport','http://www.biopax.org/release/biopax-level3.owl#Conversion'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#TransportWithBiochemicalReaction','http://www.biopax.org/release/biopax-level3.owl#Transport')]])
  )).
test(ae_twbr_e):-
  run((findall(ListExpl,sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',ListExpl),Expl),
       same_expl(Expl,[[subClassOf('http://www.biopax.org/release/biopax-level3.owl#BiochemicalReaction', 'http://www.biopax.org/release/biopax-level3.owl#Conversion'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#Conversion', 'http://www.biopax.org/release/biopax-level3.owl#Interaction'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#Interaction', 'http://www.biopax.org/release/biopax-level3.owl#Entity'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#TransportWithBiochemicalReaction', 'http://www.biopax.org/release/biopax-level3.owl#BiochemicalReaction')],
       [subClassOf('http://www.biopax.org/release/biopax-level3.owl#Conversion', 'http://www.biopax.org/release/biopax-level3.owl#Interaction'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#Interaction', 'http://www.biopax.org/release/biopax-level3.owl#Entity'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#Transport', 'http://www.biopax.org/release/biopax-level3.owl#Conversion'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#TransportWithBiochemicalReaction', 'http://www.biopax.org/release/biopax-level3.owl#Transport')]])
  )).

:- end_tests(trill_biopax).


:- begin_tests(trill_dbpedia, []).

:-ensure_loaded(library('examples/DBPedia.pl')).

test(rkb_dbp):-
  run((reload_kb(false),true)).
test(p_p_pp):-
  run((prob_sub_class('dbpedia:Place','dbpedia:PopulatedPlace',Prob),close_to(Prob,0.8273765902816))).
test(ae_p_pp):-
  run((findall(ListExpl,sub_class('dbpedia:Place','dbpedia:PopulatedPlace',ListExpl),Expl),
       same_expl(Expl,[[equivalentClasses(['http://dbpedia.org/ontology/A73_A0_',intersectionOf(['http://dbpedia.org/ontology/PopulatedPlace','http://dbpedia.org/ontology/Settlement'])]),subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/A73_A0_')],[subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/PopulatedPlace')],[equivalentClasses(['http://dbpedia.org/ontology/A0_144_',intersectionOf(['http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/PopulatedPlace'])]),subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/Settlement'),subClassOf('http://dbpedia.org/ontology/Settlement','http://dbpedia.org/ontology/A0_144_')],[subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/Settlement'),subClassOf('http://dbpedia.org/ontology/Settlement','http://dbpedia.org/ontology/PopulatedPlace')]])
  )).

:- end_tests(trill_dbpedia).


:- begin_tests(trill_johnEmployee, []).

:-ensure_loaded(library(examples/johnEmployee)).

test(rkb_je):-
  run((reload_kb(false),true)).
test(e_p_j):-
  run((instanceOf('johnEmployee:person','johnEmployee:john',Expl),
       same_expl([Expl],[[classAssertion('http://example.foo#employee', 'http://example.foo#john'), subClassOf('http://example.foo#employee', 'http://example.foo#worker'), subClassOf('http://example.foo#worker', 'http://example.foo#person')]])
  )).
  
:- end_tests(trill_johnEmployee).


:- begin_tests(trill_pizza, []).

:- ensure_loaded(library(examples/pizza)).

test(rkb_pizza):-
  run((reload_kb(false),true)).
test(p_inc_kb):-
  run((prob_inconsistent_theory(Prob),close_to(Prob,0.0))).
test(p_uns_tof):-
  run((prob_unsat('tofu',Prob),close_to(Prob,1.0))).
test(e_uns_tof):-
  run((unsat('tofu',Expl),
       same_expl([Expl],[[disjointClasses([cheeseTopping, vegetableTopping]), subClassOf(soyCheeseTopping, cheeseTopping), subClassOf(soyCheeseTopping, vegetableTopping), subClassOf(tofu, soyCheeseTopping)]])
  )).

:- end_tests(trill_pizza).

