:- module(test_tornado,
  [test_tornado/0]).
:- use_module(library(plunit)).

test_tornado:-
    trill:set_algorithm(tornado),
    run_tests([tornado_biopax,
    %tornado_biopax_rdf,
    tornado_dbpedia,
    tornado_brca,
    tornado_commander,
    tornado_johnEmployee,
    tornado_peoplePets,
    tornado_vicodi,
    tornado_pizza,
    non_det,
    local_cons]).

:- use_module(library(trill_test/trill_test)).

:- begin_tests(tornado_brca, []).

:- consult(library('examples/BRCA.pl')).

test(p_wlbrcr_h):-
  run((prob_instanceOf('WomanUnderLifetimeBRCRisk','Helen',Prob),close_to(Prob,0.123))).
test(ne_wlbrcr_h):-
  run((instanceOf('WomanUnderLifetimeBRCRisk','Helen',ListExpl),length(ListExpl,Count), Count = 5)).
test(p_wa_wulbrcr):-
  run((prob_sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',Prob),close_to(Prob,0.123))).
test(ne_wa_wulbrcr):-
  run((sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',ListExpl),length(ListExpl,Count), Count = 2)).

:- end_tests(tornado_brca).


:- begin_tests(tornado_vicodi, []).

:- consult(library(examples/vicodi)).

test(p_r_avdpf):-
  run((prob_instanceOf('vicodi:Role','vicodi:Anthony-van-Dyck-is-Painter-in-Flanders',Prob),close_to(Prob,0.27540000000000003))).
test(p_p_r):-
  run((prob_sub_class('vicodi:Painter','vicodi:Role',Prob),close_to(Prob,0.30600000000000005))).

:- end_tests(tornado_vicodi).


:- begin_tests(tornado_commander, []).

:- consult(library(examples/commander)).

test(e_c_j):-
  run((instanceOf(commander,john,Expl),
    same_expl(Expl,[[equivalentClasses([guard, soldier]), classAssertion(allValuesFrom(commands, guard), john), subClassOf(allValuesFrom(commands, soldier), commander)]])
  )).

:- end_tests(tornado_commander).


:- begin_tests(tornado_peoplePets, []).

:- consult(library(examples/peoplePets)).

test(p_nl_k):-
  run((prob_instanceOf('natureLover','Kevin',Prob),close_to(Prob,0.8696))).
test(ne_nl_k):-
  run((instanceOf('natureLover','Kevin',ListExpl),length(ListExpl,Count),Count = 3)).


:- end_tests(tornado_peoplePets).


:- begin_tests(tornado_biopax, []).

:- consult(library(examples/biopaxLevel3)).

test(p_twbr_e):-
  run((prob_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Prob),close_to(Prob,0.98))).
test(e_twbr_e):-
  run((sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',ListExpl),
    same_expl(ListExpl,[[subClassOf('http://www.biopax.org/release/biopax-level3.owl#BiochemicalReaction','http://www.biopax.org/release/biopax-level3.owl#Conversion'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#Conversion','http://www.biopax.org/release/biopax-level3.owl#Interaction'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#Interaction','http://www.biopax.org/release/biopax-level3.owl#Entity'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#TransportWithBiochemicalReaction','http://www.biopax.org/release/biopax-level3.owl#BiochemicalReaction')],
[subClassOf('http://www.biopax.org/release/biopax-level3.owl#Conversion','http://www.biopax.org/release/biopax-level3.owl#Interaction'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#Interaction','http://www.biopax.org/release/biopax-level3.owl#Entity'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#Transport','http://www.biopax.org/release/biopax-level3.owl#Conversion'),subClassOf('http://www.biopax.org/release/biopax-level3.owl#TransportWithBiochemicalReaction','http://www.biopax.org/release/biopax-level3.owl#Transport')]])
  )).
test(ae_twbr_e):-
  run((all_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Expl),
       same_expl(Expl,[[subClassOf('http://www.biopax.org/release/biopax-level3.owl#BiochemicalReaction', 'http://www.biopax.org/release/biopax-level3.owl#Conversion'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#Conversion', 'http://www.biopax.org/release/biopax-level3.owl#Interaction'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#Interaction', 'http://www.biopax.org/release/biopax-level3.owl#Entity'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#TransportWithBiochemicalReaction', 'http://www.biopax.org/release/biopax-level3.owl#BiochemicalReaction')],
       [subClassOf('http://www.biopax.org/release/biopax-level3.owl#Conversion', 'http://www.biopax.org/release/biopax-level3.owl#Interaction'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#Interaction', 'http://www.biopax.org/release/biopax-level3.owl#Entity'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#Transport', 'http://www.biopax.org/release/biopax-level3.owl#Conversion'),
       subClassOf('http://www.biopax.org/release/biopax-level3.owl#TransportWithBiochemicalReaction', 'http://www.biopax.org/release/biopax-level3.owl#Transport')]])
  )).

:- end_tests(tornado_biopax).

:- begin_tests(tornado_biopax_rdf, []).

:- ensure_loaded(library(trill)).

test(p_twbr_e):-
  run((init_trill(tornado),load_owl_kb('../examples/biopaxLevel3_rdf.owl'),prob_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Prob),close_to(Prob,0.98))).

:- end_tests(tornado_biopax_rdf).


:- begin_tests(tornado_dbpedia, []).

:- consult(library('examples/DBPedia.pl')).

test(p_p_pp):-
  run((prob_sub_class('dbpedia:Place','dbpedia:PopulatedPlace',Prob),close_to(Prob,0.8273765902816))).
test(ae_p_pp):-
  run((all_sub_class('dbpedia:Place','dbpedia:PopulatedPlace',Expl),
       same_expl(Expl,[[equivalentClasses(['http://dbpedia.org/ontology/A73_A0_',intersectionOf(['http://dbpedia.org/ontology/PopulatedPlace','http://dbpedia.org/ontology/Settlement'])]),subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/A73_A0_')],[subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/PopulatedPlace')],[equivalentClasses(['http://dbpedia.org/ontology/A0_144_',intersectionOf(['http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/PopulatedPlace'])]),subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/Settlement'),subClassOf('http://dbpedia.org/ontology/Settlement','http://dbpedia.org/ontology/A0_144_')],[subClassOf('http://dbpedia.org/ontology/Place','http://dbpedia.org/ontology/Settlement'),subClassOf('http://dbpedia.org/ontology/Settlement','http://dbpedia.org/ontology/PopulatedPlace')]])
  )).

:- end_tests(tornado_dbpedia).


:- begin_tests(tornado_johnEmployee, []).

:- consult(library(examples/johnEmployee)).

test(e_p_j):-
  run((instanceOf('johnEmployee:person','johnEmployee:john',Expl),
       same_expl(Expl,[[classAssertion('http://example.foo#employee', 'http://example.foo#john'), subClassOf('http://example.foo#employee', 'http://example.foo#worker'), subClassOf('http://example.foo#worker', 'http://example.foo#person')]])
  )).

:- end_tests(tornado_johnEmployee).

:- begin_tests(tornado_pizza, []).

:- consult(library(examples/pizza)).

test(p_inc_kb):-
  run((prob_inconsistent_theory(Prob),close_to(Prob,0.0))).
test(p_uns_tof):-
  run((prob_unsat('tofu',Prob),close_to(Prob,1.0))).
test(e_uns_tof):-
  run((unsat('tofu',Expl),
       same_expl(Expl,[[disjointClasses([cheeseTopping, vegetableTopping]), subClassOf(soyCheeseTopping, cheeseTopping), subClassOf(soyCheeseTopping, vegetableTopping), subClassOf(tofu, soyCheeseTopping)]])
  )).

:- end_tests(tornado_pizza).

:- begin_tests(non_det, []).

:- consult(library(examples/example_or_rule)).

test(p_u_a):-
  run((prob_unsat(a,Prob),close_to(Prob,0.03393568))).

test(e_u_a):-
  run((all_unsat(a,Expl),
  same_expl(Expl,[
      [subClassOf(a,intersectionOf([b,someValuesFrom(r,e)])),subClassOf(a,unionOf([complementOf(c),complementOf(d)])),subClassOf(b,intersectionOf([c,d]))],
      [subClassOf(a,intersectionOf([b,someValuesFrom(r,e)])),subClassOf(a,unionOf([f,allValuesFrom(r,b)])),subClassOf(a,unionOf([complementOf(c),complementOf(f)])),subClassOf(b,complementOf(e)),subClassOf(b,intersectionOf([c,d]))],
      [subClassOf(a,intersectionOf([b,someValuesFrom(r,e)])),subClassOf(a,unionOf([f,allValuesFrom(r,b)])),subClassOf(a,unionOf([intersectionOf([c,complementOf(c)]),complementOf(f)])),subClassOf(b,complementOf(e))],
      [subClassOf(a,intersectionOf([b,someValuesFrom(r,e)])),subClassOf(a,unionOf([f,allValuesFrom(r,b)])),subClassOf(b,complementOf(e)),subClassOf(b,complementOf(f))],
      [subClassOf(a,intersectionOf([b,someValuesFrom(r,e)])),subClassOf(b,complementOf(e)),subClassOf(b,intersectionOf([c,d])),subClassOf(c,intersectionOf([minCardinality(1,r),e]))]
      ])
  )).

:- end_tests(non_det).


:- begin_tests(local_cons, []).

:- consult(library(examples/local_inconsistent_kb)).

%test(p_in):-
%  run((prob_inconsistent_theory(Prob),close_to(Prob,1.0))).

test(p_pv_3_4):-
  run((prob_property_value(t,ind3,ind4,Prob),close_to(Prob,1.0))).

test(e_pv_3_4):-
  run((all_property_value(r,ind3,ind4,Expl),
       same_expl(Expl,[[subPropertyOf(s, t), subPropertyOf(t, r), subPropertyOf(u, s), propertyAssertion(u, ind3, ind4)]])
  )).

test(p_i_x_4):-
  run((prob_instanceOf(x,ind4,Prob),close_to(Prob,1.0))).

test(e_i_x_4):-
  run((all_instanceOf(x,ind4,Expl),
       same_expl(Expl,[[classAssertion(a, ind3), subClassOf(a, allValuesFrom(r, x)), subPropertyOf(s, t), subPropertyOf(t, r), subPropertyOf(u, s), propertyAssertion(u, ind3, ind4)]])
  )).

:- end_tests(local_cons).

