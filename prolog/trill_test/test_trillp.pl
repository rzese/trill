:- module(test_trillp,
  [test_trillp/0]).
:- use_module(library(plunit)).

test_trillp:-
    trill:set_algorithm(trillp),
    run_tests([trillp_biopax,
    trillp_dbpedia,
    trillp_brca,
    trillp_commander,
    trillp_johnEmployee,
    trillp_peoplePets,
    trillp_vicodi,
    trillp_pizza]).


:- use_module(library(trill_test/trill_test)).

:- begin_tests(trillp_brca, []).

:- ensure_loaded(library('examples/BRCA.pl')).

test(rkb_brca):-
  run((reload_kb(false),true)).
test(p_wlbrcr_h):-
  run((prob_instanceOf('WomanUnderLifetimeBRCRisk','Helen',Prob),close_to(Prob,0.123))).
test(ne_wlbrcr_h):-
  run((instanceOf('WomanUnderLifetimeBRCRisk','Helen',Expl),
       test_formula(Expl,+[*([subClassOf('Woman', 'WomanUnderLifetimeBRCRisk'), +[*([classAssertion('WomanAged3040', 'Helen'), +[*([equivalentClasses(['WomanUnderShortTermBRCRisk', intersectionOf(['Woman', someValuesFrom(hasRisk, 'ShortTermBRCRisk')])]), subClassOf('WomanAged3040', 'WomanUnderShortTermBRCRisk')]), subClassOf('WomanAged3040', 'Woman')]]), classAssertion('Woman', 'Helen'), *([classAssertion('PostmenopausalWoman', 'Helen'), subClassOf('PostmenopausalWoman', 'Woman')]), *([classAssertion('WomanTakingEstrogen', 'Helen'), subClassOf('WomanTakingEstrogen', 'Woman')])]])]))).
test(p_wa_wulbrcr):-
  run((prob_sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',Prob),close_to(Prob,0.123))).
test(ne_wa_wulbrcr):-
  run((sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',Expl),
       test_formula(Expl,+[*([subClassOf('Woman', 'WomanUnderLifetimeBRCRisk'), +[*([equivalentClasses(['WomanUnderShortTermBRCRisk', intersectionOf(['Woman', someValuesFrom(hasRisk, 'ShortTermBRCRisk')])]), subClassOf('WomanAged3040', 'WomanUnderShortTermBRCRisk')]), subClassOf('WomanAged3040', 'Woman')]])]))).

:- end_tests(trillp_brca).


:- begin_tests(trillp_vicodi, []).

:-ensure_loaded(library(examples/vicodi)).

test(rkb_v):-
  run((reload_kb(false),true)).
test(p_r_avdpf):-
  run((prob_instanceOf('vicodi:Role','vicodi:Anthony-van-Dyck-is-Painter-in-Flanders',Prob),close_to(Prob,0.27540000000000003))).
test(p_p_r):-
  run((prob_sub_class('vicodi:Painter','vicodi:Role',Prob),close_to(Prob,0.30600000000000005))).

:- end_tests(trillp_vicodi).


:- begin_tests(trillp_commander, []).

:-ensure_loaded(library(examples/commander)).

test(rkb_c):-
  run((reload_kb(false),true)).
test(e_c_j):-
  run((instanceOf(commander,john,Expl),
       test_formula(Expl,+[*([equivalentClasses([guard, soldier]), classAssertion(allValuesFrom(commands, guard), john), subClassOf(allValuesFrom(commands, soldier), commander)])])
  )).

:- end_tests(trillp_commander).


:- begin_tests(trillp_peoplePets, []).

:-ensure_loaded(library(examples/peoplePets)).

test(rkb_pp):-
  run((reload_kb(false),true)).
test(p_nl_k):-
  run((prob_instanceOf('natureLover','Kevin',Prob),close_to(Prob,0.348))).
test(ne_nl_k):-
  run((instanceOf('natureLover','Kevin',Expl),
       test_formula(Expl,+[*([subClassOf('http://cohse.semanticweb.org/ontologies/people#cat', 'http://cohse.semanticweb.org/ontologies/people#pet'), subClassOf(someValuesFrom('http://cohse.semanticweb.org/ontologies/people#has_animal', 'http://cohse.semanticweb.org/ontologies/people#pet'), 'http://cohse.semanticweb.org/ontologies/people#natureLover'), +[*([classAssertion('http://cohse.semanticweb.org/ontologies/people#cat', 'http://cohse.semanticweb.org/ontologies/people#Fluffy'), propertyAssertion('http://cohse.semanticweb.org/ontologies/people#has_animal', 'http://cohse.semanticweb.org/ontologies/people#Kevin', 'http://cohse.semanticweb.org/ontologies/people#Fluffy')]), *([classAssertion('http://cohse.semanticweb.org/ontologies/people#cat', 'http://cohse.semanticweb.org/ontologies/people#Tom'), propertyAssertion('http://cohse.semanticweb.org/ontologies/people#has_animal', 'http://cohse.semanticweb.org/ontologies/people#Kevin', 'http://cohse.semanticweb.org/ontologies/people#Tom')])]])]))).

:- end_tests(trillp_peoplePets).


:- begin_tests(trillp_biopax, []).

:-ensure_loaded(library(examples/biopaxLevel3)).

test(rkb_bp):-
  run((reload_kb(false),true)).
test(p_twbr_e):-
  run((prob_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Prob),close_to(Prob,0.98))).

:- end_tests(trillp_biopax).


:- begin_tests(trillp_dbpedia, []).

:-ensure_loaded(library('examples/DBPedia.pl')).

test(rkb_dbp):-
  run((reload_kb(false),true)).
test(p_p_pp):-
  run((prob_sub_class('dbpedia:Place','dbpedia:PopulatedPlace',Prob),close_to(Prob,0.8273765902816))).
test(ae_p_pp):-
  run((sub_class('dbpedia:Place','dbpedia:PopulatedPlace',Expl),
       test_formula(Expl,+[*([subClassOf('http://dbpedia.org/ontology/Place', 'http://dbpedia.org/ontology/Settlement'), +[*([equivalentClasses(['http://dbpedia.org/ontology/A0_144_', intersectionOf(['http://dbpedia.org/ontology/Place', 'http://dbpedia.org/ontology/PopulatedPlace'])]), subClassOf('http://dbpedia.org/ontology/Settlement', 'http://dbpedia.org/ontology/A0_144_')]), subClassOf('http://dbpedia.org/ontology/Settlement', 'http://dbpedia.org/ontology/PopulatedPlace')]]), subClassOf('http://dbpedia.org/ontology/Place', 'http://dbpedia.org/ontology/PopulatedPlace'), *([equivalentClasses(['http://dbpedia.org/ontology/A73_A0_', intersectionOf(['http://dbpedia.org/ontology/PopulatedPlace', 'http://dbpedia.org/ontology/Settlement'])]), subClassOf('http://dbpedia.org/ontology/Place', 'http://dbpedia.org/ontology/A73_A0_')])])
  )).

:- end_tests(trillp_dbpedia).


:- begin_tests(trillp_johnEmployee, []).

:-ensure_loaded(library(examples/johnEmployee)).

test(rkb_je):-
  run((reload_kb(false),true)).
test(e_p_j):-
  run((instanceOf('johnEmployee:person','johnEmployee:john',Expl),
       test_formula(Expl,+[*([classAssertion('http://example.foo#employee', 'http://example.foo#john'), subClassOf('http://example.foo#employee', 'http://example.foo#worker'), subClassOf('http://example.foo#worker', 'http://example.foo#person')])])
  )).
  
:- end_tests(trillp_johnEmployee).

:- begin_tests(trillp_pizza, []).

:- ensure_loaded(library(examples/pizza)).

test(rkb_pizza):-
  run((reload_kb(false),true)).
test(p_inc_kb):-
  run((prob_inconsistent_theory(Prob),close_to(Prob,0.0))).
test(p_uns_tof):-
  run((prob_unsat('tofu',Prob),close_to(Prob,1.0))).
test(e_uns_tof):-
  run((unsat('tofu',Expl),
       test_formula(Expl,+[*([disjointClasses([cheeseTopping, vegetableTopping]), subClassOf(soyCheeseTopping, cheeseTopping), subClassOf(soyCheeseTopping, vegetableTopping), subClassOf(tofu, soyCheeseTopping)])])
  )).

:- end_tests(trillp_pizza).
