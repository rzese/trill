/** <module> tornado_internal

This module implements TORNADO (Trill OveR BDDs for Approximate reasoning
in Description logics with Or), a BDD-based probabilistic reasoning engine.

## Overview

TORNADO extends TRILL's tableau algorithm by building Binary Decision
Diagrams (BDDs) incrementally during the completion process. This approach
enables efficient computation of probabilities for queries over large
probabilistic knowledge bases.

## Key Features

1. **Incremental BDD Construction**: BDDs are built during tableau expansion
   rather than after finding all explanations

2. **Environment Management**: BDD environment (via CUDD library) is managed
   throughout the query lifecycle

3. **Simplified Tableau Rules**: Uses same rule configuration as TRILL^P
   - Deterministic: and_rule, unfold_rule, add_exists_rule, forall_rule,
     forall_plus_rule, exists_rule
   - Non-deterministic: or_rule

4. **DOT Export**: Can export BDD structure as DOT format for visualization

## BDD Structure

- Uses the bddem library for BDD operations
- Maintains a global BDD environment per query
- Combines explanations using AND/OR operations on BDDs

## Main Predicates

### Environment Management
- get_bdd_environment/2: Gets/creates BDD environment
- clean_environment/2: Cleans up BDD environment
- keep_env: Flag to keep environment between calls

### Query Processing
- find_n_explanations/5: Computes BDD for a query
- find_expls_from_tab_list/3: Extracts BDD from completed tableaux

### Explanation Management
- and_f/4: AND two BDDs
- or_f/3: OR two BDDs
- initial_expl/2: Initial BDD (one)

### Output
- check_and_close/3: Returns BDD or DOT string

## Differences from TRILL^P

While TRILL^P uses CLP(B) for symbolic manipulation, TORNADO uses
actual BDD data structures (via CUDD). This can be more efficient
for certain types of queries but requires more careful memory management.

## References

See https://github.com/rzese/trill/blob/master/doc/manual.pdf or
http://ds.ing.unife.it/~rzese/software/trill/manual.html for details.

[1] Thea OWL library: http://vangelisv.github.io/thea/

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

/********************************
  SETTINGS
*********************************/
:- multifile setting_trill_default/2.
setting_trill_default(det_rules,[and_rule,unfold_rule,add_exists_rule,forall_rule,forall_plus_rule,exists_rule]).
setting_trill_default(nondet_rules,[or_rule]).

set_up(M):-
  set_up_parser(M),
  M:(dynamic exp_found/2, keep_env/0, tornado_bdd_environment/1, inconsistent_theory_flag/0, setting_trill/2, tab_end/1, query_option/2, tab_util/2),
  retractall(M:setting_trill(_,_)),
  retractall(M:query_option(_,_)),
  retractall(M:tab_end(_)),
  retractall(M:tab_util(_,_)).
  %retractall(M:setting_trill(_,_)),
  %prune_tableau_rules(M).
  %foreach(setting_trill_default(DefaultSetting,DefaultVal),assert(M:setting_trill(DefaultSetting,DefaultVal))).

clean_up(M):-
  set_up_parser(M),
  M:(dynamic exp_found/2, keep_env/0, tornado_bdd_environment/1, inconsistent_theory_flag/0, setting_trill/2, tab_end/1, query_option/2),
  retractall(M:exp_found(_,_)),
  retractall(M:keep_env),
  retractall(M:tornado_bdd_environment(_)),
  retractall(M:inconsistent_theory_flag),
  retractall(M:setting_trill(_,_)),
  retractall(M:query_option(_,_)),
  retractall(M:tab_end(_)).

/*****************************
  MESSAGES
******************************/
:- multifile prolog:message/1.

prolog:message(or_in_or) -->
  [ 'Boolean formula wrongly built: or in or' ].

prolog:message(and_in_and) -->
  [ 'Boolean formula wrongly built: and in and' ].

/****************************
  QUERY PREDICATES
*****************************/

/***********
  Utilities for queries
 ***********/

% findall
find_n_explanations(M,QueryType,QueryArgs,Expls,_):- % This will not check the arg max_expl as TRILLP returns a pinpointing formula
 assert(M:keep_env),
 find_single_explanation(M,QueryType,QueryArgs,Expls-_),!.

find_n_explanations(M,_,_,Expls,_):-
 initial_expl(M,Expls-_).


compute_prob_and_close(M,Exps-_,QueryOptions):-
  M:query_option(compute_prob,CPType),!,
  get_from_query_options(QueryOptions,compute_prob,CPType,Prob),
  compute_prob(M,Exps,Prob),!,
  retractall(M:keep_env),!.

compute_prob_and_close(_M,_,_):-!.

% checks the explanation
check_and_close(M,Expl,Expl):-
  M:keep_env,!.

check_and_close(M,Expl,dot(Dot)):-
  get_bdd_environment(M,Env),
  create_dot_string(Env,Expl,Dot),
  clean_environment(M,Env).

is_expl(M,Expl):-
  initial_expl(M,EExpl-_),
  dif(Expl,EExpl).


find_expls(M,_,_,_):-
  (M:inconsistent_theory_flag -> print_message(warning,inconsistent) ; true),!,false.

% checks if an explanations was already found
find_expls_from_tab_list(M,[],BDD):-
  empty_expl(M,BDD),!.

% checks if an explanations was already found (instance_of version)
find_expls_from_tab_list(M,[Tab|T],E):-
  get_solved_clashes(Tab,Clashes),
  findall(E0,(member(Clash,Clashes),clash(M,Clash,Tab,E0)),Expls0),!,
  % this predicate checks if there are inconsistencies in the KB, i.e., explanations without query placeholder qp
  consistency_check(M,Expls0,Q),
  ( dif(Q,['inconsistent','kb']) -> true ;  
     ( check_open_query_monitor_status(M,it,['inconsistent','kb']) -> true ; print_message(warning,inconsistent)) ),
  or_all_f(M,Expls0,Expls1),
  find_expls_from_tab_list(M,T,E1),
  and_f(M,Expls1,E1,E).

  find_expls_from_tab_list(M,[_Tab|T],Expl):-
  \+ length(T,0),
  find_expls_from_tab_list(M,T,Expl).

% this predicate checks if there are inconsistencies in the KB, i.e., explanations without query placeholder qp
consistency_check(_,[],qp):-!.

consistency_check(M,[_-CPs|T],Q):-
  dif(CPs,[]),!,
  member(qp,CPs),!,
  consistency_check(M,T,Q).

consistency_check(M,_,['inconsistent','kb']):-!,
  assert(M:inconsistent_theory_flag).

/****************************/

/****************************
  TABLEAU ALGORITHM
****************************/

% --------------
findClassAssertion4OWLNothing(M,ABox,Expl):-
  findall(Expl1,findClassAssertion('http://www.w3.org/2002/07/owl#Nothing',_Ind,Expl1,ABox),Expls),
  dif(Expls,[]),
  or_all_f(M,Expls,Expl).

/* ************* */

/***********
  update abox
  utility for tableau
************/
modify_ABox(_,Tab,sameIndividual(LF),_Expl1,Tab):-
  length(LF,1),!.

modify_ABox(M,Tab0,sameIndividual(LF),L0,Tab):-
  get_abox(Tab0,ABox0),
  find((sameIndividual(L),Expl1),ABox0),!,
  sort(L,LS),
  sort(LF,LFS),
  LS = LFS,!,
  dif(L0,Expl1),
  test(M,L0,Expl1,Expl),
  remove_from_abox(ABox0,[(sameIndividual(L),Expl1)],ABox),
  set_abox(Tab0,[(sameIndividual(L),Expl)|ABox],Tab).

modify_ABox(M,Tab0,sameIndividual(LF),L0,Tab):-
  add_clash_to_tableau(M,Tab0,sameIndividual(LF),Tab1),
  get_abox(Tab0,ABox0),
  set_abox(Tab1,[(sameIndividual(LF),L0)|ABox0],Tab).

modify_ABox(_,Tab,differentIndividuals(LF),_Expl1,Tab):-
  length(LF,1),!.

modify_ABox(M,Tab0,differentIndividuals(LF),L0,Tab):-
  get_abox(Tab0,ABox0),
  find((sameIndividual(L),Expl1),ABox0),!,
  sort(L,LS),
  sort(LF,LFS),
  LS = LFS,!,
  dif(L0,Expl1),
  test(M,L0,Expl1,Expl),
  remove_from_abox(ABox0,[(differentIndividuals(L),Expl1)],ABox),
  set_abox(Tab0,[(differentIndividuals(L),Expl)|ABox],Tab).

modify_ABox(M,Tab0,differentIndividuals(LF),L0,Tab):-
  add_clash_to_tableau(M,Tab0,differentIndividuals(LF),Tab1),
  get_abox(Tab0,ABox),
  set_abox(Tab1,[(differentIndividuals(LF),L0)|ABox],Tab).

modify_ABox(M,Tab0,C,Ind,L0,Tab):-
  get_abox(Tab0,ABox0),
  findClassAssertion(C,Ind,Expl1,ABox0),!,
  dif(L0,Expl1),
  test(M,L0,Expl1,Expl),
  remove_from_abox(ABox0,(classAssertion(C,Ind),Expl1),ABox),
  set_abox(Tab0,[(classAssertion(C,Ind),Expl)|ABox],Tab1),
  update_expansion_queue_in_tableau(M,C,Ind,Tab1,Tab).
  
modify_ABox(M,Tab0,C,Ind,L0,Tab):-
  add_clash_to_tableau(M,Tab0,C-Ind,Tab1),
  get_abox(Tab0,ABox),
  set_abox(Tab1,[(classAssertion(C,Ind),L0)|ABox],Tab2),
  update_expansion_queue_in_tableau(M,C,Ind,Tab2,Tab).


modify_ABox(M,Tab0,P,Ind1,Ind2,L0,Tab):-
  get_abox(Tab0,ABox0),
  findPropertyAssertion(P,Ind1,Ind2,Expl1,ABox0),!,
  dif(L0,Expl1),
  test(M,L0,Expl1,Expl),
  remove_from_abox(ABox0,(propertyAssertion(P,Ind1,Ind2),Expl1),ABox),
  set_abox(Tab0,[(propertyAssertion(P,Ind1,Ind2),Expl)|ABox],Tab1),
  update_expansion_queue_in_tableau(M,P,Ind1,Ind2,Tab1,Tab).
  
  
modify_ABox(M,Tab0,P,Ind1,Ind2,L0,Tab):-
  add_clash_to_tableau(M,Tab0,P-Ind1-Ind2,Tab1),
  get_abox(Tab0,ABox0),
  set_abox(Tab1,[(propertyAssertion(P,Ind1,Ind2),L0)|ABox0],Tab2),
  update_expansion_queue_in_tableau(M,P,Ind1,Ind2,Tab2,Tab).

/* ************* */


/*
  build_abox
  ===============
*/

build_abox(M,Tableau,QueryType,QueryArgs):-
  retractall(M:final_abox(_)),
  retractall(v(_,_,_)),
  retractall(na(_,_)),
  retractall(rule_n(_)),
  assert(rule_n(0)),
  collect_individuals(M,QueryType,QueryArgs,ConnectedInds),
  get_axioms_of_individuals(M,ConnectedInds,LCA,LPA,LNA,LDIA,LSIA),
  new_abox(ABox0),
  new_tabs(Tabs0),
  init_expansion_queue(LCA,LPA,ExpansionQueue),
  init_tableau(ABox0,Tabs0,ExpansionQueue,Tableau0),
  %append([LCA,LDIA,LPA],CreateTabsList),
  %create_tabs(CreateTabsList,Tableau0,Tableau1),
  append([LCA,LPA,LNA,LDIA,LSIA],AddAllList),
  add_all_to_tableau(M,AddAllList,Tableau0,Tableau2),
  merge_all_individuals(M,LSIA,Tableau2,Tableau3),
  add_owlThing_list(M,Tableau3,Tableau),
  !.

get_axioms_of_individuals(M,ConnectedInds,LCA,LPA,LNA,LDIA,LSIA):-
  get_bdd_environment(M,Env),
  ( dif(ConnectedInds,[]) ->
    ( findall((classAssertion(Class,Individual),BDDCA-[]),(member(Individual,ConnectedInds),M:classAssertion(Class,Individual),bdd_and(M,Env,[classAssertion(Class,Individual)],BDDCA)),LCA),
      findall((propertyAssertion(Property,Subject, Object),BDDPA-[]),(member(Subject,ConnectedInds),M:propertyAssertion(Property,Subject, Object),dif('http://www.w3.org/2000/01/rdf-schema#comment',Property),bdd_and(M,Env,[propertyAssertion(Property,Subject, Object)],BDDPA)),LPA),
      % findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property),propertyAssertion(SubProperty,Subject,Object)]),subProp(M,SubProperty,Property,Subject,Object),LSPA),
      findall(nominal(NominalIndividual),(member(NominalIndividual,ConnectedInds),M:classAssertion(oneOf(_),NominalIndividual)),LNA),
      findall((differentIndividuals(Ld),BDDDIA-[]),(M:differentIndividuals(Ld),intersect(Ld,ConnectedInds),bdd_and(M,Env,[differentIndividuals(Ld)],BDDDIA)),LDIA),
      findall((sameIndividual(L),BDDSIA-[]),(M:sameIndividual(L),intersect(L,ConnectedInds),bdd_and(M,Env,[sameIndividual(L)],BDDSIA)),LSIA)
    )
    ; % all the individuals
    ( findall((classAssertion(Class,Individual),BDDCA-[]),(M:classAssertion(Class,Individual),bdd_and(M,Env,[classAssertion(Class,Individual)],BDDCA)),LCA),
      findall((propertyAssertion(Property,Subject, Object),BDDPA-[]),(M:propertyAssertion(Property,Subject, Object),dif('http://www.w3.org/2000/01/rdf-schema#comment',Property),bdd_and(M,Env,[propertyAssertion(Property,Subject, Object)],BDDPA)),LPA),
      % findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property),propertyAssertion(SubProperty,Subject,Object)]),subProp(M,SubProperty,Property,Subject,Object),LSPA),
      findall(nominal(NominalIndividual),M:classAssertion(oneOf(_),NominalIndividual),LNA),
      findall((differentIndividuals(Ld),BDDDIA-[]),(M:differentIndividuals(Ld),bdd_and(M,Env,[differentIndividuals(Ld)],BDDDIA)),LDIA),
      findall((sameIndividual(L),BDDSIA-[]),(M:sameIndividual(L),bdd_and(M,Env,[sameIndividual(L)],BDDSIA)),LSIA)
    )
  ).

/**********************

Explanation Management

***********************/

initial_expl(M,BDD-[]):-
  get_bdd_environment(M,Env),
  zero(Env,BDD).

empty_expl(M,BDD-[]):-
  get_bdd_environment(M,Env),
  one(Env,BDD).

delete_qp(Expl,_,Expl):-!. % TODO probalby to fix

and_f_ax(M,Axiom,BDD0,BDD):-
  get_bdd_environment(M,Env),
  bdd_and(M,Env,[Axiom],BDDAxiom),
  and_f(M,BDDAxiom-[],BDD0,BDD).

% and between two BDDs
and_f(_,[],BDD,BDD):- !.

and_f(_,BDD,[],BDD):- !.

and_f(M,BDD0-CP0,BDD1-CP1,BDD-CP):-
  get_bdd_environment(M,Env),
  and(Env,BDD0,BDD1,BDD),
  append(CP0,CP1,CP).


% or between two formulae
or_all_f(M,[],BDD):-
  initial_expl(M,BDD),!.

or_all_f(M,[H|T],Expl):-
  or_all_f(M,T,Expl1),
  or_f(M,H,Expl1,Expl),!.

or_f(_,[],BDD,BDD):- !.
  
or_f(_,BDD,[],BDD):- !.
  
or_f(M,BDD0-CP0,BDD1-CP1,BDD-CP):-
  get_bdd_environment(M,Env),
  or(Env,BDD0,BDD1,BDD),
  append(CP0,CP1,CP).


/**********************

TORNADO TEST

***********************/

test(M,L1,L2-CP2,F-CP):-
  %build_f(L1,L2,F),
  %sat(F).
  or_f(M,L1,L2-CP2,F-CP),
  dif(L2,F).


/**********************

Choice Points Management

***********************/

get_choice_point_id(_,0).

create_choice_point(_,_,_,_,_,0).

add_choice_point(_,qp,Expl-CP0,Expl-CP):- !,
  (memberchk(qp,CP0) -> CP=CP0; CP=[qp]).

add_choice_point(_,_,Expl,Expl):- !.


/**********************

 TORNADO Probability Computation

***********************/

get_bdd_environment(M,Env):- 
  M:tornado_bdd_environment(Env),!.

get_bdd_environment(M,Env):-
  init(Env),
  M:assert(tornado_bdd_environment(Env)).

clean_environment(M,Env):-
  end(Env),
  retractall(M:tornado_bdd_environment(_)).

build_bdd(_,Env,[],BDD):- !,
  zero(Env,BDD).

build_bdd(_,_Env,BDD,BDD).

bdd_and(M,Env,[X],BDDX):-
  get_prob_ax(M,X,AxN,Prob),!,
  ProbN is 1-Prob,
  get_var_n(Env,AxN,[],[Prob,ProbN],VX),
  equality(Env,VX,0,BDDX),!.

bdd_and(_M,Env,[_X],BDDX):- !,
  one(Env,BDDX).


% TODO use new BDDEM for ret_equation_bdd_c
get_symbolic_equation(BDD,SEq):-
  get_module(M),
  get_bdd_environment(M,Env),
  findall([VX,AxS,Prob],(na(Ax,AxN),get_var_n(Env,AxN,[],[Prob,_ProbN],VX),term_string(Ax,AxS)),LIndexNameProb),
  ret_equation_bdd_c(Env,(_,BDD),LIndexNameProb,SEq0),
  evaluate_expr(SEq0,LIndexNameProb,SEq).