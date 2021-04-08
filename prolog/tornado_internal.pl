


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




build_bdd(_,Env,[],BDD):- !,
  zero(Env,BDD).

build_bdd(_,_Env,BDD,BDD).

build_bdd_inc(_,Env,BDDQ,BDDInc,BDDQC,BDDC):-
  bdd_not(Env,BDDInc,BDDC), % BDD consistency's explanations
  and(Env,BDDQ,BDDC,BDDQC). % BDD query and consistency's explanations

build_bdd_inc(_,Env,BDDQ,BDDInc,BDDQC,BDDNQC,BDDC):-
  bdd_not(Env,BDDInc,BDDC), % BDD consistency's explanations
  bdd_not(Env,BDDQ,BDDNQ), % BDD for the query to be false
  and(Env,BDDQ,BDDC,BDDQC), % BDD query and consistency's explanations
  and(Env,BDDNQ,BDDC,BDDNQC). % BDD of query not true in consistent worlds

bdd_and(M,Env,[X],BDDX):-
  get_prob_ax(M,X,AxN,Prob),!,
  ProbN is 1-Prob,
  get_var_n(Env,AxN,[],[Prob,ProbN],VX),
  equality(Env,VX,0,BDDX),!.

bdd_and(_M,Env,[_X],BDDX):- !,
  one(Env,BDDX).
