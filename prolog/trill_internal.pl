



clean_up(M):-
  utility_translation:clean_up(M),
  M:(dynamic exp_found/2, setting_trill/2),
  retractall(M:exp_found(_,_)),
  retractall(M:setting_trill(_,_)).

/***********
  Utilities for queries
 ***********/






% to find all explanations for probabilistic queries
all_sub_class_int(M:ClassEx,SupClassEx,Exps):-
  all_unsat_int(M:intersectionOf([ClassEx,complementOf(SupClassEx)]),Exps).

all_instanceOf_int(M:ClassEx,IndEx,Exps):-
  findall(Expl,instanceOf(M:ClassEx,IndEx,Expl),Exps).

all_property_value_int(M:PropEx,Ind1Ex,Ind2Ex,Exps):-
  findall(Expl,property_value(M:PropEx,Ind1Ex,Ind2Ex,Expl),Exps).

all_unsat_int(M:ConceptEx,Exps):-
  findall(Expl,unsat_internal(M:ConceptEx,Expl),Exps).


all_inconsistent_theory_int(M:Exps):-
  findall(Expl,inconsistent_theory(M:Expl),Exps).

















check_presence_of_other_choices([],[],[]).

check_presence_of_other_choices([E-[]|ExplanationsList],[E|Explanations],Choices):- !,
  check_presence_of_other_choices(ExplanationsList,Explanations,Choices).

check_presence_of_other_choices([E-CP|ExplanationsList],[E|Explanations],[CP|Choices]):-
  check_presence_of_other_choices(ExplanationsList,Explanations,Choices).

check_CP([],_).

check_CP([cp(CP,N)|CPT],L):-
  findall(cp,member(_-[cp(CP,N)|CPT],L),ExplPartsList),
  length(ExplPartsList,N),
  check_CP(CPT,L).


not_already_found(_M,[],_Q,_E):-!.

not_already_found(_M,[H|_T],_Q,E):-
  subset(H,E),!,
  fail.

not_already_found(M,[H|_T],Q,E):-
  subset(E,H),!,
  retract(M:exp_found(Q,H)).

not_already_found(M,[_H|T],Q,E):-
  not_already_found(M,T,Q,E).











/****************************/

/****************************
  TABLEAU ALGORITHM
****************************/












/***********
  rules
************/

/*
  unfold_rule
  ===========
*/





/* ************* */



/* ************* */

% -------------------
notDifferentIndividuals(M,X,Y,ABox):-
  \+ inAssertDifferentIndividuals(M,X,Y),
  \+ inABoxDifferentIndividuals(X,Y,ABox).

% --------------

inAssertDifferentIndividuals(M,differentIndividuals(X),differentIndividuals(Y)):-
  !,
  M:differentIndividuals(LI),
  member(X0,X),
  member(X0,LI),
  member(Y0,Y),
  member(Y0,LI).

inAssertDifferentIndividuals(M,X,sameIndividual(Y)):-
  !,
  M:differentIndividuals(LI),
  member(X,LI),
  member(Y0,Y),
  member(Y0,LI).

inAssertDifferentIndividuals(M,sameIndividual(X),Y):-
  !,
  M:differentIndividuals(LI),
  member(X0,X),
  member(X0,LI),
  member(Y,LI).

inAssertDifferentIndividuals(M,X,Y):-
  M:differentIndividuals(LI),
  member(X,LI),
  member(Y,LI).

% ------------------

inABoxDifferentIndividuals(sameIndividual(X),sameIndividual(Y),ABox):-
  !,
  find((differentIndividuals(LI),_),ABox),
  member(X0,X),
  member(X0,LI),
  member(Y0,Y),
  member(Y0,LI).

inABoxDifferentIndividuals(X,sameIndividual(Y),ABox):-
  !,
  find((differentIndividuals(LI),_),ABox),
  member(X,LI),
  member(Y0,Y),
  member(Y0,LI).

inABoxDifferentIndividuals(sameIndividual(X),Y,ABox):-
  !,
  find((differentIndividuals(LI),_),ABox),
  member(X0,X),
  member(X0,LI),
  member(Y,LI).

inABoxDifferentIndividuals(X,Y,ABox):-
  find((differentIndividuals(LI),_),ABox),
  member(X,LI),
  member(Y,LI).

% --------------------



% ---------------

findExplForClassOf(LC,LI,ABox0,Expl):-
  member(C,LC),
  member(I,LI),
  findClassAssertion(C,I,Expl,ABox0).
%  member((classAssertion(C,I),Expl),ABox0).

/* ************ */




/* **************** */




/* ********** */




/**********************

Choice Points Management

***********************/












/**********************

 TRILL Probability Computation

***********************/








