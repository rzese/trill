



clean_up(M):-
  utility_translation:clean_up(M),
  M:(dynamic exp_found/2, setting_trill/2),
  retractall(M:exp_found(_,_)),
  retractall(M:setting_trill(_,_)).

/***********
  Utilities for queries
 ***********/


% takes a list of dicts expl{query,expl,incons} and create a single disct of the same shape with all values from expls and incons merged
merge_explanations_from_dicts_list(ExplsList,expl{expl:Ec,incons:Inc}):-
  merge_explanations_from_dicts_list(ExplsList,Ec,Inc),!.

merge_explanations_from_dicts_list([],[],[]).

merge_explanations_from_dicts_list([expl{expl:[],incons:Inc0}|T],Ec,[Inc0|Inc]):-
  merge_explanations_from_dicts_list(T,Ec,Inc).

merge_explanations_from_dicts_list([expl{expl:Ec0,incons:[]}|T],[Ec0|Ec],Inc):-
  merge_explanations_from_dicts_list(T,Ec,Inc).



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


% if there is not inconsistency, perform classical probability computation
compute_prob_and_close(M,expl{expl:Exps,incons:[[]]},Prob,false):- !,
  compute_prob(M,Exps,Prob),!.
% if there is not inconsistency, perform classical probability computation
compute_prob_and_close(M,expl{expl:[[]],incons:Exps},Prob,false):- !,
  compute_prob(M,Exps,Prob),!.

compute_prob_and_close(M,Exps,Prob,Inc):-
  compute_prob_inc(M,Exps,Prob,Inc),!.

% checks the explanation
check_and_close(_,Expl0,Expl):-
  QExpl0=Expl0.expl,
  dif(QExpl0,[]),!,
  sort(QExpl0,QExpl),
  Expl=Expl0.put(expl,QExpl).

check_and_close(_,Expl0,Expl):-
  QExpl0=Expl0.incons,
  dif(QExpl0,[]),
  sort(QExpl0,QExpl),
  Expl=Expl0.put(incons,QExpl).


% checks if an explanations was already found
find_expls(M,[],Q,E):-
  %findall(Exp-CPs,M:exp_found([C,I,CPs],Exp),Expl),
  %dif(Expl,[]),
  find_expls_from_choice_point_list(M,Q,E).

find_expls(M,[],['inconsistent','kb'],expl{expl:E,incons:[]}):-!,
  findall(Exp,M:exp_found(['inconsistent','kb'],Exp),Expl0),
  remove_supersets(Expl0,Expl),!,
  member(E,Expl).

find_expls(M,[],_,expl{expl:[],incons:E}):-
  %M:exp_found(['inconsistent','kb'],_),!,
  %print_message(warning,inconsistent),!,false.
  findall(Exp,M:exp_found(['inconsistent','kb'],Exp),Expl0),
  remove_supersets(Expl0,Expl),
  member(E,Expl).

find_expls(M,[],Q,expl{expl:E,incons:[]}):-
  findall(Exp,M:exp_found(Q,Exp),Expl0),
  remove_supersets(Expl0,Expl),!,
  member(E,Expl).

% checks if an explanations was already found (instance_of version)
find_expls(M,[Tab|_T],Q0,E):- %gtrace,  % QueryArgs
  get_clashes(Tab,Clashes),
  member(Clash,Clashes),
  clash(M,Clash,Tab,EL0),
  member(E0-CPs0,EL0),
  sort(CPs0,CPs1),
  sort(E0,E),
  % this predicate checks if there are inconsistencies in the KB, i.e., explanations without query placeholder qp
  % if it is so, the explanation is labelled as inconsistent kb via Q
  consistency_check(CPs1,CPs2,Q0,Q),
  (dif(CPs2,[]) ->
    (
    get_latest_choice(CPs2,ID,Choice),
    subtract(CPs1,[cpp(ID,Choice)],CPs), %remove cpp from CPs1 so the qp remains inside choice points list
    update_choice_point_list(M,ID,Choice,E,CPs),
    fail
    )
    ;
    (%findall(Exp,M:exp_found([C,I],Exp),Expl),
    %not_already_found(M,Expl,[C,I],E),
    assert(M:exp_found(Q,E)), % QueryArgs
    fail
    )
  ).

find_expls(M,[_Tab|T],Query,Expl):-
  %\+ length(T,0),
  find_expls(M,T,Query,Expl).


combine_expls_from_nondet_rules(M,Q0,cp(_,_,_,_,_,Expl),E):-%gtrace,
  check_non_empty_choice(Expl,ExplList),
  and_all_f(M,ExplList,ExplanationsList),
  %check_presence_of_other_choices(ExplanationsList,Explanations,Choices),
  member(E0-Choices0,ExplanationsList),
  sort(E0,E),
  sort(Choices0,Choices1),
  % this predicate checks if there are inconsistencies in the KB, i.e., explanations without query placeholder qp
  % if it is so, the explanation is labelled as inconsistent kb via Q
  consistency_check(Choices1,Choices,Q0,Q),
  (
    dif(Choices,[]) ->
    (
      %TODO gestione altri cp
      get_latest_choice(Choices,ID,Choice),
      subtract(Choices0,[cpp(ID,Choice)],CPs), %remove cpp from Choices1 so the qp remains inside choice points list
      update_choice_point_list(M,ID,Choice,E,CPs),
      fail % to force recursion
    ) ;
    (
      %findall(Exp,M:exp_found([C,I],Exp),ExplFound),
      %not_already_found(M,ExplFound,[C,I],E),
      assert(M:exp_found(Q,E)),
      fail
    )
  ).

find_expls_from_choice_point_list(M,QI,E):-
  extract_choice_point_list(M,CP),
  (
    combine_expls_from_nondet_rules(M,QI,CP,E) ;
    find_expls_from_choice_point_list(M,QI,E)
  ).


check_non_empty_choice(Expl,ExplList):-
  dict_pairs(Expl,_,PairsList),
  findall(Ex,member(_-Ex,PairsList),ExplList),
  \+ memberchk([],ExplList).


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


get_latest_choice([],0,0).

get_latest_choice(CPs,ID,Choice):-
  get_latest_choice_point(CPs,0,ID),
  get_latest_choice_of_cp(CPs,ID,0,Choice).

get_latest_choice_point([],ID,ID).

get_latest_choice_point([cpp(ID0,_)|T],ID1,ID):-
  ID2 is max(ID1,ID0),
  get_latest_choice_point(T,ID2,ID).


get_latest_choice_of_cp([],_,C,C).

get_latest_choice_of_cp([cpp(ID,C0)|T],ID,C1,C):- !,
  C2 is max(C1,C0),
  get_latest_choice_of_cp(T,ID,C2,C).

get_latest_choice_of_cp([_|T],ID,C1,C):-
  get_latest_choice_of_cp(T,ID,C1,C).


remove_supersets([H|T],ExplanationsList):-
  remove_supersets([H],T,ExplanationsList).

remove_supersets(E,[],E).

remove_supersets(E0,[H|T],ExplanationsList):-
  remove_supersets_int(E0,H,E),
  remove_supersets(E,T,ExplanationsList).

remove_supersets_int(E0,H,E0):-
  memberchk(H,E0),!.

remove_supersets_int(E0,H,E0):-
  member(H1,E0),
  subset(H1,H),!.

remove_supersets_int(E0,H,E):-
  member(H1,E0),
  subset(H,H1),!,
  nth0(_,E0,H1,E1),
  remove_supersets_int(E1,H,E).

remove_supersets_int(E,H,[H|E]).


% this predicate checks if there are inconsistencies in the KB, i.e., explanations with query placeholder qp
% if it is so, the explanation is labelled as inconsistent kb
consistency_check(CPs,CPs,['inconsistent','kb'],['inconsistent','kb']):- !.

consistency_check(CPs0,CPs,Q0,Q):-
  (nth0(_,CPs0,qp,CPs) -> (Q=Q0) ; (Q=['inconsistent','kb'],CPs=CPs0)).


/****************************/

/****************************
  TABLEAU ALGORITHM
****************************/

% --------------
findClassAssertion4OWLNothing(_M,ABox,Expl):-
  findClassAssertion('http://www.w3.org/2002/07/owl#Nothing',_Ind,Expl,ABox).


%-------------
% clash managing

%------------
:- multifile clash/4.

clash(M,maxCardinality(N,S,C)-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 9'),nl,
  findClassAssertion(maxCardinality(N,S,C),Ind,Expl1,ABox),
  s_neighbours(M,Ind,S,Tab,SN),
  individual_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  LSS @> N,
  make_expl(M,Ind,S,SNC,Expl1,ABox,Expl).

clash(M,maxCardinality(N,S)-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 10'),nl,
  findClassAssertion(maxCardinality(N,S),Ind,Expl1,ABox),
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  LSS @> N,
  make_expl(M,Ind,S,SN,Expl1,ABox,Expl).

clash(M,exactCardinality(N,S,C)-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 9'),nl,
  findClassAssertion(exactCardinality(N,S,C),Ind,Expl1,ABox),
  s_neighbours(M,Ind,S,Tab,SN),
  individual_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  dif(LSS,N),
  make_expl(M,Ind,S,SNC,Expl1,ABox,Expl).

clash(M,exactCardinality(N,S)-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 10'),nl,
  findClassAssertion(exactCardinality(N,S),Ind,Expl1,ABox),
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  dif(LSS,N),
  make_expl(M,Ind,S,SN,Expl1,ABox,Expl).





% --------------

make_expl(_,_,_,[],Expl,_,Expl).

make_expl(M,Ind,S,[H|T],Expl0,ABox,Expl):-
  findPropertyAssertion(S,Ind,H,Expl2,ABox),
  and_f(M,Expl2,Expl0,Expl1),
  make_expl(M,Ind,S,T,Expl1,ABox,Expl).
% --------------


/***********
  rules
************/

/*
  unfold_rule
  ===========
*/

% ----------------
% unionOf, intersectionOf, subClassOf, negation, allValuesFrom, someValuesFrom, exactCardinality(min and max), maxCardinality, minCardinality
:- multifile find_neg_class/2.

find_neg_class(exactCardinality(N,R,C),unionOf([maxCardinality(NMax,R,C),minCardinality(NMin,R,C)])):-
  NMax is N - 1,
  NMin is N + 1.

find_neg_class(minCardinality(N,R,C),maxCardinality(NMax,R,C)):-
  NMax is N - 1.

find_neg_class(maxCardinality(N,R,C),minCardinality(NMin,R,C)):-
  NMin is N + 1.

%-----------------
:- multifile find_sub_sup_class/4.

%role for concepts exactCardinality
find_sub_sup_class(M,exactCardinality(N,R),exactCardinality(N,S),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%concept for concepts exactCardinality
find_sub_sup_class(M,exactCardinality(N,R,C),exactCardinality(N,R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax).

%role for concepts exactCardinality
find_sub_sup_class(M,exactCardinality(N,R,C),exactCardinality(N,S,C),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%role for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R),maxCardinality(N,S),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%concept for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R,C),maxCardinality(N,R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax).

%role for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R,C),maxCardinality(N,S,C),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%role for concepts minCardinality
find_sub_sup_class(M,minCardinality(N,R),minCardinality(N,S),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%concept for concepts minCardinality
find_sub_sup_class(M,minCardinality(N,R,C),minCardinality(N,R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax).

%role for concepts minCardinality
find_sub_sup_class(M,minCardinality(N,R,C),minCardinality(N,S,C),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

/* ************* */

/***********
  update abox
  utility for tableau
************/
modify_ABox(_,Tab,sameIndividual(LF),_Expl1,Tab):-
  length(LF,1),!.

modify_ABox(M,Tab0,sameIndividual(LF),Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find((sameIndividual(L),Expl0),ABox0) ->
  	( sort(L,LS),
  	  sort(LF,LFS),
  	  LS = LFS,!,
  	  absent(Expl0,Expl1,Expl),
      remove_from_abox(ABox0,[(sameIndividual(L),Expl0)],ABox),
      Tab1=Tab0
  	)
  ;
  	(ABox = ABox0,Expl = Expl1,L = LF,
     add_clash_to_tableau(M,Tab0,sameIndividual(LF),Tab1))
  ),
  set_abox(Tab1,[(sameIndividual(L),Expl)|ABox],Tab).

modify_ABox(_,Tab,differentIndividuals(LF),_Expl1,Tab):-
  length(LF,1),!.

modify_ABox(M,Tab0,differentIndividuals(LF),Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find((differentIndividuals(L),Expl0),ABox0) ->
  	( sort(L,LS),
  	  sort(LF,LFS),
  	  LS = LFS,!,
  	  absent(Expl0,Expl1,Expl),
  	  remove_from_abox(ABox0,[(differentIndividuals(L),Expl0)],ABox),
      Tab1=Tab0
  	)
  ;
  	(ABox = ABox0,Expl = Expl1,L = LF,
    add_clash_to_tableau(M,Tab0,differentIndividuals(LF),Tab1))
  ),
  set_abox(Tab1,[(differentIndividuals(L),Expl)|ABox],Tab).

modify_ABox(M,Tab0,C,Ind,Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find((classAssertion(C,Ind),Expl0),ABox0) ->
    ( absent(Expl0,Expl1,Expl),
      remove_from_abox(ABox0,(classAssertion(C,Ind),Expl0),ABox),
      Tab1=Tab0
    )
  ;
    (ABox = ABox0,Expl = Expl1,
    add_clash_to_tableau(M,Tab0,C-Ind,Tab1))
  ),
  set_abox(Tab1,[(classAssertion(C,Ind),Expl)|ABox],Tab2),
  update_expansion_queue_in_tableau(M,C,Ind,Tab2,Tab).

modify_ABox(M,Tab0,P,Ind1,Ind2,Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find((propertyAssertion(P,Ind1,Ind2),Expl0),ABox0) ->
    ( absent(Expl0,Expl1,Expl),
      remove_from_abox(ABox0,(propertyAssertion(P,Ind1,Ind2),Expl0),ABox),
      Tab1=Tab0
    )
  ;
    (ABox = ABox0,Expl = Expl1,
    add_clash_to_tableau(M,Tab0,P-Ind1-Ind2,Tab1))
  ),
  set_abox(Tab1,[(propertyAssertion(P,Ind1,Ind2),Expl)|ABox],Tab2),
  update_expansion_queue_in_tableau(M,P,Ind1,Ind2,Tab2,Tab).

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

listIntersection([],_,[]).

listIntersection([HX|TX],LCY,TI):-
  \+ member(HX,LCY),
  listIntersection(TX,LCY,TI).

listIntersection([HX|TX],LCY,[HX|TI]):-
  member(HX,LCY),
  listIntersection(TX,LCY,TI).

% ---------------

findExplForClassOf(LC,LI,ABox0,Expl):-
  member(C,LC),
  member(I,LI),
  findClassAssertion(C,I,Expl,ABox0).
%  member((classAssertion(C,I),Expl),ABox0).

/* ************ */


/*  absent
  =========
*/
absent(Expl0,Expl1,Expl):- % Expl0 already present expls, Expl1 new expls to add, Expl the combination of two lists
  absent0(Expl0,Expl1,Expl),!.

%------------------
absent0(Expl0,Expl1,Expl):-
  absent1(Expl0,Expl1,Expl,Added),
  dif(Added,0).

absent1(Expl,[],Expl,0).

absent1(Expl0,[H-CP|T],[H-CP|Expl],1):-
  absent2(Expl0,H-CP),!,
  absent1(Expl0,T,Expl,_).

absent1(Expl0,[_|T],Expl,Added):-
  absent1(Expl0,T,Expl,Added).

% if the query placeholder is present in both or absent in both, I must check the subset condition. Otherwise, I must keep both.  
absent2([H-CPH],Expl-CP):- 
  (check_query_placeholder(CPH,CP) ->  \+ subset(H,Expl) ; true),!.

absent2([H-CPH|T],Expl-CP):-
  check_query_placeholder(CPH,CP),!,
  \+ subset(H,Expl),!,
  absent2(T,Expl-CP).

absent2([_|T],Expl-CP):-
  absent2(T,Expl-CP).


check_query_placeholder(CP0,CP1):-
  (memberchk(qp,CP0),memberchk(qp,CP1)),!.

check_query_placeholder(CP0,CP1):-
  (\+ memberchk(qp,CP0), \+ memberchk(qp,CP1)),!.

/* **************** */




/* ********** */




/**********************

Choice Points Management

***********************/

/*
  Initializes delta/2 containing the list of choice points and the number of choice points created.
  Every choice point is modeled by the predicate cp/5 containing the ID of the choice point,
  the individual and the class that triggered the creation of the choice point,
  the rule that created the cp:
  - or: or_rule
  - mr: max_rule
  Also it contains the list of possible choices and the explanations for each choice.
*/
init_delta(M):-
  retractall(M:delta(_,_)),
  assert(M:delta([],0)).

get_choice_point_id(M,ID):-
  M:delta(_,ID).

% Creates a new choice point and adds it to the delta/2 set of choice points.
create_choice_point(M,Ind,Rule,Class,Choices,ID0):-
  init_expl_per_choice(Choices,ExplPerChoice),
  M:delta(CPList,ID0),
  ID is ID0 + 1,
  retractall(M:delta(_,_)),
  assert(M:delta([cp(ID0,Ind,Rule,Class,Choices,ExplPerChoice)|CPList],ID)).


init_expl_per_choice(Choices,ExplPerChoice):-
  length(Choices,N),
  init_expl_per_choice_int(0,N,epc{0:[]},ExplPerChoice).

init_expl_per_choice_int(N,N,ExplPerChoice,ExplPerChoice).

init_expl_per_choice_int(N0,N,ExplPerChoice0,ExplPerChoice):-
  ExplPerChoice1 = ExplPerChoice0.put(N0,[]),
  N1 is N0 + 1,
  init_expl_per_choice_int(N1,N,ExplPerChoice1,ExplPerChoice).





get_choice_point_list(M,CP):-
  M:delta(CP,_).

extract_choice_point_list(M,CP):-
  M:delta([CP|CPList],ID),
  retractall(M:delta(_,_)),
  assert(M:delta(CPList,ID)).

update_choice_point_list(M,ID,Choice,E,CPs):-
  M:delta(CPList0,ID0),
  memberchk(cp(ID,Ind,Rule,Class,Choices,ExplPerChoice0),CPList0),
  ExplToUpdate = ExplPerChoice0.get(Choice), 
  ( % if the set of explanations for the choice is empty it simply adds the new explanation -> union i.e., append([E-CPs],ExplToUpdate,ExplUpdated)
    % otherwise it adds only new explanations dropping those that are already present or those that are supersets of 
    % already present explanations -> absent(ExplToUpdate,[E-CPs],ExplUpdated)
    dif(ExplToUpdate,[]) ->
    (
      or_f(ExplToUpdate,[E-CPs],ExplUpdated)
    ) ;
    (
      ExplUpdated=[E-CPs]
    )
  ),
  ExplPerChoice = ExplPerChoice0.put(Choice,ExplUpdated),
  update_choice_point_list_int(CPList0,cp(ID,Ind,Rule,Class,Choices,ExplPerChoice0),ExplPerChoice,CPList),
  retractall(M:delta(_,_)),
  assert(M:delta(CPList,ID0)).

update_choice_point_list_int([],_,_,[]):-
  writeln("Probably something wrong happened. Please report the problem opening an issue on github!").
  % It should never arrive here.

update_choice_point_list_int([cp(ID,Ind,Rule,Class,Choices,ExplPerChoice0)|T],
                    cp(ID,Ind,Rule,Class,Choices,ExplPerChoice0),ExplPerChoice,
                    [cp(ID,Ind,Rule,Class,Choices,ExplPerChoice)|T]) :- !.

update_choice_point_list_int([H|T],
                  cp(ID,Ind,Rule,Class,Choices,ExplPerChoice0),ExplPerChoice,
                  [H|T1]):-
  update_choice_point_list_int(T,cp(ID,Ind,Rule,Class,Choices,ExplPerChoice0),ExplPerChoice,T1).

/**********************

 TRILL Probability Computation

***********************/

get_bdd_environment(_M,Env):-
  init(Env).

clean_environment(_M,Env):-
  end(Env).


build_bdd_inc(M,Env,Expl,Inc,BDDQC,BDDC):- !,
  build_bdd(M,Env,Expl,BDDQ), % BDD query's explanations
  build_bdd(M,Env,Inc,BDDInc), % BDD inconsistency's explanations
  bdd_not(Env,BDDInc,BDDC), % BDD consistency's explanations
  and(Env,BDDQ,BDDC,BDDQC). % BDD query and consistency's explanations

build_bdd_inc(M,Env,Expl,Inc,BDDQC,BDDNQC,BDDC):- !,
  build_bdd(M,Env,Expl,BDDQ), % BDD query's explanations
  build_bdd(M,Env,Inc,BDDInc), % BDD inconsistency's explanations
  bdd_not(Env,BDDInc,BDDC), % BDD consistency's explanations
  bdd_not(Env,BDDQ,BDDNQ), % BDD for the query to be false
  and(Env,BDDQ,BDDC,BDDQC), % BDD query and consistency's explanations
  and(Env,BDDNQ,BDDC,BDDNQC). % BDD of query not true in consistent worlds

build_bdd(M,Env,[X],BDD):- !,
  bdd_and(M,Env,X,BDD).

build_bdd(M,Env, [H|T],BDD):-
  build_bdd(M,Env,T,BDDT),
  bdd_and(M,Env,H,BDDH),
  or(Env,BDDH,BDDT,BDD).

build_bdd(_M,Env,[],BDD):- !,
  zero(Env,BDD).


bdd_and(M,Env,[X],BDDX):-
  get_prob_ax(M,X,AxN,Prob),!,
  ProbN is 1-Prob,
  get_var_n(Env,AxN,[],[Prob,ProbN],VX),
  equality(Env,VX,0,BDDX),!.

bdd_and(_M,Env,[_X],BDDX):- !,
  one(Env,BDDX).

bdd_and(M,Env,[H|T],BDDAnd):-
  get_prob_ax(M,H,AxN,Prob),!,
  ProbN is 1-Prob,
  get_var_n(Env,AxN,[],[Prob,ProbN],VH),
  equality(Env,VH,0,BDDH),
  bdd_and(M,Env,T,BDDT),
  and(Env,BDDH,BDDT,BDDAnd).
  
bdd_and(M,Env,[_H|T],BDDAnd):- !,
  one(Env,BDDH),
  bdd_and(M,Env,T,BDDT),
  and(Env,BDDH,BDDT,BDDAnd).
