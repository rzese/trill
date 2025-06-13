/* trill predicates

This module performs reasoning over probabilistic description logic knowledge bases.
It reads probabilistic knowledge bases in RDF format or in Prolog format, a functional-like
sintax based on definitions of Thea library, and answers queries by finding the set 
of explanations or computing the probability.

[1] http://vangelisv.github.io/thea/

See https://github.com/rzese/trill/blob/master/doc/manual.pdf or
http://ds.ing.unife.it/~rzese/software/trill/manual.html for
details.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

/********************************
  SETTINGS
*********************************/
:- multifile setting_trill_default/2.
setting_trill_default(det_rules,[o_rule,and_rule,unfold_rule,add_exists_rule,forall_rule,forall_plus_rule,exists_rule,min_rule]).
setting_trill_default(nondet_rules,[or_rule,max_rule,ch_rule]).

set_up(M):-
  utility_translation:set_up(M),
  init_delta(M),
  M:(dynamic exp_found/2, setting_trill/2, tab_end/1, query_option/2, tab_util/2),
  retractall(M:setting_trill(_,_)),
  retractall(M:query_option(_,_)),
  retractall(M:tab_end(_)),
  retractall(M:tab_util(_,_)).
  %foreach(setting_trill_default(DefaultSetting,DefaultVal),assert(M:setting_trill(DefaultSetting,DefaultVal))).

clean_up(M):-
  utility_translation:clean_up(M),
  M:(dynamic exp_found/2, setting_trill/2, tab_end/1, query_option/2),
  retractall(M:exp_found(_,_)),
  retractall(M:setting_trill(_,_)),
  retractall(M:query_option(_,_)),
  retractall(M:tab_end(_)),
  retractall(M:delta(_,_)).

/***********
  Utilities for queries
 ***********/

% findall
find_n_explanations(M,QueryType,QueryArgs,Expls,all):-
  !, % CUT so that no other calls to find_explanation can be ran (to avoid running that with variable N)
  findall(Expl,find_single_explanation(M,QueryType,QueryArgs,Expl),Expls).

% find one in backtracking
find_n_explanations(M,QueryType,QueryArgs,Expl,bt):-
  !, % CUT so that no other calls to find_explanation can be ran (to avoid running that with variable N)
  find_single_explanation(M,QueryType,QueryArgs,Expl).

% find_n_sol
find_n_explanations(M,QueryType,QueryArgs,Expls,N):-
  (number(N) -> % CUT so that no other calls to find_explanation can be ran
    (findnsols(N,Expl,find_single_explanation(M,QueryType,QueryArgs,Expl),Expls),!) % CUT otherwise findnsols would backtracks to look for another N sols
    ;
    (print_message(warning,wrong_number_max_expl),!,false)
  ).


% to find all axplanations for probabilistic queries
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


compute_prob_and_close(M,Expl,QueryOptions):-
  M:query_option(compute_prob,expl),!,
  get_from_query_options(QueryOptions,compute_prob,expl,Prob),
  compute_prob_single_explanation(M,Expl,Prob),!.

compute_prob_and_close(M,_,QueryOptions):-
  M:query_option(compute_prob,query),!,
  get_from_query_options(QueryOptions,compute_prob,query,Prob),
  findall(Exp,M:exp_found(qp,Exp),Exps),
  compute_prob(M,Exps,Prob),!.

compute_prob_and_close(_M,_,_):-!.

% checks the explanation
check_and_close(_,Expl0,Expl):-
  dif(Expl0,[]),
  sort(Expl0,Expl).

is_expl(M,Expl):-
  dif(Expl,[]),
  dif(Expl,[[]]),
  initial_expl(M,EExpl),
  dif(Expl,EExpl).

/*
find_expls(M,[],['inconsistent','kb'],E):-!,
  findall(Exp,M:exp_found(['inconsistent','kb'],Exp),Expl0),
  remove_supersets(Expl0,Expl),!,
  member(E,Expl).

find_expls(M,[],_Q,_):-
  M:exp_found(['inconsistent','kb'],_),!,
  print_message(warning,inconsistent),!,false.

find_expls(M,[],Q,E):-
  findall(Exp,M:exp_found(Q,Exp),Expl0),
  remove_supersets(Expl0,Expl),!,
  member(E,Expl).
*/
% checks if an explanations was already found (instance_of version)
find_expls(M,[Clash|_],Tab,E):- %gtrace,  % QueryArgs
  findall(EL0,clash(M,Clash,Tab,EL0),LEL0),!,
  member(EL0,LEL0),
  member(E0-CPs0,EL0),
  sort(CPs0,CPs1),
  dif(E0,[]),
  sort(E0,E),
  % this predicate checks if there are inconsistencies in the KB, i.e., explanations without query placeholder qp
  % if it is so, the explanation is labelled as inconsistent kb via Q
  consistency_check(CPs1,[],Q),
  %findall(Exp,M:exp_found([C,I],Exp),Expl),
  %not_already_found(M,Expl,[C,I],E),
  ( dif(Q,['inconsistent','kb']) -> true ; 
    (check_open_query_monitor_status(M,it,['inconsistent','kb']) -> true ; print_message(warning,inconsistent))
  ),
  \+ M:exp_found(Q,E),
  assert(M:exp_found(Q,E)). % QueryArgs

find_expls(M,[_Clash|Clashes],Tab,E):-
  find_expls(M,Clashes,Tab,E).

% checks if an explanations was already found
find_expls_from_tab_list(M,[],E):-%gtrace,
  %findall(Exp-CPs,M:exp_found([C,I,CPs],Exp),Expl),
  %dif(Expl,[]),
  findall(Ex0,find_expls_from_choice_point_list(M,Ex0),L0),
  findall(Ex1,M:exp_found(_,Ex1),L1),
  append(L0,L1,L),
  remove_supersets(L,Ls),
  member(E,Ls),
  \+ M:exp_found(_,E),
  assert(M:exp_found(tc,E)).

find_expls_from_tab_list(M,[Tab|_T],E):- %gtrace,  % QueryArgs
  get_solved_clashes(Tab,Clashes),
  member(Clash,Clashes),
  findall(EL0,clash(M,Clash,Tab,EL0),LEL0),
  member(EL0,LEL0),
  member(E0-CPs0,EL0),
  sort(CPs0,CPs1),
  dif(E0,[]),
  sort(E0,E),
  % this predicate checks if there are inconsistencies in the KB, i.e., explanations without query placeholder qp
  % if it is so, the explanation is labelled as inconsistent kb via Q
  consistency_check(CPs1,CPs2,_),
  %dif(CPs2,[]),
  get_latest_choice(CPs2,ID,Choice),
  subtract(CPs1,[cpp(ID,Choice)],CPs), %remove cpp from CPs1 so the qp remains inside choice points list
  update_choice_point_list(M,ID,Choice,E,CPs),
  fail.


find_expls_from_tab_list(M,[_Tab|T],Expl):-
  %\+ length(T,0),
  find_expls_from_tab_list(M,T,Expl).


combine_expls_from_nondet_rules(M,cp(_,_,_,_,_,Expl),E):-%gtrace,
  check_non_empty_choice(Expl,ExplList),
  and_all_f(M,ExplList,ExplanationsList),
  %check_presence_of_other_choices(ExplanationsList,Explanations,Choices),
  member(E0-Choices0,ExplanationsList),
  sort(E0,E),
  sort(Choices0,Choices1),
  % this predicate checks if there are inconsistencies in the KB, i.e., explanations without query placeholder qp
  % if it is so, the explanation is labelled as inconsistent kb via Q
  consistency_check(Choices1,Choices,Q),
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
      ( dif(Q,['inconsistent','kb']) -> true ; 
        (check_open_query_monitor_status(M,it,['inconsistent','kb']) -> true ; print_message(warning,inconsistent))
      ),
      \+ M:exp_found(Q,E)
    )
  ).

find_expls_from_choice_point_list(M,E):-
  extract_choice_point_list(M,CP),
  (
    combine_expls_from_nondet_rules(M,CP,E) ;
    find_expls_from_choice_point_list(M,E)
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


get_latest_choice([],0,0):-!,fail.

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
%consistency_check(CPs,CPs,['inconsistent','kb'],['inconsistent','kb']):- !.

consistency_check(CPs0,CPs,Q):-
  (nth0(_,CPs0,qp,CPs) -> (Q=qp) ; (Q=['inconsistent','kb'],CPs=CPs0)).


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

/*
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



:- multifile check_clash/3.

check_clash(M,maxCardinality(N,S,C)-Ind,Tab):-
  get_abox(Tab,ABox),
  %write('clash 9'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  individual_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  LSS @> N,!.
  
check_clash(M,maxCardinality(N,S)-Ind,Tab):-
  %write('clash 10'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  LSS @> N,!.
  
check_clash(M,exactCardinality(N,S,C)-Ind,Tab):-
  get_abox(Tab,ABox),
  %write('clash 9'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  individual_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  dif(LSS,N),!.
  
check_clash(M,exactCardinality(N,S)-Ind,Tab):-
  %write('clash 10'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  dif(LSS,N),!.
*/

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
  find_sub_sup_class(M,C,D,Ax),
  atomic(D).

%role for concepts exactCardinality
find_sub_sup_class(M,exactCardinality(N,R,C),exactCardinality(N,S,C),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%role for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R),maxCardinality(N,S),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%concept for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R,C),maxCardinality(N,R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax),
  atomic(D).

%role for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R,C),maxCardinality(N,S,C),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%role for concepts minCardinality
find_sub_sup_class(M,minCardinality(N,R),minCardinality(N,S),subPropertyOf(R,S)):-
  M:subPropertyOf(R,S).

%concept for concepts minCardinality
find_sub_sup_class(M,minCardinality(N,R,C),minCardinality(N,R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax),
  atomic(D).

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
      remove_from_abox(ABox0,[(sameIndividual(L),Expl0)],ABox)
  	)
  ;
  	(ABox = ABox0,Expl = Expl1,L = LF)
  ),
  add_clash_to_tableau(M,Tab0,sameIndividual(LF),Tab1),
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
  	  remove_from_abox(ABox0,[(differentIndividuals(L),Expl0)],ABox)
  	)
  ;
  	(ABox = ABox0,Expl = Expl1,L = LF)
  ),
  add_clash_to_tableau(M,Tab0,differentIndividuals(LF),Tab1),
  set_abox(Tab1,[(differentIndividuals(L),Expl)|ABox],Tab).

modify_ABox(M,Tab0,C,Ind,Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find((classAssertion(C,Ind),Expl0),ABox0) ->
    ( absent(Expl0,Expl1,Expl),
      remove_from_abox(ABox0,(classAssertion(C,Ind),Expl0),ABox)
    )
  ;
    (ABox = ABox0,Expl = Expl1)
  ),
  add_clash_to_tableau(M,Tab0,C-Ind,Tab1),
  set_abox(Tab1,[(classAssertion(C,Ind),Expl)|ABox],Tab2),
  update_expansion_queue_in_tableau(M,C,Ind,Tab2,Tab).

modify_ABox(M,Tab0,P,Ind1,Ind2,Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find((propertyAssertion(P,Ind1,Ind2),Expl0),ABox0) ->
    ( absent(Expl0,Expl1,Expl),
      remove_from_abox(ABox0,(propertyAssertion(P,Ind1,Ind2),Expl0),ABox)
    )
  ;
    (ABox = ABox0,Expl = Expl1)
  ),
  add_clash_to_tableau(M,Tab0,P-Ind1-Ind2,Tab1),
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
  absent2(Expl0,H),!,
  absent1(Expl0,T,Expl,_).

absent1(Expl0,[_|T],Expl,Added):-
  absent1(Expl0,T,Expl,Added).

absent2([H-_],Expl):- !,
  \+ subset(H,Expl).

absent2([H-_|T],Expl):-
  \+ subset(H,Expl),!,
  absent2(T,Expl).

/* **************** */

/*
  build_abox
  ===============
*/

/*build_abox(M,ABox):-
  findall((classAssertion(Class,Individual),[classAssertion(Class,Individual)]),classAssertion(Class,Individual),LCA),
  findall((propertyAssertion(Property,Subject, Object),[propertyAssertion(Property,Subject, Object)]),propertyAssertion(Property,Subject, Object),LPA),
  findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property,Subject,Object),propertyAssertion(SubProperty,Subject,Object)]),subPropertyOf(SubProperty,Property),LSPA),
  new_abox(ABox0),
  add_all_to_tableau(LCA,ABox0,ABox1),
  add_all_to_tableau(LPA,ABox1,ABox2),
  add_all_to_tableau(LSPA,ABox2,ABox).
*/


build_abox(M,Tableau,QueryType,QueryArgs):-
  retractall(M:final_abox(_)),
  collect_individuals(M,QueryType,QueryArgs,ConnectedInds),
  get_axioms_of_individuals(M,ConnectedInds,LCA,LPA,LNA,LDIA,LSIA),
  new_abox(ABox0),
  new_tabs(Tabs0),
  init_expansion_queue(LCA,LPA,ExpansionQueue),
  init_tableau(ABox0,Tabs0,ExpansionQueue,Tableau0),
  %append([LCA,LPA,LDIA],CreateTabsList),
  %create_tabs(CreateTabsList,Tableau0,Tableau1),
  append([LCA,LPA,LNA,LDIA,LSIA],AddAllList),%gtrace,
  add_all_to_tableau(M,AddAllList,Tableau0,Tableau2),
  merge_all_individuals(M,LSIA,Tableau2,Tableau3),
  add_owlThing_list(M,Tableau3,Tableau),
  !.


get_axioms_of_individuals(M,IndividualsList,LCA,LPA,LNA,LDIA,LSIA):-
  ( dif(IndividualsList,[]) ->
    ( findall((classAssertion(Class,Individual),[[classAssertion(Class,Individual)]-[]]),(member(Individual,IndividualsList),M:classAssertion(Class,Individual)),LCA),
      findall((propertyAssertion(Property,Subject, Object),[[propertyAssertion(Property,Subject, Object)]-[]]),(member(Subject,IndividualsList),M:propertyAssertion(Property,Subject, Object),dif('http://www.w3.org/2000/01/rdf-schema#comment',Property)),LPA),
      findall(nominal(NominalIndividual),(member(NominalIndividual,IndividualsList),M:classAssertion(oneOf(_),NominalIndividual)),LNA),
      findall((differentIndividuals(Ld),[[differentIndividuals(Ld)]-[]]),(M:differentIndividuals(Ld),intersect(Ld,IndividualsList)),LDIA),
      findall((sameIndividual(L),[[sameIndividual(L)]-[]]),(M:sameIndividual(L),intersect(L,IndividualsList)),LSIA)
    )
    ; % all the individuals
    ( findall((classAssertion(Class,Individual),[[classAssertion(Class,Individual)]-[]]),M:classAssertion(Class,Individual),LCA),
      findall((propertyAssertion(Property,Subject, Object),[[propertyAssertion(Property,Subject, Object)]-[]]),(M:propertyAssertion(Property,Subject, Object),dif('http://www.w3.org/2000/01/rdf-schema#comment',Property)),LPA),
      findall(nominal(NominalIndividual),M:classAssertion(oneOf(_),NominalIndividual),LNA),
      findall((differentIndividuals(Ld),[[differentIndividuals(Ld)]-[]]),M:differentIndividuals(Ld),LDIA),
      findall((sameIndividual(L),[[sameIndividual(L)]-[]]),M:sameIndividual(L),LSIA)
    )
  ).


/* ********** */

/**********************

  Explanation Management

***********************/

and_all_f(M,ExplPartsList,E) :-
  empty_expl(M,EmptyE),
  and_all_f(M,ExplPartsList,EmptyE,E).

and_all_f(_,[],E,E) :- !.

and_all_f(M,[H|T],E0,E):-
  and_f(M,E0,H,E1),
  and_all_f(M,T,E1,E).

initial_expl(_M,[[]-[]]):-!.

empty_expl(_M,[[]-[]]):-!.

and_f_ax(M,Axiom,F0,F):-
  and_f(M,[[Axiom]-[]],F0,F).

and_f(_M,[],[],[]):- !.

and_f(_M,[],L,L):- !.

and_f(_M,L,[],L):- !.

and_f(_M,L1,L2,F):-
  and_f1(L1,L2,[],F).

and_f1([],_,L,L).

and_f1([H1-CP1|T1],L2,L3,L):-
  and_f2(H1,CP1,L2,L12),
  append(L3,L12,L4),
  and_f1(T1,L2,L4,L).

and_f2(_,_,[],[]):- !.

/*
and_f2(L1,CP1,[H2-CP2|T2],[H-CP|T]):-%gtrace,
  can_i_and(L1,CP1,H2,CP2),!,
  ( subset(L1,H2) -> 
    H = H2
    ;
    ( subset(H2,L1) -> 
      H = L1
      ;
      append(L1,H2,H)
    )
  ),
  append(CP1,CP2,CP),
  and_f2(L1,CP1,T2,T).
*/


and_f2(L1,CP1,[H2-CP2|T2],[H-CP|T]):-%gtrace,
  append(L1,H2,H),
  append(CP1,CP2,CP),
  and_f2(L1,CP1,T2,T).


can_i_and(L1,CP1,H2,CP2):-
  dif(L1,[]),
  dif(H2,[]),
  (member(A,CP1),
  member(A,CP2)),!.

same_cpp_or_not(CP1,CP2):-
  (\+ member(cpp(_,_),CP1) ; \+ member(cpp(_,_),CP2)),!.

or_f([],E,E).

or_f([E0|T],E1,E):-
  memberchk(E0,E1),!,
  or_f(T,E1,E).

or_f([E0|T],E1,[E0|E]):-
  or_f(T,E1,E).

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


% cpp/2 is the choice point pointer. It contains the CP's ID (from the list of choice points delta/2)
% and the pointer of the choice maide at the choice point
add_choice_point(_,_,[],[]). 

add_choice_point(_,CPP,[Expl-CP0|T0],[Expl-CP|T]):- %CPP=cpp(CPID,N)
  (
    dif(CP0,[]) ->
    (
        append([CPP],CP0,CP)
    )
    ;
    (
      CP = [CPP]
    )
  ),
  add_choice_point(_,CPP,T0,T).


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
