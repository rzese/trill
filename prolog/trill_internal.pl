





/***********
  Utilities for queries
 ***********/


























check_CP([],_).

check_CP([cp(CP,N)|CPT],L):-
  findall(cp,member(_-[cp(CP,N)|CPT],L),ExplPartsList),
  length(ExplPartsList,N),
  check_CP(CPT,L).














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








