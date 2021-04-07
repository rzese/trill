/* trill predicates

This file contains the settings needed by TRILL to properly work.

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



/*****************************
  MESSAGES
******************************/
:- multifile prolog:message/1.

prolog:message(iri_not_exists(IRIs)) -->
  [ 'IRIs not existent: ~w' -[IRIs] ].

prolog:message(inconsistent) -->
  [ 'The KB is inconsitent' ].

prolog:message(completely_inconsistent) -->
  [ 'The KB is certainly inconsistent, I cannot prove the truth of any explanation.' ].

prolog:message(inconsistence_expl) -->
  [ 'Inconsistence explanation:' ].

prolog:message(consistent) -->
  [ 'Consistent ABox' ].

/*
prolog:message(locally_inconsistent) -->
  [ 'The KB is probably locally inconsitent, i.e., inconsistency is not certain.' ].

prolog:message(wrong_number_max_expl) -->
  [ 'max_expl option can take integer values or "all"' ].

prolog:message(timeout_reached) -->
  [ 'Timeout reached' ].
*/

/*****************************
  QUERY OPTIONS

  List of query options:
  - return_prob - Prob:Variable
  - return_incons_expl - ListOfExpl:Variable
  - assert_abox - Boolean
  - max_expl - Integer|all|bt finds N or all the explanations or one single explanation at a time if bt or not set
  - time_limit - Integer (seconds)

  TODO
  - return_final_prob - only|also|false used when trill returns one explanation at a time. If only returns only the probability of all the explanations,
                                        if also returns both probability of single explanation and the probability of all the explanations
                                        if false or not set returns only the probability of the single explanations
  
******************************/
:- multifile query_option/3.
query_option(OptList,Option,Value):-
  Opt=..[Option,Value],
  memberchk(Opt,OptList).


:- multifile set_tableau_expansion_rules/2.
set_tableau_expansion_rules(M:DetRules,NondetRules):-
  retractall(M:setting_trill(det_rules,_)),
  retractall(M:setting_trill(nondet_rules,_)),
  assert(M:setting_trill(det_rules,DetRules)),
  assert(M:setting_trill(nondet_rules,NondetRules)).


% ===================================
% UTULITIES
% ===================================

/**************/
:- multifile get_trill_current_module/1.
/*get_trill_current_module('utility_translation'):-
  pengine_self(_Name),!.*/
%get_trill_current_module(Name):-
%  pengine_self(Name),!.
%get_trill_current_module('utility_translation'):- !.
get_trill_current_module(M):-
  utility_translation:get_module(M).
/**************/
