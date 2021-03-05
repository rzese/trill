/** <module> trill

This module performs reasoning over probabilistic description logic knowledge bases.
It reads probabilistic knowledge bases in RDF format or in Prolog format, a functional-like
sintax based on definitions of Thea library, and answers queries by finding the set 
of explanations or computing the probability.

[1] http://vangelisv.github.io/thea/

See https://github.com/rzese/trill/blob/master/doc/manual.pdf or
http://ml.unife.it/trill-framework/ for details.

@version 7.0.0
@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

% Module definition. TODO to check if it possible to remove something
:- module(trill,[ instanceOf/4, instanceOf/3, instanceOf/2, all_instanceOf/3,
                  property_value/5, property_value/4, property_value/3, all_property_value/4,
                  sub_class/4, sub_class/3, sub_class/2, all_sub_class/3,
                  unsat/3, unsat/2, unsat/1, all_unsat/2,
                  inconsistent_theory/2, inconsistent_theory/1, inconsistent_theory/0, all_inconsistent_theory/1,
                  prob_instanceOf/3, prob_property_value/4, prob_sub_class/3, prob_unsat/2, prob_inconsistent_theory/1,
                  load_kb/1, load_owl_kb/1, load_owl_kb_from_string/1, init_trill/0,
                  axiom/1, add_axiom/1, add_axioms/1, remove_axiom/1, remove_axioms/1,
                  kb_prefixes/1, add_kb_prefix/2, add_kb_prefixes/1, remove_kb_prefix/2, remove_kb_prefix/1,
                  set_tableau_expansion_rules/2] ).

:- meta_predicate instanceOf(:,+,-,+).
:- meta_predicate instanceOf(:,+,-).
:- meta_predicate instanceOf(:,+).
:- meta_predicate all_instanceOf(:,+,-).

:- meta_predicate property_value(:,+,+,-,+).
:- meta_predicate property_value(:,+,+,-).
:- meta_predicate property_value(:,+,+).
:- meta_predicate all_property_value(:,+,+,-).

:- meta_predicate sub_class(:,+,-,+).
:- meta_predicate sub_class(:,+,-).
:- meta_predicate sub_class(:,+).
:- meta_predicate all_sub_class(:,+,-).

:- meta_predicate unsat(:,-,+).
:- meta_predicate unsat(:,-).
:- meta_predicate unsat(:).
:- meta_predicate all_unsat(:,-).

:- meta_predicate inconsistent_theory(:,+).
:- meta_predicate inconsistent_theory(:).
:- meta_predicate inconsistent_theory.
:- meta_predicate all_inconsistent_theory(:).

:- meta_predicate prob_instanceOf(:,+,-).
:- meta_predicate prob_property_value(:,+,+,-).
:- meta_predicate prob_sub_class(:,+,-).
:- meta_predicate prob_unsat(:,-).
:- meta_predicate prob_inconsistent_theory(:).

:- meta_predicate load_kb(+).
:- meta_predicate load_owl_kb(+).
:- meta_predicate load_owl_kb_from_string(+).

:- meta_predicate axiom(:).
:- meta_predicate add_axiom(:).
:- meta_predicate add_axioms(:).
:- meta_predicate remove_axiom(:).
:- meta_predicate remove_axioms(:).
:- meta_predicate kb_prefixes(:).
:- meta_predicate add_kb_prefix(:,+).
:- meta_predicate add_kb_prefixes(:).
:- meta_predicate remove_kb_prefix(:,+).
:- meta_predicate remove_kb_prefix(:).

:- meta_predicate set_tableau_expansion_rules(:,+).

:- use_module(library(lists)).
:- use_module(library(ugraphs)).
:- use_module(library(rbtrees)).
:- use_module(library(dif)).
:- use_module(library(pengines)).
:- use_module(library(sandbox)).

:- reexport(library(bddem)).

:- style_check(-discontiguous).

/********************************
  SETTINGS
*********************************/
:- multifile setting_trill_default/2.
:- multifile query_option/3.
/** 
 * query_option(+OptList:list,+Option:term,?Value:term)
 * 
 * Check if the option defined by Option is in OptList and returns the option Value.

 * Options can be:
 * - assert_abox(Boolean) if Boolean is set to true the list of aboxes is asserted with the predicate final_abox/1
 * - return_prob(Prob) if present the probability of the query is computed and unified with Prob
 * - return_single_prob(Boolean) must be used with return_prob(Prob). It forces TRILL to return the probability of each single explanation
 * - max_expl(Value) to limit the maximum number of explanations to find. Value must be an integer. The predicate will return a list containing at most Value different explanations
 * - time_limit(Value) to limit the time for the inference. The predicate will return the explanations found in the time allowed. Value is the number of seconds allowed for the search of explanations 
*/
:- multifile set_tableau_expansion_rules/2.
/**
 * set_tableau_expansion_rules(:DetRules:list,++NondetRules:list) is det
 * 
 * This predicate set the rules as taken in input, maintaining order and number of rules.
 * DetRules is the list of deterministic rules, NondetRules the list of non-deterministic ones.
 */

:- multifile get_trill_current_module/1.
/**
 * get_trill_current_module(--M:module)
 * 
 * Returns the module under which trill is executed.
 */
:- consult(library(trill_settings)).

/********************************
  Specific query predicates
  - with and without explanations -
 *********************************/


/**
 * instanceOf(:Class:concept_description,++Ind:individual_name,-Expl:list,-Expl:list,++Opt:list)
 *
 * This predicate takes as input the name or the full URI of a class or the definition
 * of a complex concept as a ground term and name or the full URI of an individual and
 * returns one explanation for the instantiation of the individual to the given class.
 * The returning explanation is a set of axioms.
 * The predicate fails if the individual does not belong to the class.
 * Opt is a list containing settings for the execution of the query. 
 */
instanceOf(M:Class,Ind,Expl,Opt):-
  execute_query(M,io,[Class,Ind],Expl,Opt).


/**
 * instanceOf(:Class:concept_description,++Ind:individual_name)
 *
 * This predicate takes as input the name or the full URI of a class or the definition
 * of a complex concept as a ground term and name or the full URI of an individual and
 * returns one explanation for the instantiation of the individual to the given class.
 * The returning explanation is a set of axioms.
 * The predicate fails if the individual does not belong to the class.
 */
instanceOf(M:Class,Ind,Expl):-
  instanceOf(M:Class,Ind,Expl,[]).

/**
 * instanceOf(:Class:concept_description,++Ind:individual_name) is det
 *
 * This predicate takes as input the name or the full URI of a class or the definition
 * of a complex concept as a ground term and name or the full URI of an individual and
 * returns true if the individual belongs to the class, false otherwise.
 */
instanceOf(M:Class,Ind):-
  execute_query(M,io,[Class,Ind],_,[max_expl(1)]),!.

/**
 * all_instanceOf(:Class:concept_description,++Ind:individual_name)
 *
 * This predicate takes as input the name or the full URI of a class or the definition
 * of a complex concept as a ground term and name or the full URI of an individual and
 * returns all the explanations for the instantiation of the individual to the given class.
 * The returning explanations are in the form if a list (set) of set of axioms.
 * The predicate fails if the individual does not belong to the class.
 */
all_instanceOf(M:Class,Ind,Expl):-
  execute_query(M,io,[Class,Ind],Expl,[max_expl(all)]),
  empty_expl(M,EExpl),
  dif(Expl,EExpl).

/**
 * property_value(:Prop:property_name,++Ind1:individual_name,++Ind2:individual_name,-Expl:list,++Opt:list)
 *
 * This predicate takes as input the name or the full URI of a property and of two individuals
 * and returns one explanation for the fact Ind1 is related with Ind2 via Prop.
 * The returning explanation is a set of axioms.
 * The predicate fails if the two individual are not Prop-related. * 
 * Opt is a list containing settings for the execution of the query. 
 */
property_value(M:Prop, Ind1, Ind2,Expl,Opt):-
  execute_query(M,pv,[Prop, Ind1, Ind2],Expl,Opt).

/**
 * property_value(:Prop:property_name,++Ind1:individual_name,++Ind2:individual_name,-Expl:list)
 *
 * This predicate takes as input the name or the full URI of a property and of two individuals
 * and returns one explanation for the fact Ind1 is related with Ind2 via Prop.
 * The returning explanation is a set of axioms.
 * The predicate fails if the two individual are not Prop-related.
 */
property_value(M:Prop, Ind1, Ind2,Expl):-
  property_value(M:Prop, Ind1, Ind2,Expl,[]).

/**
 * property_value(:Prop:property_name,++Ind1:individual_name,++Ind2:individual_name) is det
 *
 * This predicate takes as input the name or the full URI of a property and of two individuals
 * and returns true if the two individual are Prop-related, false otherwise.
 */
property_value(M:Prop, Ind1, Ind2):-
  execute_query(M,pv,[Prop, Ind1, Ind2],_,[max_expl(1)]),!.

/**
 * all_property_value(:Prop:property_name,++Ind1:individual_name,++Ind2:individual_name,-Expl:list)
 *
 * This predicate takes as input the name or the full URI of a property and of two individuals
 * and returns all the explanations for the fact Ind1 is related with Ind2 via Prop.
 * The returning explanations are in the form if a list (set) of set of axioms.
 * The predicate fails if the individual does not belong to the class.
 */
all_property_value(M:Prop, Ind1, Ind2,Expl):-
  execute_query(M,pv,[Prop, Ind1, Ind2],Expl,[max_expl(all)]),
  empty_expl(M,EExpl),
  dif(Expl,EExpl).

/**
 * sub_class(:Class:concept_description,++SupClass:concept_description,-Expl:list,++Opt:list)
 *
 * This predicate takes as input two concepts which can be given by the name or the full URI 
 * of two a simple concept or the definition of a complex concept as a ground term and returns
 * one explanation for the subclass relation between Class and SupClass.
 * The returning explanation is a set of axioms.
 * The predicate fails if there is not a subclass relation between the two classes.
 * Opt is a list containing settings for the execution of the query. 
 */
sub_class(M:Class,SupClass,Expl,Opt):-
  execute_query(M,sc,[Class,SupClass],Expl,Opt).

/**
 * sub_class(:Class:concept_description,++SupClass:concept_description,-Expl:list)
 *
 * This predicate takes as input two concepts which can be given by the name or the full URI 
 * of two a simple concept or the definition of a complex concept as a ground term and returns
 * one explanation for the subclass relation between Class and SupClass.
 * The returning explanation is a set of axioms.
 * The predicate fails if there is not a subclass relation between the two classes.
 */
sub_class(M:Class,SupClass,Expl):-
  sub_class(M:Class,SupClass,Expl,[]).

/**
 * sub_class(:Class:concept_description,++SupClass:concept_description) is det
 *
 * This predicate takes as input two concepts which can be given by the name or the full URI 
 * of two a simple concept or the definition of a complex concept as a ground term and returns
 * true if Class is a subclass of SupClass, and false otherwise.
 */
sub_class(M:Class,SupClass):-
  execute_query(M,sc,[Class,SupClass],_,[max_expl(1)]),!.

/**
 * all_sub_class(:Class:concept_description,++SupClass:concept_description,-Expl:list)
 *
 * This predicate takes as input two concepts which can be given by the name or the full URI 
 * of two a simple concept or the definition of a complex concept as a ground term and returns
 * all the explanations for the subclass relation between Class and SupClass.
 * The returning explanations are in the form if a list (set) of set of axioms.
 * The predicate fails if the individual does not belong to the class.
 */
all_sub_class(M:Class,SupClass,Expl):-
  execute_query(M,sc,[Class,SupClass],Expl,[max_expl(all)]).

/**
 * unsat(:Concept:concept_description,-Expl:list,++Opt:list)
 *
 * This predicate takes as input the name or the full URI of a class or the definition of 
 * a complex concept as a ground term and returns one explanation for the unsatisfiability of the concept.
 * The returning explanation is a set of axioms.
 * The predicate fails if the concept is satisfiable.
 * Opt is a list containing settings for the execution of the query. 
 */
unsat(M:Concept,Expl,Opt):-
  execute_query(M,un,[Concept],Expl,Opt).

/**
 * unsat(:Concept:concept_description,-Expl:list)
 *
 * This predicate takes as input the name or the full URI of a class or the definition of 
 * a complex concept as a ground term and returns one explanation for the unsatisfiability of the concept.
 * The returning explanation is a set of axioms.
 * The predicate fails if the concept is satisfiable.
 */
unsat(M:Concept,Expl):-
  unsat(M:Concept,Expl,[]).

/**
 * unsat(:Concept:concept_description) is det
 *
 * This predicate takes as input the name or the full URI of a class or the definition of 
 * a complex concept as a ground term and returns true if the concept is unsatisfiable, false otherwise.
 */
unsat(M:Concept):-
  execute_query(M,un,[Concept],_,[max_expl(1)]),!.

/**
 * all_unsat(:Concept:concept_description,-Expl:list)
 *
 * This predicate takes as input the name or the full URI of a class or the definition of 
 * a complex concept as a ground term and returns all the explanations for the unsatisfiability of the concept.
 * The returning explanations are in the form if a list (set) of set of axioms.
 * The predicate fails if the individual does not belong to the class.
 */
all_unsat(M:Concept,Expl):-
  execute_query(M,un,[Concept],Expl,[max_expl(all)]),
  empty_expl(M,EExpl),
  dif(Expl,EExpl).

/**
 * inconsistent_theory(:Expl:list,++Opt:list)
 *
 * This predicate returns one explanation for the inconsistency of the loaded knowledge base.
 * Opt is a list containing settings for the execution of the query. 
 */
inconsistent_theory(M:Expl,Opt):-
  execute_query(M,it,[],Expl,Opt).

/**
 * inconsistent_theory(:Expl:list)
 *
 * This predicate returns one explanation for the inconsistency of the loaded knowledge base.
 */
inconsistent_theory(M:Expl):-
  inconsistent_theory(M:Expl,[]).

/**
 * all_inconsistent_theory(:Expl:list)
 *
 * This predicate returns all the explanations for the inconsistency of the loaded knowledge base.
 * The returning explanations are in the form if a list (set) of set of axioms.
 * The predicate fails if the individual does not belong to the class.
 */
all_inconsistent_theory(M:Expl):-
  execute_query(M,it,[],Expl,[max_expl(all)]),
  empty_expl(M,EExpl),
  dif(Expl,EExpl).

/**
 * inconsistent_theory
 *
 * This predicate returns true if the loaded knowledge base is inconsistent, otherwise it fails.
 */
inconsistent_theory:-
  get_trill_current_module(M),
  execute_query(M,it,[],_,[max_expl(1)]),!.

/**
 * prob_instanceOf(:Class:concept_description,++Ind:individual_name,--Prob:double) is det
 *
 * This predicate takes as input the name or the full URI of a class or the definition
 * of a complex concept as a ground term and name or the full URI of an individual and
 * returns the probability of the instantiation of the individual to the given class.
 */
prob_instanceOf(M:Class,Ind,Prob):-
  instanceOf(M:Class,Ind,_,[return_prob(Prob)]).

/**
 * prob_property_value(:Prop:property_name,++Ind1:individual_name,++Ind2:individual_name,--Prob:double) is det
 *
 * This predicate takes as input the name or the full URI of a property and of two individuals
 * and returns the probability of the fact Ind1 is related with Ind2 via Prop.
 */
prob_property_value(M:Prop, Ind1, Ind2,Prob):-
  property_value(M:Prop, Ind1, Ind2,_,[return_prob(Prob)]).

/**
 * prob_sub_class(:Class:concept_description,++SupClass:class_name,--Prob:double) is det
 *
 * This predicate takes as input two concepts which can be given by the name or the full URI 
 * of two a simple concept or the definition of a complex concept as a ground term and returns 
 * the probability of the subclass relation between Class and SupClass.
 */
prob_sub_class(M:Class,SupClass,Prob):-
  sub_class(M:Class,SupClass,_,[return_prob(Prob)]).

/**
 * prob_unsat(:Concept:concept_description,--Prob:double) is det
 *
 * This predicate takes as input the name or the full URI of a class or the definition of 
 * a complex concept as a ground term and returns the probability of the unsatisfiability
 * of the concept.
 */
prob_unsat(M:Concept,Prob):-
  unsat(M:Concept,_,[return_prob(Prob)]).

/**
 * prob_inconsistent_theory(:Prob:double) is det
 *
 * If the knowledge base is inconsistent, this predicate returns the probability of the inconsistency.
 */
prob_inconsistent_theory(M:Prob):-
  inconsistent_theory(M:_,[return_prob(Prob)]).




/****************************
QUERY PREDICATES
*****************************/

/**
 * execute_query(+Module:module_name,+QueryType:string,+QueryArgsNC:list,--Expl:list,+QueryOptions:list)
 * 
 * This is the general predicate that asnwers a given query. It parses the arguments (individuals, classes, etc.)
 * and looks for the set of explanations following the given options.
 * Uses exceute_query_int/6 to perform the inference.
 */
execute_query(M,QueryType,QueryArgsNC,ExplOut,QueryOptions):-
  check_query_args(M,QueryArgsNC,QueryArgs,QueryArgsNotPresent),
  execute_query_int(M,QueryType,QueryArgs,QueryArgsNotPresent,ExplOut,QueryOptions).

% IF QueryArgsNotPresent is an empty list, all the arguments are present in the KB.
% The inference can proceed.
execute_query_int(M,QueryType,QueryArgs,[],ExplOut,QueryOptions):- !,
find_explanations(M,QueryType,QueryArgs,ExplInc,QueryOptions),
Expl=ExplInc.expl,
Inc=ExplInc.incons, %TODO remove this if to return always both expls
( dif(Expl,[]) -> ExplOut=Expl 
  ; 
  ( dif(Inc,[]) -> (ExplOut=Inc,print_message(warning,inconsistent),print_message(warning,inconsistence_expl)) ; true)
),
( query_option(QueryOptions,max_expl,bt) -> ExplIncP = ExplInc.put(expl,[Expl]).put(incons,[Inc]) ; ExplIncP = ExplInc),
( query_option(QueryOptions,return_prob,Prob) ->
  (
    compute_prob_and_close(M,ExplIncP,Prob,IncCheck),
    (dif(IncCheck,false) -> print_message(warning,completely_inconsistent) ; true),
    ( query_option(QueryOptions,return_incons_expl,Inc) -> true ; true) % does nothing, just unifies with the variable in the option
  )
  ; true
).

% IF QueryArgsNotPresent is not empty, the inference must be stopped.
execute_query_int(_M,_QueryType,_QueryArgs,QueryArgsNotPresent,_ExplOut,_QueryOptions):- !,
  %dif(QueryArgsNotPresent,[]), % if execution reaches this point, QueryArgsNotPresent is not empty, so this line is always true.
  print_message(warning,iri_not_exists(QueryArgsNotPresent)),!.
  

/**
 * find_explanations(+M:module,+QueryType:string,+QueryArgs:list,--Expl:list,+QueryOptions:list)
 * 
 * This predicate acts as the execution monitor, managing the search for explanations.
 */
% Execution monitor
% TODO put here multi-threading
find_explanations(M,QueryType,QueryArgs,Expl,QueryOptions):-
  assert(M:keep_env),
  ( query_option(QueryOptions,assert_abox,AssertABox) -> Opt=[assert_abox(AssertABox)] ; Opt=[]),
  ( query_option(QueryOptions,max_expl,N) -> 
    MonitorNExpl = N
    ; 
    ( ( query_option(QueryOptions,return_prob,_) -> MonitorNExpl=all ; MonitorNExpl=bt) ) % if return_prob is present and no max_expl force to find all the explanations
  ),
  ( query_option(QueryOptions,time_limit,MonitorTimeLimit) ->
    find_n_explanations_time_limit(M,QueryType,QueryArgs,Expl,MonitorNExpl,MonitorTimeLimit,Opt) 
    ;
    find_n_explanations(M,QueryType,QueryArgs,Expl,MonitorNExpl,Opt)
  ).

% Find explanations in a given limited time.
% TODO multi-thearding here
find_n_explanations_time_limit(M,QueryType,QueryArgs,Expl,MonitorNExpl,MonitorTimeLimit,Opt):-
  retractall(M:setting_trill(timeout,_)),
  get_time(Start),
  Timeout is Start + MonitorTimeLimit,
  assert(M:setting_trill(timeout,Timeout)),
  find_n_explanations(M,QueryType,QueryArgs,Expl,MonitorNExpl,Opt),
  get_time(End),
  (End<Timeout -> true ; print_message(warning,timeout_reached)).


% TODO merge tornado
% findall
find_n_explanations(M,QueryType,QueryArgs,Expls,all,Opt):-
  !, % CUT so that no other calls to find_explanation can be ran (to avoid running that with variable N)
  findall(Expl,find_single_explanation(M,QueryType,QueryArgs,Expl,Opt),Expls0),
  merge_explanations_from_dicts_list(Expls0,Expls).

% find one in backtracking
find_n_explanations(M,QueryType,QueryArgs,Expl,bt,Opt):-
  !, % CUT so that no other calls to find_explanation can be ran (to avoid running that with variable N)
  find_single_explanation(M,QueryType,QueryArgs,Expl,Opt).

% find_n_sol
find_n_explanations(M,QueryType,QueryArgs,Expls,N,Opt):-
  (number(N) -> % CUT so that no other calls to find_explanation can be ran
    (findnsols(N,Expl,find_single_explanation(M,QueryType,QueryArgs,Expl,Opt),Expls),!) % CUT otherwise findnsols would backtracks to look for another N sols
    ;
    (print_message(warning,wrong_number_max_expl),!,false)
  ).

% collect explanations one at a time. This is where the inference starts.
find_single_explanation(M,QueryType,QueryArgs,Expl,Opt):-
  set_up_reasoner(M),
  build_abox(M,Tableau,QueryType,QueryArgs), % will expand the KB without the query
  (absence_of_clashes(Tableau) ->  % TODO if QueryType is inconsistent no check
    (
      add_q(M,QueryType,Tableau,QueryArgs,Tableau0),
      set_up_tableau(M),
      findall(Tableau1,expand_queue(M,Tableau0,Tableau1),L),
      (query_option(Opt,assert_abox,true) -> (writeln('Asserting ABox...'), M:assert(final_abox(L)), writeln('Done. Asserted in final_abox/1...')) ; true),
      find_expls(M,L,QueryArgs,Expl1),
      check_and_close(M,Expl1,Expl)
    )
  ;
    print_message(warning,inconsistent),!,false
  ).


/****************************
REASONER MANAGEMENT
*****************************/

% Initializes the reasoner by removing explanations found and setting the counter for anonymous individuals
set_up_reasoner(M):-
  %clean_up(M),
  set_up(M),
  assert(M:trillan_idx(1)).

% General setting up
% TODO merge tornado
set_up(M):-
  utility_translation:set_up(M),
  init_delta(M),
  M:(dynamic exp_found/2, exp_found/3, keep_env/0, tornado_bdd_environment/1, setting_trill/2),
  retractall(M:setting_trill(_,_)).
  %foreach(setting_trill_default(DefaultSetting,DefaultVal),assert(M:setting_trill(DefaultSetting,DefaultVal))).


set_up_tableau(M):-
  % TODO move to KB loading
  %setting_trill_default(det_rules,DetRules),
  %setting_trill_default(nondet_rules,NondetRules),
  %set_tableau_expansion_rules(M:DetRules,NondetRules). 
  prune_tableau_rules(M).

clean_up(M):-
  utility_translation:clean_up(M),
  M:(dynamic exp_found/2, exp_found/3, keep_env/0, tornado_bdd_environment/1, setting_trill/2),
  %retractall(M:trillan_idx(_)),
  retractall(M:exp_found(_,_)),
  retractall(M:exp_found(_,_,_)),
  retractall(M:keep_env),
  retractall(M:tornado_bdd_environment(_)),
  retractall(M:setting_trill(_,_)).

/*
set_up(M):-
  utility_translation:set_up(M),
  init_delta(M),
  M:(dynamic exp_found/2, setting_trill/2),
  retractall(M:setting_trill(_,_)).
  %foreach(setting_trill_default(DefaultSetting,DefaultVal),assert(M:setting_trill(DefaultSetting,DefaultVal))).

clean_up(M):-
  utility_translation:clean_up(M),
  M:(dynamic exp_found/2, setting_trill/2),
  retractall(M:exp_found(_,_)),
  retractall(M:setting_trill(_,_)).*/
/**
 * init_trill
 * 
 * Initializes the reasoner.
 */
init_trill:-
  get_trill_current_module(M),
  clean_up(M),
  % TODO previously set_up(M)
  set_up(M),
  %set_up_reasoner(M),
  utility_translation:set_up_kb_loading(M),
  trill:add_kb_prefixes(M:[('disponte'='http://ml.unife.it/disponte#'),('owl'='http://www.w3.org/2002/07/owl#')]).

%  creation of the query anon individual
query_ind(trillan(0)).

/*
  creation of a new anonymous individual

*/
new_ind(M,trillan(I)):-
  retract(M:trillan_idx(I)),
  I1 is I+1,
  assert(M:trillan_idx(I1)).

/****************************
REASONER MONITOR

Predicates to monitor the inference and the output of the reasoner
*****************************/

check_time_monitor(M):-
  M:setting_trill(timeout,Timeout),!,
  get_time(Now),
  Timeout<Now. % I must stop

% TODO merge with tornado
% checks the explanation, if it is for the query of the inconsistency
check_and_close(M,Expl0,Expl):-
  M:keep_env,
  QExpl0=Expl0.expl,
  dif(QExpl0,[]),!,
  sort(QExpl0,QExpl),
  Expl=Expl0.put(expl,QExpl).

check_and_close(M,Expl0,Expl):-
  M:keep_env,
  QExpl0=Expl0.incons,
  dif(QExpl0,[]),
  sort(QExpl0,QExpl),
  Expl=Expl0.put(incons,QExpl).

% TODO merge with tornado
% if there is not inconsistency, perform classical probability computation
compute_prob_and_close(M,expl{expl:Exps,incons:[[]]},Prob,false):- !,
  compute_prob(M,Exps,Prob),
  retractall(M:keep_env),!.
% if there is not inconsistency, perform classical probability computation
compute_prob_and_close(M,expl{expl:[[]],incons:Exps},Prob,false):- !,
  compute_prob(M,Exps,Prob),
  retractall(M:keep_env),!.

compute_prob_and_close(M,Exps,Prob,Inc):-
  compute_prob_inc(M,Exps,Prob,Inc),
  retractall(M:keep_env),!.

% takes a list of dicts expl{query,expl,incons} and create a single dict of the same shape with all values from expls and incons merged
merge_explanations_from_dicts_list(ExplsList,expl{expl:Ec,incons:Inc}):-
  merge_explanations_from_dicts_list(ExplsList,Ec,Inc),!.

merge_explanations_from_dicts_list([],[],[]).

merge_explanations_from_dicts_list([expl{expl:[],incons:Inc0}|T],Ec,[Inc0|Inc]):-
  merge_explanations_from_dicts_list(T,Ec,Inc).

merge_explanations_from_dicts_list([expl{expl:Ec0,incons:[]}|T],[Ec0|Ec],Inc):-
  merge_explanations_from_dicts_list(T,Ec,Inc).

/****************************
REASONER'S RULES MANAGEMENT
*****************************/
/*
  adds the tableau rules necessary to manage the class taken as input
*/
add_tableau_rules_from_class(M,someValuesFrom(_,_)):-
  M:setting_trill(det_rules,Rules),
  memberchk(exists_rule,Rules),!.

add_tableau_rules_from_class(M,C):-
  M:kb_atom(KBA),
  Classes=KBA.class,
  setting_trill_default(det_rules,DetRules),
  prune_tableau_rules([C|Classes],DetRules,PrunedDetRules),
  setting_trill_default(nondet_rules,NondetRules),
  prune_tableau_rules([C|Classes],NondetRules,PrunedNondetRules),
  set_tableau_expansion_rules(M:PrunedDetRules,PrunedNondetRules).


/*
  check the KB atoms to consider only the necessary expansion rules, pruning the useless ones
*/
prune_tableau_rules(M):-
  M:kb_atom(KBA),
  Classes=KBA.class,
  setting_trill_default(det_rules,DetRules),
  prune_tableau_rules(Classes,DetRules,PrunedDetRules),
  setting_trill_default(nondet_rules,NondetRules),
  prune_tableau_rules(Classes,NondetRules,PrunedNondetRules),
  set_tableau_expansion_rules(M:PrunedDetRules,PrunedNondetRules).

% o_rule,and_rule,unfold_rule,add_exists_rule,forall_rule,forall_plus_rule,exists_rule,min_rule,or_rule,max_rule,ch_rule
prune_tableau_rules(_,[],[]).

prune_tableau_rules(KBA,[o_rule|TR],[o_rule|PTR]):-
  memberchk(oneOf(_),KBA),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[and_rule|TR],[and_rule|PTR]):-
  memberchk(intersectionOf(_),KBA),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[unfold_rule|TR],[unfold_rule|PTR]):-
  !,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[add_exists_rule|TR],[add_exists_rule|PTR]):-
  !,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[forall_rule|TR],[forall_rule|PTR]):-
  memberchk(allValuesFrom(_,_),KBA),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[forall_plus_rule|TR],[forall_plus_rule|PTR]):-
  memberchk(allValuesFrom(_,_),KBA),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[exists_rule|TR],[exists_rule|PTR]):-
  memberchk(someValuesFrom(_,_),KBA),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[min_rule|TR],[min_rule|PTR]):-
  (memberchk(minCardinality(_,_),KBA); memberchk(minCardinality(_,_,_),KBA);memberchk(exactCardinality(_,_),KBA);memberchk(exactCardinality(_,_,_),KBA)),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[or_rule|TR],[or_rule|PTR]):-
  memberchk(unionOf(_),KBA),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[max_rule|TR],[max_rule|PTR]):-
  (memberchk(maxCardinality(_,_),KBA); memberchk(maxCardinality(_,_,_),KBA);memberchk(exactCardinality(_,_),KBA);memberchk(exactCardinality(_,_,_),KBA)),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[ch_rule|TR],[ch_rule|PTR]):-
  (memberchk(maxCardinality(_,_),KBA); memberchk(maxCardinality(_,_,_),KBA);memberchk(exactCardinality(_,_),KBA);memberchk(exactCardinality(_,_,_),KBA)),!,
  prune_tableau_rules(KBA,TR,PTR).

prune_tableau_rules(KBA,[_|TR],PTR):-
  prune_tableau_rules(KBA,TR,PTR).

% ==============================
% Collect individual
% Auxiliary predicates to extract the set of individuals connected to the query
% ==============================

% Builds the list of individuals conneted given the query type
collect_individuals(M,io,[_,IndEx],IndividualsSet):-
  scan_connected_individuals(M,[IndEx],[],[IndEx],IndividualsSet).

collect_individuals(M,pv,[_,Ind1Ex,Ind2Ex],IndividualsSet):-
  scan_connected_individuals(M,[Ind1Ex,Ind2Ex],[],[Ind1Ex,Ind2Ex],IndividualsSet).

collect_individuals(_,sc,[_,_],[QInd]):- % It is not necessary to check the KB as the individual of the query is a new fresh individual not included in the KB.
  query_ind(QInd).

collect_individuals(_,un,['unsat',_],[QInd]):- % It is not necessary to check the KB as the individual of the query is a new fresh individual not included in the KB.
  query_ind(QInd).

collect_individuals(_,it,['inconsistent','kb'],[]):-!.

% Recursively gather all the connected individuals, i.e., isolate the relevant fragment of the KB.
%scan_connected_individuals(M,IndividualsToCheck,IndividualsChecked,IndividualsSet0,IndividualsSet).
scan_connected_individuals(_,[],_,IndividualsSet0,IndividualsSet):-
  sort(IndividualsSet0,IndividualsSet).

scan_connected_individuals(M,[H|IndividualsToCheck],IndividualsChecked,IndividualsSet0,IndividualsSet):-
  memberchk(H,IndividualsChecked),!,
  scan_connected_individuals(M,IndividualsToCheck,IndividualsChecked,IndividualsSet0,IndividualsSet).


scan_connected_individuals(M,[H|IndividualsToCheck0],IndividualsChecked,IndividualsSet0,IndividualsSet):-
  gather_connected_individuals(M,H,NewIndividualsToCheck),
  append(IndividualsSet0,NewIndividualsToCheck,IndividualsSet1),
  append(IndividualsToCheck0,NewIndividualsToCheck,IndividualsToCheck),
  scan_connected_individuals(M,IndividualsToCheck,[H|IndividualsChecked],IndividualsSet1,IndividualsSet).

% Find the individuals directly connected to the given one
gather_connected_individuals(M,Ind,ConnectedInds):-
  find_successors(M,Ind,SuccInds),
  find_predecessors(M,Ind,PredInds),
  append(SuccInds,PredInds,ConnectedInds).


/****************************
REASONER'S RULES
*****************************/

% -------------
% expansion queue driven rules application
% -------------
expand_queue(M,Tab,Tab):-
  test_end_expand_queue(M,Tab),!.

expand_queue(M,Tab0,Tab):-
  extract_from_expansion_queue(Tab0,EA,Tab1),!,
  apply_all_rules(M,Tab1,EA,Tab2),
  % update_queue(M,T,NewExpQueue),
  expand_queue(M,Tab2,Tab).

test_end_expand_queue(M,_):-
  check_time_monitor(M),!.

test_end_expand_queue(_,Tab):-
  expansion_queue_is_empty(Tab).

% -------------
% rules application
% -------------
apply_all_rules(M,Tab0,EA,Tab):-
  M:setting_trill(det_rules,Rules),
  apply_det_rules(M,Rules,Tab0,EA,Tab1),
  (test_end_apply_rule(M,Tab0,Tab1) ->
  Tab=Tab1;
  apply_all_rules(M,Tab1,EA,Tab)).

apply_det_rules(M,[],Tab0,EA,Tab):-
  M:setting_trill(nondet_rules,Rules),
  apply_nondet_rules(M,Rules,Tab0,EA,Tab).

apply_det_rules(M,[H|_],Tab0,EA,Tab):-
  %C=..[H,Tab,Tab1],
  call(H,M,Tab0,EA,Tab),!.

apply_det_rules(M,[_|T],Tab0,EA,Tab):-
  apply_det_rules(M,T,Tab0,EA,Tab).


apply_nondet_rules(_,[],Tab,_EA,Tab).

apply_nondet_rules(M,[H|_],Tab0,EA,Tab):-
  %C=..[H,Tab,L],
  call(H,M,Tab0,EA,L),!,
  member(Tab,L),
  dif(Tab0,Tab).

apply_nondet_rules(M,[_|T],Tab0,EA,Tab):-
  apply_nondet_rules(M,T,Tab0,EA,Tab).


test_end_apply_rule(M,_,_):-
  check_time_monitor(M),!.

test_end_apply_rule(_,Tab0,Tab1):-
  same_tableau(Tab0,Tab1).

% -------------
% rules
% -------------

/*
  add_exists_rule
  
  Looks up for a role that links 2 individuals, if it find it, it searches a subclass axiom
  in the KB that contains 'someValuesFrom(R,C)' where R is the role which links the 2 individuals
  and C is a class in which the 2nd individual belongs to.
  
  This rule hasn't a corresponding rule in the tableau
  ========================
*/
add_exists_rule(M,Tab0,[R,Ind1,Ind2],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(C,Ind2,Expl2,ABox),
  (unifiable(C,someValuesFrom(_,_),_)->false;
  ( %existsInKB(M,R,C),
    add_tableau_rules_from_class(M,someValuesFrom(R,C)),
    findPropertyAssertion(R,Ind1,Ind2,Expl1,ABox),
    and_f(M,Expl1,Expl2,Expl),
    update_abox(M,Tab0,someValuesFrom(R,C),Ind1,Expl,Tab)
  )).

add_exists_rule(M,Tab0,[C,Ind2],Tab):-
  (unifiable(C,someValuesFrom(_,_),_)->false;
  ( get_abox(Tab0,ABox),
    findPropertyAssertion(R,Ind1,Ind2,Expl1,ABox),
    %existsInKB(M,R,C),
    add_tableau_rules_from_class(M,someValuesFrom(R,C)),
    findClassAssertion(C,Ind2,Expl2,ABox),
    and_f(M,Expl1,Expl2,Expl),
    update_abox(M,Tab0,someValuesFrom(R,C),Ind1,Expl,Tab)
  )).

/* *************** */ 

/*
  and_rule
  =================
*/
and_rule(M,Tab0,[intersectionOf(LC),Ind],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(intersectionOf(LC),Ind,Expl,ABox),
  \+ indirectly_blocked(Ind,Tab0),
  scan_and_list(M,LC,Ind,Expl,Tab0,Tab,0).


%----------------
scan_and_list(_M,[],_Ind,_Expl,Tab,Tab,Mod):-
  dif(Mod,0).

scan_and_list(M,[C|T],Ind,Expl,Tab0,Tab,_Mod):-
  update_abox(M,Tab0,C,Ind,Expl,Tab1),!,
  scan_and_list(M,T,Ind,Expl,Tab1,Tab,1).

scan_and_list(M,[_C|T],Ind,Expl,Tab0,Tab,Mod):-
  scan_and_list(M,T,Ind,Expl,Tab0,Tab,Mod).
/* ************* */

/*
  or_rule
  ===============
*/
or_rule(M,Tab0,[unionOf(LC),Ind],L):- 
  get_abox(Tab0,ABox),
  findClassAssertion(unionOf(LC),Ind,Expl,ABox),
  \+ indirectly_blocked(Ind,Tab0),
  %not_ind_intersected_union(Ind,LC,ABox),
  % length(LC,NClasses),
  get_choice_point_id(M,ID),
  scan_or_list(M,LC,0,ID,Ind,Expl,Tab0,L),
  dif(L,[]),
  create_choice_point(M,Ind,or,unionOf(LC),LC,_),!. % last variable whould be equals to ID

not_ind_intersected_union(Ind,LC,ABox):-
  \+ ind_intersected_union(Ind,LC,ABox).

ind_intersected_union(Ind,LC,ABox) :-
  member(C,LC),
  findClassAssertion(C,Ind,_,ABox),!.
%---------------
scan_or_list(_,[],_,_,_,_,_,[]):- !.

scan_or_list(M,[C|T],N0,CP,Ind,Expl0,Tab0,[Tab|L]):-
  add_choice_point(M,cpp(CP,N0),Expl0,Expl),
  update_abox(M,Tab0,C,Ind,Expl,Tab),
  N is N0 + 1,
  scan_or_list(M,T,N,CP,Ind,Expl0,Tab0,L).

/* **************** */

/*
  exists_rule
  ==================
*/
exists_rule(M,Tab0,[someValuesFrom(R,C),Ind1],Tab):-
  get_abox(Tab0,ABox0),
  findClassAssertion(someValuesFrom(R,C),Ind1,Expl,ABox0),
  \+ blocked(Ind1,Tab0),
  \+ connected_individual(R,C,Ind1,ABox0),
  new_ind(M,Ind2),
  add_edge(R,Ind1,Ind2,Tab0,Tab1),
  add_owlThing_ind(M,Tab1,Ind2,Tab2),
  update_abox(M,Tab2,C,Ind2,Expl,Tab3),
  update_abox(M,Tab3,R,Ind1,Ind2,Expl,Tab).

%---------------
connected_individual(R,C,Ind1,ABox):-
  findPropertyAssertion(R,Ind1,Ind2,_,ABox),
  findClassAssertion(C,Ind2,_,ABox).

/* ************ */

/*
  forall_rule
  ===================
*/
forall_rule(M,Tab0,[allValuesFrom(R,C),Ind1],Tab):-
  get_abox(Tab0,ABox),
  findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
  \+ indirectly_blocked(Ind1,Tab0),
  findClassAssertion(allValuesFrom(R,C),Ind1,Expl1,ABox),
  and_f(M,Expl1,Expl2,Expl),
  update_abox(M,Tab0,C,Ind2,Expl,Tab).

forall_rule(M,Tab0,[R,Ind1,Ind2],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(allValuesFrom(R,C),Ind1,Expl1,ABox),
  \+ indirectly_blocked(Ind1,Tab0),
  findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
  and_f(M,Expl1,Expl2,Expl),
  update_abox(M,Tab0,C,Ind2,Expl,Tab).

/* ************** */

/*
  forall_plus_rule
  =================
*/
forall_plus_rule(M,Tab0,[allValuesFrom(S,C),Ind1],Tab):-
  get_abox(Tab0,ABox),
  findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
  find_sub_sup_trans_role(M,R,S,Expl3),
  findClassAssertion(allValuesFrom(S,C),Ind1,Expl1,ABox),
  \+ indirectly_blocked(Ind1,Tab0),
  and_f(M,Expl1,Expl2,ExplT),
  and_f(M,ExplT,Expl3,Expl),
  update_abox(M,Tab0,allValuesFrom(R,C),Ind2,Expl,Tab).

forall_plus_rule(M,Tab0,[R,Ind1,Ind2],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(allValuesFrom(S,C),Ind1,Expl1,ABox),
  \+ indirectly_blocked(Ind1,Tab0),
  findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
  find_sub_sup_trans_role(M,R,S,Expl3),
  and_f(M,Expl1,Expl2,ExplT),
  and_f(M,ExplT,Expl3,Expl),
  update_abox(M,Tab0,allValuesFrom(R,C),Ind2,Expl,Tab). 

% --------------
find_sub_sup_trans_role(M,R,S,Expl):-
  find_sub_sup_property(M,R,S,_),
  % TODO previously
  % M:subPropertyOf(R,S),
  M:transitiveProperty(R),
  initial_expl(M,EExpl),
  and_f_ax(M,subPropertyOf(R,S),EExpl,Expl0),
  and_f_ax(M,transitive(R),Expl0,Expl).

find_sub_sup_trans_role(M,R,S,Expl):-
  find_sub_sup_property(M,R,S,_),
  % TODO previously
  % M:subPropertyOf(R,S),
  \+ M:transitiveProperty(R),
  initial_expl(M,EExpl),
  and_f_ax(M,subPropertyOf(R,S),EExpl,Expl).

/* ************ */

/*
  unfold_rule
  ===========
*/

unfold_rule(M,Tab0,[C,Ind],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(C,Ind,Expl,ABox),
  find_sub_sup_class(M,C,D,Ax),
  and_f_ax(M,Ax,Expl,AxL),
  update_abox(M,Tab0,D,Ind,AxL,Tab1),
  add_nominal(M,D,Ind,Tab1,Tab).

/* -- unfold_rule
      takes a class C1 in which Ind belongs, find a not atomic class C
      that contains C1 (C is seen as list of classes), controls if
      the individual Ind belongs to all those classes, if yes it finds a class D (if exists)
      that is the superclass or an equivalent class of C and adds D to label of Ind
      - for managing tableau with more than one clash -
      correspond to the ce_rule
   --
*/
unfold_rule(M,Tab0,[C1,Ind],Tab):-
  find_not_atomic(M,C1,C,L),
  get_abox(Tab0,ABox),
  ( C = unionOf(_) -> findClassAssertion(C1,Ind,Expl,ABox)
   ; find_all_expls_from_class_list(M,Ind,L,ABox,Expl)),
  %find_sub_sup_class(M,C,D,Ax),
  %and_f_ax(M,Ax,Expl1,AxL1),
  update_abox(M,Tab0,C,Ind,Expl,Tab1),
  add_nominal(M,C,Ind,Tab1,Tab).

/* -- unfold_rule
 *    control propertyRange e propertyDomain
 * --
 */
unfold_rule(M,Tab0,[P,S,O],Tab):-
  get_abox(Tab0,ABox),
  find_class_prop_range_domain(M,P,S,O,Ind,D,Expl,ABox),
  update_abox(M,Tab0,D,Ind,Expl,Tab1),
  add_nominal(M,D,Ind,Tab1,Tab).

/*
 * -- unfold_rule
 *    manage the negation
 * --
 */
unfold_rule(M,Tab0,[complementOf(C),Ind],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(complementOf(C),Ind,Expl,ABox),
  find_neg_class(C,D),
  and_f_ax(M,complementOf(C),Expl,AxL),
  update_abox(M,Tab0,D,Ind,AxL,Tab1),
  add_nominal(M,D,Ind,Tab1,Tab).

/*
 * -- unfold_rule
 *    unfold_rule to unfold roles
 * --
 */
% sub properties
unfold_rule(M,Tab0,[C,Ind1,Ind2],Tab):-
  get_abox(Tab0,ABox),
  findPropertyAssertion(C,Ind1,Ind2,Expl,ABox),
  find_sub_sup_property(M,C,D,Ax),
  and_f_ax(M,Ax,Expl,AxL),
  update_abox(M,Tab0,D,Ind1,Ind2,AxL,Tab1),
  add_nominal(M,D,Ind1,Tab1,Tab2),
  add_nominal(M,D,Ind2,Tab2,Tab).

%inverseProperties
unfold_rule(M,Tab0,[C,Ind1,Ind2],Tab):-
  get_abox(Tab0,ABox),
  findPropertyAssertion(C,Ind1,Ind2,Expl,ABox),
  find_inverse_property(M,C,D,Ax),
  and_f_ax(M,Ax,Expl,AxL),
  update_abox(M,Tab0,D,Ind2,Ind1,AxL,Tab1),
  add_nominal(M,D,Ind1,Tab1,Tab2),
  add_nominal(M,D,Ind2,Tab2,Tab).

% ----------------
% add_nominal

add_nominal(M,D,Ind,Tab0,Tab):-
  get_abox(Tab0,ABox0),
  ((D = oneOf(_),
    \+ member(nominal(Ind),ABox0))
    ->
   (
     ABox1 = [nominal(Ind)|ABox0],
     (member((classAssertion('http://www.w3.org/2002/07/owl#Thing',Ind),_E),ABox1)
     ->
     set_abox(Tab0,ABox1,Tab)
     ;
     (empty_expl(M,Expl),set_abox(Tab0,[(classAssertion('http://www.w3.org/2002/07/owl#Thing',Ind),Expl)|ABox1],Tab))
     )
   )
    ;
  set_abox(Tab0,ABox0,Tab)
  ).

% puts together the explanations of all the concepts found by find_not_atomic/3
%TODO previously find_all/5
%TODO merge tornado
%TODO make it tail recursive
find_all_expls_from_class_list(_M,_,[],_,[]).

find_all_expls_from_class_list(M,Ind,[H|T],ABox,ExplT):-
  findClassAssertion(H,Ind,Expl1,ABox),
  find_all_expls_from_class_list(M,Ind,T,ABox,Expl2),
  and_f(M,Expl1,Expl2,ExplT).

/* ************* */

/*
  ce_rule
  =============
*/
ce_rule(M,Tab0,Tab):-
  get_tabs(Tab0,(T,_,_)),
  find_not_sub_sup_class(M,Ax,UnAx),
  vertices(T,Inds),
  apply_ce_to(M,Inds,Ax,UnAx,Tab0,Tab,C),
  C @> 0.

%---------------------
apply_ce_to(_M,[],_,_,Tab,Tab,0).

apply_ce_to(M,[Ind|T],Ax,UnAx,Tab0,Tab,C):-
  \+ indirectly_blocked(Ind,Tab),
  update_abox(M,Tab0,UnAx,Ind,[Ax],Tab1),!,
  apply_ce_to(M,T,Ax,UnAx,Tab1,Tab,C0),
  C is C0 + 1.

apply_ce_to(M,[_Ind|T],Ax,UnAx,Tab0,Tab,C):-
  apply_ce_to(M,T,Ax,UnAx,Tab0,Tab,C).

/* **************** */

/*
  min_rule
  =============
*/
% minCardinality(N,S)
min_rule(M,Tab0,[minCardinality(N,S),Ind1],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(minCardinality(N,S),Ind1,Expl,ABox),
  \+ blocked(Ind1,Tab0),
  s_neighbours(M,Ind1,S,Tab0,SN),
  safe_s_neigh(SN,S,Tab0,SS),
  length(SS,LSS),
  LSS @< N,
  NoI is N-LSS,
  min_rule_neigh(M,NoI,S,Ind1,Expl,NI,Tab0,Tab1),
  update_abox(M,Tab1,differentIndividuals(NI),Expl,Tab).

% minCardinality(N,S,C)
min_rule(M,Tab0,[minCardinality(N,S,C),Ind1],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(minCardinality(N,S,C),Ind1,Expl,ABox),
  \+ blocked(Ind1,Tab0),
  s_neighbours(M,Ind1,S,Tab0,SN),
  safe_s_neigh_C(SN,S,C,Tab0,ABox,SS),
  length(SS,LSS),
  LSS @< N,
  NoI is N-LSS,
  min_rule_neigh_C(M,NoI,S,C,Ind1,Expl,NI,Tab0,Tab1),
  update_abox(M,Tab1,differentIndividuals(NI),Expl,Tab).

% exactCardinality(N,S)
min_rule(M,Tab0,[exactCardinality(N,S),Ind1],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S),Ind1,Expl,ABox),
  \+ blocked(Ind1,Tab0),
  s_neighbours(M,Ind1,S,Tab0,SN),
  safe_s_neigh(SN,S,Tab0,SS),
  length(SS,LSS),
  LSS @< N,
  NoI is N-LSS,
  min_rule_neigh(M,NoI,S,Ind1,Expl,NI,Tab0,Tab1),
  update_abox(M,Tab1,differentIndividuals(NI),Expl,Tab).

% exactCardinality(N,S,C)
min_rule(M,Tab0,[exactCardinality(N,S,C),Ind1],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S,C),Ind1,Expl,ABox),
  \+ blocked(Ind1,Tab0),
  s_neighbours(M,Ind1,S,Tab0,SN),
  safe_s_neigh_C(SN,S,C,Tab0,SS),
  length(SS,LSS),
  LSS @< N,
  NoI is N-LSS,
  min_rule_neigh_C(M,NoI,S,C,Ind1,Expl,NI,Tab0,Tab1),
  update_abox(M,Tab1,differentIndividuals(NI),Expl,Tab).

% differentIndividuals with exactCardinality(N,S)
% TODO to test
min_rule(M,Tab0,[differentIndividuals(NI)],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S),Ind1,Expl,ABox),
  \+ blocked(Ind1,Tab0),
  s_neighbours(M,Ind1,S,Tab0,SN),
  safe_s_neigh(SN,S,Tab0,SS),
  length(SS,LSS),
  LSS @< N,
  NoI is N-LSS,
  min_rule_neigh(M,NoI,S,Ind1,Expl,NI,Tab0,Tab).

% differentIndividuals with exactCardinality(N,S,C)
% TODO to test
min_rule(M,Tab0,[differentIndividuals(NI)],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S,C),Ind1,Expl,ABox),
  \+ blocked(Ind1,Tab0),
  s_neighbours(M,Ind1,S,Tab0,SN),
  safe_s_neigh(SN,S,Tab0,SS),
  length(SS,LSS),
  LSS @< N,
  NoI is N-LSS,
  min_rule_neigh_C(M,NoI,S,C,Ind1,Expl,NI,Tab0,Tab).

% ----------------------
min_rule_neigh(_,0,_,_,_,[],Tab,Tab).

min_rule_neigh(M,N,S,Ind1,Expl,[Ind2|NI],Tab0,Tab):-
  N > 0,
  NoI is N-1,
  new_ind(M,Ind2),
  add_edge(S,Ind1,Ind2,Tab0,Tab1),
  add_owlThing_ind(M,Tab1,Ind2,Tab2),
  update_abox(M,Tab2,S,Ind1,Ind2,Expl,Tab3),
  %check_block(Ind2,Tab3),
  min_rule_neigh(M,NoI,S,Ind1,Expl,NI,Tab3,Tab).

%----------------------
min_rule_neigh_C(_,0,_,_,_,_,[],Tab,Tab).

min_rule_neigh_C(M,N,S,C,Ind1,Expl,[Ind2|NI],Tab0,Tab):-
  N > 0,
  NoI is N-1,
  new_ind(M,Ind2),
  add_edge(S,Ind1,Ind2,Tab0,Tab1),
  add_owlThing_ind(M,Tab1,Ind2,Tab2),
  update_abox(M,Tab2,S,Ind1,Ind2,Expl,Tab3),
  update_abox(M,Tab3,C,Ind2,[propertyAssertion(S,Ind1,Ind2)|Expl],Tab4),
  %check_block(Ind2,Tab4),
  min_rule_neigh_C(M,NoI,S,C,Ind1,Expl,NI,Tab4,Tab).
/* **************** */

/*
  max_rule
  ================
*/
% maxCardinality(N,S)
max_rule(M,Tab0,[maxCardinality(N,S),Ind],L):-
  get_abox(Tab0,ABox),
  findClassAssertion(maxCardinality(N,S),Ind,Expl0,ABox),
  \+ indirectly_blocked(Ind,Tab0),
  s_neighbours(M,Ind,S,Tab0,SN),
  length(SN,LSS),
  LSS @> N,
  get_choice_point_id(M,ID),
  scan_max_list(M,maxCardinality(N,S),S,'http://www.w3.org/2002/07/owl#Thing',SN,ID,Ind,Expl0,Tab0,L),!. 

% maxCardinality(N,S,C)
max_rule(M,Tab0,[maxCardinality(N,S,C),Ind],L):-
  get_abox(Tab0,ABox),
  findClassAssertion(maxCardinality(N,S,C),Ind,Expl0,ABox),
  \+ indirectly_blocked(Ind,Tab0),
  s_neighbours(M,Ind,S,Tab0,SN),
  individuals_of_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  LSS @> N,
  get_choice_point_id(M,ID),%gtrace,
  scan_max_list(M,maxCardinality(N,S,C),S,C,SNC,ID,Ind,Expl0,Tab0,L),!. % last variable whould be equals to ID

%---------------------

% exactCardinality(N,S)
max_rule(M,Tab0,[exactCardinality(N,S),Ind],L):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S),Ind,Expl0,ABox),
  \+ indirectly_blocked(Ind,Tab0),
  s_neighbours(M,Ind,S,Tab0,SN),
  length(SN,LSS),
  LSS @> N,
  get_choice_point_id(M,ID),
  scan_max_list(M,exactCardinality(N,S),S,'http://www.w3.org/2002/07/owl#Thing',SN,ID,Ind,Expl0,Tab0,L),!. 

% exactCardinality(N,S,C)
max_rule(M,Tab0,[exactCardinality(N,S,C),Ind],L):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S,C),Ind,Expl0,ABox),
  \+ indirectly_blocked(Ind,Tab0),
  s_neighbours(M,Ind,S,Tab0,SN),
  individuals_of_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  LSS @> N,
  get_choice_point_id(M,ID),%gtrace,
  scan_max_list(M,exactCardinality(N,S,C),S,C,SNC,ID,Ind,Expl0,Tab0,L),!. % last variable whould be equals to ID

% propertyAssertion(S,Ind,anon) with exactCardinality(N,S)
max_rule(M,Tab0,[S,Ind,_],L):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S),Ind,Expl0,ABox),
  \+ indirectly_blocked(Ind,Tab0),
  s_neighbours(M,Ind,S,Tab0,SN),
  length(SN,LSS),
  LSS @> N,
  get_choice_point_id(M,ID),
  scan_max_list(M,exactCardinality(N,S),S,'http://www.w3.org/2002/07/owl#Thing',SN,ID,Ind,Expl0,Tab0,L),!. 

% propertyAssertion(S,Ind,anon) with exactCardinality(N,S,C)
max_rule(M,Tab0,[S,Ind,_],L):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S,C),Ind,Expl0,ABox),
  \+ indirectly_blocked(Ind,Tab0),
  s_neighbours(M,Ind,S,Tab0,SN),
  individuals_of_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  LSS @> N,
  get_choice_point_id(M,ID),
  scan_max_list(M,exactCardinality(N,S,C),S,C,SNC,ID,Ind,Expl0,Tab0,L),!. % last variable whould be equals to ID

%---------------------

scan_max_list(M,MaxCardClass,S,C,SN,CP,Ind,Expl,Tab0,Tab_list):- %here
  create_couples_for_merge(SN,[],Ind_couples), % TODO MAYBE check_individuals_not_equal(M,YI,YJ,ABox), instead of dif
  length(Ind_couples,NChoices),
  (
    NChoices @> 1 -> (FirstChoice = -1) ; (FirstChoice = 0)
  ),
  create_list_for_max_rule(M,Ind_couples,FirstChoice,CP,Ind,S,C,Expl,Tab0,Tab_list),
  dif(Tab_list,[]),
  create_choice_point(M,Ind,mr,MaxCardClass,Ind_couples,_). % last variable whould be equals to ID

% Creates the couple of individuals to merge for max_rule
create_couples_for_merge([],Ind_couples,Ind_couples).

create_couples_for_merge([H|T],Ind_couples0,Ind_couples):-
  create_couples_for_merge_int(H,T,Ind_couples0,Ind_couples1),
  create_couples_for_merge(T,Ind_couples1,Ind_couples).

create_couples_for_merge_int(_,[],Ind_couples,Ind_couples).

create_couples_for_merge_int(I,[H|T],Ind_couples0,Ind_couples):-
  create_couples_for_merge_int(I,T,[I-H|Ind_couples0],Ind_couples).

% Creates the new tableau by mergin individuals from couples list.
create_list_for_max_rule(_,[],_,_,_,_,_,_,_,[]).

create_list_for_max_rule(M,[YI-YJ|Ind_couples],N0,CP,Ind,S,C,Expl0,Tab0,[Tab|Tab_list]):-
  get_abox(Tab0,ABox),
  findPropertyAssertion(S,Ind,YI,ExplYI,ABox),
  findPropertyAssertion(S,Ind,YJ,ExplYJ,ABox),
  findClassAssertion(C,YI,ExplCYI,ABox),
  findClassAssertion(C,YJ,ExplCYJ,ABox),
  and_f(M,ExplYI,ExplYJ,ExplS0),
  and_f(M,ExplS0,ExplCYI,ExplS1),
  and_f(M,ExplS1,ExplCYJ,ExplC0),
  and_f(M,ExplC0,Expl0,ExplT0),
  (
    dif(N0,-1) ->
    (
      add_choice_point(M,cpp(CP,N0),ExplT0,ExplT),
      N is N0 + 1
    ) ;
    (
      ExplT = ExplT0,
      N = N0
    )
  ),
  flatten([YI,YJ],LI),
  merge_all_individuals(M,[(sameIndividual(LI),ExplT)],Tab0,Tab),
  create_list_for_max_rule(M,Ind_couples,N,CP,Ind,S,C,Expl0,Tab0,Tab_list).

/*
scan_max_list(M,S,SN,CP,Ind,Expl,ABox0,Tabs0,YI-YJ,ABox,Tabs):-
  member(YI,SN),
  member(YJ,SN),
  % generate cp
  check_individuals_not_equal(M,YI,YJ,ABox0),
  findPropertyAssertion(S,Ind,YI,ExplYI,ABox0),
  findPropertyAssertion(S,Ind,YJ,ExplYJ,ABox0),
  and_f(M,ExplYI,ExplYJ,Expl0),
  and_f(M,Expl0,Expl,ExplT0),
  add_choice_point(M,cpp(CP,N0),ExplT0,ExplT),
  merge_all_individuals(M,[(sameIndividual([YI,YJ]),ExplT)],ABox0,Tabs0,ABox,Tabs).
*/


/* *************** */

/*
  ch_rule
  ================
*/
% maxCardinality(N,S,C)
ch_rule(M,Tab0,[maxCardinality(N,S,C),Ind1],L):-
  get_abox(Tab0,ABox),
  findPropertyAssertion(S,Ind1,Ind2,Expl2,ABox),
  \+ indirectly_blocked(Ind1,Tab0),
  findClassAssertion(maxCardinality(N,S,C),Ind1,Expl1,ABox),
  absent_c_not_c(Ind2,C,ABox),
  and_f(M,Expl1,Expl2,Expl),
  get_choice_point_id(M,ID),%gtrace,
  neg_class(C,NC),
  scan_or_list(M,[C,NC],0,ID,Ind2,Expl,Tab0,L),
  dif(L,[]),
  create_choice_point(M,Ind2,ch,maxCardinality(N,S,C),[C,NC],_),!. % last variable whould be equals to ID

% exactCardinality(N,S,C)
ch_rule(M,Tab0,[exactCardinality(N,S,C),Ind1],L):-
  get_abox(Tab0,ABox),
  findPropertyAssertion(S,Ind1,Ind2,Expl2,ABox),
  \+ indirectly_blocked(Ind1,Tab0),
  findClassAssertion(exactCardinality(N,S,C),Ind1,Expl1,ABox),
  absent_c_not_c(Ind2,C,ABox),
  and_f(M,Expl1,Expl2,Expl),
  get_choice_point_id(M,ID),%gtrace,
  neg_class(C,NC),
  scan_or_list(M,[C,NC],0,ID,Ind2,Expl,Tab0,L),
  dif(L,[]),
  create_choice_point(M,Ind2,ch,exactCardinality(N,S,C),[C,NC],_),!. % last variable whould be equals to ID

% propertyAssertion(S,Ind1,Ind2) with maxCardinality(N,S,C)
ch_rule(M,Tab0,[S,Ind1,Ind2],L):-
  get_abox(Tab0,ABox),
  findClassAssertion(maxCardinality(N,S,C),Ind1,Expl1,ABox),
  \+ indirectly_blocked(Ind1,Tab0),
  findPropertyAssertion(S,Ind1,Ind2,Expl2,ABox),
  absent_c_not_c(Ind2,C,ABox),
  and_f(M,Expl1,Expl2,Expl),
  get_choice_point_id(M,ID),%gtrace,
  neg_class(C,NC),
  scan_or_list(M,[C,NC],0,ID,Ind2,Expl,Tab0,L),
  dif(L,[]),
  create_choice_point(M,Ind2,ch,maxCardinality(N,S,C),[C,NC],_),!. % last variable whould be equals to ID

% propertyAssertion(S,Ind1,Ind2) with exactCardinality(N,S,C)
ch_rule(M,Tab0,[S,Ind1,Ind2],L):-
  get_abox(Tab0,ABox),
  findClassAssertion(exactCardinality(N,S,C),Ind1,Expl1,ABox),
  \+ indirectly_blocked(Ind1,Tab0),
  findPropertyAssertion(S,Ind1,Ind2,Expl2,ABox),
  absent_c_not_c(Ind2,C,ABox),
  and_f(M,Expl1,Expl2,Expl),
  get_choice_point_id(M,ID),%gtrace,
  neg_class(C,NC),
  scan_or_list(M,[C,NC],0,ID,Ind2,Expl,Tab0,L),
  dif(L,[]),
  create_choice_point(M,Ind2,ch,exactCardinality(N,S,C),[C,NC],_),!. % last variable whould be equals to ID

%---------------------

% checks whether the individual Ind belongs to C or complementOf(C)
absent_c_not_c(Ind,C,ABox) :-
  \+ is_there_c_not_c(Ind,C,ABox).

is_there_c_not_c(Ind,C,ABox) :-
 findClassAssertion(C,Ind,_,ABox),!.

is_there_c_not_c(Ind,C,ABox) :-
  neg_class(C,NC),
  findClassAssertion(NC,Ind,_,ABox),!.

/* *************** */

/*
 o_rule
 ============
*/

o_rule(M,Tab0,[oneOf(C),X],Tab):-
  get_abox(Tab0,ABox),
  findClassAssertion(oneOf(C),X,ExplX,ABox),
  findClassAssertion(oneOf(D),Y,ExplY,ABox),
  containsCommon(C,D),
  dif(X,Y),
  notDifferentIndividuals(M,X,Y,ABox),
  nominal(C,Tab),
  ind_as_list(M,X,LX),
  ind_as_list(M,Y,LY),
  and_f(M,ExplX,ExplY,ExplC),
  merge(M,X,Y,ExplC,Tab0,Tab),
  flatten([LX,LY],LI0),
  sort(LI0,LI),
  absent(sameIndividual(LI),ExplC,ABox).

containsCommon(L1,L2):-
  member(X,L1),
  member(X,L2),!.
% -------------------

% ===================================
% TABLEAU INIT AND MANAGEMENT
%
% Contains ABOX, TABS, CLASHES
% and EXPANSION QUEUE
% 
% The Tableau is a dict containing:
% - abox: the ABox, a list containing the labels with justifications and BDDs
% - tabs: the tableau structure
% - clashes: list of clashes contined in the tableau
% - expq: the expansion queue for the expansion of the tableau
% ===================================

/**
 * init_tableau(-EmptyTableaus:dict)
 * 
 * Initialize an empty tableau.
 */
%TODO previously new_tableau/1
init_tableau(tableau{abox:ABox, tabs:Tabs, clashes:[], expq:ExpansionQueue}):-
  new_abox(ABox),
  new_tabs(Tabs),
  empty_expansion_queue(ExpansionQueue).

/**
 * init_tabelau(+ABox:abox, +Tabs:tableau, -InitializedTableaus:dict)
 * 
 * Initialize a tableau with the elements given in input.
 */
init_tableau(ABox,Tabs,tableau{abox:ABox, tabs:Tabs, clashes:[], expq:ExpansionQueue}):-
  empty_expansion_queue(ExpansionQueue).

/**
 * init_tabelau(+ABox:abox, +Tabs:tableau, +ExpansionQueue:expansion_queue, -InitializedTableaus:dict)
 * 
 * Initialize a tableau with the lements given in input.
 */
init_tableau(ABox,Tabs,ExpansionQueue,tableau{abox:ABox, tabs:Tabs, clashes:[], expq:ExpansionQueue}).


/* getters and setters for Tableau */
get_abox(Tab,ABox):-
  ABox = Tab.abox.

set_abox(Tab0,ABox,Tab):-
  Tab = Tab0.put(abox,ABox).

get_tabs(Tab,Tabs):-
  Tabs = Tab.tabs.

set_tabs(Tab0,Tabs,Tab):-
  Tab = Tab0.put(tabs,Tabs).

get_clashes(Tab,Clashes):-
  Clashes = Tab.clashes.

set_clashes(Tab0,Clashes,Tab):-
  Tab = Tab0.put(clashes,Clashes).

get_expansion_queue(Tab,ExpansionQueue):-
  ExpansionQueue = Tab.expq.

set_expansion_queue(Tab0,ExpansionQueue,Tab):-
  Tab = Tab0.put(expq,ExpansionQueue).

get_individuals_in_tableau(Tab0,Inds):-
  get_tabs(Tab0,(T,_,_)),
  vertices(T,Inds).

/*  succeeds if tha tableau does not have any clash */
absence_of_clashes(Tab):-
  get_clashes(Tab,Clashes),
  Clashes=[]. %TODO change to get_clashes(Tab,[]).

/**
 * add_to_tableau(+Tableau0:tableau,+El:tableau_label,--Tableau:tableau)
 * 
 * Adds the label El to ABox, updating the tableau.
 * NOTE: El is a new label, surely not present in the tableau.
 */
add_to_tableau(Tableau0,El,Tableau):-
  get_abox(Tableau0,ABox0),
  add_to_abox(ABox0,El,ABox),
  set_abox(Tableau0,ABox,Tableau).

/**
 * remove_from_tableau(+Tableau0:tableau,+El:tableau_label,--Tableau:tableau)
 * 
 * Removes the label El to ABox, updating the tableau.
 */
remove_from_tableau(Tableau0,El,Tableau):-
  get_abox(Tableau0,ABox0),
  remove_from_abox(ABox0,El,ABox),
  set_abox(Tableau0,ABox,Tableau).

/**
 * add_clash_to_tableau(+M:module,+Tableau0:tableau,+Clash:clash,--Tableau:tableau)
 * 
 * If the candidate clash Clash is actually a clash w.r.t. the tableau Tableao0,
 * it adds Clash to Tableau0, updating it and creating Tableau.
 * It returns the input tableau Tablea0 otherwise.
 *
 * NOTE: there is not a remove_clash_to_tableau predicate, as the logic is monotone, so clashes can only be added.
 */
% TODO remove module
add_clash_to_tableau(M,Tableau0,Clash,Tableau):-
  check_clash(M,Clash,Tableau0),!,
  get_clashes(Tableau0,Clashes0),
  add_to_clashes(Clashes0,Clash,Clashes),
  set_clashes(Tableau0,Clashes,Tableau).

add_clash_to_tableau(_,Tableau,_,Tableau).


/**
 * add_all_to_tableau(+M:module,+L:list,+Tableau0:tableau,--Tableau:tableau)
 * 
 * Adds in Tableau0 all items contained in L and returns Tableau.
 * It updates both ABox, Clashes, and Tabs
*/
add_all_to_tableau(M,L,Tableau0,Tableau):-
  get_abox(Tableau0,ABox0),
  get_clashes(Tableau0,Clashes0),
  add_all_to_abox_and_clashes(M,L,Tableau0,ABox0,ABox,Clashes0,Clashes),
  set_abox(Tableau0,ABox,Tableau1),
  set_clashes(Tableau1,Clashes,Tableau).

/**
 * add_all_to_abox(+L:list,+ABox0:abox,--ABox:abox)
 * 
 * Adds to ABox0 the assertions given in L.
 * NOTE: does not update the tableau. Use add_to_tableau to update the tableau.
 */ 
add_all_to_abox([],A,A).

add_all_to_abox([H|T],A0,A):-
  add_to_abox(A0,H,A1),
  add_all_to_abox(T,A1,A).

/**
 * add_all_to_abox_and_clashes(+M:module,+L:list,+Tableau:tableau,+ABox0:abox,--ABox:abox,+Clashes0:list,--Clashes:list)
 * 
 * Adds to ABox0 the assertions given in L and updates Clashes0 accordingly.
 * NOTE: does not update the tableau. Use add_to_tableau to update the tableau.
 */ 
add_all_to_abox_and_clashes(_,[],_,A,A,C,C).

add_all_to_abox_and_clashes(M,[(classAssertion(C,I),Expl)|T],Tab,A0,A,C0,C):-
  check_clash(M,C-I,Tab),!,
  add_to_abox(A0,(classAssertion(C,I),Expl),A1),
  add_to_clashes(C0,C-I,C1),
  add_all_to_abox_and_clashes(M,T,Tab,A1,A,C1,C).

add_all_to_abox_and_clashes(M,[(sameIndividual(LI),Expl)|T],Tab,A0,A,C0,C):-
  check_clash(M,sameIndividual(LI),Tab),!,
  add_to_abox(A0,(sameIndividual(LI),Expl),A1),
  add_to_clashes(C0,sameIndividual(LI),C1),
  add_all_to_abox_and_clashes(M,T,Tab,A1,A,C1,C).

add_all_to_abox_and_clashes(M,[(differentIndividuals(LI),Expl)|T],Tab,A0,A,C0,C):-
  check_clash(M,differentIndividuals(LI),Tab),!,
  add_to_abox(A0,(differentIndividuals(LI),Expl),A1),
  add_to_clashes(C0,differentIndividuals(LI),C1),
  add_all_to_abox_and_clashes(M,T,Tab,A1,A,C1,C).

add_all_to_abox_and_clashes(M,[H|T],Tab,A0,A,C0,C):-
  add_to_abox(A0,H,A1),
  add_all_to_abox_and_clashes(M,T,Tab,A1,A,C0,C).

/**
 * update_expansion_queue_in_tableau(+M:module,+C:concept,+Ind:individual,+Tab0:tableau,--Tab:tableau)
 * 
 * Updates expansion queue in tableau Tab0 with the given class C and individual Ind, and return the updated version in Tab.
 */
update_expansion_queue_in_tableau(M,C,Ind,Tab0,Tab):-
  get_expansion_queue(Tab0,ExpansionQueue0),
  update_expansion_queue(M,C,Ind,ExpansionQueue0,ExpansionQueue),
  set_expansion_queue(Tab0,ExpansionQueue,Tab).

/**
 * update_expansion_queue_in_tableau(+M:module,+P:property,+Ind1:individual,+Ind2:individual,+Tab0:tableau,--Tab:tableau)
 * 
 * Updates expansion queue in tableau Tab0 with the given property P and individuals Ind1 and Ind2, and return the updated version in Tab
 */
update_expansion_queue_in_tableau(M,P,Ind1,Ind2,Tab0,Tab):-
  get_expansion_queue(Tab0,ExpansionQueue0),
  update_expansion_queue(M,P,Ind1,Ind2,ExpansionQueue0,ExpansionQueue),
  set_expansion_queue(Tab0,ExpansionQueue,Tab).

/**
 * extract_from_expansion_queue(+Tab0:tableau,--EA:term,--Tab:tableau)
 * 
 * Returns the next assertion EA to be expanded by the tableau expansion rules and 
 * the updated tableau Tab (the input one with the expansion queue resulting from popping EA).
 */
extract_from_expansion_queue(Tab0,EA,Tab):-
  get_expansion_queue(Tab0,EQ0),
  extract_ea_from_expansion_queue(EQ0,EA,EQ),
  set_expansion_queue(Tab0,EQ,Tab).

/**
 * expansion_queue_is_empty(+Tab:tableau)
 * 
 * Succeeds if the expansion queue in the tableau Tab is empty. Fails otherwise.
 */
expansion_queue_is_empty(Tab):-
  get_expansion_queue(Tab,EQ),
  empty_expansion_queue(EQ).


/**
 * same_tableau(+Tab1:tableau,+Tab2:tableau)
 * 
 * Succeeds if the two input tableaus Tab1 and Tab2 contain same ABox and Tabs. Fails otherwise.
 */
same_tableau(Tab1,Tab2):-
  get_abox(Tab1,ABox),
  get_abox(Tab2,ABox),
  get_tabs(Tab1,Tabs),
  get_tabs(Tab2,Tabs).

/**
 * s_neighbours(+M:module,+Ind:string,+S:string,+Tab:tableau,--SN:list)
 * 
 * Finds all S neighbours (S is a role) of the individual Ind adding them into list SN
 */
s_neighbours(M,Ind,S,Tab,SN):- %gtrace,
  get_tabs(Tab,(_,_,RBR)),
  rb_lookup(S,VN,RBR),!,
  s_neighbours1(Ind,VN,SN0),
  flatten(SN0,SN1), %TODO is it necessary?
  get_abox(Tab,ABox),
  s_neighbours2(M,SN1,SN,ABox),!. %TODO previosuly s_neighbours2(M,SN1,SN1,SN,ABox) %TODO check max_rule_example

s_neighbours(_,_Ind,_S,_Tab,[]).
%  get_tabs(Tab,(_,_,RBR)),
%  \+ rb_lookup(S,_VN,RBR).

% For each pair (Ind1,Ind2) in the list of edges adds Ind2 to the output list IF Ind1 is the individual we are looking for.
s_neighbours1(_,[],[]).

s_neighbours1(Ind1,[(Ind1,Y)|T],[Y|T1]):-!, %TODO added the cut to avoid use of dif in next pred., may be uncorrect. CHECK!
  s_neighbours1(Ind1,T,T1).

s_neighbours1(Ind1,[(_X,_Y)|T],T1):-
  % dif(X,Ind1), %TODO should be here only if dif(C,Ind1) is true
  s_neighbours1(Ind1,T,T1).

% Checks if the collected individuals can be merged using sameIndividual.
% TODO to correct!
s_neighbours2(_,[],[],_).

s_neighbours2(M,[H|T],[H|T1],ABox):-
  s_neighbours2(M,T,T1,ABox),
  not_same_ind(M,T1,H,ABox),!.

s_neighbours2(M,[_H|T],T1,ABox):-
  s_neighbours2(M,T,T1,ABox).
  %same_ind(M,T1,H,ABox).


/**
 * s_predecessors(+M:module,+Ind:string,+S:string,+Tab:tableau,--SN:list)
 * 
 * Finds all S predecessors (S is a role) of the individual Ind adding them into list SN
 */
s_predecessors(M,Ind1,S,Tab,SN):-
  get_tabs(Tab,(_,_,RBR)),
  rb_lookup(S,VN,RBR),
  s_predecessors1(Ind1,VN,SN1),
  get_abox(Tab,ABox),
  s_predecessors2(M,SN1,SN,ABox).

s_predecessors(_M,_Ind1,S,(_ABox,(_,_,RBR)),[]):-
  \+ rb_lookup(S,_VN,RBR).

s_predecessors1(_,[],[]).

s_predecessors1(Ind1,[(Y,Ind1)|T],[Y|T1]):-
  s_predecessors1(Ind1,T,T1).

s_predecessors1(Ind1,[(_X,Y)|T],T1):-
  dif(Y,Ind1),
  s_predecessors1(Ind1,T,T1).

s_predecessors2(_M,[],[],_).

s_predecessors2(M,[H|T],[H|T1],ABox):-
  s_predecessors2(M,T,T1,ABox),
  \+ same_ind(M,T1,H,ABox).

s_predecessors2(M,[H|T],T1,ABox):-
  s_predecessors2(M,T,T1,ABox),
  same_ind(M,T1,H,ABox).

/**
 * merge_all_individuals(+M:module,+LSI:list,+Tab0:tableau,--Tab:tableau)
 * 
 * Takes a list of sameIndividual axioms and merges nodes in (ABox,Tabs) accordingly.
 */
merge_all_individuals(_,[],Tab,Tab).

merge_all_individuals(M,[(sameIndividual(H),Expl)|T],Tab0,Tab):-
  get_abox(Tab0,ABox0),
  find_same(H,ABox0,L,ExplL),
  dif(L,[]),!,
  merge_all1(M,H,Expl,L,Tab0,Tab1),
  list_as_sameIndividual([H,L],SI), %TODO fix sameIndividual management
  %flatten([H,L],L0),
  %sort(L0,SI),
  and_f(M,Expl,ExplL,ExplT),
  add_to_tableau(Tab1,(SI,ExplT),Tab2),
  remove_from_tableau(Tab2,(sameIndividual(L),ExplL),Tab3),
  retract_sameIndividual(M,L),
  merge_all_individuals(M,T,Tab3,Tab).

merge_all_individuals(M,[(sameIndividual(H),Expl)|T],Tab0,Tab):-
  %get_abox(Tab0,ABox0),
  %find_same(H,ABox0,L,_),
  %L==[],!,
  merge_all2(M,H,Expl,Tab0,Tab1),
  add_to_tableau(Tab1,(sameIndividual(H),Expl),Tab2),
  merge_all_individuals(M,T,Tab2,Tab).

merge_all1(_M,[],_,_,Tab,Tab).

merge_all1(M,[H|T],Expl,L,Tab0,Tab):-
  \+ member(H,L),
  merge(M,H,L,Expl,Tab0,Tab1),
  merge_all1(M,T,Expl,[H|L],Tab1,Tab).

merge_all1(M,[H|T],Expl,L,Tab0,Tab):-
  member(H,L),
  merge_all1(M,T,Expl,L,Tab0,Tab).

merge_all2(M,[X,Y|T],Expl,Tab0,Tab):-
  merge(M,X,Y,Expl,Tab0,Tab1),
  merge_all1(M,T,Expl,[X,Y],Tab1,Tab).


/*
 * merge
 * 
 * Implement the Merge operation of the tableau. Merge two individuals
 */
% The first three are needed because T in tabs:(T,RBN,RBR) saves sameIndividuals
% as a list instead of a single individual sameIndividual(L).
% The addition of sameIndividual is made after, during the update of the ABox.
% TODO: it could be improved!
/*
merge(M,sameIndividual(LX),sameIndividual(LY),Expl,Tableau0,Tableau):-
  !,
  get_tabs(Tableau0,Tabs0),
  merge_tabs(L,Y,Tabs0,Tabs),
  get_abox(Tableau0,ABox0),
  merge_abox(M,L,Y,Expl,ABox0,ABox),
  set_tabs(Tableau0,Tabs,Tableau1),
  set_abox(Tableau1,ABox,Tableau).

merge(M,sameIndividual(L),Y,Expl,Tableau0,Tableau):-
  !,
  get_tabs(Tableau0,Tabs0),
  merge_tabs(L,Y,Tabs0,Tabs),
  get_abox(Tableau0,ABox0),
  merge_abox(M,L,Y,Expl,ABox0,ABox),
  set_tabs(Tableau0,Tabs,Tableau1),
  set_abox(Tableau1,ABox,Tableau).
*/

merge(M,X,Y,Expl,Tableau0,Tableau):-
  !,
  get_tabs(Tableau0,Tabs0),
  % merge of tabs
  merge_tabs(X,Y,Tabs0,Tabs),
  get_abox(Tableau0,ABox0),
  flatten([X,Y],L0),
  sort(L0,L),
  list_as_sameIndividual(L,SI),
  get_clashes(Tableau0,Clashes0),
  % merge of abox
  merge_abox(M,L,SI,Expl,ABox0,ABox,ClashesToCheck),
  set_abox(Tableau0,ABox,Tableau1),
  % check for new clashes due to merge
  % TODO previously check_merged_classes/4
  check_clashes_to_add(M,ClashesToCheck,Tableau1,NewClashes),
  update_clashes_after_merge(M,L,SI,Tableau1,Clashes0,ClashesAM),
  append(NewClashes,ClashesAM,Clashes),
  set_tabs(Tableau1,Tabs,Tableau2),
  set_clashes(Tableau2,Clashes,Tableau3),
  get_expansion_queue(Tableau3,ExpQ0),
  update_expansion_queue_after_merge(L,SI,ExpQ0,ExpQ),
  set_expansion_queue(Tableau3,ExpQ,Tableau).


/**
 * add_owlThing_ind(+M:module,+Tab0:tableau,+Ind:individual,--Tab:tableau)
 * 
 * Adds to tableau Tab0, in the ABox, the label owl:Thing to the invidual Ind. It returns the updated tableau in Tab.
 */
add_owlThing_ind(M,Tab0,Ind,Tab):-
  prepare_nom_list(M,[Ind],NomListOut),
  add_all_to_tableau(M,NomListOut,Tab0,Tab).

/**
 * add_owlThing_ind_list(+M:module,+Tab0:tableau,+Inds:list,--Tab:tableau)
 * 
 * Adds to tableau Tab0, in the ABox, the label owl:Thing to the all inviduals in Inds. It returns the updated tableau in Tab.
 */
add_owlThing_ind_list(M,Tab0,Inds,Tab):- % TODO
  prepare_nom_list(M,Inds,LabelsListOut),
  add_all_to_tableau(M,LabelsListOut,Tab0,Tab).

prepare_nom_list(_,[],[]).

prepare_nom_list(M,[literal(_)|T],T1):-!,
  prepare_nom_list(M,T,T1).

prepare_nom_list(M,[H|T],[(classAssertion('http://www.w3.org/2002/07/owl#Thing',H),Expl)|T1]):-
  initial_expl(M,Expl),
  prepare_nom_list(M,T,T1).


/***********
  update abox
  utility for tableau
************/
% TODO previously modify_ABox/5
update_abox(_,Tab,sameIndividual(LF),_Expl1,Tab):-
  length(LF,1),!.

update_abox(M,Tab0,sameIndividual(LF),Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find_in_abox((sameIndividual(L),Expl0),ABox0) -> 
  	( sort(L,LS),
  	  sort(LF,LFS),
  	  LS = LFS,!,
      %------
      dif(Expl0,Expl1),
      absent(Expl0,Expl1,Expl),
      %------
      remove_from_abox(ABox0,[(sameIndividual(L),Expl0)],ABox),
      Tab1=Tab0
  	)
  ;
  	(ABox = ABox0,Expl = Expl1,L = LF,
     add_clash_to_tableau(M,Tab0,sameIndividual(LF),Tab1))
  ),
  set_abox(Tab1,[(sameIndividual(L),Expl)|ABox],Tab).

update_abox(_,Tab,differentIndividuals(LF),_Expl1,Tab):-
  length(LF,1),!.

update_abox(M,Tab0,differentIndividuals(LF),Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find_in_abox((differentIndividuals(L),Expl0),ABox0) ->
  	( sort(L,LS),
  	  sort(LF,LFS),
  	  LS = LFS,!,
      %------
      dif(Expl0,Expl1),
      absent(Expl0,Expl1,Expl),
      %------
      remove_from_abox(ABox0,[(differentIndividuals(L),Expl0)],ABox),
      Tab1=Tab0
  	)
  ;
  	(ABox = ABox0,Expl = Expl1,L = LF,
    add_clash_to_tableau(M,Tab0,differentIndividuals(LF),Tab1))
  ),
  set_abox(Tab1,[(differentIndividuals(L),Expl)|ABox],Tab).

update_abox(M,Tab0,C,Ind,Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find_in_abox((classAssertion(C,Ind),Expl0),ABox0) ->
    ( %------
      dif(Expl0,Expl1),
      absent(Expl0,Expl1,Expl),
      %------
      remove_from_abox(ABox0,(classAssertion(C,Ind),Expl0),ABox),
      Tab1=Tab0
    )
  ;
    (ABox = ABox0,Expl = Expl1,
    add_clash_to_tableau(M,Tab0,C-Ind,Tab1))
  ),
  set_abox(Tab1,[(classAssertion(C,Ind),Expl)|ABox],Tab2),
  update_expansion_queue_in_tableau(M,C,Ind,Tab2,Tab).

update_abox(M,Tab0,P,Ind1,Ind2,Expl1,Tab):-
  get_abox(Tab0,ABox0),
  ( find_in_abox((propertyAssertion(P,Ind1,Ind2),Expl0),ABox0) ->
    ( %------
      dif(Expl0,Expl1),
      absent(Expl0,Expl1,Expl),
      %------
      remove_from_abox(ABox0,(propertyAssertion(P,Ind1,Ind2),Expl0),ABox),
      Tab1=Tab0
    )
  ;
    (ABox = ABox0,Expl = Expl1,
    add_clash_to_tableau(M,Tab0,P-Ind1-Ind2,Tab1))
  ),
  set_abox(Tab1,[(propertyAssertion(P,Ind1,Ind2),Expl)|ABox],Tab2),
  update_expansion_queue_in_tableau(M,P,Ind1,Ind2,Tab2,Tab).


% -----------------------------------
% QUERY MANAGEMENT
% -----------------------------------

% expands query arguments using prefixes and checks their existence in the kb
% returns the non-present arguments
check_query_args(M,QA,QAEx,NotEx):-
  check_query_args_int(M,QA,QAExT,NotEx),!,
  ( length(QA,1) -> 
    QAEx = ['unsat'|QAExT]
    ;
    ( length(QA,0) -> QAEx = ['inconsistent','kb'] ; QAEx = QAExT)
  ).

check_query_args_int(_,[],[],[]).

check_query_args_int(M,[H|T],[HEx|TEx],NotEx):-
  check_query_args(M,[H],[HEx]),!,
  check_query_args_int(M,T,TEx,NotEx).

check_query_args_int(M,[H|T],TEx,[H|NotEx]):-
  check_query_args_int(M,T,TEx,NotEx).

% expands query arguments using prefixes and checks their existence in the kb
check_query_args(M,L,LEx) :-
  M:ns4query(NSList),
  expand_all_ns(M,L,NSList,false,LEx), %from utility_translation module
  check_query_args_presence(M,LEx).

check_query_args_presence(_M,[]):-!.

check_query_args_presence(M,['http://www.w3.org/2002/07/owl#Thing'|T]) :-
  check_query_args_presence(M,T).

check_query_args_presence(M,[H|T]) :-
  nonvar(H),
  atomic(H),!,
  find_atom_in_axioms(M,H),%!,
  check_query_args_presence(M,T).

check_query_args_presence(M,[H|T]) :-
  nonvar(H),
  \+ atomic(H),!,
  H =.. [_|L],
  flatten(L,L1),
  check_query_args_presence(M,L1),
  check_query_args_presence(M,T).


% looks for presence of atoms in kb's axioms
% TODO maybe move in utility_translate
find_atom_in_axioms(M,H):-
  M:kb_atom(L1),
  ( member(H,L1.class) ; member(H,L1.objectProperty) ; member(H,L1.individual) ; member(H,L1.dataProperty) ; member(H,L1.annotationProperty) ; member(H,L1.datatype) ),!.

% -------------------

% instanceOf
add_q(M,io,Tableau0,[ClassEx,IndEx],Tableau):- !,
  neg_class(ClassEx,NClassEx),
  add_q(M,Tableau0,classAssertion(NClassEx,IndEx),Tableau1),
  add_clash_to_tableau(M,Tableau1,NClassEx-IndEx,Tableau2),
  update_expansion_queue_in_tableau(M,NClassEx,IndEx,Tableau2,Tableau),!.

% property_value
add_q(M,pv,Tableau0,[PropEx,Ind1Ex,Ind2Ex],Tableau):-!,
  neg_class(PropEx,NPropEx), %use of neg_class to negate property
  add_q(M,Tableau0,propertyAssertion(NPropEx,Ind1Ex,Ind2Ex),Tableau1),
  add_clash_to_tableau(M,Tableau1,NPropEx-Ind1Ex-Ind2Ex,Tableau2),
  update_expansion_queue_in_tableau(M,PropEx,Ind1Ex,Ind2Ex,Tableau2,Tableau),!.


% sub_class
add_q(M,sc,Tableau0,[SubClassEx,SupClassEx],Tableau):- !,
  neg_class(SupClassEx,NSupClassEx),
  query_ind(QInd),
  add_q(M,Tableau0,classAssertion(intersectionOf([SubClassEx,NSupClassEx]),QInd),Tableau1),
  utility_translation:add_kb_atoms(M,class,[intersectionOf([SubClassEx,NSupClassEx])]), % This is necessary to correctly prune expansion rules
  add_owlThing_ind(M,Tableau1,QInd,Tableau2),
  add_clash_to_tableau(M,Tableau2,intersectionOf([SubClassEx,NSupClassEx])-QInd,Tableau3),
  update_expansion_queue_in_tableau(M,intersectionOf([SubClassEx,NSupClassEx]),QInd,Tableau3,Tableau),!.

% unsat
add_q(M,un,Tableau0,['unsat',ClassEx],Tableau):- !,
  query_ind(QInd),
  add_q(M,Tableau0,classAssertion(ClassEx,QInd),Tableau1),
  add_owlThing_ind(M,Tableau1,QInd,Tableau2),
  add_clash_to_tableau(M,Tableau2,ClassEx-QInd,Tableau3),
  update_expansion_queue_in_tableau(M,ClassEx,QInd,Tableau3,Tableau),!.

% inconsistent_theory
add_q(_,it,Tableau,['inconsistent','kb'],Tableau):- !. % Do nothing

/**************
  QUERY FUNCTIONS
***************/
% adds the query into the ABox
add_q(M,Tableau0,Query,Tableau):-
  query_empty_expl(M,Expl),
  add_to_tableau(Tableau0,(Query,Expl),Tableau1),
  update_tabs([(Query,Expl)],Tableau1,Tableau). % TODO previously create_tabs

% initialize an empty explanation for the query with the query placeholder 'qp' in the choicepoint list
query_empty_expl(M,Expl):-%gtrace,
  empty_expl(M,EExpl),
  add_choice_point(M,qp,EExpl,Expl).

% -----------------------------------
% ABOX
% -----------------------------------

/*
  ABOX INIT AND MANAGEMENT
  ===============
  abox as a list
*/

% Creation of empty ABox
new_abox([]).

/**
 * build_abox(+M:module,--Tableau:tableau,+QueryType:string,+QueryArgs:list)
 * 
 * Creates the tableau with all the labels coming from the ABox. Initializes the tracing function for each label.
 */
% TODO merge tornado
build_abox(M,Tableau,QueryType,QueryArgs):-
  retractall(M:final_abox(_)),
  retractall(v(_,_,_)),
  retractall(na(_,_)),
  retractall(rule_n(_)),
  assert(rule_n(0)),
  collect_individuals(M,QueryType,QueryArgs,ConnectedInds), 
  ( dif(ConnectedInds,[]) ->
    ( findall((classAssertion(Class,Individual),[e{expl:[classAssertion(Class,Individual)],bdd:BDDCA,cp:[]}]),(member(Individual,ConnectedInds),M:classAssertion(Class,Individual),bdd_and(M,Env,[classAssertion(Class,Individual)],BDDCA)),LCA),
      findall((propertyAssertion(Property,Subject, Object),[e{expl:[propertyAssertion(Property,Subject, Object)],bdd:BDDPA,cp:[]}]),(member(Subject,ConnectedInds),M:propertyAssertion(Property,Subject, Object),dif('http://www.w3.org/2000/01/rdf-schema#comment',Property),bdd_and(M,Env,[propertyAssertion(Property,Subject, Object)],BDDPA)),LPA),
      % findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property),propertyAssertion(SubProperty,Subject,Object)]),subProp(M,SubProperty,Property,Subject,Object),LSPA),
      findall(nominal(NominalIndividual),(member(NominalIndividual,ConnectedInds),M:classAssertion(oneOf(_),NominalIndividual)),LNA),
      findall((differentIndividuals(Ld),[e{expl:[differentIndividuals(Ld)],bdd:BDDDIA,cp:[]}]),(M:differentIndividuals(Ld),intersect(Ld,ConnectedInds),bdd_and(M,Env,[differentIndividuals(Ld)],BDDDIA)),LDIA),
      findall((sameIndividual(L),[e{expl:[sameIndividual(L)],bdd:BDDSIA,cp:[]}]),(M:sameIndividual(L),intersect(L,ConnectedInds),bdd_and(M,Env,[sameIndividual(L)],BDDSIA)),LSIA)
    )
    ; % all the individuals
    ( findall((classAssertion(Class,Individual),[e{expl:[classAssertion(Class,Individual)],bdd:BDDCA,cp:[]}]),(M:classAssertion(Class,Individual),bdd_and(M,Env,[classAssertion(Class,Individual)],BDDCA)),LCA),
      findall((propertyAssertion(Property,Subject, Object),[e{expl:[propertyAssertion(Property,Subject, Object)],bdd:BDDPA,cp:[]}]),(M:propertyAssertion(Property,Subject, Object),dif('http://www.w3.org/2000/01/rdf-schema#comment',Property),bdd_and(M,Env,[propertyAssertion(Property,Subject, Object)],BDDPA)),LPA),
      % findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property),propertyAssertion(SubProperty,Subject,Object)]),subProp(M,SubProperty,Property,Subject,Object),LSPA),
      findall(nominal(NominalIndividual),M:classAssertion(oneOf(_),NominalIndividual),LNA),
      findall((differentIndividuals(Ld),[e{expl:[differentIndividuals(Ld)],bdd:BDDDIA,cp:[]}]),(M:differentIndividuals(Ld),bdd_and(M,Env,[differentIndividuals(Ld)],BDDDIA)),LDIA),
      findall((sameIndividual(L),[e{expl:[sameIndividual(L)],bdd:BDDSIA,cp:[]}]),(M:sameIndividual(L),bdd_and(M,Env,[sameIndividual(L)],BDDSIA)),LSIA)
    )
  ),
  new_abox(ABox0),
  new_tabs(Tabs0),
  init_expansion_queue(LCA,LPA,ExpansionQueue),
  init_tableau(ABox0,Tabs0,ExpansionQueue,Tableau0),
  append([LCA,LDIA,LPA],CreateTabsList),
  update_tabs(CreateTabsList,Tableau0,Tableau1), % TODO previously create_tabs
  append([LCA,LPA,LNA,LDIA],AddAllList),
  add_all_to_tableau(M,AddAllList,Tableau1,Tableau2),
  merge_all_individuals(M,LSIA,Tableau2,Tableau3),
  get_individuals_in_tableau(Tableau3,Inds),
  add_owlThing_ind_list(M,Tableau3,Inds,Tableau),
  !.

/*
  find & absent in abox (not find)
*/
% TODO previously find/2
find_in_abox(El,ABox):-
  member(El,ABox).

% TODO previously control/2
absent_in_abox(El,ABox):-
  \+ find_in_abox(El,ABox).

/*
  insertion into and deletion from ABox of an assertion
*/
add_to_abox(ABox,El,[El|ABox]).

remove_from_abox(ABox0,El,ABox):-
  delete(ABox0,El,ABox).

/*
  merge node in ABox
*/
% TODO update
merge_abox(_M,_L,_,_,[],[],[]).

merge_abox(M,L,SI,Expl0,[(classAssertion(C,Ind),ExplT)|T],[(classAssertion(C,SI),Expl)|ABox],[C-SI|CTC]):-
  member(Ind,L),!,
  and_f(M,Expl0,ExplT,Expl),
  %and_f_ax(M,sameIndividual(L),Expl1,Expl),
  merge_abox(M,L,SI,Expl0,T,ABox,CTC).

merge_abox(M,L,SI,Expl0,[(propertyAssertion(P,Ind1,Ind2),ExplT)|T],[(propertyAssertion(P,SI,Ind2),Expl)|ABox],CTC):-
  member(Ind1,L),!,
  and_f(M,Expl0,ExplT,Expl),
  %and_f_ax(M,sameIndividual(L),Expl1,Expl),
  merge_abox(M,L,SI,Expl0,T,ABox,CTC).

merge_abox(M,L,SI,Expl0,[(propertyAssertion(P,Ind1,Ind2),ExplT)|T],[(propertyAssertion(P,Ind1,SI),Expl)|ABox],CTC):-
  member(Ind2,L),!,
  and_f(M,Expl0,ExplT,Expl),
  %and_f_ax(M,sameIndividual(L),Expl1,Expl),
  merge_abox(M,L,SI,Expl0,T,ABox,CTC).

merge_abox(M,L,SI,Expl0,[H|T],[H|ABox],CTC):-
  merge_abox(M,L,SI,Expl0,T,ABox,CTC).


/*
  same label for two individuals

*/

same_label(X,Y,ABox):-
  \+ different_label(X,Y,ABox),
  !.

/*
  different label in two individuals

*/
% TODO maybe rewrite
different_label(X,Y,ABox):-
  findClassAssertion(C,X,_,ABox),
  \+ findClassAssertion(C,Y,_,ABox).

different_label(X,Y,ABox):-
  findClassAssertion(C,Y,_,ABox),
  \+ findClassAssertion(C,X,_,ABox).


/**************
  FIND FUNCTIONS
***************/

findClassAssertion(C,Ind,Expl1,ABox):-
  (
    is_list(Ind) ->
    (
      find_in_abox((classAssertion(C,sameIndividual(Ind)),Expl1),ABox)
    ) ;
    (
      find_in_abox((classAssertion(C,Ind),Expl1),ABox)
    )
  ).

findPropertyAssertion(R,Ind1,Ind2,Expl1,ABox):-
	(
    is_list(Ind1) ->
    (
      Ind1S=sameIndividual(Ind1)
    ) ;
    (
      Ind1S=Ind1
    )
  ),
  (
    is_list(Ind2) ->
    (
      Ind2S=sameIndividual(Ind2)
    ) ;
    (
      Ind2S=Ind2
    )
  ),
  find_in_abox((propertyAssertion(R,Ind1S,Ind2S),Expl1),ABox).


% --------------
findClassAssertion4OWLNothing(_M,ABox,Expl):-
  findClassAssertion('http://www.w3.org/2002/07/owl#Nothing',_Ind,Expl,ABox).

% -----------------------------------
% TABS
% -----------------------------------

/*
  initialize the tableau
  tableau is composed of:
  	a directed graph T => tableau without label
  	a red black tree RBN => each node is a pair of inds that contains the label for the edge
  	a red black tree RBR => each node is a property that contains the pairs of inds
*/
new_tabs(([],ItR,RtI)):-
  rb_new(ItR),
  rb_new(RtI).

/**
 * exists_edge(+Ind1:atom,+Ind2:atom,+T:ugraph)
 * 
 * Check  the existence of the edge Ind1-Ind2 in ugraph T.
*/
%TODO previsouly graph_edge/3
exists_edge(Ind1,Ind2,T0):-
  edges(T0, Edges),
  member(Ind1-Ind2, Edges),!.

/*
  Adds nodes and edges to tabs given axioms

  To use this, it is necessary o first extract Tabs from the tableau
  using get_tabs/2 and then update the tableau qith set_tabs/3.
*/
% TODO previously create_tabs
update_tabs(L,Tableau0,Tableau):-
  get_tabs(Tableau0,Tabs0),
  update_tabs_int(L,Tabs0,Tabs),
  set_tabs(Tableau0,Tabs,Tableau).


update_tabs_int([],G,G).
  
update_tabs_int([(propertyAssertion(P,S,O),_Expl)|T],Tabl0,Tabl):-
  add_edge_int(P,S,O,Tabl0,Tabl1),
  update_tabs_int(T,Tabl1,Tabl).
  
update_tabs_int([(differentIndividuals(Ld),_Expl)|Tail],(T0,RBN,RBR),Tabs):-
  add_vertices(T0,Ld,T1),
  update_tabs_int(Tail,(T1,RBN,RBR),Tabs).

update_tabs_int([(classAssertion(_,I),_Expl)|Tail],(T0,RBN,RBR),Tabs):-
  add_vertices(T0,[I],T1),
  update_tabs_int(Tail,(T1,RBN,RBR),Tabs).


/**
 * add_edge(+Property:string,+Subject:individual,+Object:individual,+Tab0:tableau,--Tab:tableau)
 * 
 * Adds edge fron Subject to Object labelled as Property to tableau Tab0 returning Tab.
 */
add_edge(P,S,O,Tableau0,Tableau):-
  get_tabs(Tableau0,Tabs0),
  add_edge_int(P,S,O,Tabs0,Tabs),
  set_tabs(Tableau0,Tabs,Tableau).

% Adds an edge to tabs, taken in input.
% To use this, it is necessary o first extract Tabs from the tableau
% using get_tabs/2 and then update the tableau qith set_tabs/3.
add_edge_int(P,S,O,(T0,ItR0,RtI0),(T1,ItR1,RtI1)):-
  add_node_to_tree(P,S,O,ItR0,ItR1),
  add_role_to_tree(P,S,O,RtI0,RtI1),
  add_edge_to_tabl(P,S,O,T0,T1).

add_node_to_tree(P,S,O,RB0,RB1):-
  rb_lookup((S,O),V,RB0),
  \+ member(P,V),!,
  rb_update(RB0,(S,O),[P|V],RB1).

add_node_to_tree(P,S,O,RB0,RB0):-
  rb_lookup((S,O),V,RB0),
  member(P,V),!.

add_node_to_tree(P,S,O,RB0,RB1):-
  \+ rb_lookup([S,O],_,RB0),!,
  rb_insert(RB0,(S,O),[P],RB1).

add_role_to_tree(P,S,O,RB0,RB1):-
  rb_lookup(P,V,RB0),
  \+ member((S,O),V),!,
  rb_update(RB0,P,[(S,O)|V],RB1).

add_role_to_tree(P,S,O,RB0,RB0):-
  rb_lookup(P,V,RB0),
  member((S,O),V),!.

add_role_to_tree(P,S,O,RB0,RB1):-
  \+ rb_lookup(P,_,RB0),!,
  rb_insert(RB0,P,[(S,O)],RB1).

add_edge_to_tabl(_R,Ind1,Ind2,T0,T0):-
  exists_edge(Ind1,Ind2,T0),!.

add_edge_to_tabl(_R,Ind1,Ind2,T0,T1):-
  add_edges(T0,[Ind1-Ind2],T1).


/*
 * merge node in tableau. X and Y single individuals
 */

merge_tabs(X,Y,(T0,RBN0,RBR0),(T,RBN,RBR)):-
  (neighbours(X,T0,LSX0)*->assign(LSX0,LSX);assign([],LSX)),
  (neighbours(Y,T0,LSY0)*->assign(LSY0,LSY);assign([],LSY)),
  transpose_ugraph(T0,TT),
  (neighbours(X,TT,LPX0)*->assign(LPX0,LPX);assign([],LPX)),
  (neighbours(Y,TT,LPY0)*->assign(LPY0,LPY);assign([],LPY)),
  % list_as_sameIndividual([X,Y],SI), %TODO
  flatten([X,Y],L0),
  sort(L0,SI),
  set_predecessor(SI,X,LPX,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),!,
  set_successor(SI,X,LSX,(T1,RBN1,RBR1),(T2,RBN2,RBR2)),!,
  set_predecessor(SI,Y,LPY,(T2,RBN2,RBR2),(T3,RBN3,RBR3)),!,
  set_successor(SI,Y,LSY,(T3,RBN3,RBR3),(T4,RBN4,RBR4)),!,
  remove_nodes(X,Y,(T4,RBN4,RBR4),(T,RBN,RBR)).

remove_nodes(X,Y,Tabs0,Tabs):-
  remove_node(X,Tabs0,Tabs1),
  remove_node(Y,Tabs1,Tabs).

% Collects all the nodes connected in input (LP, predecessor) or in output (LS, successor) for node X
% removes from RBN (remove_all_nodes_from_tree) all the pairs key-value where the key contains node X (pairs (X,Ind1) and (Ind1,X))
% and from RBR (remove_edges->remove_role_from_tree) all the pairs containing X from the values of the roles entering in or exiting from X
remove_node(X,(T0,RBN0,RBR0),(T,RBN,RBR)):-
  (neighbours(X,T0,LS0)*->assign(LS0,LS);assign([],LS)),
  transpose_ugraph(T0,TT),
  (neighbours(X,TT,LP0)*->assign(LP0,LP);assign([],LP)),
  remove_node1(X,LS,RBN0,RBR0,RBN1,RBR1),
  remove_node2(X,LP,RBN1,RBR1,RBN,RBR),
  (vertices(T0,VS),member(X,VS)*->del_vertices(T0,[X],T);assign(T0,T)).

remove_node1(_,[],RBN,RBR,RBN,RBR).

remove_node1(X,[H|T],RBN0,RBR0,RBN,RBR):-
  rb_lookup((X,H),V,RBN0),
  remove_edges(V,X,H,RBR0,RBR1),
  remove_all_nodes_from_tree(_,X,H,RBN0,RBN1),
  remove_node1(X,T,RBN1,RBR1,RBN,RBR).

remove_node2(_,[],RBN,RBR,RBN,RBR).

remove_node2(X,[H|T],RBN0,RBR0,RBN,RBR):-
  rb_lookup((H,X),V,RBN0),
  remove_edges(V,H,X,RBR0,RBR1),
  remove_all_nodes_from_tree(_,H,X,RBN0,RBN1),
  remove_node1(X,T,RBN1,RBR1,RBN,RBR).

remove_edges([],_,_,RBR,RBR).

remove_edges([H|T],S,O,RBR0,RBR):-
  remove_role_from_tree(H,S,O,RBR0,RBR1),
  remove_edges(T,S,O,RBR1,RBR).


set_predecessor(_NN,_,[],Tabs,Tabs).

set_predecessor(NN,X,[H|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
  rb_lookup((H,X),LR,RBN0),
  set_predecessor1(NN,H,LR,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
  set_predecessor(NN,X,L,(T1,RBN1,RBR1),(T,RBN,RBR)).

set_predecessor1(_NN,_H,[],Tabs,Tabs).

set_predecessor1(NN,H,[R|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
  add_edge_int(R,H,NN,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
  set_predecessor1(NN,H,L,(T1,RBN1,RBR1),(T,RBN,RBR)).

set_successor(_NN,_X,[],Tabs,Tabs).

set_successor(NN,X,[H|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
  rb_lookup((X,H),LR,RBN0),
  set_successor1(NN,H,LR,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
  set_successor(NN,X,L,(T1,RBN1,RBR1),(T,RBN,RBR)).

set_successor1(_NN,_H,[],Tabs,Tabs).

set_successor1(NN,H,[R|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
  add_edge_int(R,NN,H,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
  set_successor1(NN,H,L,(T1,RBN1,RBR1),(T,RBN,RBR)).

% TODO can it be removed?
assign(L,L).

/*
  Remove edges and nodes from tableau.
  It is used by remove_node(Node,Tabs0,Tabs).

  To remove a node from the tableau use remove_node(Node,Tabs0,Tabs).
*/

% remove_all_nodes_from_tree(Property,Subject,Object,RBN0,RBN)
% removes from RBN the pair key-values with key (Subject,Object)
% key (Subject,Object) exists
remove_all_nodes_from_tree(_P,S,O,RB0,RB1):-
  rb_lookup((S,O),_,RB0),
  rb_delete(RB0,(S,O),RB1).

% key (Subject,Object) does not exist
remove_all_nodes_from_tree(_P,S,O,RB0,_RB1):-
  \+ rb_lookup((S,O),_,RB0).
% ----------------

% remove_role_from_tree(Property,Subject,Object,RBR0,RBR)
% remove in RBR the pair (Subject,Object) from the value associated with key Property
% pair (Subject,Object) does not exist for key Property
remove_role_from_tree(P,S,O,RB,RB):-
  rb_lookup(P,V,RB),
  \+ member((S,O),V).

% pair (Subject,Object) exists for key Property but it is not the only pair associated to it
remove_role_from_tree(P,S,O,RB0,RB1):-
  rb_lookup(P,V,RB0),
  member((S,O),V),
  delete(V,(S,O),V1),
  dif(V1,[]),
  rb_update(RB0,P,V1,RB1).

% pair (Subject,Object) exists for key Property and it is the only pair associated to it
remove_role_from_tree(P,S,O,RB0,RB1):-
  rb_lookup(P,V,RB0),
  member((S,O),V),
  delete(V,(S,O),V1),
  V1==[],
  rb_delete(RB0,P,RB1).


/*
 find all ancestor of a node

*/
ancestor(Ind,T,AN):-
  transpose_ugraph(T,T1),
  ancestor1([Ind],T1,[],AN).

ancestor1([],_,A,A).

ancestor1([Ind|Tail],T,A,AN):-
  neighbours(Ind,T,AT),
  % TODO previosuly add_all_n/3
  %add_all_n(AT,Tail,Tail1),
  ord_union(AT,Tail,Tail1),
  % TODO previosuly add_all_n/3
  %add_all_n(A,AT,A1),
  ord_union(A,AT,A1),
  ancestor1(Tail1,T,A1,AN).
% ----------------

/*
  find a path in the graph
*/
graph_min_path(X,Y,T,P):-
  findall(Path, graph_min_path1(X,Y,T,Path), Ps),
  min_length(Ps,P).

graph_min_path1(X,Y,T,[X,Y]):-
  member(X-L,T),
  member(Y,L).

graph_min_path1(X,Y,T,[X|P]):-
  member(X-L,T),
  member(Z,L),
  graph_min_path1(Z,Y,T,P).

min_length([H],H).

min_length([H|T],MP):-
  min_length(T,P),
  length(H,N),
  length(P,NP),
  (N<NP ->
     MP= H
   ;
     MP= P).
% ----------------

% -----------------------------------
% EXPANSION QUEUE
% -----------------------------------

% Initializes the expansion queue and adds assertions from lists LCA and LPA.
init_expansion_queue(LCA,LPA,EQ):-
  empty_expansion_queue(EmptyEQ),
  add_classes_expqueue(LCA,EmptyEQ,EQ0),
  add_prop_expqueue(LPA,EQ0,EQ).

% Creation of the empty expansion queue.
empty_expansion_queue([[],[]]).

% Adds class assertions to exp. queue
add_classes_expqueue([],EQ,EQ).

add_classes_expqueue([(classAssertion(C,I),_)|T],EQ0,EQ):-
  update_expansion_queue(_,C,I,EQ0,EQ1),
  add_classes_expqueue(T,EQ1,EQ).

% Adds property assertions to exp. queue
add_prop_expqueue([],EQ,EQ).

add_prop_expqueue([(propertyAssertion(P,S,O),_)|T],EQ0,EQ):-
  update_expansion_queue(_,P,S,O,EQ0,EQ1),
  add_prop_expqueue(T,EQ1,EQ).


/**
 * update_expansion_queue(+M:module,+C:concept,+Ind:individual,+ExpQ0:expansion_queue,--ExpQ:expansion_queue)
 * 
 * Updates expansion queue. If the assertion is already included in the expansion queue,
 * it is first removed and then added at the end.
 *
 * If the assertion is a concept whose expansion needs non-deterministic rules,
 * the assertion is added to the non-det list.
 */
% Adds class assertion to non-det queue
update_expansion_queue(_,unionOf(L),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
  delete(NDQ0,[unionOf(L),Ind],NDQ1),
  append(NDQ1,[[unionOf(L),Ind]],NDQ).

update_expansion_queue(_,maxCardinality(N,S,C),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
  delete(NDQ0,[maxCardinality(N,S,C),Ind],NDQ1),
  append(NDQ1,[[maxCardinality(N,S,C),Ind]],NDQ).

update_expansion_queue(_,maxCardinality(N,S),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
  delete(NDQ0,[maxCardinality(N,S),Ind],NDQ1),
  append(NDQ1,[[maxCardinality(N,S),Ind]],NDQ).

update_expansion_queue(_,exactCardinality(N,S,C),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
  delete(NDQ0,[exactCardinality(N,S,C),Ind],NDQ1),
  append(NDQ1,[[exactCardinality(N,S,C),Ind]],NDQ).

update_expansion_queue(_,exactCardinality(N,S),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
  delete(NDQ0,[exactCardinality(N,S),Ind],NDQ1),
  append(NDQ1,[[exactCardinality(N,S),Ind]],NDQ).

% Adds class assertions to det queue
update_expansion_queue(_,C,Ind,[DQ0,NDQ],[DQ,NDQ]):-!,
  delete(DQ0,[C,Ind],DQ1),
  append(DQ1,[[C,Ind]],DQ).

/**
 * update_expansion_queue(+M:module,+P:property,+Ind1:individual,+Ind2:individual,+ExpQ0:expansion_queue,--ExpQ:expansion_queue)
 * 
 * Updates expansion queue. If the assertion is already included in the expansion queue,
 * it is first removed and then added at the end.
 *
 * Adds property assertion to det queue.
 */
update_expansion_queue(_,P,Ind1,Ind2,[DQ0,NDQ],[DQ,NDQ]):-!,
  delete(DQ0,[P,Ind1,Ind2],DQ1),
  append(DQ1,[[P,Ind1,Ind2]],DQ).


/**
 * update_expansion_queue_after_merge(+L:list,+SI:sameIndividual/1,+ExpQ0:expansion_queue,-ExpQ:expansion_queue)
 * 
 * Substitute individuals in L with SI in assertions contained in expansion queue ExpQ0.
 * It returns the updated expansion queue of clashes in ExpQ.
 */
update_expansion_queue_after_merge(L,SI,[ExpQD0,ExpQND0],[ExpQD,ExpQND]):-
  update_expansion_queue_after_merge_int(L,SI,ExpQD0,ExpQD),
  update_expansion_queue_after_merge_int(L,SI,ExpQND0,ExpQND).

update_expansion_queue_after_merge_int(_,_,[],[]).

update_expansion_queue_after_merge_int(L,SI,[[C,I]|TC0],[[C,IN]|TC]):-
  substitute_individual(L,I,SI,IN),
  update_expansion_queue_after_merge_int(L,SI,TC0,TC).

update_expansion_queue_after_merge_int(L,SI,[[P,S,O]|TC0],[[P,SN,ON]|TC]):-
  substitute_individual(L,S,SI,SN),
  substitute_individual(L,O,SI,ON),
  update_expansion_queue_after_merge_int(L,SI,TC0,TC).

substitute_individual(L,sameIndividual(LSI),SI,SI):-
  memberchk(I,L),
  memberchk(I,LSI),!.

substitute_individual(_,I,_,I):-!.

/**
 * extract_ea_from_expansion_queue(+ExpQ0:expansion_queue,--EA:atom,--ExpQ:expansion_queue)
 * 
 * Extracts from expansion queue ExpQ0 the next assertion to expand and returns it in EA
 * together with the updated expansion queue in ExpQ
 */
extract_ea_from_expansion_queue([[],[EA|T]],EA,[[],T]).

extract_ea_from_expansion_queue([[EA|T],NonDetQ],EA,[T,NonDetQ]).


% -----------------------------------
% CLASHES
% -----------------------------------

/*
  insertion into and deletion from ABox of an assertion
*/
add_to_clashes(Clashes,'http://www.w3.org/2002/07/owl#Nothing'-_,[owlnothing|Clashes]):-!.

add_to_clashes(Clashes,El,[El|Clashes]).

remove_from_clashes(Clashes0,El,Clashes):-
  delete(Clashes0,El,Clashes).


/**
 * check_clashes_to_add(+M:module,+ClashesToCheck:list,+Tab:tableau,--ClashesList:list)
 * 
 * Collects from a list of candidate clashes ClashesToCheck those that are actually clashes w.r.t. the given tableau Tab.
 * It outputs the found clashes in the list ClashesList. 
 */
check_clashes_to_add(_,[],_,[]).

check_clashes_to_add(M,[ToCheck|TC],Tab,[ToCheck|NewClashes]):-
  check_clash(M,ToCheck,Tab),!,
  check_clashes_to_add(M,TC,Tab,NewClashes).

check_clashes_to_add(M,[_ToCheck|TC],Tab,NewClashes):-
  check_clashes_to_add(M,TC,Tab,NewClashes).

/**
 * update_clashes_after_merge(+M:module,+L:list,+SI:sameIndividual/1,+Tableau:tableau,+Clashes0:list,--Clashes:list)
 * 
 * Substitute individuals in L with SI in clashes contained in Clashes0. It returns the updated list of clashes in Clashes.
 * TODO remove Tableau
 */
update_clashes_after_merge(M,L,SI,Tableau,Clashes0,Clashes):-
  update_clashes_after_merge(M,L,SI,Tableau,Clashes0,Clashes,0).

% if last argument is 0 -> need to theck clash for sameIndividual/differentIndividual
% if there is no clash (check_clash returns false), backtrack to (*)
update_clashes_after_merge(M,_,SI,Tableau,[],[SI],0):-
  check_clash(M,SI,Tableau),!.

% (*)
update_clashes_after_merge(_,_,_,_,[],[],_).

update_clashes_after_merge(M,L,SI,Tableau,[sameIndividual(LC)|TC0],[SI|TC],0):-
  memberchk(I,L),
  memberchk(I,LC),!,
  update_clashes_after_merge(M,L,SI,Tableau,TC0,TC,1).

update_clashes_after_merge(M,L,SI,Tableau,[C-I|TC0],[C-SI|TC],UpdatedSI):-
  memberchk(I,L),!,
  update_clashes_after_merge(M,L,SI,Tableau,TC0,TC,UpdatedSI).

update_clashes_after_merge(M,L,SI,Tableau,[C-sameIndividual(LOld)|TC0],[C-SI|TC],UpdatedSI):-
  memberchk(I,L),
  memberchk(I,LOld),!,
  update_clashes_after_merge(M,L,SI,Tableau,TC0,TC,UpdatedSI).

update_clashes_after_merge(M,L,SI,Tableau,[Clash|TC0],[Clash|TC],UpdatedSI):-
  update_clashes_after_merge(M,L,SI,Tableau,TC0,TC,UpdatedSI).

/**************
  CHECK CLASHES FUNCTIONS
  % TODO maybe to move in different part??
***************/

% TODO merge with clash/4
check_clash(_,'http://www.w3.org/2002/07/owl#Nothing'-_,_):-
  %write('clash 1'),nl,
  !.

check_clash(_,C-Ind,Tab):-
  get_abox(Tab,ABox),
  %write('clash 2'),nl,
  neg_class(C,NegC),
  findClassAssertion(NegC,Ind,_,ABox),!.
  
check_clash(_,sameIndividual(LS),Tab):-
  get_abox(Tab,ABox),
  %write('clash 3.a'),nl,
  find_in_abox((differentIndividuals(LD),_Expl2),ABox),
  member(X,LS),
  member(Y,LS),
  member(X,LD),
  member(Y,LD),
  dif(X,Y),!.
  
check_clash(_,differentIndividuals(LS),Tab):-
  get_abox(Tab,ABox),
  %write('clash 3.b'),nl,
  find_in_abox((sameIndividual(LD),_Expl2),ABox),
  member(X,LS),
  member(Y,LS),
  member(X,LD),
  member(Y,LD),
  dif(X,Y),!.
  
check_clash(_,C-sameIndividual(L1),Tab):-
  get_abox(Tab,ABox),
  %write('clash 4'),nl,
  neg_class(C,NegC),
  findClassAssertion(NegC,sameIndividual(L2),_Expl2,ABox),
  member(X,L1),
  member(X,L2),!.
  
check_clash(_,C-Ind1,Tab):-
  get_abox(Tab,ABox),
  %write('clash 5'),nl,
  neg_class(C,NegC),
  findClassAssertion(NegC,sameIndividual(L2),_Expl2,ABox),
  member(Ind1,L2),!.
  
check_clash(_,C-sameIndividual(L1),Tab):-
  get_abox(Tab,ABox),
  %write('clash 6'),nl,
  neg_class(C,NegC),
  findClassAssertion(NegC,Ind2,_,ABox),
  member(Ind2,L1),!.
  
check_clash(M,C1-Ind,Tab):-
  get_abox(Tab,ABox),
  %write('clash 7'),nl,
  M:disjointClasses(L), % TODO use hierarchy
  member(C1,L),
  member(C2,L),
  dif(C1,C2),
  findClassAssertion(C2,Ind,_,ABox),!.
  
check_clash(M,C1-Ind,Tab):-
  get_abox(Tab,ABox),
  %write('clash 8'),nl,
  M:disjointUnion(_Class,L), % TODO use hierarchy
  member(C1,L),
  member(C2,L),
  dif(C1,C2),
  findClassAssertion(C2,Ind,_,ABox),!.

check_clash(_,P-Ind1-Ind2,Tab):-
  get_abox(Tab,ABox),
  %write('clash 9'),nl,
  neg_class(P,NegP),  % use of neg_class with a property
  findPropertyAssertion(NegP,Ind1,Ind2,_,ABox),!.

check_clash(M,maxCardinality(N,S,C)-Ind,Tab):-
  get_abox(Tab,ABox),
  %write('clash 10'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  individuals_of_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  LSS @> N,!.
  
check_clash(M,maxCardinality(N,S)-Ind,Tab):-
  %write('clash 11'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  LSS @> N,!.
  
check_clash(M,exactCardinality(N,S,C)-Ind,Tab):-
  get_abox(Tab,ABox),
  %write('clash 12'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  individuals_of_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  dif(LSS,N),!.
  
check_clash(M,exactCardinality(N,S)-Ind,Tab):-
  %write('clash 13'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  dif(LSS,N),!.

% -----------------

%-------------
% clash managing
% previous version, manages only one clash at time
% need some tricks in some rules for managing the cases of more than one clash
% TO IMPROVE!
%------------
% TODO merge with check_clash/4
clash(M,owlnothing,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 6'),nl,
  findClassAssertion4OWLNothing(M,ABox,Expl).

clash(M,C-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 1'),nl,
  findClassAssertion(C,Ind,Expl1,ABox),
  neg_class(C,NegC),
  findClassAssertion(NegC,Ind,Expl2,ABox),
  and_f(M,Expl1,Expl2,Expl).

clash(M,sameIndividual(LS),Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 2.a'),nl,
  find_in_abox((sameIndividual(LS),Expl1),ABox),
  find_in_abox((differentIndividuals(LD),Expl2),ABox),
  member(X,LS),
  member(Y,LS),
  member(X,LD),
  member(Y,LD),
  dif(X,Y),
  and_f(M,Expl1,Expl2,Expl).

clash(M,differentIndividuals(LS),Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 2.b'),nl,
  find_in_abox((differentIndividuals(LS),Expl1),ABox),
  find_in_abox((sameIndividual(LD),Expl2),ABox),
  member(X,LS),
  member(Y,LS),
  member(X,LD),
  member(Y,LD),
  dif(X,Y),
  and_f(M,Expl1,Expl2,Expl).

clash(M,C-sameIndividual(L1),Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 3'),nl,
  findClassAssertion(C,sameIndividual(L1),Expl1,ABox),
  neg_class(C,NegC),
  findClassAssertion(NegC,sameIndividual(L2),Expl2,ABox),
  samemember(L1,L2),!,
  and_f(M,Expl1,Expl2,Expl).

samemember(L1,L2):-
  member(X,L1),
  member(X,L2),!.

clash(M,C-Ind1,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 4'),nl,
  findClassAssertion(C,Ind1,Expl1,ABox),
  neg_class(C,NegC),
  findClassAssertion(NegC,sameIndividual(L2),Expl2,ABox),
  member(Ind1,L2),
  and_f(M,Expl1,Expl2,Expl).

clash(M,C-sameIndividual(L1),Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 5'),nl,
  findClassAssertion(C,sameIndividual(L1),Expl1,ABox),
  neg_class(C,NegC),
  findClassAssertion(NegC,Ind2,Expl2,ABox),
  member(Ind2,L1),
  and_f(M,Expl1,Expl2,Expl).

clash(M,C1-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 7'),nl,
  M:disjointClasses(L), % TODO use hierarchy
  member(C1,L),
  member(C2,L),
  dif(C1,C2),
  findClassAssertion(C1,Ind,Expl1,ABox),
  findClassAssertion(C2,Ind,Expl2,ABox),
  and_f(M,Expl1,Expl2,ExplT),
  and_f_ax(M,disjointClasses(L),ExplT,Expl).

clash(M,C1-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 8'),nl,
  M:disjointUnion(Class,L), % TODO use hierarchy
  member(C1,L),
  member(C2,L),
  dif(C1,C2),
  findClassAssertion(C1,Ind,Expl1,ABox),
  findClassAssertion(C2,Ind,Expl2,ABox),
  and_f(M,Expl1,Expl2,ExplT),
  and_f_ax(M,disjointUnion(Class,L),ExplT,Expl).

clash(M,P-Ind1-Ind2,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 11'),nl,
  findPropertyAssertion(P,Ind1,Ind2,Expl1,ABox),
  neg_class(P,NegP), % use of neg_class with a property
  findPropertyAssertion(NegP,Ind1,Ind2,Expl2,ABox),
  and_f(M,Expl1,Expl2,Expl).

clash(M,maxCardinality(N,S,C)-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 9'),nl,
  findClassAssertion(maxCardinality(N,S,C),Ind,Expl1,ABox),
  s_neighbours(M,Ind,S,Tab,SN),
  individuals_of_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  LSS @> N,
  join_expls_for_propAss(M,Ind,S,SNC,Expl1,ABox,Expl).

clash(M,maxCardinality(N,S)-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 10'),nl,
  findClassAssertion(maxCardinality(N,S),Ind,Expl1,ABox),
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  LSS @> N,
  join_expls_for_propAss(M,Ind,S,SN,Expl1,ABox,Expl).

clash(M,exactCardinality(N,S,C)-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 9'),nl,
  findClassAssertion(exactCardinality(N,S,C),Ind,Expl1,ABox),
  s_neighbours(M,Ind,S,Tab,SN),
  individuals_of_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  dif(LSS,N),
  join_expls_for_propAss(M,Ind,S,SNC,Expl1,ABox,Expl).

clash(M,exactCardinality(N,S)-Ind,Tab,Expl):-
  get_abox(Tab,ABox),
  %write('clash 10'),nl,
  findClassAssertion(exactCardinality(N,S),Ind,Expl1,ABox),
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  dif(LSS,N),
  join_expls_for_propAss(M,Ind,S,SN,Expl1,ABox,Expl).

% -----------------------------------

% -----------------------------------
% BLOCKING MANAGEMENT
% -----------------------------------

/*
 * nominal/2, blockable/2, blocked/2, indirectly_blocked/2 and safe/3
 *
 */

nominal(Inds,Tab):-
  get_abox(Tab,ABox),
  find_in_abox((nominal(Ind)),ABox),
  member(Ind,Inds).

% ----------------

blockable(Ind,Tab):-
  get_abox(Tab,ABox),
  ( find_in_abox((nominal(Ind)),ABox)
    ->
    false
    ;
    true ).

/*
  all nodes in path from X to Y are blockable?

*/
% TODO previously all_node_blockable/3
all_nodes_blockable(X,Y,Tab):-
  get_tabs(Tab,(T,_,_)),
  graph_min_path(X,Y,T,P), 
  all_nodes_blockable_int(P,Tab).

all_nodes_blockable_int([],_).

all_nodes_blockable_int([H|Tail],Tab):-
  blockable(H,Tab),
  all_nodes_blockable_int(Tail,Tab).
% ---------------

blocked(Ind,Tab):-
  check_block(Ind,Tab).

/*

  control for blocking an individual

*/

check_block(Ind,Tab):-
  blockable(Ind,Tab),
  get_tabs(Tab,(T,_,_)),
  transpose_ugraph(T,T1),
  ancestor(Ind,T,A),
  neighbours(Ind,T1,N),
  check_block1(Ind,A,N,Tab),!.

check_block(Ind,Tab):-
  blockable(Ind,Tab),
  get_tabs(Tab,(T,_,_)),
  transpose_ugraph(T,T1),
  neighbours(Ind,T1,N),
  check_block2(N,Tab),!.


check_block1(Indx,A,N,Tab):-
  % TODO member replaced with ord_memberchk
  ord_memberchk(Indx0,N),
  ord_memberchk(Indy,A),
  ord_memberchk(Indy0,A),
  get_tabs(Tab,(T,RBN,_)),
  neighbours(Indy,T,N2),
  % TODO previosuly member
  %member(Indy0,N2),
  ord_memberchk(Indy0,N2),
  rb_lookup((Indx0,Indx),V,RBN),
  rb_lookup((Indy0,Indy),V2,RBN),
  % TODO maybe replace with ord_memberchk
  member(R,V),
  member(R,V2),
  get_abox(Tab,ABox),
  same_label(Indx,Indy0,ABox),
  same_label(Indx0,Indy,ABox),
  all_nodes_blockable(Indx0,Indy0,Tab),!.

%check_block2([],_).

check_block2([H|Tail],Tab):-
  blocked(H,Tab),
  check_block2(Tail,Tab).

%---------------
indirectly_blocked(Ind,Tab):-
  get_tabs(Tab,(T,_RBN,_RBR)),
  transpose_ugraph(T,T1),
  neighbours(Ind,T1,N),
  % TODO previosuly member
  %member(A,N),
  ord_memberchk(A,N),
  blocked(A,Tab),!.

%---------------------
/*
  An R-neighbour y of a node x is safe if
  (i)  x is blockable or
  (ii) x is a nominal node and y is not blocked.
*/

safe(Ind,R,Tab):-
  get_tabs(Tab,(_,_,RBR)),
  rb_lookup(R,V,RBR),
  get_parent(X,Ind,V),
  blockable(X,Tab),!.

safe(Ind,R,Tab):-
  get_tabs(Tab,(_,_,RBR)),
  rb_lookup(R,V,RBR),
  get_parent(X,Ind,V),
  nominal(X,Tab),!,
  \+ blocked(Ind,Tab).

get_parent(X,Ind,[(X,Ind)|_T]):-!.

get_parent(X,Ind,[(X,LI)|_T]):-
  is_list(LI),
  member(Ind,LI),!.

get_parent(X,Ind,[_|T]):-
  get_parent(X,Ind,T).


%---------------------
% Checks if all individuals in the input list are safe
safe_s_neigh([],_,_,[]):-!.

safe_s_neigh([H|T],S,Tab,[H|ST]):-
  safe(H,S,Tab),
  safe_s_neigh(T,S,Tab,ST).

% Checks if all individuals in the input list are safe and belongs to class C
safe_s_neigh_C(L,S,C,Tab,LT):-
  get_abox(Tab,ABox),
  safe_s_neigh_C(L,S,C,Tab,ABox,LT).

safe_s_neigh_C([],_,_,_,_,_,[]):-!.

safe_s_neigh_C([H|T],S,C,Tab,ABox,[H|ST]):-
  safe(H,S,Tab),
  findClassAssertion(C,H,_,ABox),!,
  safe_s_neigh_C(T,S,C,Tab,ABox,ST).

/* ***** */


% -----------------------------------
% JUSTIFICATIONS MANAGEMENT
% -----------------------------------
% TODO merge tornado
% TODO change name of empty and initial to a clearer name
initial_expl(M,[e{expl:[],bdd:BDD,cp:[]}]):-!,
  get_bdd_environment(M,Env),
  zero(Env,BDD).

empty_expl(M,[e{expl:[],bdd:BDD,cp:[]}]):-!,
  get_bdd_environment(M,Env),
  one(Env,BDD).

/*
  and of justifications
*/
and_all_f(M,ExplPartsList,E) :-
  empty_expl(M,EmptyE),
  and_all_f(M,ExplPartsList,EmptyE,E).

and_all_f(_,[],E,E) :- !.

and_all_f(M,[H|T],E0,E):-
  and_f(M,E0,H,E1),
  and_all_f(M,T,E1,E).

and_f_ax(M,Axiom,F0,F):-
  get_bdd_environment(M,Env),
  bdd_and(M,Env,[Axiom],BDDAxiom),
  and_f(M,[e{expl:[Axiom],bdd:BDDAxiom,cp:[]}],F0,F).

and_f(_M,[],[],[]):- !.

and_f(_M,[],L,L):- !.

and_f(_M,L,[],L):- !.

and_f(_M,L1,L2,F):-
  and_f1(L1,L2,[],F).

and_f1([],_,L,L).

and_f1([e{expl:H1,bdd:BDD1,cp:CP1}|T1],L2,L3,L):-
  and_f2(H1,CP1,L2,L12),
  append(L3,L12,L4),
  and_f1(T1,L2,L4,L).

and_f2(_,_,[],[]):- !.

and_f2(L1,CP1,[e{expl:H2,bdd:BDD2,cp:CP2}|T2],[e{expl:H,bdd:BDD,cp:CP}|T]):-
  append(L1,H2,H),
  append(CP1,CP2,CP),
  and_f2(L1,CP1,T2,T).

/*
  or of justifications
*/
or_f([],E,E).

or_f([E0|T],E1,E):-
  memberchk(E0,E1),!,
  or_f(T,E1,E).

or_f([E0|T],E1,[E0|E]):-
  or_f(T,E1,E).

% Takes a list of explanations and return a list of justifications, i.e., a list of explanations that are minimal
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

% --------------
% TODO previously make_expl/7
join_expls_for_propAss(_,_,_,[],Expl,_,Expl).

join_expls_for_propAss(M,Ind,S,[H|T],Expl0,ABox,Expl):-
  findPropertyAssertion(S,Ind,H,Expl2,ABox),
  and_f(M,Expl2,Expl0,Expl1),
  join_expls_for_propAss(M,Ind,S,T,Expl1,ABox,Expl).
% --------------


% -----------------------------------
% PROBABILITY COMPUTATION
% -----------------------------------
% TODO merge tornado
:- thread_local
        rule_n/1,
        na/2,
        v/3.


% for query with no inconsistency
compute_prob(M,Expl,Prob):-
  %retractall(v(_,_,_)),
  %retractall(na(_,_)),
  %retractall(rule_n(_)),
  %assert(rule_n(0)),
  %findall(1,M:annotationAssertion('http://ml.unife.it/disponte#probability',_,_),NAnnAss),length(NAnnAss,NV),
  get_bdd_environment(M,Env),
  build_bdd(M,Env,Expl,BDD),
  ret_prob(Env,BDD,Prob),
  clean_environment(M,Env), !.

% for query with inconsistency P1(Q) = P(Q|cons) = P(Q,cons)/P(cons) (Fabrizio's proposal)
/**/
compute_prob_inc(M,expl{expl:Expl,incons:Inc},Prob,IncCheck):-
  %retractall(v(_,_,_)),
  %retractall(na(_,_)),
  %retractall(rule_n(_)),
  %assert(rule_n(0)),
  %findall(1,M:annotationAssertion('http://ml.unife.it/disponte#probability',_,_),NAnnAss),length(NAnnAss,NV),
  get_bdd_environment(M,Env),
  build_bdd_inc(M,Env,Expl,Inc,BDDQC,BDDC),
  ret_prob(Env,BDDQC,ProbQC),
  ret_prob(Env,BDDC,ProbC),
  (dif(ProbC,0.0) -> 
    (Prob is ProbQC/ProbC,IncCheck=false)
    ;
    (Prob is 0.0,IncCheck=true)
  ),
  clean_environment(M,Env), !.
/**/

% Using weigths (https://dtai.cs.kuleuven.be/problog/tutorial/advanced/03_aproblog.html)
/*
compute_prob_inc(M,expl{expl:Expl,incons:Inc},Prob,IncCheck):-
  retractall(v(_,_,_)),
  retractall(na(_,_)),
  retractall(rule_n(_)),
  assert(rule_n(0)),
  %findall(1,M:annotationAssertion('http://ml.unife.it/disponte#probability',_,_),NAnnAss),length(NAnnAss,NV),
  get_bdd_environment(M,Env),gtrace,
  build_bdd(M,Env,Expl,BDDQC),
  build_bdd(M,Env,Inc,BDDI),
  build_formula(M,Env,BDDI,FI),
  write(FI),
  build_formula(M,Env,BDDQC,FQC),
  write(FQC),
  ret_prob(Env,BDDQC,ProbQC),
  ret_prob(Env,BDDI,ProbI),
  PQCM is min(ProbQC,0.999999999999999999),
  WQC is -log(1-PQCM),
  PIM is min(ProbI,0.999999999999999999),
  WI is -log(1-PIM),
  WQ is WQC/exp(-WI),
  Prob is 1-exp(-WQ),
  clean_environment(M,Env), !.


build_formula(M,Env,BDDI,F):-
  findall(VH,v(_,_,VH),LV),
  build_formula_int(M,Env,BDDI,LV,F).

build_formula_int(M,Env,BDDI,_,1):-
  one(Env,BDDI).

build_formula_int(M,Env,BDDI,_,0):-
  zero(Env,BDDI).

build_formula_int(M,Env,BDDI,LV,Var*(FT)*(1-FV)):-
  get_var_bdd(M,Env,BDDI,LV,Var),
  get_child_t(Env,Var,0,BDDT),
  get_child_f(Env,Var,0,BDDF),
  build_formula_int(M,Env,BDDT,LV,FT),
  build_formula_int(M,Env,BDDF,LV,FV).


get_var_bdd(M,Env,BDDI,LV,Var):-
  equality(Env,Var,0,BDDI),!.

get_var_bdd(M,Env,BDDI,LV,Var):-
  member(Var,LV),
  equality(Env,Var,1,BDDI).

*/

% for query with inconsistency P2(Q) = P(Q)(1-P(incons)) (Riccardo's proposal)
/*
compute_prob_inc(M,expl{expl:Expl,incons:Inc},Prob,IncCheck):-
  retractall(v(_,_,_)),
  retractall(na(_,_)),
  retractall(rule_n(_)),
  assert(rule_n(0)),
  %findall(1,M:annotationAssertion('http://ml.unife.it/disponte#probability',_,_),NAnnAss),length(NAnnAss,NV),
  get_bdd_environment(M,Env),
  build_bdd(M,Env,Expl,BDDQ),
  build_bdd(M,Env,Inc,BDDI),
  ret_prob(Env,BDDQ,ProbQ),
  ret_prob(Env,BDDI,ProbI),
  Prob is ProbQ*(1-ProbI),
  %bdd_not(Env,BDDI,BDDC),
  %ret_prob(Env,BDDC,ProbC),
  %Prob is ProbQ*ProbC,
  clean_environment(M,Env), !.
*/

% for query with inconsistency P1(Q) = P(Q|cons) = P(Q,cons)/P(cons) with AR (repair semantics) check
/*
compute_prob_inc(M,expl{expl:Expl,incons:Inc},Prob-ProbNQC,IncCheck):-
  retractall(v(_,_,_)),
  retractall(na(_,_)),
  retractall(rule_n(_)),
  assert(rule_n(0)),
  %findall(1,M:annotationAssertion('http://ml.unife.it/disponte#probability',_,_),NAnnAss),length(NAnnAss,NV),
  get_bdd_environment(M,Env),
  build_bdd_inc(M,Env,Expl,Inc,BDDQC,BDDNQC,BDDC),
  ret_prob(Env,BDDQC,ProbQC),
  ret_prob(Env,BDDC,ProbC),
  (dif(ProbC,0.0) -> 
    (Prob is ProbQC/ProbC,IncCheck=false)
    ;
    (Prob is 0.0,IncCheck=true)
  ),
  ret_prob(Env,BDDNQC,ProbNQC),
  clean_environment(M,Env), !.
*/

/*
  BDD Management
*/
%TODO merge with tornado
get_bdd_environment(_M,Env):-
  init(Env).

%TODO merge with tornado
clean_environment(_M,Env):-
  end(Env).

/**
 * build_bdd(+M:module,+Env:atom,+Expls:list,--BDD:atom)
 * 
 * Takes as input the BDD environment Env and a list of justifications Expls and returns the corresponding BDD.
 */
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

/**
 * build_bdd_inc(+M:module,+Env:atom,+Expls:list,+Inc:list,--BDDQC:atom,--BDDC:atom)
 * 
 * Takes as input the BDD environment Env, a list of justifications Expls for the query, and a list of explanations
 * for the inconsistency Inc and returns the BDD for the query and the consistency in BDDQC and the BDD for the consistency in BDDC.
 */
build_bdd_inc(M,Env,Expl,Inc,BDDQC,BDDC):- !,
  build_bdd(M,Env,Expl,BDDQ), % BDD query's explanations
  build_bdd(M,Env,Inc,BDDInc), % BDD inconsistency's explanations
  bdd_not(Env,BDDInc,BDDC), % BDD consistency's explanations
  and(Env,BDDQ,BDDC,BDDQC). % BDD query and consistency's explanations

/**
 * build_bdd_inc(+M:module,+Env:atom,+Expls:list,+Inc:list,--BDDQC:atom,--BDDNQC:atom,--BDDC:atom)
 * 
 * Takes as input the BDD environment Env, a list of justifications Expls for the query, and a list of explanations
 * for the inconsistency Inc and returns the BDD for the query and the consistency in BDDQC,
 * the BDD for the negation of the query and the consistency in BDDNQC, and the BDD for the consistency in BDDC.
 * It is used for computing the wuery truth under the AR repair semantics.
 */
build_bdd_inc(M,Env,Expl,Inc,BDDQC,BDDNQC,BDDC):- !,
  build_bdd(M,Env,Expl,BDDQ), % BDD query's explanations
  build_bdd(M,Env,Inc,BDDInc), % BDD inconsistency's explanations
  bdd_not(Env,BDDInc,BDDC), % BDD consistency's explanations
  bdd_not(Env,BDDQ,BDDNQ), % BDD for the query to be false
  and(Env,BDDQ,BDDC,BDDQC), % BDD query and consistency's explanations
  and(Env,BDDNQ,BDDC,BDDNQC). % BDD of query not true in consistent worlds


/* Utilities */
% Returns the variable corresponding with axiom R having the probabilities in Prob.
% If it does not exist it assings a new variable to axiom
get_var_n(Env,R,S,Probs,V):-
  (
    v(R,S,V) ->
      true
    ;
      %length(Probs,L),
      add_var(Env,Probs,R,V),
      assert(v(R,S,V))
  ).

% Returns the probability of an axiom. If the axiom is associated with more probabilisty values it computes the noisy-or.
get_prob_ax(M,(Ax,_Ind),N,Prob):- !,
  compute_prob_ax(M,Ax,Prob),
  ( na(Ax,N) ->
      true
    ;
      rule_n(N),
      assert(na(Ax,N)),
      retract(rule_n(N)),
      N1 is N + 1,
      assert(rule_n(N1))
  ).
get_prob_ax(M,Ax,N,Prob):- !,
  compute_prob_ax(M,Ax,Prob),
  ( na(Ax,N) ->
      true
    ;
      rule_n(N),
      assert(na(Ax,N)),
      retract(rule_n(N)),
      N1 is N + 1,
      assert(rule_n(N1))
  ).


compute_prob_ax(M,Ax,Prob):-
  findall(ProbA,(M:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',Ax,literal(ProbAT)),prob_number(ProbAT,ProbA)),ProbsOld), % Retro-compatibility
  findall(ProbA,(M:annotationAssertion('http://ml.unife.it/disponte#probability',Ax,literal(ProbAT)),prob_number(ProbAT,ProbA)),ProbsNew),
  append(ProbsNew, ProbsOld, Probs),
  compute_prob_ax1(Probs,Prob).

compute_prob_ax1([Prob],Prob):-!.

compute_prob_ax1([Prob1,Prob2],Prob):-!,
  Prob is Prob1+Prob2-(Prob1*Prob2).

compute_prob_ax1([Prob1 | T],Prob):-
  compute_prob_ax1(T,Prob0),
  Prob is Prob1 + Prob0 - (Prob1*Prob0).

% Subtracts a very small epsilon to probability  values equal to 1 in order to avoid using values
% equal to 0 during the computation of a probability.
prob_number(ProbAT,ProbA):-
  atom_number(ProbAT,ProbAC),
  ProbAC==1,!,
  Epsilon is 10**(-10),
  ProbA is ProbAC - Epsilon.

prob_number(ProbAT,ProbA):-
  atom_number(ProbAT,ProbAC),
  ProbAC==1.0,!,
  Epsilon is 10**(-10),
  ProbA is ProbAC - Epsilon.

prob_number(ProbAT,ProbA):-
  atom_number(ProbAT,ProbA).

% ===================================
% CHOICE POINTS MANAGEMENT
% ===================================

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

% returns the choice point list
get_choice_point_list(M,CP):-
  M:delta(CP,_).

% returns the choice point id
get_choice_point_id(M,ID):-
  M:delta(_,ID).

% extracts from the choice point list a choice point and updates the list
extract_choice_point_list(M,CP):-
  M:delta([CP|CPList],ID),
  retractall(M:delta(_,_)),
  assert(M:delta(CPList,ID)).


% Creates a new choice point and adds it to the delta/2 set of choice points.
create_choice_point(M,Ind,Rule,Class,Choices,ID0):-
  init_expl_per_choice(Choices,ExplPerChoice),
  M:delta(CPList,ID0),
  ID is ID0 + 1,
  retractall(M:delta(_,_)),
  assert(M:delta([cp(ID0,Ind,Rule,Class,Choices,ExplPerChoice)|CPList],ID)).

% returns choice points in order of creation (LIFO)
get_latest_choice([],0,0).

get_latest_choice(CPs,ID,Choice):-
  get_latest_choice_point(CPs,0,ID),
  get_latest_choice_of_cp(CPs,ID,0,Choice).

get_latest_choice_point([],ID,ID).

get_latest_choice_point([cpp(ID0,_)|T],ID1,ID):-
  ID2 is max(ID1,ID0),
  get_latest_choice_point(T,ID2,ID).

% Checks whether the explanations are empty or not
check_non_empty_choice(Expl,ExplList):-
  dict_pairs(Expl,_,PairsList),
  findall(Ex,member(_-Ex,PairsList),ExplList),
  \+ memberchk([],ExplList).

% Initializes the explanations of a choice point
% TODO merge tornado
init_expl_per_choice(Choices,ExplPerChoice):-
  length(Choices,N),
  init_expl_per_choice_int(0,N,epc{0:[]},ExplPerChoice).

init_expl_per_choice_int(N,N,ExplPerChoice,ExplPerChoice).

init_expl_per_choice_int(N0,N,ExplPerChoice0,ExplPerChoice):-
  ExplPerChoice1 = ExplPerChoice0.put(N0,[]),
  N1 is N0 + 1,
  init_expl_per_choice_int(N1,N,ExplPerChoice1,ExplPerChoice).

% Returns the lastest choice of a given choice point
get_latest_choice_of_cp([],_,C,C).

get_latest_choice_of_cp([cpp(ID,C0)|T],ID,C1,C):- !,
  C2 is max(C1,C0),
  get_latest_choice_of_cp(T,ID,C2,C).

get_latest_choice_of_cp([_|T],ID,C1,C):-
  get_latest_choice_of_cp(T,ID,C1,C).


% Updates the choice point list saved as delta/2
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

% this predicate checks if there are inconsistencies in the KB, i.e., explanations without query placeholder qp
% if it is so, the explanation is labelled as inconsistent kb
consistency_check(CPs,CPs,['inconsistent','kb'],['inconsistent','kb']):- !.

consistency_check(CPs0,CPs,Q0,Q):-
  (nth0(_,CPs0,qp,CPs) -> (Q=Q0) ; (Q=['inconsistent','kb'],CPs=CPs0)).





% ===================================
% COLLECTING JUSTIFICATIONS FROM TABLEAU
% ===================================
%TODO merge tornado

/**
 * find_expls(+M:module,+Tabs:list,+Q:list,--E:explanation)
 * 
 * Takes a list of tableaus Tabs, the current query Q and returns an explanation for Q.
 * At the moment it reads the list of choice points (asserted with delta/2) and asserts all the found justification (exp_found/2),
 * then it backtracks to collect all the exp_found and returnsthe minimal justifications
 */
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



find_expls_from_choice_point_list(M,QI,E):-
  extract_choice_point_list(M,CP),
  (
    combine_expls_from_nondet_rules(M,QI,CP,E) ;
    find_expls_from_choice_point_list(M,QI,E)
  ).


combine_expls_from_nondet_rules(M,Q0,cp(_,_,_,_,_,Expl),E):-
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

/*
check_presence_of_other_choices([],[],[]).

check_presence_of_other_choices([E-[]|ExplanationsList],[E|Explanations],Choices):- !,
  check_presence_of_other_choices(ExplanationsList,Explanations,Choices).

check_presence_of_other_choices([E-CP|ExplanationsList],[E|Explanations],[CP|Choices]):-
  check_presence_of_other_choices(ExplanationsList,Explanations,Choices).

not_already_found(_M,[],_Q,_E):-!.

not_already_found(_M,[H|_T],_Q,E):-
  subset(H,E),!,
  fail.

not_already_found(M,[H|_T],Q,E):-
  subset(E,H),!,
  retract(M:exp_found(Q,H)).

not_already_found(M,[_H|T],Q,E):-
  not_already_found(M,T,Q,E).
*/

% ===================================
% OWL AXIOM RELATED PREDICATES
% ===================================

% ---------------

% SUCCESSORS and PREDECESSORS
% Create the set of predecessors and successors.
find_successors(M,Ind,List) :- findall(ConnectedInd, (M:propertyAssertion(_,Ind,ConnectedInd)), List).
find_predecessors(M,Ind,List) :- findall(ConnectedInd, (M:propertyAssertion(_,ConnectedInd,Ind)), List).

% ---------------

% Checks if the two lists of individuals share individuals that are asserted as sameIndividuals
% TODO rewrite
not_same_ind(M,SN,H,_ABox):-
  M:differentIndividuals(SI),
  member(H,SI),
  member(H2,SI),
  member(H2,SN),
  dif(H,H2),!.

not_same_ind(_,SN,H,ABox):-
  find_in_abox((differentIndividuals(SI),_),ABox),
  member(H,SI),
  member(H2,SI),
  member(H2,SN),
  dif(H,H2),!.

not_same_ind(M,SN,H,ABox):-
  \+ same_ind(M,SN,H,ABox),!.

same_ind(M,SN,H,_ABox):-
  M:sameIndividual(SI),
  member(H,SI),
  member(H2,SI),
  member(H2,SN),
  dif(H,H2).

same_ind(_,SN,H,ABox):-
  find_in_abox((sameIndividual(SI),_),ABox),
  member(H,SI),
  member(H2,SI),
  member(H2,SN),
  dif(H,H2).

%--------------------
check_individuals_not_equal(M,X,Y,ABox):-
  dif(X,Y),
  \+ same_ind(M,[X],Y,ABox).
%--------------------
% TODO to rewrite and move into ABox management
% looks in the ABox to find sameindividuals
find_same(H,ABox,sameIndividual(L),Expl):-
  find_in_abox((sameIndividual(L),Expl),ABox),
  member(X,L),
  member(X,H),!.

find_same(_H,_ABox,[],[]).


%--------------------
% TODO previously individual_class_C/4
individuals_of_class_C([],_,_,[]).

individuals_of_class_C([H|T],C,ABox,[H|T1]):-
  findClassAssertion(C,H,_,ABox),!,
  individuals_of_class_C(T,C,ABox,T1).

individuals_of_class_C([_H|T],C,ABox,T1):-
  %\+ findClassAssertion(C,H,_,ABox),
  individuals_of_class_C(T,C,ABox,T1).

%--------------------
% Takes the list of individuals L0 and creates a definition sameIndividual/1 containing all the individuals in L0
% L0 may contain also sameIndividual/2 terms.
list_as_sameIndividual(L0,sameIndividual(L)):-
  list_as_sameIndividual_int(L0,L1),
  sort(L1,L).

list_as_sameIndividual_int([],[]).

list_as_sameIndividual_int([sameIndividual(L0)|T0],L):-
  !,
  append(L0,T0,L1),
  list_as_sameIndividual_int(L1,L).

list_as_sameIndividual_int([H|T0],[H|T]):-
  list_as_sameIndividual_int(T0,T).


% -------------------
% Checks whether X and Y are not different individuals
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
  find_in_abox((differentIndividuals(LI),_),ABox),
  member(X0,X),
  member(X0,LI),
  member(Y0,Y),
  member(Y0,LI).

inABoxDifferentIndividuals(X,sameIndividual(Y),ABox):-
  !,
  find_in_abox((differentIndividuals(LI),_),ABox),
  member(X,LI),
  member(Y0,Y),
  member(Y0,LI).

inABoxDifferentIndividuals(sameIndividual(X),Y,ABox):-
  !,
  find_in_abox((differentIndividuals(LI),_),ABox),
  member(X0,X),
  member(X0,LI),
  member(Y,LI).

inABoxDifferentIndividuals(X,Y,ABox):-
  find_in_abox((differentIndividuals(LI),_),ABox),
  member(X,LI),
  member(Y,LI).

% --------------------

% Transform an individual in a list if the individual is atomic or extract the list of individuals from sameIndividual/1
ind_as_list(M,sameIndividual(L),L):-
  retract_sameIndividual(M,L),!.

ind_as_list(_,X,[X]):-
  atomic(X).

/**
 * retract_sameIndividual(+M:module,+L)
 * 
 * Given L as sameIndividual/1 it retracts L, given L a list it retracts sameIndividual(L).
 */
retract_sameIndividual(M,sameIndividual(L)):-
  !,
  retract_sameIndividual(M,L).

retract_sameIndividual(M,L):-
  retract(M:sameIndividual(L)).

retract_sameIndividual(M,L):-
  \+ retract(M:sameIndividual(L)).

% TODO move here all class and proeprty find, negation, sub-sup, ecc.
% ----------------
% Negates a given concept
neg_class(complementOf(C),C):- !.

neg_class(C,complementOf(C)).

% Negates each class in a list
%TODO previously neg_list/2
neg_class_list([],[]).

neg_class_list([H|T],[NH|T1]):-
  neg_class(H,NH),
  neg_class_list(T,T1).

% -----------------
% subClassOf
find_sub_sup_class(M,C,D,subClassOf(C,D)):-
  M:subClassOf(C,D).

%equivalentClasses
find_sub_sup_class(M,C,D,equivalentClasses(L)):-
  M:equivalentClasses(L),
  member(C,L),
  member(D,L),
  dif(C,D).

%concept for concepts allValuesFrom
find_sub_sup_class(M,allValuesFrom(R,C),allValuesFrom(R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax).

%role for concepts allValuesFrom
find_sub_sup_class(M,allValuesFrom(R,C),allValuesFrom(S,C),subPropertyOf(R,S)):-
  find_sub_sup_property(M,R,S,_).
  % TODO previously
  % M:subPropertyOf(R,S).

%concept for concepts someValuesFrom
find_sub_sup_class(M,someValuesFrom(R,C),someValuesFrom(R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax).

%role for concepts someValuesFrom
find_sub_sup_class(M,someValuesFrom(R,C),someValuesFrom(S,C),subPropertyOf(R,S)):-
  find_sub_sup_property(M,R,S,_).
  % TODO previously
  % M:subPropertyOf(R,S).

%role for concepts exactCardinality
find_sub_sup_class(M,exactCardinality(N,R),exactCardinality(N,S),subPropertyOf(R,S)):-
  find_sub_sup_property(M,R,S,_).
  % TODO previously
  % M:subPropertyOf(R,S).

%concept for concepts exactCardinality
find_sub_sup_class(M,exactCardinality(N,R,C),exactCardinality(N,R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax).

%role for concepts exactCardinality
find_sub_sup_class(M,exactCardinality(N,R,C),exactCardinality(N,S,C),subPropertyOf(R,S)):-
  find_sub_sup_property(M,R,S,_).
  % TODO previously
  % M:subPropertyOf(R,S).

%role for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R),maxCardinality(N,S),subPropertyOf(R,S)):-
  find_sub_sup_property(M,R,S,_).
  % TODO previously
  % M:subPropertyOf(R,S).

%concept for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R,C),maxCardinality(N,R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax).

%role for concepts maxCardinality
find_sub_sup_class(M,maxCardinality(N,R,C),maxCardinality(N,S,C),subPropertyOf(R,S)):-
  find_sub_sup_property(M,R,S,_).
  % TODO previously
  % M:subPropertyOf(R,S).

%role for concepts minCardinality
find_sub_sup_class(M,minCardinality(N,R),minCardinality(N,S),subPropertyOf(R,S)):-
  find_sub_sup_property(M,R,S,_).
  % TODO previously
  % M:subPropertyOf(R,S).

%concept for concepts minCardinality
find_sub_sup_class(M,minCardinality(N,R,C),minCardinality(N,R,D),Ax):-
  find_sub_sup_class(M,C,D,Ax).

%role for concepts minCardinality
find_sub_sup_class(M,minCardinality(N,R,C),minCardinality(N,S,C),subPropertyOf(R,S)):-
  find_sub_sup_property(M,R,S,_).
  % TODO previously
  % M:subPropertyOf(R,S).


/*******************
 managing the concept (C subclassOf Thing)
 this implementation doesn't work well in a little set of cases
 TO IMPROVE!
 *******************/
/*
find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:subClassOf(A,B),
  member(C,[A,B]),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:classAssertion(C,_),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:equivalentClasses(L),
  member(C,L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:unionOf(L),
  member(C,L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:equivalentClasses(L),
  member(someValuesFrom(_,C),L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:equivalentClasses(L),
  member(allValuesFrom(_,C),L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:equivalentClasses(L),
  member(minCardinality(_,_,C),L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:equivalentClasses(L),
  member(maxCardinality(_,_,C),L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
  M:equivalentClasses(L),
  member(exactCardinality(_,_,C),L),!.

*/

% ----------------
% unionOf, intersectionOf, subClassOf, negation, allValuesFrom, someValuesFrom, exactCardinality(min and max), maxCardinality, minCardinality

find_neg_class(unionOf(L),intersectionOf(NL)):-
  neg_class_list(L,NL).

find_neg_class(intersectionOf(L),unionOf(NL)):-
  neg_class_list(L,NL).

find_neg_class(subClassOf(C,D),intersectionOf(C,ND)):-
  neg_class(D,ND).

find_neg_class(complementOf(C),C).

find_neg_class(allValuesFrom(R,C),someValuesFrom(R,NC)):-
  neg_class(C,NC).

find_neg_class(someValuesFrom(R,C),allValuesFrom(R,NC)):-
  neg_class(C,NC).

find_neg_class(exactCardinality(N,R,C),unionOf([maxCardinality(NMax,R,C),minCardinality(NMin,R,C)])):-
  NMax is N - 1,
  NMin is N + 1.

find_neg_class(minCardinality(N,R,C),maxCardinality(NMax,R,C)):-
  NMax is N - 1.

find_neg_class(maxCardinality(N,R,C),minCardinality(NMin,R,C)):-
  NMin is N + 1.

% ---------------

%--------------------
% looks for not atomic concepts descriptions containing class C
find_not_atomic(M,C,Ax,LC):-
  M:subClassOf(A,B),
  find_not_atomic_int(C,[A,B],Ax,LC).

find_not_atomic(M,C,Ax,LC):-
  M:equivalentClasses(L),
  find_not_atomic_int(C,L,Ax,LC).

/*
find_not_atomic(M,C,unionOf(L1),L1):-
  M:subClassOf(A,B),
  member(unionOf(L1),[A,B]),
  member(C,L1).

find_not_atomic(M,C,unionOf(L1),L1):-
  M:equivalentClasses(L),
  member(unionOf(L1),L),
  member(C,L1).
*/

find_not_atomic_int(C,LC0,intersectionOf(L1),L1):-
  member(intersectionOf(L1),LC0),
  member(C,L1).

find_not_atomic_int(C,LC0,Ax,LC):-
  member(intersectionOf(L1),LC0),
  find_not_atomic_int(C,L1,Ax,LC).

find_not_atomic_int(C,LC0,unionOf(L1),L1):-
  member(unionOf(L1),LC0),
  member(C,L1).

find_not_atomic_int(C,LC0,Ax,LC):-
  member(unionOf(L1),LC0),
  find_not_atomic_int(C,L1,Ax,LC).

%-----------------
% subPropertyOf
% TODO check if there exists something in utility_translation
find_sub_sup_property(M,C,D,subPropertyOf(C,D)):-
  M:subPropertyOf(C,D).

%equivalentProperties
find_sub_sup_property(M,C,D,equivalentProperties(L)):-
  M:equivalentProperties(L),
  member(C,L),
  member(D,L),
  dif(C,D).

%-----------------
%inverseProperties
find_inverse_property(M,C,D,inverseProperties(C,D)):-
  M:inverseProperties(C,D).

find_inverse_property(M,C,D,inverseProperties(D,C)):-
  M:inverseProperties(D,C).

%inverseProperties
find_inverse_property(M,C,C,symmetricProperty(C)):-
  M:symmetricProperty(C).

% -----------------------
% range and domain
find_class_prop_range_domain(M,P,S,O,O,D,Expl,ABox):-
  findPropertyAssertion(P,S,O,ExplPA,ABox),
  %ind_as_list(IndL,L),
  %member(Ind,L),
  M:propertyRange(P,D),
  and_f_ax(M,propertyRange(P,D),ExplPA,Expl).

find_class_prop_range_domain(M,P,S,O,S,D,Expl,ABox):-
  findPropertyAssertion(P,S,O,ExplPA,ABox),
  %ind_as_list(IndL,L),
  %member(Ind,L),
  M:propertyDomain(P,D),
  and_f_ax(M,propertyDomain(P,D),ExplPA,Expl).

% ------------------
% negates a subclass axioms
find_not_sub_sup_class(M,subClassOf(C,D),unionOf(complementOf(C),D)):-
  M:subClassOf(C,D),
  \+ atomic(C).


find_not_sub_sup_class(M,equivalentClasses(L),unionOf(L1)):-
  M:equivalentClasses(L),
  member(C,L),
  \+ atomic(C),
  copy_neg_c(C,L,L1).

%-------------------------
copy_neg_c(_,[],[]).

copy_neg_c(C,[C|T],[complementOf(C)|T1]):-
  !,
  copy_neg_c(C,T,T1).

copy_neg_c(C,[H|T],[H|T1]):-
  copy_neg_c(C,T,T1).

% ===================================
% GENERAL UTILITIES
% ===================================

/**
 * intersect(+L1:list,+L2:list)
 * 
 * Succeeds if L1 intersects L2, fails otehrwise.
 */
intersect([H|_], List) :- member(H, List), !.
intersect([_|T], List) :- intersect(T, List).

/**
 * listIntersection(+L1:list,+L2:list,L3:list)
 * 
 * Returns the intersection of L1 and L2 in L3.
 */
%TODO use ord_intersection and ord_subset
listIntersection([],_,[]).

listIntersection([HX|TX],LCY,TI):-
  \+ member(HX,LCY),
  listIntersection(TX,LCY,TI).

listIntersection([HX|TX],LCY,[HX|TI]):-
  member(HX,LCY),
  listIntersection(TX,LCY,TI).


/********************************
  LOAD KNOWLEDGE BASE
*********************************/
/**
 * load_kb(++FileName:kb_file_name) is det
 *
 * The predicate loads the knowledge base contained in the given file. 
 * The knowledge base must be defined in TRILL format, to use also OWL/RDF format
 * use the predicate owl_rdf/1.
 */
load_kb(FileName):-
  user:consult(FileName).

/**
 * load_owl_kb(++FileName:kb_file_name) is det
 *
 * The predicate loads the knowledge base contained in the given file. 
 * The knowledge base must be defined in pure OWL/RDF format.
 */
load_owl_kb(FileName):-
  load_owl(FileName).

/**
 * load_owl_kb_from_string(++KB:string) is det
 *
 * The predicate loads the knowledge base contained in the given string. 
 * The knowledge base must be defined in pure OWL/RDF format.
 */
load_owl_kb_from_string(String):-
  load_owl_from_string(String).


/*****************************
  UTILITY PREDICATES
******************************/
%defined in utility_translation
:- multifile axiom/1.
/**
 * axiom(:Axiom:axiom) is det
 *
 * This predicate searches in the loaded knowledge base axioms that unify with Axiom.
 */

:- multifile add_axiom/1.
/**
 * add_axiom(:Axiom:axiom) is det
 *
 * This predicate adds the given axiom to the knowledge base.
 * The axiom must be defined following the TRILL syntax.
 */

:- multifile add_axioms/1.
/**
 * add_axioms(:Axioms:list) is det
 *
 * This predicate adds the axioms of the list to the knowledge base.
 * The axioms must be defined following the TRILL syntax.
 */

:- multifile remove_axiom/1.
/**
 * remove_axiom(:Axiom:axiom) is det
 *
 * This predicate removes the given axiom from the knowledge base.
 * The axiom must be defined following the TRILL syntax.
 */

:- multifile remove_axioms/1.
/**
 * remove_axioms(++Axioms:list) is det
 *
 * This predicate removes the axioms of the list from the knowledge base.
 * The axioms must be defined following the TRILL syntax.
 */

:- multifile kb_prefixes/1.
/**
 * kb_prefixes(:Prefs:list) is det
 *
 * This predicate returns the list of pairs key-value representing the prefixes considered by the reasoner.
 */

:- multifile add_kb_prefix/2.
/**
 * add_kb_prefix(:ShortPref:string,++LongPref:string) is det
 *
 * This predicate registers the alias ShortPref for the prefix defined in LongPref.
 * The empty string '' can be defined as alias.
 */
:- multifile add_kb_prefixes/1.
/**
 * add_kb_prefixes(:Prefixes:list) is det
 *
 * This predicate registers all the alias prefixes contained in Prefixes.
 * The input list must contain pairs alias=prefix, i.e., [('foo'='http://example.foo#')].
 * The empty string '' can be defined as alias.
 */

:- multifile remove_kb_prefix/2.
/**
 * remove_kb_prefix(:ShortPref:string,++LongPref:string) is det
 *
 * This predicate removes from the registered aliases the one given in input.
 */

:- multifile remove_kb_prefix/1.
/**
 * remove_kb_prefix(:Name:string) is det
 *
 * This predicate takes as input a string that can be an alias or a prefix and 
 * removes the pair containing the string from the registered aliases.
 */


% ==================================================================================================================


:- multifile sandbox:safe_meta/2.

sandbox:safe_meta(trill:instanceOf(_,_,_,_),[]).
sandbox:safe_meta(trill:instanceOf(_,_,_),[]).
sandbox:safe_meta(trill:instanceOf(_,_),[]).
sandbox:safe_meta(trill:all_instanceOf(_,_,_),[]).

sandbox:safe_meta(trill:property_value(_,_,_,_,_),[]).
sandbox:safe_meta(trill:property_value(_,_,_,_),[]).
sandbox:safe_meta(trill:property_value(_,_,_),[]).
sandbox:safe_meta(trill:all_property_value(_,_,_,_),[]).

sandbox:safe_meta(trill:sub_class(_,_,_,_),[]).
sandbox:safe_meta(trill:sub_class(_,_,_),[]).
sandbox:safe_meta(trill:sub_class(_,_),[]).
sandbox:safe_meta(trill:all_sub_class(_,_,_),[]).

sandbox:safe_meta(trill:unsat(_,_,_),[]).
sandbox:safe_meta(trill:unsat(_,_),[]).
sandbox:safe_meta(trill:unsat(_),[]).
sandbox:safe_meta(trill:all_unsat(_,_),[]).

sandbox:safe_meta(trill:inconsistent_theory(_,_),[]).
sandbox:safe_meta(trill:inconsistent_theory(_),[]).
sandbox:safe_meta(trill:inconsistent_theory,[]).
sandbox:safe_meta(trill:all_inconsistent_theory(_),[]).

sandbox:safe_meta(trill:prob_instanceOf(_,_,_),[]).
sandbox:safe_meta(trill:prob_property_value(_,_,_,_),[]).
sandbox:safe_meta(trill:prob_sub_class(_,_,_),[]).
sandbox:safe_meta(trill:prob_unsat(_,_),[]).
sandbox:safe_meta(trill:prob_inconsistent_theory(_),[]).

sandbox:safe_meta(trill:load_kb(_),[]).
sandbox:safe_meta(trill:load_owl_kb(_),[]).
sandbox:safe_meta(trill:load_owl_kb_from_string(_),[]).

sandbox:safe_meta(trill:axiom(_),[]).
sandbox:safe_meta(trill:add_axiom(_),[]).
sandbox:safe_meta(trill:add_axioms(_),[]).
sandbox:safe_meta(trill:remove_axiom(_),[]).
sandbox:safe_meta(trill:remove_axioms(_),[]).
sandbox:safe_meta(trill:kb_prefixes(_),[]).
sandbox:safe_meta(trill:add_kb_prefix(_,_),[]).
sandbox:safe_meta(trill:add_kb_prefixes(_),[]).
sandbox:safe_meta(trill:remove_kb_prefix(_,_),[]).
sandbox:safe_meta(trill:remove_kb_prefix(_),[]).

sandbox:safe_meta(trill:set_tableau_expansion_rules(_,_),[]).


:- use_module(library(utility_translation)).


