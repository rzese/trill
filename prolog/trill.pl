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
                axiom/1, kb_prefixes/1, add_kb_prefix/2, add_kb_prefixes/1, add_axiom/1, add_axioms/1, remove_kb_prefix/2, remove_kb_prefix/1, remove_axiom/1, remove_axioms/1,
                load_kb/1, load_owl_kb/1, load_owl_kb_from_string/1, init_trill/1,
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

:- meta_predicate axiom(:).
:- meta_predicate kb_prefixes(:).
:- meta_predicate add_kb_prefix(:,+).
:- meta_predicate add_kb_prefixes(:).
:- meta_predicate add_axiom(:).
:- meta_predicate add_axioms(:).
:- meta_predicate remove_kb_prefix(:,+).
:- meta_predicate remove_kb_prefix(:).
:- meta_predicate remove_axiom(:).
:- meta_predicate remove_axioms(:).
:- meta_predicate load_kb(+).
:- meta_predicate load_owl_kb(+).
:- meta_predicate load_owl_kb_from_string(+).
:- meta_predicate set_algorithm(:).
:- meta_predicate init_trill(+).
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
find_explanations(M,QueryType,QueryArgs,ExplInc,QueryOptions), %here 1
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
  ( query_option(QueryOptions,assert_abox,AssertABox) -> Opt=[assert_abox(AssertABox)] ; Opt=[]),
  ( query_option(QueryOptions,max_expl,N) -> 
    MonitorNExpl = N
    ; 
    ( ( query_option(QueryOptions,return_prob,_) -> MonitorNExpl=all ; MonitorNExpl=bt) ) % if return_prob is present and no max_expl force to find all the explanations
  ),
  ( query_option(QueryOptions,time_limit,MonitorTimeLimit) ->
    find_n_explanations_time_limit(M,QueryType,QueryArgs,Expl,MonitorNExpl,MonitorTimeLimit,Opt) 
    ;
    find_n_explanations(M,QueryType,QueryArgs,Expl,MonitorNExpl,Opt) %here 2
  ).

% Find explanations in a given limited time.
% TODO multi-thearding here
find_n_explanations_time_limit(M,QueryType,QueryArgs,Expl,MonitorNExpl,MonitorTimeLimit,Opt):-
  retractall(M:setting_trill(timeout,_)),
  get_time(Start),
  Timeout is Start + MonitorTimeLimit,
  assert(M:setting_trill(timeout,Timeout)),
  find_n_explanations(M,QueryType,QueryArgs,Expl,MonitorNExpl,Opt), %here 3
  get_time(End),
  (End<Timeout -> true ; print_message(warning,timeout_reached)).


% TODO merge tornado
% findall
find_n_explanations(M,QueryType,QueryArgs,Expls,all,Opt):-
!, % CUT so that no other calls to find_explanation can be ran (to avoid running that with variable N)
findall(Expl,find_single_explanation(M,QueryType,QueryArgs,Expl,Opt),Expls0), %here 4
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
      findall(Tableau1,expand_queue(M,Tableau0,Tableau1),L), %here 5
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
  set_up(M),
  retractall(M:exp_found(_,_)),
  retractall(M:exp_found(_,_,_)),
  retractall(M:trillan_idx(_)),
  assert(M:trillan_idx(1)).

% General setting up
% TODO merge tornado
set_up(M):-
  utility_translation:set_up(M),
  init_delta(M),
  M:(dynamic exp_found/2, setting_trill/2),
  retractall(M:setting_trill(_,_)).
  %foreach(setting_trill_default(DefaultSetting,DefaultVal),assert(M:setting_trill(DefaultSetting,DefaultVal))).

set_up_tableau(M):-
  % TODO move to KB loading
  %setting_trill_default(det_rules,DetRules),
  %setting_trill_default(nondet_rules,NondetRules),
  %set_tableau_expansion_rules(M:DetRules,NondetRules). 
  prune_tableau_rules(M).


%  creation of the query anon individual
query_ind(trillan(0)).

/****************************
REASONER'S RULE MANAGEMENT
*****************************/
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
 * add_all_to_abox_and_clashes(+M:module,+L:list,+Tableau:tableau,+ABox0:abox,--ABox:abox,+Clashes0:list,--Clashes:list)
 * 
 * Adds to ABox0 the assertions given in L and updates Clashes0 accordingly.
 * NOTE: does not update the a tableau. Use add_to_tableau to update the tableau.
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

% -----------------------------------
% QUERY MANAGEMENT
% -----------------------------------
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
  collect_individuals(M,QueryType,QueryArgs,ConnectedInds), 
  ( dif(ConnectedInds,[]) ->
    ( findall((classAssertion(Class,Individual),[[classAssertion(Class,Individual)]-[]]),(member(Individual,ConnectedInds),M:classAssertion(Class,Individual)),LCA),
      findall((propertyAssertion(Property,Subject, Object),[[propertyAssertion(Property,Subject, Object)]-[]]),(member(Subject,ConnectedInds),M:propertyAssertion(Property,Subject, Object),dif('http://www.w3.org/2000/01/rdf-schema#comment',Property)),LPA),
      % findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property),propertyAssertion(SubProperty,Subject,Object)]),subProp(M,SubProperty,Property,Subject,Object),LSPA),
      findall(nominal(NominalIndividual),(member(NominalIndividual,ConnectedInds),M:classAssertion(oneOf(_),NominalIndividual)),LNA),
      findall((differentIndividuals(Ld),[[differentIndividuals(Ld)]-[]]),(M:differentIndividuals(Ld),intersect(Ld,ConnectedInds)),LDIA),
      findall((sameIndividual(L),[[sameIndividual(L)]-[]]),(M:sameIndividual(L),intersect(L,ConnectedInds)),LSIA)
    )
    ; % all the individuals
    ( findall((classAssertion(Class,Individual),[[classAssertion(Class,Individual)]-[]]),M:classAssertion(Class,Individual),LCA),
      findall((propertyAssertion(Property,Subject, Object),[[propertyAssertion(Property,Subject, Object)]-[]]),(M:propertyAssertion(Property,Subject, Object),dif('http://www.w3.org/2000/01/rdf-schema#comment',Property)),LPA),
      % findall((propertyAssertion(Property,Subject,Object),[subPropertyOf(SubProperty,Property),propertyAssertion(SubProperty,Subject,Object)]),subProp(M,SubProperty,Property,Subject,Object),LSPA),
      findall(nominal(NominalIndividual),M:classAssertion(oneOf(_),NominalIndividual),LNA),
      findall((differentIndividuals(Ld),[[differentIndividuals(Ld)]-[]]),M:differentIndividuals(Ld),LDIA),
      findall((sameIndividual(L),[[sameIndividual(L)]-[]]),M:sameIndividual(L),LSIA)
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
  graph_edge(Ind1,Ind2,T0),!.

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
  CHECK FUNCTIONS
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

% -----------------------------------

% -----------------------------------
% JUSTIFICATIONS MANAGEMENT
% -----------------------------------
% TODO merge tornado
% TODO change name of empty and initial to a clearer name
initial_expl(_M,[[]-[]]):-!.

empty_expl(_M,[[]-[]]):-!.

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

and_f2(L1,CP1,[H2-CP2|T2],[H-CP|T]):-
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


% ===================================
% CHOICE POINTS MANAGEMENT
% ===================================

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

% ===================================
% OWL AXIOM RELATED PREDICATES
% ===================================

% Negates a given concept
neg_class(complementOf(C),C):- !.

neg_class(C,complementOf(C)).

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
% L0 may contain also sameIndividual/2 literals.
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





















:- multifile kb_prefixes/1.
:- use_module(library(utility_translation)).