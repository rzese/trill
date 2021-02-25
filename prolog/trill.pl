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
find_explanations(M,QueryType,QueryArgs,ExplInc,QueryOptions), % here 1
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
  build_abox(M,Tableau,QueryType,QueryArgs), % will expand the KB without the query %here 5
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
REASONER INITALIZATION
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


%  creation of the query anon individual
query_ind(trillan(0)).

/****************************
ABOX INIT AND MANAGEMENT
*****************************/

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
  add_all_to_tableau(M,AddAllList,Tableau1,Tableau2), %here 6
  merge_all_individuals(M,LSIA,Tableau2,Tableau3),
  add_owlThing_list(M,Tableau3,Tableau),
  !.


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


/**
 * add_all_to_tableau(+M:module,+L:list,+Tableau0:tableau,--Tableau:tableau)
 * 
 * Adds in Tableau0 all items contained in L and returns Tableau.
 * It updates both ABox, Clashes, and Tabs
*/
add_all_to_tableau(M,L,Tableau0,Tableau):-
  get_abox(Tableau0,ABox0),
  get_clashes(Tableau0,Clashes0),
  add_all_to_abox_and_clashes(M,L,Tableau0,ABox0,ABox,Clashes0,Clashes), %here 7
  set_abox(Tableau0,ABox,Tableau1),
  set_clashes(Tableau1,Clashes,Tableau).

/**
 * add_all_to_abox_and_clashes(+M:module,+L:list,+Tableau:tableau,+ABox0:abox,--ABox:abox,+Clashes0:list,--Clashes:list)
 * 
 * Adds to ABox0 the assertions given in L and updates Clashes0 accordingly.
 */ 
add_all_to_abox_and_clashes(_,[],_,A,A,C,C).

add_all_to_abox_and_clashes(M,[(classAssertion(C,I),Expl)|T],Tab,A0,A,C0,C):-
  check_clash(M,C-I,Tab),!, %here 8
  add_to_abox(A0,(classAssertion(C,I),Expl),A1),
  add_to_clashes(C0,C-I,C1),
  add_all_to_abox_and_clashes(M,T,A1,A,C1,C).

add_all_to_abox_and_clashes(M,[(sameIndividual(LI),Expl)|T],Tab,A0,A,C0,C):-
  check_clash(M,sameIndividual(LI),Tab),!,
  add_to_abox(A0,(sameIndividual(LI),Expl),A1),
  add_to_clashes(C0,sameIndividual(LI),C1),
  add_all_to_abox_and_clashes(M,T,A1,A,C1,C).

add_all_to_abox_and_clashes(M,[(differentIndividuals(LI),Expl)|T],Tab,A0,A,C0,C):-
  check_clash(M,differentIndividuals(LI),Tab),!,
  add_to_abox(A0,(differentIndividuals(LI),Expl),A1),
  add_to_clashes(C0,differentIndividuals(LI),C1),
  add_all_to_abox_and_clashes(M,T,A1,A,C1,C).

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
  %flatten(SN0,SN1), %TODO is it necessary?
  get_abox(Tab,ABox),
  s_neighbours2(M,SN0,SN,ABox),!. %TODO previosuly s_neighbours2(M,SN1,SN1,SN,ABox) %here 10

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

% 
s_neighbours2(_,[],[],_).

s_neighbours2(M,[H|T],[H|T1],ABox):-
  s_neighbours2(M,T,T1,ABox),
  not_same_ind(M,T1,H,ABox),!.

s_neighbours2(M,[_H|T],T1,ABox):-
  s_neighbours2(M,T,T1,ABox).
  %same_ind(M,T1,H,ABox).

% -----------------------------------
% ABOX
% -----------------------------------

/* abox as a list */

% Creation of empty ABox
new_abox([]).

/*
  find & absent in abox (not find)
*/
% TODO previously find/2
find_in_abox(El,ABox):-
  member(El,ABox).

% TODO previously control/2
absent_in_abox(El,ABox):-
  \+ find_in_abox(El,ABox).


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


% Updates expansion queue. If the assertion is already included in the expansion queue,
% it is first removed and then added at the end.

% If the assertion is a concept whose expansion needs non-deterministic rules
% the assertion is added to the non-det list.
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

% Adds property assertions to det queue
update_expansion_queue(_,P,Ind1,Ind2,[DQ0,NDQ],[DQ,NDQ]):-!,
  delete(DQ0,[P,Ind1,Ind2],DQ1),
  append(DQ1,[[P,Ind1,Ind2]],DQ).


% -----------------------------------
% CLASHES
% -----------------------------------

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
  s_neighbours(M,Ind,S,Tab,SN),  %here 9
  individual_class_C(SN,C,ABox,SNC),
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
  individual_class_C(SN,C,ABox,SNC),
  length(SNC,LSS),
  dif(LSS,N),!.
  
check_clash(M,exactCardinality(N,S)-Ind,Tab):-
  %write('clash 13'),nl,
  s_neighbours(M,Ind,S,Tab,SN),
  length(SN,LSS),
  dif(LSS,N),!.

% -----------------------------------

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