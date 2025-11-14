/** <module> javaOWLAPI_parser

This module implements the ontology_parser interface.
It uses Java OWL API and JPL to parse an ONWL ontology.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(javaOWLAPI_parser, []).

:- use_module(library(trill_utility)).

/*****************************/

/************************************
 * 
 * ABSTRACT PREDICATES FROM
 * ontology_parser
 * 
 * In the following there is the
 * implementation of the abstract
 * predicates of the ontology_parser
 * interface.
 * 
 ************************************/

/******************************/

/********************************
  AXIOMS MANAGEMENT
*********************************/
%% axiom(:Axiom)
% The main component of an OWL 2 ontology is a set of axioms - statements that say what is true in the domain being modeled.
% @see classAxiom/1, propertyAxiom/1, fact/1
:- multifile ontology_parser:axiom/1.

ontology_parser:axiom(M:A) :- classAxiom(M:A).
ontology_parser:axiom(M:A) :- propertyAxiom(M:A).
ontology_parser:axiom(M:hasKey(A,B)) :- M:hasKey(A,B).
ontology_parser:axiom(M:A) :- fact(M:A).
ontology_parser:axiom(M:A) :- declarationAxiom(M:A).
%axiom(annotation(A,B,C)) :-
%	annotation(A,B,C). % CJM-treat annotations as axioms

:- multifile ontology_parser:add_axiom/1.
ontology_parser:add_axiom(M:Ax):-
  assert(M:addKBName),
  %init_kb_atom(M),
  create_and_assert_axioms(M,Ax),!,
  retractall(M:addKBName),
  ontology_parser:update_tabs(M,Ax),!.

prolog:message(axiom_not_added(Ax,M)) -->
  [ 'Problems in adding axiom ~w ~w' -[Ax,M] ].

ontology_parser:add_axiom(M:Ax):-
  print_message(warning,axiom_not_added(Ax,M)).

:- multifile ontology_parser:add_axioms/1.
ontology_parser:add_axioms(_:[]).

ontology_parser:add_axioms(M:[H|T]) :-
  ontology_parser:add_axiom(M:H),
  ontology_parser:add_axioms(M:T).

:- multifile ontology_parser:remove_axiom/1.
ontology_parser:remove_axiom(M:Ax):-
  %print_message(warning,under_development),
  ( M:ns4query(NSList) -> true; NSList = []),
  expand_axiom(M,Ax,NSList,ExpAx),
  retract_axiom(M,ExpAx),
  retractall(M:owl(ExpAx,'ont')),!,
  trill:reset_query.


/*
ontology_parser:remove_axiom(M:subClassOf(C,D)):-
  print_message(warning,under_development),
  ( M:ns4query(NSList) -> true; NSList = []),
  expand_axiom(M,subClassOf(C,D),NSList,subClassOf(ExpC,ExpD)),
  remove_subClassOf(M,ExpC,ExpD),
  retract_axiom(M,subClassOf(ExpC,ExpD)),
  retractall(M:owl(subClassOf(ExpC,ExpD),'ont')),!.

ontology_parser:remove_axiom(M:Ax):-
  print_message(warning,under_development),
  ( M:ns4query(NSList) *-> true; NSList = []),
  Ax =.. [P|Args],
  ( (length(Args,1), Args = [IntArgs], is_list(IntArgs)) -> 
       ( expand_all_ns(M,IntArgs,NSList,false,ArgsExp),
         AxEx =.. [P,ArgsExp]
       )
     ;
       ( expand_all_ns(M,Args,NSList,false,ArgsExp),
         AxEx =.. [P|ArgsExp]
       )
  ),
  retract_axiom(M,AxEx),
  retractall(M:owl(AxEx,'ont')),!.
*/

:- multifile ontology_parser:remove_axioms/1.
ontology_parser:remove_axioms(_:[]):-!.

ontology_parser:remove_axioms(M:[H|T]) :-
  ontology_parser:remove_axiom(M:H),
  ontology_parser:remove_axioms(M:T).

test_and_assert(M,Ax,O):-
  (\+ M:owl(Ax,O) ->
    (assert_axiom(M,Ax,O), assert(M:owl(Ax,O)))
   ;
    true
  ).

/*
create_and_assert_axioms(M,Axiom) :-
  Axiom=..[P|Args],
  ( M:ns4query(NSList) -> true; NSList = []),
  ( (length(Args,1), Args = [IntArgs], is_list(IntArgs)) -> 
       ( expand_all_ns(M,IntArgs,NSList,ArgsExp),
         ExpAxiom =.. [P,ArgsExp]
       )
     ;
       ( expand_axiom(M,Axiom,NSList,ExpAxiom)
         %NewTRILLAxiom =.. [P|ArgsExp]
       )
  ),
  test_and_assert(M,ExpAxiom,'ont').
*/

create_and_assert_axioms(M,Axiom) :-
  ( M:ns4query(NSList) -> true; NSList = []),
  expand_axiom(M,Axiom,NSList,ExpAxiom),
  test_and_assert(M,ExpAxiom,'ont').


:- multifile ontology_parser:is_axiom/1.
/**
 * is_axiom(?Axiom:string) is det
 *
 * This predicate unifies Pred with one of the possible type of axioms managed by TRILL and 
 * by the translation module.
 */
ontology_parser:is_axiom(Axiom) :-
	functor(Axiom,Pred,Arity),
	axiompred(Pred/Arity),!.

/********************************
  AXIOMS SEARCH
*********************************/

:- multifile ontology_parser:get_axiom_subClassOf/3, ontology_parser:get_axiom_subPropertyOf/3,
             ontology_parser:get_axiom_equivalentClasses/2, ontology_parser:get_axiom_differentIndividuals/2,
             ontology_parser:get_axiom_sameIndividual/2, ontology_parser:get_axiom_propertyAssertion/4,
             ontology_parser:get_axiom_classAssertion/3, ontology_parser:get_axiom_propertyRange/3,
             ontology_parser:get_axiom_propertyDomain/3, ontology_parser:get_axiom_disjointClasses/2,
             ontology_parser:get_axiom_disjointUnion/3, ontology_parser:get_axiom_transitiveProperty/2,
             ontology_parser:get_axiom_symmetricProperty/2, ontology_parser:get_axiom_inverseProperties/3,
             ontology_parser:get_axiom_equivalentProperties/2, ontology_parser:get_axiom_annotationAssertion/4.


ontology_parser:get_axiom_subClassOf(M,A,B):-
  M:subClassOf(A,B).

ontology_parser:get_axiom_subPropertyOf(M,R,S):-
  M:subPropertyOf(R,S).

ontology_parser:get_axiom_equivalentClasses(M,L):-
  M:equivalentClasses(L).

ontology_parser:get_axiom_differentIndividuals(M,SI):-
  M:differentIndividuals(SI).

ontology_parser:get_axiom_sameIndividual(M,SI):-
  M:sameIndividual(SI).

ontology_parser:get_axiom_propertyAssertion(M,P,S,O):-
  M:propertyAssertion(P,S,O).

ontology_parser:get_axiom_classAssertion(M,C,I):-
  M:classAssertion(C,I).

ontology_parser:get_axiom_propertyRange(M,P,D):-
  M:propertyRange(P,D).

ontology_parser:get_axiom_propertyDomain(M,P,D):-
  M:propertyDomain(P,D).

ontology_parser:get_axiom_disjointClasses(M,L):-
  M:disjointClasses(L).

ontology_parser:get_axiom_disjointUnion(M,C,L):-
  M:disjointUnion(C,L).

ontology_parser:get_axiom_transitiveProperty(M,P):-
  M:transitiveProperty(P).

ontology_parser:get_axiom_symmetricProperty(M,P):-
  M:symmetricProperty(P).

ontology_parser:get_axiom_inverseProperties(M,P,S):-
  M:inverseProperties(P,S).

ontology_parser:get_axiom_equivalentProperties(M,L):-
  M:equivalentProperties(L).

ontology_parser:get_axiom_annotationAssertion(M,AnnIRI,Ax,AnnVal):-
  M:annotationAssertion(AnnIRI,Ax,AnnVal).

/********************************
  CLASSES, PREDICATES AND
  INDIVIDUALS MANAGEMENT
*********************************/


:- multifile ontology_parser:get_classes_list/2.

ontology_parser:get_classes_list(M,Classes):-
  M:kb_atom(KBA),
  Classes=KBA.class.

/********************************
  PREFIXES MANAGEMENT
*********************************/

% Get the KB's prefixes contained into ns4query
:- multifile ontology_parser:kb_prefixes/1.

ontology_parser:kb_prefixes(M:L):-
  M:ns4query(L),!.

% Adds a list of kb prefixes into ns4query
:- multifile ontology_parser:add_kb_prefixes/1.

ontology_parser:add_kb_prefixes(_:[]):-!.

ontology_parser:add_kb_prefixes(M:[(H=H1)|T]):-
  ontology_parser:add_kb_prefix(M:H,H1),
  ontology_parser:add_kb_prefixes(M:T).

% Adds a prefix into ns4query
:- multifile ontology_parser:add_kb_prefix/2.

ontology_parser:add_kb_prefix(M:'',B):- !,
  ontology_parser:add_kb_prefix(M:[],B).

ontology_parser:add_kb_prefix(M:A,B):-
  M:ns4query(L),!,
  (\+ member((A=_),L) ->
      (retract(M:ns4query(L)),
       append(L,[(A=B)],NL),
       assert(M:ns4query(NL))
      )
    ;
      true
   ).
   
ontology_parser:add_kb_prefix(M:A,B):-
  assert(M:ns4query([(A=B)])).

% Removes a prefix from ns4query
:- multifile ontology_parser:remove_kb_prefix/2.
ontology_parser:remove_kb_prefix(M:A,B):-
  M:ns4query(L),!,
  (member((A=B),L) ->
      (retract(M:ns4query(L)),
       delete(L,(A=B),NL),
       assert(M:ns4query(NL))
      )
    ;
      true
   ).

:- multifile ontology_parser:remove_kb_prefix/1.
ontology_parser:remove_kb_prefix(M:A):-
  M:ns4query(L),!,
  (member((A=B),L) *->
      (retract(M:ns4query(L)),
       delete(L,(A=B),NL),
       assert(M:ns4query(NL))
      )
    ;
      (member((B=A),L),! *->
        (retract(M:ns4query(L)),
         delete(L,(B=A),NL),
         assert(M:ns4query(NL))
        )
      ;
        true
     )
   ).


:- multifile ontology_parser:expand_all_ns/4.
/**
 * expand_all_ns(++Module:string,++Args:list,++NSList:list,--ExpandedArgs:list) is det
 *
 * The predicate takes as input a list containing strings and expands these strings
 * using the list of prefixes. Finally, it returns the list of expanded strings.
 * It adds names in Args to the list of known elements.
 */
ontology_parser:expand_all_ns(M,Args,NSList,ExpandedArgs):-
  ontology_parser:expand_all_ns(M,Args,NSList,true,ExpandedArgs).

:- multifile ontology_parser:expand_all_ns/5.
/**
 * expand_all_ns(++Module:string,++Args:list,++NSList:list,++AddName:boolean,--ExpandedArgs:list) is det
 *
 * The predicate takes as input a list containing strings and expands these strings
 * using the list of prefixes. Finally, it returns the list of expanded strings.
 * If AddName is set true it adds names in Args in the list of known elements.
 */
ontology_parser:expand_all_ns(_M,[],_,_,[]):- !.

ontology_parser:expand_all_ns(M,[P|T],NSList,AddName,[PNewArgs|NewArgs]):-
  is_list(P),!,
  ontology_parser:expand_all_ns(M,P,NSList,AddName,PNewArgs),
  ontology_parser:expand_all_ns(M,T,NSList,AddName,NewArgs).

ontology_parser:expand_all_ns(M,[P|T],NSList,AddName,[NP|NewArgs]):-
  expand_argument(M,P,NSList,NP),
  ontology_parser:expand_all_ns(M,T,NSList,AddName,NewArgs).

/*
expand_all_ns(M,[P|T],NSList,AddName,[NP|NewArgs]):-
  compound(P),
  P =.. [N | Args],!,
  expand_all_ns(M,Args,NSList,AddName,NewPArgs),
  NP =.. [N| NewPArgs],
  expand_all_ns(M,T,NSList,AddName,NewArgs).

expand_all_ns(M,[H|T],NSList,AddName,[H|NewArgs]):-
  check_query_arg(M,H),!,
  expand_all_ns(M,T,NSList,AddName,NewArgs).

expand_all_ns(M,[H|T],NSList,AddName,[NewArg|NewArgs]):-
  expand_ns4query(M,H,NSList,AddName,NewArg),
  expand_all_ns(M,T,NSList,AddName,NewArgs).

check_query_arg(M,Arg) :-
  atomic(Arg),!,
  trill:axiom(M:Ax),
  in_axiom(Arg,[Ax]),!,
  add_kb_atom(M,Arg).

expand_ns4query(M,NS_URL,NSList,AddName, Full_URL):- 
	nonvar(NS_URL),
	NS_URL \= literal(_),
	uri_split(NS_URL,Short_NS,Term, ':'),
	member((Short_NS=Long_NS),NSList),
	concat_atom([Long_NS,Term],Full_URL),!,
	( AddName == true *-> add_kb_atom(M,Full_URL) ; true).

expand_ns4query(M,NS_URL,NSList,AddName, Full_URL):- 
	nonvar(NS_URL),
	NS_URL \= literal(_),
	\+ sub_atom(NS_URL,_,_,_,':'),
	member(([]=Long_NS),NSList),
	concat_atom([Long_NS,NS_URL],Full_URL),!,
	( AddName == true *-> add_kb_atom(M,Full_URL) ; true).

expand_ns4query(_M,URL,_,_,URL).
*/
/*
expand_ns4query(_M,URL,_,_,URL):-
    var(URL),!.
*/


/********************************
  LOAD KNOWLEDGE BASE
*********************************/
:- multifile ontology_parser:load_kb/1, ontology_parser:load_owl_kb/1, ontology_parser:load_owl_kb_from_string/1.
/**
 * load_kb(++FileName:kb_file_name) is det
 *
 * The predicate loads the knowledge base contained in the given file. 
 * 
 */
ontology_parser:load_kb(FileName):-
  get_module(M),
  get_parser(M,Parser),
  jpl_call(Parser, 'loadOntology', [URI], Ret),
  ( dif(Ret,@(false)) -> 
    assert(M:javaOWLAPI_ontology_wrapper(Parser))
    ;
    (print_message(warning,kb_loading_error), fail)
  ).

/**
 * load_owl_kb(++FileName:kb_file_name) is det
 *
 * The predicate performs the same operations as load_kb.
 * Maintained for compatibility with internal_parser.
 */
ontology_parser:load_owl_kb(FileName):-
  ontology_parser:load_kb(FileName).

/**
 * load_owl_kb_from_string(++KB:string) is det
 *
 * The predicate loads the knowledge base contained in the given string. 
 * The knowledge base can be defined in every OWL format.
 */
ontology_parser:load_owl_kb_from_string(String):-
  get_module(M),
  get_parser(M,Parser),
  jpl_call(Parser, 'loadOntologyFromString', [String], Ret),
  ( dif(Ret,@(false)) -> 
    assert(M:javaOWLAPI_ontology_wrapper(Parser))
    ;
    (print_message(warning,kb_loading_error), fail)
  ).


/********************************
  CHECK QUERY ARGS
*********************************/ 

:- multifile ontology_parser:check_query_args_1/5.

ontology_parser:check_query_args_1(_,_,[],[],[]).

ontology_parser:check_query_args_1(M,[ATH|ATT],[H|T],[HEx|TEx],NotEx):-
  check_query_args_2(M,[ATH],[H],[HEx]),!,
  ontology_parser:check_query_args_1(M,ATT,T,TEx,NotEx).

ontology_parser:check_query_args_1(M,[_|ATT],[H|T],TEx,[H|NotEx]):-
  ontology_parser:check_query_args_1(M,ATT,T,TEx,NotEx).

% expands query arguments using prefixes and checks their existence in the kb
check_query_args_2(M,AT,L,LEx) :-
  M:ns4query(NSList),
  ontology_parser:expand_all_ns(M,L,NSList,false,LEx), %from internal_parser module
  check_query_args_presence(M,AT,LEx).

check_query_args_presence(_M,_AT,[]):-!.

check_query_args_presence(M,[class|ATT],['http://www.w3.org/2002/07/owl#Thing'|T]) :-
  check_query_args_presence(M,ATT,T).

check_query_args_presence(M,[AT|ATT],[H|T]) :-
  nonvar(H),
  atomic(H),!,
  find_atom_in_axioms(M,AT,H),%!,
  check_query_args_presence(M,ATT,T).

check_query_args_presence(M,[AT|ATT],[H|T]) :-
  nonvar(H),
  \+ atomic(H),!,
  H =.. [CE|L],
  flatten(L,L1),
  from_expression_to_args_type(CE,AT,L1,ATs),
  check_query_args_presence(M,ATs,L1),
  check_query_args_presence(M,ATT,T).

/*
check_query_args_presence(M,[_|T]):-
  check_query_args_presence(M,T).
*/

% looks for presence of atoms in kb's axioms
find_atom_in_axioms(M,class,H):-
  M:kb_atom(L1),
  ( member(H,L1.class) ),!.

find_atom_in_axioms(M,ind,H):-
  M:kb_atom(L1),
  ( member(H,L1.individual) ; member(H,L1.datatype) ),!.

find_atom_in_axioms(M,prop,H):-
  M:kb_atom(L1),
  ( member(H,L1.objectProperty) ; member(H,L1.dataProperty) ; member(H,L1.annotationProperty) ),!.

find_atom_in_axioms(_,num,H):-
  integer(H),!.

from_expression_to_args_type(complementOf,class,_,[class]) :- !.
from_expression_to_args_type(someValuesFrom,class,_,[prop,class]) :- !.
from_expression_to_args_type(allValuesFrom,class,_,[prop,class]) :- !.
from_expression_to_args_type(hasValue,class,_,[prop,ind]) :- !.
from_expression_to_args_type(hasSelf,class,_,[prop]) :- !.
from_expression_to_args_type(minCardinality,class,[_,_,_],[num,prop,class]) :- !.
from_expression_to_args_type(minCardinality,class,[_,_],[num,prop]) :- !.
from_expression_to_args_type(maxCardinality,class,[_,_,_],[num,prop,class]) :- !.
from_expression_to_args_type(maxCardinality,class,[_,_],[num,prop]) :- !.
from_expression_to_args_type(exactCardinality,class,[_,_,_],[num,prop,class]) :- !.
from_expression_to_args_type(exactCardinality,class,[_,_],[num,prop]) :- !.
from_expression_to_args_type(inverseOf,prop,_,[prop]) :- !.
from_expression_to_args_type(ExprList,AT,L1,ATs):-
  is_expr_list(ExprList,AT,ListType),!,
  create_list(ListType,L1,ATs).


is_expr_list(intersectionOf,class,class).
is_expr_list(unionOf,class,class).
is_expr_list(oneOf,class,ind).
is_expr_list(propertyChain,prop,prop).

create_list([],_,[]).

create_list([_|T],AT,[AT|ATT]):-
  create_list(T,AT,ATT).

/********************************
  PARSER MANAGEMENT
*********************************/ 

:- multifile ontology_parser:set_up_kb_loading/1.

ontology_parser:set_up_kb_loading(M):-
  retractall(M:kb_atom(_)),
  init_kb_atom(M),
  retractall(M:addKBName),
  assert(M:addKBName),
  assert(trill_input_mode(M)).
  %format("Loading knowledge base...~n",[]),
  %statistics(walltime,[_,_]).

init_kb_atom(M):-
  assert(M:kb_atom(kbatoms{annotationProperty:[],class:[],dataProperty:[],datatype:[],individual:[],objectProperty:[]})).

init_kb_atom(M,AnnProps,Classes,DataProps,Datatypes,Inds,ObjectProps):-
  assert(M:kb_atom(kbatoms{annotationProperty:AnnProps,class:Classes,dataProperty:DataProps,datatype:Datatypes,individual:Inds,objectProperty:ObjectProps})).

init_kb_atom(M,KB):-
  assert(M:kb_atom(kbatoms{annotationProperty:KB.annotationProperties,class:KB.classesName,dataProperty:KB.dataProperties,datatype:KB.datatypes,individual:KB.individuals,objectProperty:KB.objectProperties})).


:- multifile ontology_parser:clean_up_parser/1.

ontology_parser:clean_up_parser(M):-
  rdf_reset_db,
  M:(dynamic class/1, datatype/1, objectProperty/1, dataProperty/1, annotationProperty/1),
  M:(dynamic namedIndividual/1, anonymousIndividual/1, subClassOf/2, equivalentClasses/1, disjointClasses/1, disjointUnion/2),
  M:(dynamic subPropertyOf/2, equivalentProperties/1, disjointProperties/1, inverseProperties/2, propertyDomain/2, propertyRange/2),
  M:(dynamic functionalProperty/1, inverseFunctionalProperty/1, reflexiveProperty/1, irreflexiveProperty/1, symmetricProperty/1, asymmetricProperty/1, transitiveProperty/1, hasKey/2),
  M:(dynamic sameIndividual/1, differentIndividuals/1, classAssertion/2, propertyAssertion/3, negativePropertyAssertion/3),
  M:(dynamic annotationAssertion/3, annotation/3, ontology/1, ontologyAxiom/2, ontologyImport/2, ontologyVersionInfo/2),
  M:(dynamic owl/4, owl/3, owl/2, blanknode/3, outstream/1, aNN/3, annotation_r_node/4, axiom_r_node/4, owl_repository/2, trdf_setting/2),
  M:(dynamic ns4query/1),
  retractall(M:kb_atom([])),
  forall(ontology_parser:axiom(M:A),retractall(M:A)),
  retractall(M:blanknode(_,_,_)),
  retractall(M:aNN(_,_,_)),
  retractall(M:annotation_r_node(_,_,_)),
  retractall(M:axiom_r_node(_,_,_)),
  retractall(M:annotation(_,_,_)),
  retractall(M:owl(_,_,_)),
  retractall(M:owl(_,_,_,_)),
  retractall(M:owl(_,_)),
  retractall(M:ontologyAxiom(_,_)),
  retractall(M:ontologyImport(_,_)),
  retractall(M:ontologyVersionInfo(_,_)),
  retractall(M:rdf(_,_,_)).


:- multifile ontology_parser:set_up_parser/1.

ontology_parser:set_up_parser(M):-
  M:(dynamic class/1, datatype/1, objectProperty/1, dataProperty/1, annotationProperty/1),
  M:(dynamic namedIndividual/1, anonymousIndividual/1, subClassOf/2, equivalentClasses/1, disjointClasses/1, disjointUnion/2),
  M:(dynamic subPropertyOf/2, equivalentProperties/1, disjointProperties/1, inverseProperties/2, propertyDomain/2, propertyRange/2),
  M:(dynamic functionalProperty/1, inverseFunctionalProperty/1, reflexiveProperty/1, irreflexiveProperty/1, symmetricProperty/1, asymmetricProperty/1, transitiveProperty/1, hasKey/2),
  M:(dynamic sameIndividual/1, differentIndividuals/1, classAssertion/2, propertyAssertion/3, negativePropertyAssertion/3),
  M:(dynamic annotationAssertion/3, annotation/3, ontology/1, ontologyAxiom/2, ontologyImport/2, ontologyVersionInfo/2),
  M:(dynamic owl/4, owl/3, owl/2, blanknode/3, outstream/1, aNN/3, annotation_r_node/4, axiom_r_node/4, owl_repository/2, trdf_setting/2),
  M:(dynamic ns4query/1, addKBName/0),
  retractall(M:addKBName).
  %retractall(M:rules(_,_)),
  %assert(M:rules([],[])),
  %retractall(M:expressivity(_,_)),
  %assert(M:expressivity(1,[0,0,0,0,0,0])).


/* ************************************** */




/*****************************/

/************************************
 * 
 * INTERNAL PARSER IMPLEMENTATION
 * 
 * In the following there is the
 * implementation of the actual 
 * parser, exploiting Java ProbOWLAPI.
 * 
 ************************************/

/******************************/

/*****************************
  MESSAGES
******************************/
:- multifile prolog:message/1.

prolog:message(kb_loading_error) -->
  [ 'Error in loading the given file. Please, check the path.' ].


/*****************************
  PARSER INITIALIZATION
******************************/

get_parser(M,Parser):-
  M:javaOWLAPI_ontology_wrapper(Parser),!.

get_parser(M,Parser):-
  internal_parser_init(M),
  M:javaOWLAPI_ontology_wrapper(Parser),!.

internal_parser_init(M) :-
  retractall(M:javaOWLAPI_ontology_wrapper(_)),
  jpl_new('it.unife.ml.probowlapi.trill.TRILLOWLAPIOntologyWrapper',[],JRef),
  assert(M:javaOWLAPI_ontology_wrapper(JRef)).