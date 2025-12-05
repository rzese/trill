/** <module> ontology_parser

This module provides the abstract interface for OWL ontology parsers in TRILL.
It serves as a facade that manages the initialization, loading, and switching
between different parser implementations. The module also defines the abstract
interface predicates that all parser implementations must provide.

TRILL supports multiple parser backends:
  - internal: The original parser based on the Thea OWL library, handles TRILL
              syntax and OWL/RDF files
  - wrapper: Uses Java OWL API via JPL, parses the ontology and stores axioms
             in the Prolog database
  - java: Uses Java OWL API and maintains reference to Java objects during inference

This module provides:
  1. Parser loading/unloading predicates
  2. Abstract axiom search predicates (multifile)
  3. Query argument validation
  4. Setup/cleanup hooks for parser implementations

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(ontology_parser,
          [ % parser loading
            unload_all_parsers/0,
            load_default_parser/1,
            load_parser_module/1,
            % ====
            % expand_all_ns/4,
            % ====     
            check_query_args/4,
            set_up_parser/1, clean_up_parser/1,
            get_axiom_subClassOf/3, get_axiom_equivalentClasses/2,
            get_axiom_disjointClasses/2, get_axiom_disjointUnion/3,
            get_axiom_subPropertyOf/3, get_axiom_equivalentProperties/2,
            get_axiom_differentIndividuals/2, get_axiom_sameIndividual/2,
            get_axiom_classAssertion/3, get_axiom_propertyAssertion/4,
            get_axiom_propertyRange/3, get_axiom_propertyDomain/3, 
            get_axiom_transitiveProperty/2,
            get_axiom_symmetricProperty/2, get_axiom_inverseProperties/3,
            get_axiom_annotationAssertion/4,
            %---------
            add_rule/2,
            add_rule_from_functor/2,
            get_rules/2
          ]).


% Meta-predicate declarations for module-aware axiom retrieval
:- meta_predicate check_query_args(+,+,+,-).
:- meta_predicate get_axiom_subClassOf(+,-,-).
:- meta_predicate get_axiom_subPropertyOf(+,-,-).
:- meta_predicate get_axiom_equivalentClasses(+,-).
:- meta_predicate get_axiom_differentIndividuals(+,-).
:- meta_predicate get_axiom_sameIndividual(+,-). 
:- meta_predicate get_axiom_propertyAssertion(+,-,-,-).
:- meta_predicate get_axiom_classAssertion(+,-,-). 
:- meta_predicate get_axiom_propertyRange(+,-,-).
:- meta_predicate get_axiom_propertyDomain(+,-,-). 
:- meta_predicate get_axiom_disjointClasses(+,-).
:- meta_predicate get_axiom_disjointUnion(+,-,-). 
:- meta_predicate get_axiom_transitiveProperty(+,-).
:- meta_predicate get_axiom_symmetricProperty(+,-). 
:- meta_predicate get_axiom_inverseProperties(+,-,-).
:- meta_predicate get_axiom_equivalentProperties(+,-). 
:- meta_predicate get_axiom_annotationAssertion(+,-,-,-).

/*****************************
  LOADING PARSER
  
  This section handles the dynamic loading and unloading of parser modules.
  Only one parser module should be active at a time.
******************************/

%% Message hook for missing JPL library
prolog:message(no_jpl) -->
  [ 'JPL not available! Use of old parsing library handling only TRILL syntax and OWL/RDF files.' ].

%% Message hook for unknown parser specification
prolog:message(wrong_parser(Parser)) -->
  [ 'Unknown parser: ~w' -[Parser] ].

/*
load_best_library :- fail,
    use_module(library(jpl)),!,
    set_augmented_classpath,
    use_module(library(javaOWLAPI_parser)).

load_best_library :- !,
    print_message(warning, no_jpl),
    use_module(library(internal_parser)).

set_augmented_classpath :-
    % The folder you want to add
    NewFolder = './target/prob-owlapi-2.0.8.jar',

    % Get existing CLASSPATH env var (not the JVM one, but often aligns)
    (   getenv('CLASSPATH', ExistingCP)
    ->  true
    ;   ExistingCP = ''
    ),

    % On Windows, use ; separator
    atomic_list_concat([ExistingCP, NewFolder], ';', FullCP),
    atomic_list_concat(['-Djava.class.path=', FullCP], JVMOpt),

    % Set JVM options
    jpl_set_default_jvm_opts([JVMOpt]).
*/

/**
 * unload_all_parsers is det
 *
 * Unloads all currently loaded parser modules.
 * This ensures a clean state before loading a different parser.
 * Currently unloads wrapper_parser and internal_parser modules.
 */
unload_all_parsers :-
  unload_file(library(wrapper_parser)),
  unload_file(library(internal_parser)),
  unload_file(library(encapsulated_parser)).

/**
 * load_default_parser(+Module:atom) is det
 *
 * Loads the parser specified in the module's settings.
 * Retrieves the parser type from the setting_trill(parser, Parser) fact
 * and loads the corresponding parser module.
 *
 * @param Module The module context containing parser settings
 */
load_default_parser(M):-
  M:setting_trill(parser,Parser),
  load_parser_module(Parser).

/**
 * load_parser_module(+Parser:atom) is det
 *
 * Loads a specific parser module by name.
 * Supported parsers:
 *   - java: Uses ontology_parser_test1 (Java OWL API with persistent Java refs)
 *   - wrapper: Uses wrapper_parser (Java OWL API, stores axioms in Prolog DB)
 *   - internal: Uses internal_parser (Pure Prolog, based on Thea library)
 *
 * If an unknown parser is specified, falls back to internal parser with a warning.
 *
 * @param Parser The parser type to load (java, wrapper, or internal)
 */
load_parser_module(java):-!,
  unload_all_parsers,
  consult(library(encapsulated_parser)),write('encapsulated_parser').
load_parser_module(wrapper):-!,
  unload_all_parsers,
  consult(library(wrapper_parser)),write('wrapper_parser').
load_parser_module(Parser):- %Fallback to internal
  unload_all_parsers,
  ( dif(Parser,internal) -> print_message(warning, wrong_parser(Parser)) ; true ),
  consult(library(internal_parser)),write('internal_parser').

/*****************************
  ABSTRACT UTILITY PREDICATES
  
  The following predicates are declared as multifile to allow
  different parser implementations to provide their own definitions.
******************************/


/********************************
  AXIOMS SEARCH
  
  These multifile predicates define the abstract interface for
  retrieving axioms from the knowledge base. Each parser module
  must implement these predicates according to its storage format.
*********************************/

:- multifile get_axiom_subClassOf/3, get_axiom_subPropertyOf/3,
             get_axiom_equivalentClasses/2, get_axiom_differentIndividuals/2,
             get_axiom_sameIndividual/2, get_axiom_propertyAssertion/4,
             get_axiom_classAssertion/3, get_axiom_propertyRange/3,
             get_axiom_propertyDomain/3, get_axiom_disjointClasses/2,
             get_axiom_disjointUnion/3, get_axiom_transitiveProperty/2,
             get_axiom_symmetricProperty/2, get_axiom_inverseProperties/3,
             get_axiom_equivalentProperties/2, get_axiom_annotationAssertion/4.

/********************************
  CLASSES, PREDICATES AND
  INDIVIDUALS MANAGEMENT
  
  Predicates for retrieving lists of entities defined in the KB.
*********************************/
%:- multifile get_classes_list/2.

/**
 * check_query_args(+Module:atom, +QueryType:atom, +QueryArgs:list, -ExpandedArgs:list) is semidet
 *
 * Validates and expands query arguments using namespace prefixes.
 * Checks that all referenced entities exist in the knowledge base.
 * 
 * Fails with a warning message if any required IRIs don't exist in the KB.
 *
 * @param Module The module context
 * @param QueryType The type of query (io, pv, sc, un, it)
 * @param QueryArgs The raw query arguments to validate
 * @param ExpandedArgs The validated and expanded arguments
 */
check_query_args(M,QT,QA,QAEx):-
  from_query_type_to_args_type(QT,AT),
  check_query_args_1(M,AT,QA,QAExT,NotEx),!,
  check_query_not_existent_args(QA,QAExT,NotEx,QAEx),!.

/**
 * check_query_not_existent_args(+OrigArgs:list, +ExpandedArgs:list, +NotFound:list, -FinalArgs:list) is semidet
 *
 * Handles query arguments that were not found in the knowledge base.
 * For unsat queries (single arg), prepends 'unsat' marker.
 * For inconsistent_theory queries (no args), returns special marker.
 * Fails with warning if any arguments weren't found.
 *
 * @param OrigArgs Original query arguments
 * @param ExpandedArgs Successfully expanded arguments
 * @param NotFound Arguments not found in KB
 * @param FinalArgs Final processed arguments
 */
check_query_not_existent_args(QA,QAExT,[],QAEx) :- !,
  ( length(QA,1) -> 
    QAEx = ['unsat'|QAExT]
    ;
    ( length(QA,0) -> QAEx = ['inconsistent','kb'] ; QAEx = QAExT)
  ).
check_query_not_existent_args(_QA,_QAExT,NotEx,_QAEx) :-
  print_message(warning,iri_not_exists(NotEx)),!,fail.

/**
 * from_query_type_to_args_type(+QueryType:atom, -ArgTypes:list) is det
 *
 * Maps query types to their expected argument types for validation.
 *   - io (instanceOf): [class, ind]
 *   - pv (property_value): [prop, ind, ind]
 *   - sc (sub_class): [class, class]
 *   - un (unsat): [class]
 *   - it (inconsistent_theory): []
 *
 * @param QueryType The query type identifier
 * @param ArgTypes List of expected argument types
 */
from_query_type_to_args_type(io,[class,ind]):- !.
from_query_type_to_args_type(pv,[prop,ind,ind]):- !.
from_query_type_to_args_type(sc,[class,class]):- !.
from_query_type_to_args_type(un,[class]):- !.
from_query_type_to_args_type(it,[]):- !.

%% Multifile hook for parser-specific argument checking
:- multifile check_query_args_1/5.

% ========================================
% Parser Setup and Cleanup Hooks
% ========================================

%% Multifile hooks that parser implementations must provide
:- multifile set_up_parser/1.
:- multifile clean_up_parser/1.

% ========================================
% Retrieve list of rules for pruning rule in trill
% ========================================
/**
 * add_rule(+Module:string, +Rule:string) is det
 *
 * This predicate adds to the rules list the rule in Rule
 */
add_rule(M,Rule):-
  M:rule(Rule),!.
  
add_rule(M,Rule):- !,
  assert(M:rule(Rule)).

get_rules(M,Rules):-
  findall(Rule,M:rule(Rule),Rules), !.

add_rule_from_functor(M,Functor):-
  funct_to_rule(M,Functor),!.

add_rule_from_functor(_M,_F):-!.

funct_to_rule(M,intersectionOf):-
  ontology_parser:add_rule(M,and_rule).
funct_to_rule(M,transitiveProperty):-
  ontology_parser:add_rule(M,forall_plus_rule).
funct_to_rule(M,unionOf):-
  ontology_parser:add_rule(M,or_rule).
funct_to_rule(M,oneOf):-
  ontology_parser:add_rule(M,o_rule).
funct_to_rule(M,someValuesFrom):-
  ontology_parser:add_rule(M,exists_rule).
funct_to_rule(M,allValuesFrom):-
  ontology_parser:add_rule(M,forall_rule).
funct_to_rule(M,minCardinality):-
  ontology_parser:add_rule(M,min_rule).
funct_to_rule(M,maxCardinality):-
  ontology_parser:add_rule(M,max_rule),
  ontology_parser:add_rule(M,ch_rule).
funct_to_rule(M,exactCardinality):-
  ontology_parser:add_rule(M,min_rule),
  ontology_parser:add_rule(M,max_rule),
  ontology_parser:add_rule(M,ch_rule).

% ========================================
% Sandbox Safety Declarations
% ========================================

:- multifile sandbox:safe_primitive/1.

% Declare all exported predicates as safe for sandboxed execution
sandbox:safe_primitive(ontology_parser:check_query_args(_,_,_,_)).
sandbox:safe_meta(get_axiom_subClassOf(_,_,_),[]).
sandbox:safe_meta(get_axiom_subPropertyOf(_,_,_),[]).
sandbox:safe_meta(get_axiom_equivalentClasses(_,_),[]).
sandbox:safe_meta(get_axiom_differentIndividuals(_,_),[]).
sandbox:safe_meta(get_axiom_sameIndividual(_,_),[]). 
sandbox:safe_meta(get_axiom_propertyAssertion(_,_,_,_),[]).
sandbox:safe_meta(get_axiom_classAssertion(_,_,_),[]). 
sandbox:safe_meta(get_axiom_propertyRange(_,_,_),[]).
sandbox:safe_meta(get_axiom_propertyDomain(_,_,_),[]). 
sandbox:safe_meta(get_axiom_disjointClasses(_,_),[]).
sandbox:safe_meta(get_axiom_disjointUnion(_,_,_),[]). 
sandbox:safe_meta(get_axiom_transitiveProperty(_,_),[]).
sandbox:safe_meta(get_axiom_symmetricProperty(_,_),[]). 
sandbox:safe_meta(get_axiom_inverseProperties(_,_,_),[]).
sandbox:safe_meta(get_axiom_equivalentProperties(_,_),[]). 
sandbox:safe_meta(get_axiom_annotationAssertion(_,_,_,_),[]).
%sandbox:safe_meta(get_classes_list(_,_),[]).
