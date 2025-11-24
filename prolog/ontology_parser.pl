/** <module> ontology_parser

This module manages the initialization of the parser for OWL KBs.
It also serves as interface for a TRILL parser.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(ontology_parser,
          [ load_kb/1,
            load_owl_kb/1,
            load_owl_kb_from_string/1,
            % ====
            % expand_all_ns/4,
            % expand_all_ns/5,
            % ====
            axiom/1,
            % multifile API used by trill.pl
            kb_prefixes/1,
            add_kb_prefix/2,
            add_kb_prefixes/1,
            remove_kb_prefix/1,
            remove_kb_prefix/2,
            add_axiom/1,
            add_axioms/1,
            remove_axiom/1,
            remove_axioms/1,
            %---------
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
            get_classes_list/2
          ]).

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
******************************/

prolog:message(noJPL) -->
  [ 'JPL not available! Use of old parsing library handling only TRILL syntax and OWL/RDF files.' ].

load_best_library :- fail,
    use_module(library(jpl)),!,
    set_augmented_classpath,
    use_module(library(javaOWLAPI_parser)).

load_best_library :- !,
    print_message(warning, noJPL),
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

/*****************************
  ABSTRACT UTILITY PREDICATES
******************************/


/********************************
  AXIOMS MANAGEMENT
*********************************/

:- multifile axiom/1,
             add_axiom/1, add_axioms/1,
             remove_axiom/1, remove_axioms/1.

/**
 * axiom(:Axiom:axiom) is det
 *
 * This predicate searches in the loaded knowledge base axioms that unify with Axiom.
 */

/**
 * add_axiom(:Axiom:axiom) is det
 *
 * This predicate adds the given axiom to the knowledge base.
 * The axiom must be defined following the TRILL syntax.
 */

/**
 * add_axioms(:Axioms:list) is det
 *
 * This predicate adds the axioms of the list to the knowledge base.
 * The axioms must be defined following the TRILL syntax.
 */

/**
 * remove_axiom(:Axiom:axiom) is det
 *
 * This predicate removes the given axiom from the knowledge base.
 * The axiom must be defined following the TRILL syntax.
 */

/**
 * remove_axioms(++Axioms:list) is det
 *
 * This predicate removes the axioms of the list from the knowledge base.
 * The axioms must be defined following the TRILL syntax.
 */

/********************************
  AXIOMS SEARCH
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
*********************************/
:- multifile get_classes_list/2.

/********************************
  PREFIXES MANAGEMENT
*********************************/

%defined in internal_parser
:- multifile kb_prefixes/1,
             add_kb_prefix/2, add_kb_prefixes/1,
             remove_kb_prefix/2, remove_kb_prefix/1.
/**
 * kb_prefix(:Prefixes:list) is det
 *
 * This predicate returns the list of prefixes used by the parser.
 */

/**
 * add_kb_prefix(:ShortPref:string,++LongPref:string) is det
 *
 * This predicate registers the alias ShortPref for the prefix defined in LongPref.
 * The empty string '' can be defined as alias.
 */

/**
 * add_kb_prefixes(:Prefixes:list) is det
 *
 * This predicate registers all the alias prefixes contained in Prefixes.
 * The input list must contain pairs alias=prefix, i.e., [('foo'='http://example.foo#')].
 * The empty string '' can be defined as alias.
 */

/**
 * remove_kb_prefix(:ShortPref:string,++LongPref:string) is det
 *
 * This predicate removes from the registered aliases the one given in input.
 */

/**
 * remove_kb_prefix(:Name:string) is det
 *
 * This predicate takes as input a string that can be an alias or a prefix and 
 * removes the pair containing the string from the registered aliases.
 */

/********************************
  LOAD KNOWLEDGE BASE
*********************************/

:- multifile load_kb/1, load_owl_kb/1, load_owl_kb_from_string/1, is_axiom/1.

% expands query arguments using prefixes and checks their existence in the kb
% returns the non-present arguments
check_query_args(M,QT,QA,QAEx):-
  from_query_type_to_args_type(QT,AT),
  check_query_args_1(M,AT,QA,QAExT,NotEx),!,
  check_query_not_existent_args(QA,QAExT,NotEx,QAEx),!.

check_query_not_existent_args(QA,QAExT,[],QAEx) :- !,
  ( length(QA,1) -> 
    QAEx = ['unsat'|QAExT]
    ;
    ( length(QA,0) -> QAEx = ['inconsistent','kb'] ; QAEx = QAExT)
  ).
check_query_not_existent_args(_QA,_QAExT,NotEx,_QAEx) :-
  print_message(warning,iri_not_exists(NotEx)),!,fail.

from_query_type_to_args_type(io,[class,ind]):- !.
from_query_type_to_args_type(pv,[prop,ind,ind]):- !.
from_query_type_to_args_type(sc,[class,class]):- !.
from_query_type_to_args_type(un,[class]):- !.
from_query_type_to_args_type(it,[]):- !.

:- multifile check_query_args_1/5.

% ========================================

:- multifile set_up_parser/1.
:- multifile clean_up_parser/1.

% ========================================

:- multifile sandbox:safe_primitive/1.

sandbox:safe_primitive(ontology_parser:load_kb(_)).
sandbox:safe_primitive(ontology_parser:load_owl_kb(_)).
sandbox:safe_primitive(ontology_parser:load_owl_kb_from_string(_)).
sandbox:safe_primitive(ontology_parser:is_axiom(_)).
sandbox:safe_meta(ontology_parser:axiom(_),[]).
sandbox:safe_meta(ontology_parser:kb_prefixes(_),[]).
sandbox:safe_meta(ontology_parser:add_kb_prefix(_,_),[]).
sandbox:safe_meta(ontology_parser:add_kb_prefixes(_),[]).
sandbox:safe_meta(ontology_parser:remove_kb_prefix(_,_),[]).
sandbox:safe_meta(ontology_parser:remove_kb_prefix(_),[]).
sandbox:safe_meta(ontology_parser:add_axiom(_),[]).
sandbox:safe_meta(ontology_parser:add_axioms(_),[]).
sandbox:safe_meta(ontology_parser:load_kb(_),[]).
sandbox:safe_meta(ontology_parser:load_owl_kb(_),[]).
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
sandbox:safe_meta(get_classes_list(_,_),[]).
