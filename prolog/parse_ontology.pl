/** <module> parse_ontology

This module manages the initialization of the parser for OWL KBs.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(parse_ontology, [expand_all_ns/4, expand_all_ns/5,
                           is_axiom/1, axiom/1, kb_prefixes/1,
                           add_kb_prefix/2, add_kb_prefixes/1, remove_kb_prefix/2, remove_kb_prefix/1,
                           add_axiom/1, add_axioms/1, remove_axiom/1, remove_axioms/1,
                           load_kb/1, load_owl_kb/1, load_owl_kb_from_string/1]).

:- initialization(load_best_library).


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

/*****************************
  LOADING PARSER
******************************/

prolog:message(noJPL) -->
  [ 'JPL not available! Use of old parsing library handling only TRILL syntax and OWL/RDF files.' ].

load_best_library :-fail,
    use_module(library(jpl)),!,
    set_augmented_classpath.

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
  UTILITY PREDICATES
******************************/

%defined in internal_parser
:- multifile kb_prefixes/1,
             add_kb_prefix/2, add_kb_prefixes/1,
             remove_kb_prefix/2, remove_kb_prefix/1.
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


:- multifile load_kb/1, load_owl_kb/1, load_owl_kb_from_string/1, expand_all_ns/4, expand_all_ns/5, is_axiom/1.


:- multifile sandbox:safe_primitive/1.

sandbox:safe_primitive(parse_ontology:load_kb(_)).
sandbox:safe_primitive(parse_ontology:load_owl_kb(_)).
sandbox:safe_primitive(parse_ontology:load_owl_kb_from_string(_)).
sandbox:safe_primitive(parse_ontology:expand_all_ns(_,_,_,_)).
sandbox:safe_primitive(parse_ontology:expand_all_ns(_,_,_,_,_)).
sandbox:safe_primitive(parse_ontology:is_axiom(_)).
sandbox:safe_meta(parse_ontology:axiom(_),[]).
sandbox:safe_meta(parse_ontology:kb_prefixes(_),[]).
sandbox:safe_meta(parse_ontology:add_kb_prefix(_,_),[]).
sandbox:safe_meta(parse_ontology:add_kb_prefixes(_),[]).
sandbox:safe_meta(parse_ontology:remove_kb_prefix(_,_),[]).
sandbox:safe_meta(parse_ontology:remove_kb_prefix(_),[]).
sandbox:safe_meta(parse_ontology:add_axiom(_),[]).
sandbox:safe_meta(parse_ontology:add_axioms(_),[]).
sandbox:safe_meta(parse_ontology:load_kb(_),[]).
sandbox:safe_meta(parse_ontology:load_owl_kb(_),[]).

