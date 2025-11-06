/** <module> parse_ontology

This module manages the initialization of the parser for OWL KBs.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(parse_ontology, [get_module/1]).

:- initialization(load_best_library).


load_best_library :-
    use_module(library(jpl)),!,
    set_augmented_classpath.

load_best_library :- !,
    print_message(warning, 'JPL not available! Use of old parsing library handling only TRILL syntax and OWL/RDF files.'),
    use_module(library(utility_translation)).

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

