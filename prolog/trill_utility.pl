/** <module> trill_utility

This module provides utility predicates shared across all TRILL modules.
It contains helper predicates for module management, context detection,
and other cross-cutting concerns that are needed by multiple components
of the TRILL reasoning system.

The primary utility provided is get_module/1, which determines the current
execution context module, supporting both pengine-based web execution
and standard Prolog execution.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(trill_utility, [get_module/1]).

:- meta_predicate get_module(-).
:- multifile sandbox:safe_meta/2.

%% Sandbox safety declaration for get_module/1
%  Allows get_module/1 to be safely used in sandboxed environments like SWISH.
sandbox:safe_meta(trill_utility:get_module(),[]).

/**
 * get_module(-Module:atom) is det
 *
 * Determines the current execution module context.
 * 
 * This predicate is essential for TRILL's modular architecture, as it allows
 * predicates to dynamically identify the module they are operating within.
 * This is particularly important when TRILL is used in pengine-based web
 * applications (like SWISH) where each query runs in its own isolated module.
 *
 * The predicate works in two modes:
 *   1. Pengine mode: If running within a pengine, retrieves the pengine's module
 *   2. Standard mode: Otherwise, uses the prolog_load_context to get the module
 *
 * @param Module The atom representing the current execution module
 *
 * @example
 *   ?- get_module(M).
 *   M = user.
 */
get_module(M):- 
  pengine_self(Self),
  pengine_property(Self,module(M)),!.  
get_module(M):- !,
  prolog_load_context(module,M).



