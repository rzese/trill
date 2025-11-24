/** <module> trill_utility

This module gives utility predicates for all the otehr modules.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(trill_utility, [get_module/1]).

:- meta_predicate get_module(-).
:- multifile sandbox:safe_meta/2.

sandbox:safe_meta(trill_utility:get_module(),[]).

get_module(M):- 
  pengine_self(Self),
  pengine_property(Self,module(M)),!.  
get_module(M):- !,
  prolog_load_context(module,M).



