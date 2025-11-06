/** <module> trill_utility

This module gives utility predicates for all the otehr modules.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(trill_utility, [get_module/1,add_kb_atoms/3, set_up_parser/1]).

:- meta_predicate get_module(-).
:- multifile sandbox:safe_meta/2.

sandbox:safe_meta(parse_ontology:get_module(),[]).

get_module(M):-
  pengine_self(Self),
  pengine_property(Self,module(M)),!.  
get_module(M):- !,
  prolog_load_context(module,M).


add_kb_atoms(_M,_Type,[]):-!.

add_kb_atoms(M,Type,[H|T]):-
  M:kb_atom(KBA0),
  L=KBA0.Type,
  ( memberchk(H,L) -> 
      true
    ;
      ( retractall(M:kb_atom(_)),
        KBA=KBA0.put(Type,[H|L]),
        assert(M:kb_atom(KBA))
      )
  ),
  add_kb_atoms(M,Type,T).


:- multifile set_up_parser/1.