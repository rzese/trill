/** <module> trill_get_expl

This module implements the explanation extraction algorithm for TRILL.
It processes the tableau to find explanations (justifications) for queries.

The main workflow is:
1. Iterate through the expansion queue extracting assertions to process
2. Apply all applicable tableau expansion rules (deterministic and non-deterministic)
3. Check for clashes (contradictions) that indicate query entailment
4. Extract explanations from clashes

An explanation in TRILL is a minimal set of axioms from the knowledge base
that, together, entail the query. Multiple explanations may exist for a
single query.

The module implements a depth-first search with backtracking to find
all explanations when requested.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

% get_explanation(M,Expl):-
    % ottengo tableau da assertion (get tableau from assertion)
    % applico regole con apply_rule finchè non arrivo a clash (apply rules until clash)
    % prendo explanation e la invio (take explanation and send it)
    % se modify_abox aggiunge clash restituisce explanation altrimenti richiama apply_rule
    %   ad esmepio, se modify_abox trova clash non fallisce, altrimenti fallisce e
    %   di seguito si ha una seconda modify_abox che  richiama applicazione regole
    %   (if modify_abox adds clash it returns explanation otherwise it calls apply_rule again)
    % serve modificare regole (need to modify rules)

/**
 * get_explanation(+Module:atom, +Tableau:dict, -Explanation:list) is nondet
 *
 * Extracts one explanation from the tableau expansion process.
 * This predicate is non-deterministic and can backtrack to find multiple explanations.
 *
 * The predicate fails if the expansion queue is exhausted and asserts the final
 * tableau state for later resumption with resume_query/1.
 *
 * @param Module The module context for the knowledge base
 * @param Tableau The current tableau state
 * @param Explanation The extracted explanation (set of axioms)
 */
get_explanation(M,Tab,_):-
    test_end_expand_queue(M,Tab),!,
    assert(M:tab_end(Tab)),
    fail.

get_explanation(M,Tab0,Expl):-
    extract_current_from_expansion_queue(Tab0,EA),
    apply_all_rules(M,Tab0,EA,Tab1,Expl0),
    ( dif(Expl0,[]) ->
        Expl = Expl0
        ;
        get_explanation(M,Tab1,Expl)
    ).

/**
 * apply_all_rules(+Module:atom, +Tab0:dict, +EA:term, -Tab:dict, -Expl:list) is nondet
 *
 * Applies all applicable tableau expansion rules to the current assertion.
 * First applies deterministic rules, then checks for explanations from clashes.
 *
 * @param Module The module context
 * @param Tab0 Initial tableau state
 * @param EA The current expansion assertion to process
 * @param Tab Updated tableau state after rule application
 * @param Expl Explanations found (empty if none found yet)
 */
apply_all_rules(M,Tab0,EA,Tab,Expl):-
    M:setting_trill(det_rules,Rules),
    apply_det_rules(M,Rules,Tab0,EA,Tab1),
    continue(M,Rules,Tab0,EA,Tab1,Tab,Expl).

/**
 * continue(+Module:atom, +Rules:list, +Tab0:dict, +EA:term, +Tab1:dict, -Tab:dict, -Expl:list) is nondet
 *
 * Continues the tableau expansion after deterministic rule application.
 * Checks for clashes to extract explanations, or continues with next assertion.
 *
 * @param Module The module context
 * @param Rules The list of expansion rules being used
 * @param Tab0 Original tableau before rule application
 * @param EA Current expansion assertion
 * @param Tab1 Tableau after deterministic rules
 * @param Tab Final tableau state
 * @param Expl Extracted explanations
 */
continue(M,Rules,_Tab0,EA,Tab1,Tab1,Expl):-
    qa(QueryArgs),
    find_expls(M,[Tab1],QueryArgs,Expl).

continue(M,Rules,Tab0,_EA,Tab1,Tab,Expl):-
    ( test_end_apply_rule(M,Tab0,Tab1) ->
        ( set_next_from_expansion_queue(Tab0,_EA,Tab), 
          Expl=[]
        ) 
        ;
        apply_all_rules(M,Tab1,EA,Tab,Expl)
    ).