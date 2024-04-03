


% get_explanation(M,Expl):-
    % ottengo tableau da assertion
    % applico regole con apply_rule finchè non arrivo a clash
    % prendo explanation e la invio
    % se modify_abox aggiunge clash restituisce explanation altrimenti richiama apply_rule
    %   ad esmepio, se modify_abox trova clash non fallisce, altrimenti fallisce e
    %   di seguito si ha una seconda modify_abox che  richiama applicazione regole
    % serve modificare regole

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

apply_all_rules(M,Tab0,EA,Tab,Expl):-
    M:setting_trill(det_rules,Rules),
    apply_det_rules(M,Rules,Tab0,EA,Tab1),
    continue(M,Rules,Tab0,EA,Tab1,Tab,Expl).

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