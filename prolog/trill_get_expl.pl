


% get_explanation(M,Expl):-
    % ottengo tableau da assertion
    % applico regole con apply_rule finchè non arrivo a clash
    % prendo explanation e la invio
    % se modify_abox aggiunge clash restituisce explanation altrimenti richiama apply_rule
    %   ad esmepio, se modify_abox trova clash non fallisce, altrimenti fallisce e
    %   di seguito si ha una seconda modify_abox che  richiama applicazione regole
    % serve modificare regole
    