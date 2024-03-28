% ==========================================================================================================
% TABLEAU MANAGER
% ==========================================================================================================

% ======================================================================
% As Dict
% ======================================================================




/* initializers */

/**
 * new_tabelau(-EmptyTableaus:dict)
 * 
 * Initialize an empty tableau.
 */
new_tableau(tableau{
                abox:ABox, 
                tabs:Tabs, 
                clashes:[], 
                expq:ExpansionQueue
            }):-
    new_abox(ABox),
    new_tabs(Tabs),
    empty_expansion_queue(ExpansionQueue).
  
  
/**
 * init_tabelau(+ABox:abox, +Tabs:tableau, -InitializedTableaus:dict)
 * 
 * Initialize a tableau with the elements given in input.
 */
init_tableau(ABox,Tabs,tableau{abox:ABox, tabs:Tabs, clashes:[], expq:ExpansionQueue}):-
    empty_expansion_queue(ExpansionQueue).

/**
 * init_tabelau(+ABox:abox, +Tabs:tableau, +ExpansionQueue:expansion_queue, -InitializedTableaus:dict)
 * 
 * Initialize a tableau with the lements given in input.
 */
init_tableau(ABox,Tabs,ExpansionQueue,tableau{abox:ABox, tabs:Tabs, clashes:[], expq:ExpansionQueue}).

/**
 * new_abox(-ABox:list)
 * 
 * Initialize the ABox as an empty list.
 */
new_abox([]).

/**
 * new_tabs(-Tableau)
 * 
 * Initialize the tableau
 * tableau is composed of:
 * 	a directed graph T => tableau without label
 * 	a red black tree RBN => each node is a pair of inds that contains the label for the edge
 * 	a red black tree RBR => each node is a property that contains the pairs of inds
 */
new_tabs(([],ItR,RtI)):-
    rb_new(ItR),
    rb_new(RtI).

/**
 * empty_expansion_queue(-Exp_queue)
 * 
 * Initialize the expansion queue as two empty lists
 */
empty_expansion_queue([[],[]]).


/* getters and setters for Tableau */

get_abox(Tab,ABox):-
    ABox = Tab.abox.
  
set_abox(Tab0,ABox,Tab):-
    Tab = Tab0.put(abox,ABox).

get_tabs(Tab,Tabs):-
    Tabs = Tab.tabs.

set_tabs(Tab0,Tabs,Tab):-
    Tab = Tab0.put(tabs,Tabs).

get_clashes(Tab,Clashes):-
    Clashes = Tab.clashes.

set_clashes(Tab0,Clashes,Tab):-
    Tab = Tab0.put(clashes,Clashes).

get_expansion_queue(Tab,ExpansionQueue):-
    ExpansionQueue = Tab.expq.
      
set_expansion_queue(Tab0,ExpansionQueue,Tab):-
    Tab = Tab0.put(expq,ExpansionQueue).



% --------------------------------------------------------------------------------

absence_of_clashes(Tab):-
    get_clashes(Tab,Clashes),
    Clashes=[].
  
  
  
  extract_from_expansion_queue(Tab0,EA,Tab):-
    get_expansion_queue(Tab0,EQ0),
    extract_from_expansion_queue_int(EQ0,EA,EQ),
    set_expansion_queue(Tab0,EQ,Tab).
  
  extract_from_expansion_queue_int([[],[EA|T]],EA,[[],T]).
  
  extract_from_expansion_queue_int([[EA|T],NonDetQ],EA,[T,NonDetQ]).
  
  expansion_queue_is_empty(Tab):-
    get_expansion_queue(Tab,EQ),
    empty_expansion_queue(EQ).
  
  
  same_tableau(Tab1,Tab2):-
    get_abox(Tab1,ABox),
    get_abox(Tab2,ABox),
    get_tabs(Tab1,Tabs),
    get_tabs(Tab2,Tabs).
  
  
  
  
  % ===================================
  % ABOX
  % ===================================
  
  /* abox as a list */
  
  
  
   
  /* add El to ABox */
  add_to_tableau(Tableau0,El,Tableau):-
    get_abox(Tableau0,ABox0),
    add_to_abox(ABox0,El,ABox),
    set_abox(Tableau0,ABox,Tableau).
  
  remove_from_tableau(Tableau0,El,Tableau):-
    get_abox(Tableau0,ABox0),
    remove_from_abox(ABox0,El,ABox),
    set_abox(Tableau0,ABox,Tableau).
  
  add_clash_to_tableau(M,Tableau0,ToCheck,Tableau):-
    check_clash(M,ToCheck,Tableau0),!,
    get_clashes(Tableau0,Clashes0),
    add_to_clashes(Clashes0,ToCheck,Clashes),
    set_clashes(Tableau0,Clashes,Tableau).
  
  add_clash_to_tableau(_,Tableau,_,Tableau).
  
  assign(L,L).
  /*
    find & control (not find)
  */
  find(El,ABox):-
    member(El,ABox).
  
  control(El,ABox):-
    \+ find(El,ABox).
  
  /* end of abox as a list */
  
  /* abox as a red-black tree */
  /*new_abox(T):-
    rb_new(T).
  
  add(A,(Ass,Ex),A1):-
    rb_insert(A,(Ass,Ex),[],A1).
  
  find((Ass,Ex),A):-
    rb_lookup((Ass,Ex),_,A).
  */
  /* end of abox as a rb tree */
  
  
  add_to_abox(ABox,El,[El|ABox]).
  
  remove_from_abox(ABox0,El,ABox):-
    delete(ABox0,El,ABox).
  
  
  add_to_clashes(Clashes,'http://www.w3.org/2002/07/owl#Nothing'-_,[owlnothing|Clashes]):-!.
  
  add_to_clashes(Clashes,El,[El|Clashes]).
  
  remove_from_abox(Clashes0,El,Clashes):-
    delete(Clashes0,El,Clashes).
  
  /*
    add_all_to_tableau(M,L1,L2,LO).
    add in L2 all item of L1
  */
  add_all_to_tableau(M,L,Tableau0,Tableau):-
    get_abox(Tableau0,ABox0),
    get_clashes(Tableau0,Clashes0),
    add_all_to_abox_and_clashes(M,L,Tableau0,ABox0,ABox,Clashes0,Clashes),
    set_abox(Tableau0,ABox,Tableau1),
    set_clashes(Tableau1,Clashes,Tableau).
  
  add_all_to_abox_and_clashes(_,[],_,A,A,C,C).
  
  add_all_to_abox_and_clashes(M,[(classAssertion(Class,I),Expl)|T],Tab0,A0,A,C0,C):-
    check_clash(M,Class-I,Tab0),!,
    add_to_abox(A0,(classAssertion(Class,I),Expl),A1),
    add_to_clashes(C0,Class-I,C1),
    set_abox(Tab0,A1,Tab),
    add_all_to_abox_and_clashes(M,T,Tab,A1,A,C1,C).
  
  add_all_to_abox_and_clashes(M,[(sameIndividual(LI),Expl)|T],Tab0,A0,A,C0,C):-
    check_clash(M,sameIndividual(LI),Tab0),!,
    add_to_abox(A0,(sameIndividual(LI),Expl),A1),
    add_to_clashes(C0,sameIndividual(LI),C1),
    set_abox(Tab0,A1,Tab),
    add_all_to_abox_and_clashes(M,T,Tab,A1,A,C1,C).
  
  add_all_to_abox_and_clashes(M,[(differentIndividuals(LI),Expl)|T],Tab0,A0,A,C0,C):-
    check_clash(M,differentIndividuals(LI),Tab0),!,
    add_to_abox(A0,(differentIndividuals(LI),Expl),A1),
    add_to_clashes(C0,differentIndividuals(LI),C1),
    set_abox(Tab0,A1,Tab),
    add_all_to_abox_and_clashes(M,T,Tab,A1,A,C1,C).
  
  add_all_to_abox_and_clashes(M,[H|T],Tab0,A0,A,C0,C):-
    add_to_abox(A0,H,A1),
    set_abox(Tab0,A1,Tab),
    add_all_to_abox_and_clashes(M,T,Tab,A1,A,C0,C).
  
  add_all_to_abox([],A,A).
  
  add_all_to_abox([H|T],A0,A):-
    add_to_abox(A0,H,A1),
    add_all_to_abox(T,A1,A).
  
  /* ************** */
  
  
  
  % ===================================
  % EXPANSION QUEUE
  % ===================================
  
  
  
  % ------------
  % Utility for rule application
  % ------------
  update_expansion_queue_in_tableau(M,C,Ind,Tab0,Tab):-
    get_expansion_queue(Tab0,ExpansionQueue0),
    update_expansion_queue(M,C,Ind,ExpansionQueue0,ExpansionQueue),
    set_expansion_queue(Tab0,ExpansionQueue,Tab).
  
  update_expansion_queue_in_tableau(M,P,Ind1,Ind2,Tab0,Tab):-
    get_expansion_queue(Tab0,ExpansionQueue0),
    update_expansion_queue(M,P,Ind1,Ind2,ExpansionQueue0,ExpansionQueue),
    set_expansion_queue(Tab0,ExpansionQueue,Tab).
  
  
  
  update_expansion_queue(_,unionOf(L),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
    delete(NDQ0,[unionOf(L),Ind],NDQ1),
    append(NDQ1,[[unionOf(L),Ind]],NDQ).
  
  update_expansion_queue(_,maxCardinality(N,S,C),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
    delete(NDQ0,[maxCardinality(N,S,C),Ind],NDQ1),
    append(NDQ1,[[maxCardinality(N,S,C),Ind]],NDQ).
  
  update_expansion_queue(_,maxCardinality(N,S),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
    delete(NDQ0,[maxCardinality(N,S),Ind],NDQ1),
    append(NDQ1,[[maxCardinality(N,S),Ind]],NDQ).
  
  update_expansion_queue(_,exactCardinality(N,S,C),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
    delete(NDQ0,[exactCardinality(N,S,C),Ind],NDQ1),
    append(NDQ1,[[exactCardinality(N,S,C),Ind]],NDQ).
  
  update_expansion_queue(_,exactCardinality(N,S),Ind,[DQ,NDQ0],[DQ,NDQ]):-!,
    delete(NDQ0,[exactCardinality(N,S),Ind],NDQ1),
    append(NDQ1,[[exactCardinality(N,S),Ind]],NDQ).
  
  update_expansion_queue(_,C,Ind,[DQ0,NDQ],[DQ,NDQ]):-!,
    delete(DQ0,[C,Ind],DQ1),
    append(DQ1,[[C,Ind]],DQ).
  
  update_expansion_queue(_,P,Ind1,Ind2,[DQ0,NDQ],[DQ,NDQ]):-!,
    delete(DQ0,[P,Ind1,Ind2],DQ1),
    append(DQ1,[[P,Ind1,Ind2]],DQ).
  
  
  init_expansion_queue(LCA,LPA,EQ):-
    empty_expansion_queue(EmptyEQ),
    add_classes_expqueue(LCA,EmptyEQ,EQ0),
    add_prop_expqueue(LPA,EQ0,EQ).
  
  add_classes_expqueue([],EQ,EQ).
  
  add_classes_expqueue([(classAssertion(C,I),_)|T],EQ0,EQ):-
    update_expansion_queue(_,C,I,EQ0,EQ1),
    add_classes_expqueue(T,EQ1,EQ).
  
  add_prop_expqueue([],EQ,EQ).
  
  add_prop_expqueue([(propertyAssertion(P,S,O),_)|T],EQ0,EQ):-
    update_expansion_queue(_,P,S,O,EQ0,EQ1),
    add_prop_expqueue(T,EQ1,EQ).
  
  
  
  
  % ===================================
  % TABS
  % ===================================
  
  
  
  /*
    adds nodes and edges to tabs given axioms
  */
  create_tabs(L,Tableau0,Tableau):-
    get_tabs(Tableau0,Tabs0),
    create_tabs_int(L,Tabs0,Tabs),
    set_tabs(Tableau0,Tabs,Tableau).
  
  
  create_tabs_int([],G,G).
    
  create_tabs_int([(propertyAssertion(P,S,O),_Expl)|T],Tabl0,Tabl):-
    add_edge_int(P,S,O,Tabl0,Tabl1),
    create_tabs_int(T,Tabl1,Tabl).
    
  create_tabs_int([(differentIndividuals(Ld),_Expl)|Tail],(T0,RBN,RBR),Tabs):-
    add_vertices(T0,Ld,T1),
    create_tabs_int(Tail,(T1,RBN,RBR),Tabs).
  
  create_tabs_int([(classAssertion(_,I),_Expl)|Tail],(T0,RBN,RBR),Tabs):-
    add_vertices(T0,[I],T1),
    create_tabs_int(Tail,(T1,RBN,RBR),Tabs).
  
  
  /*
    add edge to tableau
  
    add_edge(Property,Subject,Object,Tab0,Tab)
  */
  add_edge(P,S,O,Tableau0,Tableau):-
    get_tabs(Tableau0,Tabs0),
    add_edge_int(P,S,O,Tabs0,Tabs),
    set_tabs(Tableau0,Tabs,Tableau).
  
  add_edge_int(P,S,O,(T0,ItR0,RtI0),(T1,ItR1,RtI1)):-
    add_node_to_tree(P,S,O,ItR0,ItR1),
    add_role_to_tree(P,S,O,RtI0,RtI1),
    add_edge_to_tabl(P,S,O,T0,T1).
  
  add_node_to_tree(P,S,O,RB0,RB1):-
    rb_lookup((S,O),V,RB0),
    \+ member(P,V),!,
    rb_update(RB0,(S,O),[P|V],RB1).
  
  add_node_to_tree(P,S,O,RB0,RB0):-
    rb_lookup((S,O),V,RB0),
    member(P,V),!.
  
  add_node_to_tree(P,S,O,RB0,RB1):-
    \+ rb_lookup([S,O],_,RB0),!,
    rb_insert(RB0,(S,O),[P],RB1).
  
  add_role_to_tree(P,S,O,RB0,RB1):-
    rb_lookup(P,V,RB0),
    \+ member((S,O),V),!,
    rb_update(RB0,P,[(S,O)|V],RB1).
  
  add_role_to_tree(P,S,O,RB0,RB0):-
    rb_lookup(P,V,RB0),
    member((S,O),V),!.
  
  add_role_to_tree(P,S,O,RB0,RB1):-
    \+ rb_lookup(P,_,RB0),!,
    rb_insert(RB0,P,[(S,O)],RB1).
  
  add_edge_to_tabl(_R,Ind1,Ind2,T0,T0):-
    graph_edge(Ind1,Ind2,T0),!.
  
  add_edge_to_tabl(_R,Ind1,Ind2,T0,T1):-
    add_edges(T0,[Ind1-Ind2],T1).
  
  
  
  /*
    check for an edge
  */
  graph_edge(Ind1,Ind2,T0):-
    edges(T0, Edges),
    member(Ind1-Ind2, Edges),!.
  
  %graph_edge(_,_,_).
  
  /*
    remove edges and nodes from tableau
  
    To remove a node from the tableau use remove_node(Node,Tabs0,Tabs)
  */
  
  % remove_all_nodes_from_tree(Property,Subject,Object,RBN0,RBN)
  % removes from RBN the pair key-values with key (Subject,Object)
  % key (Subject,Object) exists
  remove_all_nodes_from_tree(_P,S,O,RB0,RB1):-
    rb_lookup((S,O),_,RB0),
    rb_delete(RB0,(S,O),RB1).
  
  % key (Subject,Object) does not exist
  remove_all_nodes_from_tree(_P,S,O,RB0,_RB1):-
    \+ rb_lookup((S,O),_,RB0).
  % ----------------
  
  % remove_role_from_tree(Property,Subject,Object,RBR0,RBR)
  % remove in RBR the pair (Subject,Object) from the value associated with key Property
  % pair (Subject,Object) does not exist for key Property
  remove_role_from_tree(P,S,O,RB,RB):-
    rb_lookup(P,V,RB),
    \+ member((S,O),V).
  
  % pair (Subject,Object) exists for key Property but it is not the only pair associated to it
  remove_role_from_tree(P,S,O,RB0,RB1):-
    rb_lookup(P,V,RB0),
    member((S,O),V),
    delete(V,(S,O),V1),
    dif(V1,[]),
    rb_update(RB0,P,V1,RB1).
  
  % pair (Subject,Object) exists for key Property and it is the only pair associated to it
  remove_role_from_tree(P,S,O,RB0,RB1):-
    rb_lookup(P,V,RB0),
    member((S,O),V),
    delete(V,(S,O),V1),
    V1==[],
    rb_delete(RB0,P,RB1).
  % ----------------
  
  % remove_edge_from_table(Property,Subject,Object,Tab0,Tab)
  % removes from T the edge from Subject to Object
  remove_edge_from_table(_P,S,O,T,T):-
    \+ graph_edge(S,O,T).
  
  remove_edge_from_table(_P,S,O,T0,T1):-
    graph_edge(S,O,T0),
    del_edges(T0,[S-O],T1).
  % ----------------
  
  % remove_node_from_table(Subject,Tab0,Tab)
  % removes from T the node corresponding to Subject
  remove_node_from_table(S,T0,T1):-
    del_vertices(T0,[S],T1).
  
  
  
  
  
  % ===================================
  % FUNCTIONS ON ABOX AND TABS
  % ===================================
  
  /*
   * merge
   * 
   * Implement the Merge operation of the tableau. Merge two individuals
   */
  % The first three are needed because T in tabs:(T,RBN,RBR) saves sameIndividuals
  % as a list instead of a single individual sameIndividual(L).
  % The addition of sameIndividual is made after, during the update of the ABox.
  % TODO: it could be improved!
  /*
  merge(M,sameIndividual(LX),sameIndividual(LY),Expl,Tableau0,Tableau):-
    !,
    get_tabs(Tableau0,Tabs0),
    merge_tabs(L,Y,Tabs0,Tabs),
    get_abox(Tableau0,ABox0),
    merge_abox(M,L,Y,Expl,ABox0,ABox),
    set_tabs(Tableau0,Tabs,Tableau1),
    set_abox(Tableau1,ABox,Tableau).
  
  merge(M,sameIndividual(L),Y,Expl,Tableau0,Tableau):-
    !,
    get_tabs(Tableau0,Tabs0),
    merge_tabs(L,Y,Tabs0,Tabs),
    get_abox(Tableau0,ABox0),
    merge_abox(M,L,Y,Expl,ABox0,ABox),
    set_tabs(Tableau0,Tabs,Tableau1),
    set_abox(Tableau1,ABox,Tableau).
  */
  
  merge(M,X,Y,Expl,Tableau0,Tableau):-
    !,
    get_tabs(Tableau0,Tabs0),
    merge_tabs(X,Y,Tabs0,Tabs),
    get_abox(Tableau0,ABox0),
    flatten([X,Y],L0),
    sort(L0,L),
    list_as_sameIndividual(L,SI),
    get_clashes(Tableau0,Clashes0),
    merge_abox(M,L,SI,Expl,ABox0,ABox,ClashesToCheck),
    set_abox(Tableau0,ABox,Tableau1),
    check_merged_classes(M,ClashesToCheck,Tableau1,NewClashes),
    update_clashes_after_merge(M,L,SI,Tableau1,Clashes0,ClashesAM),
    append(NewClashes,ClashesAM,Clashes),
    set_tabs(Tableau1,Tabs,Tableau2),
    set_clashes(Tableau2,Clashes,Tableau3),
    get_expansion_queue(Tableau3,ExpQ0),
    update_expansion_queue_after_merge(L,SI,ExpQ0,ExpQ),
    set_expansion_queue(Tableau3,ExpQ,Tableau).
  
  
  /*
   * merge node in tableau. X and Y single individuals
   */
  
  merge_tabs(X,Y,(T0,RBN0,RBR0),(T,RBN,RBR)):-
    (neighbours(X,T0,LSX0)*->assign(LSX0,LSX);assign([],LSX)),
    (neighbours(Y,T0,LSY0)*->assign(LSY0,LSY);assign([],LSY)),
    transpose_ugraph(T0,TT),
    (neighbours(X,TT,LPX0)*->assign(LPX0,LPX);assign([],LPX)),
    (neighbours(Y,TT,LPY0)*->assign(LPY0,LPY);assign([],LPY)),
    % list_as_sameIndividual([X,Y],SI), %TODO
    flatten([X,Y],L0),
    sort(L0,SI),
    set_predecessor(SI,X,LPX,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),!,
    set_successor(SI,X,LSX,(T1,RBN1,RBR1),(T2,RBN2,RBR2)),!,
    set_predecessor(SI,Y,LPY,(T2,RBN2,RBR2),(T3,RBN3,RBR3)),!,
    set_successor(SI,Y,LSY,(T3,RBN3,RBR3),(T4,RBN4,RBR4)),!,
    remove_nodes(X,Y,(T4,RBN4,RBR4),(T,RBN,RBR)).
  
  remove_nodes(X,Y,Tabs0,Tabs):-
    remove_node(X,Tabs0,Tabs1),
    remove_node(Y,Tabs1,Tabs).
  
  % Collects all the connected in input (LP, predecessor) or in output (LS, successor) for node X
  % removes from RBN (remove_all_nodes_from_tree) all the pairs key-value where the key contains node X (pairs (X,Ind1) and (Ind1,X))
  % and from RBR (remove_edges->remove_role_from_tree) all the pairs containing X from the values of the roles entering in or exiting from X
  remove_node(X,(T0,RBN0,RBR0),(T,RBN,RBR)):-
    (neighbours(X,T0,LS0)*->assign(LS0,LS);assign([],LS)),
    transpose_ugraph(T0,TT),
    (neighbours(X,TT,LP0)*->assign(LP0,LP);assign([],LP)),
    remove_node1(X,LS,RBN0,RBR0,RBN1,RBR1),
    remove_node2(X,LP,RBN1,RBR1,RBN,RBR),
    (vertices(T0,VS),member(X,VS)*->del_vertices(T0,[X],T);assign(T0,T)).
  
  remove_node1(_,[],RBN,RBR,RBN,RBR).
  
  remove_node1(X,[H|T],RBN0,RBR0,RBN,RBR):-
    rb_lookup((X,H),V,RBN0),
    remove_edges(V,X,H,RBR0,RBR1),
    remove_all_nodes_from_tree(_,X,H,RBN0,RBN1),
    remove_node1(X,T,RBN1,RBR1,RBN,RBR).
  
  remove_node2(_,[],RBN,RBR,RBN,RBR).
  
  remove_node2(X,[H|T],RBN0,RBR0,RBN,RBR):-
    rb_lookup((H,X),V,RBN0),
    remove_edges(V,H,X,RBR0,RBR1),
    remove_all_nodes_from_tree(_,H,X,RBN0,RBN1),
    remove_node1(X,T,RBN1,RBR1,RBN,RBR).
  
  remove_edges([],_,_,RBR,RBR).
  
  remove_edges([H|T],S,O,RBR0,RBR):-
    remove_role_from_tree(H,S,O,RBR0,RBR1),
    remove_edges(T,S,O,RBR1,RBR).
  
  
  set_predecessor(_NN,_,[],Tabs,Tabs).
  
  set_predecessor(NN,X,[H|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
    rb_lookup((H,X),LR,RBN0),
    set_predecessor1(NN,H,LR,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
    set_predecessor(NN,X,L,(T1,RBN1,RBR1),(T,RBN,RBR)).
  
  set_predecessor1(_NN,_H,[],Tabs,Tabs).
  
  set_predecessor1(NN,H,[R|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
    add_edge_int(R,H,NN,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
    set_predecessor1(NN,H,L,(T1,RBN1,RBR1),(T,RBN,RBR)).
  
  set_successor(_NN,_X,[],Tabs,Tabs).
  
  set_successor(NN,X,[H|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
    rb_lookup((X,H),LR,RBN0),
    set_successor1(NN,H,LR,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
    set_successor(NN,X,L,(T1,RBN1,RBR1),(T,RBN,RBR)).
  
  set_successor1(_NN,_H,[],Tabs,Tabs).
  
  set_successor1(NN,H,[R|L],(T0,RBN0,RBR0),(T,RBN,RBR)):-
    add_edge_int(R,NN,H,(T0,RBN0,RBR0),(T1,RBN1,RBR1)),
    set_successor1(NN,H,L,(T1,RBN1,RBR1),(T,RBN,RBR)).
  
  /*
    merge node in ABox
  */
  
  % TODO update
  merge_abox(_M,_L,_,_,[],[],[]).
  
  merge_abox(M,L,SI,Expl0,[(classAssertion(C,Ind),ExplT)|T],[(classAssertion(C,SI),Expl)|ABox],[C-SI|CTC]):-
    member(Ind,L),!,
    and_f(M,Expl0,ExplT,Expl),
    %and_f_ax(M,sameIndividual(L),Expl1,Expl),
    merge_abox(M,L,SI,Expl0,T,ABox,CTC).
  
  merge_abox(M,L,SI,Expl0,[(propertyAssertion(P,Ind1,Ind2),ExplT)|T],[(propertyAssertion(P,SI,Ind2),Expl)|ABox],CTC):-
    member(Ind1,L),!,
    and_f(M,Expl0,ExplT,Expl),
    %and_f_ax(M,sameIndividual(L),Expl1,Expl),
    merge_abox(M,L,SI,Expl0,T,ABox,CTC).
  
  merge_abox(M,L,SI,Expl0,[(propertyAssertion(P,Ind1,Ind2),ExplT)|T],[(propertyAssertion(P,Ind1,SI),Expl)|ABox],CTC):-
    member(Ind2,L),!,
    and_f(M,Expl0,ExplT,Expl),
    %and_f_ax(M,sameIndividual(L),Expl1,Expl),
    merge_abox(M,L,SI,Expl0,T,ABox,CTC).
  
  merge_abox(M,L,SI,Expl0,[H|T],[H|ABox],CTC):-
    merge_abox(M,L,SI,Expl0,T,ABox,CTC).
  
  
  /*
    check for new clashes due to merge
   */
  
  check_merged_classes(_,[],_,[]).
  
  check_merged_classes(M,[ToCheck|TC],Tab,[ToCheck|NewClashes]):-
    check_clash(M,ToCheck,Tab),!,
    check_merged_classes(M,TC,Tab,NewClashes).
  
  check_merged_classes(M,[_ToCheck|TC],Tab,NewClashes):-
    check_merged_classes(M,TC,Tab,NewClashes).
  
  /*
   update clashes ofter merge
   substitute ind in clashes with sameIndividual
   */
  
  update_clashes_after_merge(M,L,SI,Tableau,Clashes0,Clashes):-
    update_clashes_after_merge(M,L,SI,Tableau,Clashes0,Clashes,0).
  
  % if last argument is 0 -> need to theck clash for sameIndividual/differentIndividual
  % if there is no clash (check_clash returns false), backtrack to (*)
  update_clashes_after_merge(M,_,SI,Tableau,[],[SI],0):-
    check_clash(M,SI,Tableau),!.
  
  % (*)
  update_clashes_after_merge(_,_,_,_,[],[],_).
  
  update_clashes_after_merge(M,L,SI,Tableau,[sameIndividual(LC)|TC0],[SI|TC],0):-
    memberchk(I,L),
    memberchk(I,LC),!,
    update_clashes_after_merge(M,L,SI,Tableau,TC0,TC,1).
  
  update_clashes_after_merge(M,L,SI,Tableau,[C-I|TC0],[C-SI|TC],UpdatedSI):-
    memberchk(I,L),!,
    update_clashes_after_merge(M,L,SI,Tableau,TC0,TC,UpdatedSI).
  
  update_clashes_after_merge(M,L,SI,Tableau,[C-sameIndividual(LOld)|TC0],[C-SI|TC],UpdatedSI):-
    memberchk(I,L),
    memberchk(I,LOld),!,
    update_clashes_after_merge(M,L,SI,Tableau,TC0,TC,UpdatedSI).
  
  update_clashes_after_merge(M,L,SI,Tableau,[Clash|TC0],[Clash|TC],UpdatedSI):-
    update_clashes_after_merge(M,L,SI,Tableau,TC0,TC,UpdatedSI).
  
  
  
  
  /*
   update expansion queue ofter merge
   substitute ind in expansion queue with sameIndividual
   */
  update_expansion_queue_after_merge(L,SI,[ExpQD0,ExpQND0],[ExpQD,ExpQND]):-
    update_expansion_queue_after_merge_int(L,SI,ExpQD0,ExpQD),
    update_expansion_queue_after_merge_int(L,SI,ExpQND0,ExpQND).
  
  update_expansion_queue_after_merge_int(_,_,[],[]).
  
  update_expansion_queue_after_merge_int(L,SI,[[C,I]|TC0],[[C,IN]|TC]):-
    substitute_individual(L,I,SI,IN),
    update_expansion_queue_after_merge_int(L,SI,TC0,TC).
  
  update_expansion_queue_after_merge_int(L,SI,[[P,S,O]|TC0],[[P,SN,ON]|TC]):-
    substitute_individual(L,S,SI,SN),
    substitute_individual(L,O,SI,ON),
    update_expansion_queue_after_merge_int(L,SI,TC0,TC).
  
  substitute_individual(L,sameIndividual(LSI),SI,SI):-
    memberchk(I,L),
    memberchk(I,LSI),!.
  
  substitute_individual(_,I,_,I):-!.
  
  
  
  % ==================================================================================================================