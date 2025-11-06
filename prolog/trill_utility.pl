/** <module> trill_utility

This module gives utility predicates for all the otehr modules.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- module(trill_utility, [get_module/1,add_kb_atoms/3, set_up/1]).

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


set_up(M):-
  M:(dynamic class/1, datatype/1, objectProperty/1, dataProperty/1, annotationProperty/1),
  M:(dynamic namedIndividual/1, anonymousIndividual/1, subClassOf/2, equivalentClasses/1, disjointClasses/1, disjointUnion/2),
  M:(dynamic subPropertyOf/2, equivalentProperties/1, disjointProperties/1, inverseProperties/2, propertyDomain/2, propertyRange/2),
  M:(dynamic functionalProperty/1, inverseFunctionalProperty/1, reflexiveProperty/1, irreflexiveProperty/1, symmetricProperty/1, asymmetricProperty/1, transitiveProperty/1, hasKey/2),
  M:(dynamic sameIndividual/1, differentIndividuals/1, classAssertion/2, propertyAssertion/3, negativePropertyAssertion/3),
  M:(dynamic annotationAssertion/3, annotation/3, ontology/1, ontologyAxiom/2, ontologyImport/2, ontologyVersionInfo/2),
  M:(dynamic owl/4, owl/3, owl/2, blanknode/3, outstream/1, aNN/3, annotation_r_node/4, axiom_r_node/4, owl_repository/2, trdf_setting/2),
  M:(dynamic ns4query/1, addKBName/0),
  retractall(M:addKBName).
  %retractall(M:rules(_,_)),
  %assert(M:rules([],[])),
  %retractall(M:expressivity(_,_)),
  %assert(M:expressivity(1,[0,0,0,0,0,0])).