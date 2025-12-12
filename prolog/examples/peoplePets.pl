/** <module> peoplePets

This is a classic probabilistic ontology example demonstrating TRILL's
DISPONTE (DIstribution Semantics for Probabilistic ONTologiEs) reasoning
capabilities.

## Knowledge Base Description

This knowledge base models people and their pet relationships, inspired by
the people+pets ontology from:
  Patel-Schneider, P.F., Horrocks, I., and Bechhofer, S. 2003. Tutorial on OWL.

The ontology defines:
  - **Classes**: cat, dog, dinosaur, pet, natureLover
  - **Properties**: has_animal, is_animal_of (inverse properties)
  - **Individuals**: Kevin, Tom, Fluffy, Dino, Fred, Spike

## Probabilistic Annotations

Several axioms have DISPONTE probability annotations:
  - P(cat subClassOf pet) = 0.6
  - P(dog subClassOf pet) = 0.8
  - P(Fluffy is a cat) = 0.4
  - P(Tom is a cat) = 0.3

## Reasoning Task

The key inference is: "Are individuals who own a pet considered nature lovers?"

The rule encoded is: someValuesFrom(has_animal, pet) subClassOf natureLover

Since Kevin owns Fluffy, Tom, and Spike, and these may be pets with certain
probabilities, we can compute the probability that Kevin is a nature lover.

## Example Queries

```prolog
?- prob_instanceOf('natureLover', 'Kevin', Prob).
% Returns the probability that Kevin is a nature lover

?- instanceOf('natureLover', 'Kevin', ListExpl).
% Returns explanations for why Kevin is a nature lover
```

## Reference

Zese, R.: Reasoning with Probabilistic Logics. ArXiv e-prints 1405.0915v3.
Doctoral Consortium of the 30th International Conference on Logic Programming
(ICLP 2014), July 19-22, Vienna, Austria.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:-use_module(library(trill)).

:- trill. % or :- trillp. or :- tornado.

/** <examples>

?- prob_instanceOf('natureLover','Kevin',Prob).
?- instanceOf('natureLover','Kevin',ListExpl).

*/

% OWL/RDF ontology definition embedded as string
owl_rdf('<?xml version="1.0"?>

<!DOCTYPE rdf:RDF [
    <!ENTITY owl "http://www.w3.org/2002/07/owl#" >
    <!ENTITY xsd "http://www.w3.org/2001/XMLSchema#" >
    <!ENTITY rdfs "http://www.w3.org/2000/01/rdf-schema#" >
    <!ENTITY rdf "http://www.w3.org/1999/02/22-rdf-syntax-ns#" >
    <!ENTITY disponte "https://sites.google.com/a/unife.it/ml/disponte#" >
]>


<rdf:RDF xmlns="http://cohse.semanticweb.org/ontologies/people#"
     xml:base="http://cohse.semanticweb.org/ontologies/people"
     xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
     xmlns:owl="http://www.w3.org/2002/07/owl#"
     xmlns:xsd="http://www.w3.org/2001/XMLSchema#"
     xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
     xmlns:disponte="https://sites.google.com/a/unife.it/ml/disponte#">
    <owl:Ontology rdf:about="http://cohse.semanticweb.org/ontologies/people"/>
    


    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // Annotation properties
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->

    


    <!-- https://sites.google.com/a/unife.it/ml/disponte#probability -->

    <owl:AnnotationProperty rdf:about="&disponte;probability"/>
    


    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // Object Properties
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->

    


    <!-- http://cohse.semanticweb.org/ontologies/people#has_animal -->

    <owl:ObjectProperty rdf:about="http://cohse.semanticweb.org/ontologies/people#has_animal">
        <rdfs:label>has_animal</rdfs:label>
        <rdfs:comment></rdfs:comment>
    </owl:ObjectProperty>

    <!-- http://cohse.semanticweb.org/ontologies/people#is_animal_of -->

    <owl:ObjectProperty rdf:about="http://cohse.semanticweb.org/ontologies/people#is_animal_of">
        <rdfs:label>is_animal_of</rdfs:label>
        <rdfs:comment></rdfs:comment>
    </owl:ObjectProperty>
    


    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // Classes
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->

    


    <!-- http://cohse.semanticweb.org/ontologies/people#cat -->

    <!--owl:Class rdf:about="http://cohse.semanticweb.org/ontologies/people#cat">
        <rdfs:label>cat</rdfs:label>
        <rdfs:subClassOf rdf:resource="http://cohse.semanticweb.org/ontologies/people#pet"/>
        <rdfs:comment></rdfs:comment>
    </owl:Class>
    <owl:Axiom>
        <disponte:probability rdf:datatype="&xsd;decimal">0.6</disponte:probability>
        <owl:annotatedSource rdf:resource="http://cohse.semanticweb.org/ontologies/people#cat"/>
        <owl:annotatedTarget rdf:resource="http://cohse.semanticweb.org/ontologies/people#pet"/>
        <owl:annotatedProperty rdf:resource="&rdfs;subClassOf"/>
    </owl:Axiom-->
        
    


    <!-- http://cohse.semanticweb.org/ontologies/people#dog -->
    
    <owl:Class rdf:about="http://cohse.semanticweb.org/ontologies/people#dog">
        <rdfs:label>cat</rdfs:label>
        <rdfs:subClassOf rdf:resource="http://cohse.semanticweb.org/ontologies/people#pet"/>
        <rdfs:comment></rdfs:comment>
    </owl:Class>
        
    


    <!-- http://cohse.semanticweb.org/ontologies/people#natureLover -->

    <owl:Class rdf:about="http://cohse.semanticweb.org/ontologies/people#natureLover"/>
    


    <!-- http://cohse.semanticweb.org/ontologies/people#pet -->

    <owl:Class rdf:about="http://cohse.semanticweb.org/ontologies/people#pet"/>
    


    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // Individuals
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->

    


    <!-- http://cohse.semanticweb.org/ontologies/people#Fluffy -->

    <owl:NamedIndividual rdf:about="http://cohse.semanticweb.org/ontologies/people#Fluffy">
        <rdf:type rdf:resource="http://cohse.semanticweb.org/ontologies/people#cat"/>
        <rdfs:label>Fuffy</rdfs:label>
        <rdfs:comment></rdfs:comment>
    </owl:NamedIndividual>
    <owl:Axiom>
        <disponte:probability>0.4</disponte:probability>
        <owl:annotatedSource rdf:resource="http://cohse.semanticweb.org/ontologies/people#Fluffy"/>
        <owl:annotatedTarget rdf:resource="http://cohse.semanticweb.org/ontologies/people#cat"/>
        <owl:annotatedProperty rdf:resource="&rdf;type"/>
    </owl:Axiom>
    


    <!-- http://cohse.semanticweb.org/ontologies/people#Kevin -->

    <owl:NamedIndividual rdf:about="http://cohse.semanticweb.org/ontologies/people#Kevin">
        <rdfs:label>Kevin</rdfs:label>
        <rdfs:comment></rdfs:comment>
        <has_animal rdf:resource="http://cohse.semanticweb.org/ontologies/people#Fluffy"/>
        <has_animal rdf:resource="http://cohse.semanticweb.org/ontologies/people#Tom"/>
    </owl:NamedIndividual>
    


    <!-- http://cohse.semanticweb.org/ontologies/people#Tom -->

    <owl:NamedIndividual rdf:about="http://cohse.semanticweb.org/ontologies/people#Tom">
        <rdf:type rdf:resource="http://cohse.semanticweb.org/ontologies/people#cat"/>
        <rdfs:label>Tom</rdfs:label>
        <rdfs:comment></rdfs:comment>
    </owl:NamedIndividual>
    <owl:Axiom>
        <disponte:probability>0.3</disponte:probability>
        <owl:annotatedSource rdf:resource="http://cohse.semanticweb.org/ontologies/people#Tom"/>
        <owl:annotatedTarget rdf:resource="http://cohse.semanticweb.org/ontologies/people#cat"/>
        <owl:annotatedProperty rdf:resource="&rdf;type"/>
    </owl:Axiom>
    

    <!-- http://cohse.semanticweb.org/ontologies/people#Dino -->

    <owl:NamedIndividual rdf:about="http://cohse.semanticweb.org/ontologies/people#Dino">
        <rdf:type rdf:resource="http://cohse.semanticweb.org/ontologies/people#dinosaur"/>
        <rdfs:label>Dino</rdfs:label>
        <rdfs:comment></rdfs:comment>
    </owl:NamedIndividual>
    


    <!-- http://cohse.semanticweb.org/ontologies/people#Fred -->

    <owl:NamedIndividual rdf:about="http://cohse.semanticweb.org/ontologies/people#Fred">
        <rdfs:label>Kevin</rdfs:label>
        <rdfs:comment></rdfs:comment>
        <has_animal rdf:resource="http://cohse.semanticweb.org/ontologies/people#Dino"/>
    </owl:NamedIndividual>
    


    <!-- http://cohse.semanticweb.org/ontologies/people#Spike -->

    <owl:NamedIndividual rdf:about="http://cohse.semanticweb.org/ontologies/people#Spike">
        <rdf:type rdf:resource="http://cohse.semanticweb.org/ontologies/people#dog"/>
        <rdfs:label>Spike</rdfs:label>
        <rdfs:comment></rdfs:comment>
        <is_animal_of rdf:resource="http://cohse.semanticweb.org/ontologies/people#Kevin"/>
    </owl:NamedIndividual>
    
    

    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // General axioms
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->

    <owl:Axiom>
        <owl:annotatedTarget rdf:resource="http://cohse.semanticweb.org/ontologies/people#natureLover"/>
        <owl:annotatedProperty rdf:resource="&rdfs;subClassOf"/>
        <owl:annotatedSource>
            <owl:Restriction>
                <rdfs:subClassOf rdf:resource="http://cohse.semanticweb.org/ontologies/people#natureLover"/>
                <owl:onProperty rdf:resource="http://cohse.semanticweb.org/ontologies/people#has_animal"/>
                <owl:someValuesFrom rdf:resource="http://cohse.semanticweb.org/ontologies/people#pet"/>
            </owl:Restriction>
        </owl:annotatedSource>
    </owl:Axiom>
</rdf:RDF>').

% =============================================================================
% Native TRILL Syntax Axioms
% =============================================================================

% Dinosaur is a subclass of pet (for Fred's pet Dino)
subClassOf('dinosaur','pet').

% DISPONTE probabilistic annotations for class subsumption
annotationAssertion('disponte:probability',subClassOf('cat','pet'),literal('0.6')).
annotationAssertion('disponte:probability',subClassOf('dog','pet'),literal('0.8')).

% has_animal and is_animal_of are inverse properties
inverseProperties('has_animal','is_animal_of').