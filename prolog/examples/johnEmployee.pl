/** <module> johnEmployee

This is an example knowledge base demonstrating TRILL's capability to reason
over class hierarchies defined using both OWL/RDF syntax and TRILL's native
Prolog syntax.

The ontology defines:
  - A class hierarchy: employee subClassOf worker subClassOf person
  - An individual: john who is an employee

This example shows TRILL's ability to:
  1. Load OWL/RDF ontologies inline using owl_rdf/1
  2. Mix OWL/RDF definitions with native TRILL syntax axioms
  3. Answer instance queries using class hierarchy reasoning

Expected query results:
  - instanceOf(person, john, Expl): Succeeds with explanation containing
    the class hierarchy axioms

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:-use_module(library(trill)).

:- trill. % or :- trillp. or :- tornado.

/** <examples>

?- instanceOf(person,john,Expl).

*/

% First OWL/RDF block: defines worker as subclass of person
owl_rdf('<?xml version="1.0"?>
<rdf:RDF xmlns="http://example.foo#"
     xml:base="http://example.foo"
     xmlns:johnEmployee="http://example.foo#"
     xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
     xmlns:owl="http://www.w3.org/2002/07/owl#"
     xmlns:xml="http://www.w3.org/XML/1998/namespace"
     xmlns:xsd="http://www.w3.org/2001/XMLSchema#"
     xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#">
    <owl:Ontology rdf:about="http://example.foo"/>

    <!-- Classes -->
    <owl:Class rdf:about="http://example.foo#worker">
        <rdfs:subClassOf rdf:resource="http://example.foo#person"/>
    </owl:Class>

</rdf:RDF>').

% Native TRILL syntax: employee is a subclass of worker
subClassOf('johnEmployee:employee','johnEmployee:worker').

% Second OWL/RDF block: defines john as an employee
owl_rdf('<?xml version="1.0"?>
<rdf:RDF xmlns="http://example.foo#"
     xml:base="http://example.foo"
     xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
     xmlns:owl="http://www.w3.org/2002/07/owl#"
     xmlns:xml="http://www.w3.org/XML/1998/namespace"
     xmlns:xsd="http://www.w3.org/2001/XMLSchema#"
     xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#">
    <owl:Ontology rdf:about="http://example.foo"/>
    
    <!-- Individuals -->
    <owl:NamedIndividual rdf:about="http://example.foo#john">
        <rdf:type rdf:resource="http://example.foo#employee"/>
    </owl:NamedIndividual>
</rdf:RDF>').
