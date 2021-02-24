o('<?xml version="1.0"?>
<rdf:RDF xmlns="http://dl-learner/all#"
     xml:base="http://dl-learner/all"
     xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
     xmlns:owl="http://www.w3.org/2002/07/owl#"
     xmlns:xml="http://www.w3.org/XML/1998/namespace"
     xmlns:father="http://example.com/father#"
     xmlns:xsd="http://www.w3.org/2001/XMLSchema#"
     xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
     xmlns:disponte="https://sites.google.com/a/unife.it/ml/disponte#">
    <owl:Ontology rdf:about="http://dl-learner/all"/>
    
    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // Annotation properties
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->
    
    <!-- https://sites.google.com/a/unife.it/ml/disponte#probability -->
    <owl:AnnotationProperty rdf:about="https://sites.google.com/a/unife.it/ml/disponte#probability"/>
    
    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // Object Properties
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->
    
    <!-- http://example.com/father#hasChild -->
    <owl:ObjectProperty rdf:about="http://example.com/father#hasChild"/>
    
    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // Classes
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->
    
    <!-- http://example.com/father#father -->
    <owl:Class rdf:about="http://example.com/father#father">
        <rdfs:subClassOf rdf:resource="http://example.com/father#male"/>
    </owl:Class>
    <owl:Axiom>
        <owl:annotatedSource rdf:resource="http://example.com/father#father"/>
        <owl:annotatedProperty rdf:resource="http://www.w3.org/2000/01/rdf-schema#subClassOf"/>
        <owl:annotatedTarget rdf:resource="http://example.com/father#male"/>
        <disponte:probability rdf:datatype="http://www.w3.org/2001/XMLSchema#string">0.22557</disponte:probability>
    </owl:Axiom>
    
    <!-- http://example.com/father#female -->
    <owl:Class rdf:about="http://example.com/father#female">
        <rdfs:subClassOf rdf:resource="http://example.com/father#person"/>
    </owl:Class>
    <owl:Axiom>
        <owl:annotatedSource rdf:resource="http://example.com/father#female"/>
        <owl:annotatedProperty rdf:resource="http://www.w3.org/2000/01/rdf-schema#subClassOf"/>
        <owl:annotatedTarget rdf:resource="http://example.com/father#person"/>
        <disponte:probability rdf:datatype="http://www.w3.org/2001/XMLSchema#string">0.08057</disponte:probability>
    </owl:Axiom>
    
    <!-- http://example.com/father#giacobbo -->
    <owl:Class rdf:about="http://example.com/father#giacobbo"/>
    
    <!-- http://example.com/father#male -->
    <owl:Class rdf:about="http://example.com/father#male">
        <rdfs:subClassOf rdf:resource="http://example.com/father#person"/>
    </owl:Class>
    <owl:Axiom>
        <owl:annotatedSource rdf:resource="http://example.com/father#male"/>
        <owl:annotatedProperty rdf:resource="http://www.w3.org/2000/01/rdf-schema#subClassOf"/>
        <owl:annotatedTarget rdf:resource="http://example.com/father#person"/>
        <disponte:probability rdf:datatype="http://www.w3.org/2001/XMLSchema#string">0.26468</disponte:probability>
    </owl:Axiom>
    
    <!-- http://example.com/father#person -->
    <owl:Class rdf:about="http://example.com/father#person">
        <rdfs:subClassOf rdf:resource="http://www.w3.org/2002/07/owl#Thing"/>
    </owl:Class>
    <owl:Axiom>
        <owl:annotatedSource rdf:resource="http://example.com/father#person"/>
        <owl:annotatedProperty rdf:resource="http://www.w3.org/2000/01/rdf-schema#subClassOf"/>
        <owl:annotatedTarget rdf:resource="http://www.w3.org/2002/07/owl#Thing"/>
        <disponte:probability rdf:datatype="http://www.w3.org/2001/XMLSchema#string">0.03322</disponte:probability>
    </owl:Axiom>
    
    <!-- http://www.w3.org/2002/07/owl#Thing -->
    <owl:Class rdf:about="http://www.w3.org/2002/07/owl#Thing"/>
    
    <!-- 
    ///////////////////////////////////////////////////////////////////////////////////////
    //
    // Individuals
    //
    ///////////////////////////////////////////////////////////////////////////////////////
     -->
    
    <!-- http://example.com/father#anna -->
    <owl:NamedIndividual rdf:about="http://example.com/father#anna">
        <rdf:type rdf:resource="http://example.com/father#female"/>
        <father:hasChild rdf:resource="http://example.com/father#heinz"/>
    </owl:NamedIndividual>
    
    <!-- http://example.com/father#heinz -->
    <owl:NamedIndividual rdf:about="http://example.com/father#heinz">
        <rdf:type rdf:resource="http://example.com/father#male"/>
    </owl:NamedIndividual>
    
    <!-- http://example.com/father#markus -->
    <owl:NamedIndividual rdf:about="http://example.com/father#markus">
        <rdf:type rdf:resource="http://example.com/father#father"/>
        <father:hasChild rdf:resource="http://example.com/father#anna"/>
    </owl:NamedIndividual>
    
    <!-- http://example.com/father#martin -->
    <owl:NamedIndividual rdf:about="http://example.com/father#martin">
        <rdf:type rdf:resource="http://example.com/father#father"/>
        <rdf:type rdf:resource="http://example.com/father#male"/>
        <father:hasChild rdf:resource="http://example.com/father#heinz"/>
    </owl:NamedIndividual>
    
    <!-- http://example.com/father#michelle -->
    <owl:NamedIndividual rdf:about="http://example.com/father#michelle">
        <rdf:type rdf:resource="http://example.com/father#female"/>
    </owl:NamedIndividual>
    
    <!-- http://example.com/father#stefan -->
    <owl:NamedIndividual rdf:about="http://example.com/father#stefan">
        <rdf:type rdf:resource="http://example.com/father#father"/>
        <rdf:type rdf:resource="http://example.com/father#male"/>
        <father:hasChild rdf:resource="http://example.com/father#markus"/>
    </owl:NamedIndividual>
</rdf:RDF>
<!-- Generated by the OWL API (version 4.1.3.20151118-2017) https://github.com/owlcs/owlapi -->
').