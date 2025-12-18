package it.unife.ml.probowlapi.trill;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.parameters.Imports;

/**
 * Utility to compute all individuals connected (directly or indirectly)
 * via object property assertions. Designed to be invoked from Prolog via JPL.
 */
public final class ConnectedIndividuals {

    private ConnectedIndividuals() {
    }

    /**
     * Compute the connected component starting from the given seed IRIs.
     * The ontology is pulled from the provided {@link TrillEncapsulated} instance.
     *
     * @param encapsulated the TRILL encapsulated backend holding the ontology
     * @param seedIris     array of individual IRIs (strings) to start from
     * @return array of IRIs of all reachable individuals (order preserved by discovery)
     */
    public static String[] connectedIndividuals(TrillEncapsulated encapsulated, String[] seedIris) {
        Objects.requireNonNull(encapsulated, "encapsulated backend is required");
        Objects.requireNonNull(seedIris, "seeds array is required");

        OWLOntology ontology = encapsulated.getOntology();
        if (ontology == null) {
            return new String[0];
        }

        // seed set with stable insertion order
        Set<String> seeds = Arrays.stream(seedIris)
                .filter(Objects::nonNull)
                .collect(Collectors.toCollection(LinkedHashSet::new));

        if (seeds.isEmpty()) {
            return new String[0];
        }

        Map<String, Set<String>> graph = buildUndirectedGraph(ontology);

        // BFS over the undirected graph
        Set<String> visited = new LinkedHashSet<>(seeds);
        ArrayDeque<String> frontier = new ArrayDeque<>(seeds);

        while (!frontier.isEmpty()) {
            String current = frontier.poll();
            for (String neighbor : graph.getOrDefault(current, Collections.emptySet())) {
                if (visited.add(neighbor)) {
                    frontier.add(neighbor);
                }
            }
        }

        return visited.toArray(new String[0]);
    }

    private static Map<String, Set<String>> buildUndirectedGraph(OWLOntology ontology) {
        ConcurrentHashMap<String, Set<String>> graph = new ConcurrentHashMap<>();

        ontology.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION, Imports.INCLUDED)
                .parallelStream()
                .forEach(ax -> addBidirectionalEdge(graph, ax));

        return graph;
    }

    private static void addBidirectionalEdge(Map<String, Set<String>> graph, OWLObjectPropertyAssertionAxiom ax) {
        OWLIndividual subj = ax.getSubject();
        OWLIndividual obj = ax.getObject();

        if (!subj.isNamed() || !obj.isNamed()) {
            return; // skip anonymous individuals
        }

        String s = iri(subj.asOWLNamedIndividual());
        String o = iri(obj.asOWLNamedIndividual());

        addEdge(graph, s, o);
        addEdge(graph, o, s);
    }

    private static void addEdge(Map<String, Set<String>> graph, String from, String to) {
        graph.computeIfAbsent(from, k -> ConcurrentHashMap.newKeySet()).add(to);
    }

    private static String iri(OWLNamedIndividual ind) {
        return ind.getIRI().toString();
    }
}
