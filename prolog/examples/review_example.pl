/** <module> review_example

This example demonstrates subsumption reasoning with union (disjunction)
and cardinality restrictions.

## Knowledge Base Description

This is a test case for subsumption queries involving union expressions
and cardinality constraints.

## Ontology Structure

- a subClassOf f subClassOf b (simple chain)
- a subClassOf unionOf([b, c, d]) (disjunction)
- a subClassOf minCardinality(5, r) (at least 5 r-successors)
- c subClassOf maxCardinality(4, r) (at most 4 r-successors)
- d subClassOf maxCardinality(3, r) (at most 3 r-successors)

## Query

```prolog
?- sub_class(a, b).
```

## Expected Result

The query `sub_class(a, b)` should succeed because:
1. Directly: a -> f -> b (via transitivity)
2. Via union: a -> unionOf([b,c,d])
   - If a is b, then done
   - If a is c, then a has at least 5 r-successors but c has at most 4 - contradiction
   - If a is d, then a has at least 5 r-successors but d has at most 3 - contradiction
   - So a must be b

## Demonstrated Features

- Subsumption with union expressions
- Cardinality restrictions
- Disjunctive reasoning (eliminating impossible alternatives)

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- use_module(library(trill)).

:- trill.

% =============================================================================
% Axioms
% =============================================================================

% Class hierarchy
subClassOf(a,f).
subClassOf(f,b).

% Disjunction: a is b or c or d
subClassOf(a,unionOf([b,c,d])).

% Cardinality restrictions creating contradictions
subClassOf(a,minCardinality(5,r)).   % a has at least 5 r-successors
subClassOf(c,maxCardinality(4,r)).   % c has at most 4 r-successors
subClassOf(d,maxCardinality(3,r)).   % d has at most 3 r-successors

% Query to test: sub_class(a,b).
