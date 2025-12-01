/** <module> example_or_rule

This example demonstrates TRILL's handling of disjunction (union)
using the or_rule tableau expansion rule, along with complex
probabilistic annotations.

## Knowledge Base Description

This is a test case for the or_rule and complex class expressions
with probabilistic annotations. The KB contains multiple axioms
with nested class expressions and DISPONTE probabilities.

## Ontology Structure

The KB includes several complex axioms:
- Intersection and union combinations
- someValuesFrom and allValuesFrom restrictions
- Cardinality restrictions
- Complement (negation) expressions

## Key Axioms

1. a subClassOf (b AND someValuesFrom(r, e)) with P=0.1
2. a subClassOf (f OR allValuesFrom(r, b)) with P=0.2
3. b subClassOf (c AND d) with P=0.3
4. c subClassOf (minCardinality(1, r) AND e) with P=0.4
5. b subClassOf NOT(e) with P=0.5
6. b subClassOf NOT(f) with P=0.6
7. Complex union expressions with various probabilities

## Tableau Rule Tested

- **or_rule**: Handles unionOf expressions by creating choice points
  for each disjunct. This is a non-deterministic rule.

## Notes

The commented code shows debugging notes about how clashes are
generated in the or_rule context and how explanations are built.

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- use_module(library(trill)).

:- trill.

% =============================================================================
% Axioms
% =============================================================================

% Complex class inclusion axioms
subClassOf(a,intersectionOf([b,someValuesFrom(r,e)])).
subClassOf(a,unionOf([f,allValuesFrom(r,b)])).
subClassOf(b,intersectionOf([c,d])).
subClassOf(c,intersectionOf([minCardinality(1,r),e])).
subClassOf(b,complementOf(e)).

subClassOf(b,complementOf(f)).

subClassOf(a,unionOf([intersectionOf([c,complementOf(c)]),complementOf(f)])).
subClassOf(a, unionOf([complementOf(c),complementOf(f)])).
subClassOf(a, unionOf([complementOf(c),complementOf(d)])).

% =============================================================================
% DISPONTE Probabilistic Annotations
% =============================================================================

annotationAssertion('disponte:probability',subClassOf(a,intersectionOf([b,someValuesFrom(r,e)])),literal('0.1')).
annotationAssertion('disponte:probability',subClassOf(a,unionOf([f,allValuesFrom(r,b)])),literal('0.2')).
annotationAssertion('disponte:probability',subClassOf(b,intersectionOf([c,d])),literal('0.3')).
annotationAssertion('disponte:probability',subClassOf(c,intersectionOf([minCardinality(1,r),e])),literal('0.4')).
annotationAssertion('disponte:probability',subClassOf(b,complementOf(e)),literal('0.5')).

annotationAssertion('disponte:probability',subClassOf(b,complementOf(f)),literal('0.6')).

annotationAssertion('disponte:probability',subClassOf(a,unionOf([intersectionOf([c,complementOf(c)]),complementOf(f)])),literal('0.7')).
annotationAssertion('disponte:probability',subClassOf(a, unionOf([complementOf(c),complementOf(f)])),literal('0.8')).
annotationAssertion('disponte:probability',subClassOf(a, unionOf([complementOf(c),complementOf(d)])),literal('0.9')).


% =============================================================================
% Additional test axioms (commented out)
% =============================================================================
/*
subClassOf(a,complementOf(f)).
subClassOf(unionOf([complementOf(c),complementOf(f)]),z).
subClassOf(a, unionOf([complementOf(c),complementOf(f)])).

classAssertion(a,1).
*/

% TODO: Notes for testing
% - Check how clashes are inserted in or_rule case
% - When arriving at complement(e) from a->b or c, c->e, there should be no clash
% - Consider how to integrate partial explanations leading to clash
