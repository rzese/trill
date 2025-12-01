/** <module> example_max_rule

This example demonstrates TRILL's handling of maximum cardinality
restrictions using the max_rule tableau expansion rule.

## Knowledge Base Description

This is a test case for the maximum cardinality restriction handling.
The max_rule creates non-deterministic choices when an individual has
more role successors than allowed by the restriction.

## Ontology Structure

- Class a is a subclass of maxCardinality(1, s, c)
  - This means: members of a have at most 1 s-successor that is a c
- Individual 1 is of class a
- Individual 1 has s-relationships to individuals 2, 3, and 4
- All of 2, 3, and 4 are of class c
- Additionally, 2, 3, and 4 have mutually disjoint classes (b, e, f)

## Inconsistency

Since individual 1 is of class a, it should have at most 1 s-successor
of type c. But it has 3 (individuals 2, 3, 4 are all c).

The max_rule will try to merge individuals to satisfy the restriction,
but since 2, 3, 4 are pairwise disjoint (b, e, f are disjoint), no
valid merge is possible, leading to inconsistency.

## Tableau Rule Tested

- **max_rule**: Handles maxCardinality restrictions by attempting to
  merge individuals that exceed the cardinality limit

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- use_module(library(trill)).

:- trill.

% =============================================================================
% Axioms
% =============================================================================

% Class a has at most 1 s-successor of type c
subClassOf('a', maxCardinality(1, 's', 'c')).

% Individuals 2, 3, 4 are all of class c
classAssertion('c', '2').
classAssertion('c', '3').
classAssertion('c', '4').

% But they belong to disjoint classes (prevents merging)
classAssertion('b', '2').
classAssertion('e', '3').
classAssertion('f', '4').
disjointClasses(['b','e','f']).

% Individual 1 is of class a and has 3 s-successors
classAssertion('a', '1').
propertyAssertion('s', '1', '2').
propertyAssertion('s', '1', '3').
propertyAssertion('s', '1', '4').