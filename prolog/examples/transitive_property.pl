/** <module> transitive_property

This example demonstrates TRILL's handling of transitive and symmetric
properties, as well as inverse property declarations.

## Knowledge Base Description

This is a test case for role (property) characteristics:
- Transitive properties
- Symmetric properties
- Inverse properties

## Ontology Structure

- Property tp is transitive: if tp(a,b) and tp(b,c) then tp(a,c)
- Property tp is symmetric: if tp(a,b) then tp(b,a)
- Property tpi is the inverse of tp: tp(a,b) iff tpi(b,a)

## Assertions

- tp(a, b) holds
- tp(b, c) holds

## Expected Inferences

Due to transitivity:
- tp(a, c) holds (from tp(a,b) and tp(b,c))

Due to symmetry:
- tp(b, a) holds
- tp(c, b) holds

Due to inverse:
- tpi(b, a), tpi(c, b), etc.

## Property Characteristics Tested

1. **transitiveProperty/1**: Marks a property as transitive
2. **symmetricProperty/1**: Marks a property as symmetric
3. **inverseProperties/2**: Declares two properties as inverses

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- use_module(library(trill)).


:- trill. % or :- trillp. or :- tornado.

% =============================================================================
% Axioms
% =============================================================================

% Property assertions
propertyAssertion( tp, a, b).
propertyAssertion( tp, b, c).

% Property characteristics
transitiveProperty(tp).
symmetricProperty(tp).
inverseProperties(tp,tpi).