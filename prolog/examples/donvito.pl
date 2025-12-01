/** <module> donvito

This example demonstrates probabilistic reasoning about property chains
and class membership with DISPONTE annotations.

## Knowledge Base Description

This is a simple example showing how to determine if Don Vito is a
"good person" based on pet ownership and probabilistic inference.

## Inference Chain

1. Don Vito has a pet (Tom the cat): propertyAssertion(hasPet, donVito, tom)
2. Tom is a cat: classAssertion(cat, tom)
3. Cats are pets: subClassOf(cat, pet)
4. hasPet is a subproperty of hasAnimal
5. Having an animal that is a pet makes you a nature lover
6. Nature lovers are good persons (with probability 0.2)

## Probabilistic Annotation

The axiom `natureLover subClassOf goodPerson` has probability 0.2,
meaning there's a 20% chance that being a nature lover implies being
a good person.

## Example Query

```prolog
?- prob_instanceOf(goodPerson, donVito, Prob).
% Computes the probability that Don Vito is a good person
```

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:-use_module(library(trill)).

:- trill. % or :- trillp. or :- tornado.

/** <examples>

?- prob_instanceOf(goodPerson,donVito,Prob).

*/

% =============================================================================
% Axioms
% =============================================================================

% Tom is a cat belonging to Don Vito
classAssertion(cat, tom).
propertyAssertion(hasPet, donVito, tom).

% Class hierarchy
subClassOf(cat, pet).
subClassOf(someValuesFrom(hasAnimal, pet), natureLover).
subClassOf(natureLover,goodPerson).

% Property hierarchy
subPropertyOf(hasPet,hasAnimal).
 
% Probabilistic annotation: nature lovers are good persons with P=0.2
annotationAssertion('disponte:probability',subClassOf(natureLover,goodPerson),literal('0.2')).
 
