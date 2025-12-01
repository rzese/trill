/** <module> pizza

This example demonstrates TRILL's ability to detect inconsistencies
and unsatisfiable concepts in an OWL ontology.

## Knowledge Base Description

This is an extract of the well-known Pizza ontology, simplified to demonstrate
class inconsistency detection. The example comes from:
  N. Drummond. A Practical Guide to Building OWL Ontologies, v1.2.
  University of Manchester, 2009.

## Ontology Structure

- soyCheeseTopping is a subclass of both cheeseTopping and vegetableTopping
- tofu is a subclass of soyCheeseTopping
- cheeseTopping and vegetableTopping are declared disjoint

This creates an unsatisfiable class (tofu) because:
  - tofu is a soyCheeseTopping
  - soyCheeseTopping is both a cheeseTopping AND a vegetableTopping
  - But cheeseTopping and vegetableTopping cannot overlap (disjoint)

## Example Queries

```prolog
?- unsat('tofu', Expls).
% Returns explanations for why tofu is unsatisfiable

?- inconsistent_theory(Expls).
% Checks if the entire KB is inconsistent
```

## Demonstrated Features

- Class hierarchy with multiple inheritance
- Disjointness constraints
- Unsatisfiability detection
- Equivalence axioms

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:-use_module(library(trill)).

:- trill. % or :- trillp. or :- tornado.

/** <examples>

?- unsat('tofu',Expls).
?- inconsistent_theory(Expls).

*/

% =============================================================================
% Axioms
% =============================================================================

% soyCheeseTopping is a type of cheese topping
subClassOf(soyCheeseTopping,cheeseTopping).

% soyCheeseTopping is also a type of vegetable topping (problematic!)
subClassOf(soyCheeseTopping,vegetableTopping).

% tofu is a soyCheeseTopping
subClassOf(tofu,soyCheeseTopping).

% cheeseTopping and vegetableTopping are mutually exclusive
% This causes tofu to be unsatisfiable since it's in both
disjointClasses([cheeseTopping,vegetableTopping]).

% Equivalence axiom demonstrating class equivalence
equivalentClasses([pizza1,pizza2]). %pizza1 = pizza2

% classAssertion(tofu,'tofu-1').

