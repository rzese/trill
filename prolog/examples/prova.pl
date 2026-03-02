/** <module> prova

This is a test example demonstrating sameIndividual chains
(individual equality/identity reasoning).

## Knowledge Base Description

This simple test KB shows how TRILL handles chains of individual
equality assertions using sameIndividual.

## Ontology Structure

- Individual 'a' is of class 't'
- Individuals are connected through sameIndividual chains:
  - a = b
  - b = c
  - c = d
  - d = e

## Expected Inferences

Due to transitivity of equality:
- All of a, b, c, d, e refer to the same individual
- All of them should be inferred to be of class 't'

## Example Queries

```prolog
?- instanceOf(t, e, Expl).
% Should succeed since e is same as a, which is of class t

?- instanceOf(t, c, Expl).
% Should also succeed for the same reason
```

## Feature Tested

- **sameIndividual/1**: Declares that a list of individuals refer to
  the same real-world entity (OWL SameIndividual axiom)

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- use_module(library(trill)).

:- trill.

% =============================================================================
% Axioms
% =============================================================================

% Individual a is of class t
classAssertion(t,a).

% Individual c is of class t
classAssertion(t,c).

% Chain of individual equalities: a = b = c = d = e
sameIndividual([a,b]).
sameIndividual([b,c]).
sameIndividual([c,d]).
sameIndividual([d,e]).


% Chain of individual equalities: a = b = c = d = e
%sameIndividual([a,x]).
%sameIndividual([x,y]).
%sameIndividual([y,c]).