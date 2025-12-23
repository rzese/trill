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

:- tornado.

% =============================================================================
% Axioms
% =============================================================================

% Individual a is of class t
classAssertion(t,a).

% Chain of individual equalities: a = b = c = d = e
%classAssertion(complementOf(t),a).
%classAssertion(k,a).
%subClassOf(k,t).

propertyAssertion(r,a,z).
propertyAssertion(s,a,b).
propertyAssertion(r,b,z).

sameIndividual([a,b]).
sameIndividual([a,f]).
%sameIndividual([b,c]).
%sameIndividual([c,d]).
%sameIndividual([d,e]).