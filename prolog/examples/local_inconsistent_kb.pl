/** <module> local_inconsistent_kb

This example demonstrates TRILL's handling of local vs global inconsistency
in a knowledge base.

## Knowledge Base Description

This is a toy knowledge base designed to test local consistency handling.
The KB contains individuals that lead to local inconsistencies when certain
queries are made, without making the entire KB inconsistent.

## Ontology Structure

- Individual ind1 is of class a
- Class a is a subclass of allValuesFrom(r, x)
- ind1 is related to ind2 via property r
- ind2 is of class complementOf(x) (when uncommented)
- This creates an inconsistency: ind2 must be x (via the universal restriction)
  but is also not-x

## Local vs Global Inconsistency

- **Local inconsistency**: Query `instanceOf(b, ind1, E)` involves the
  inconsistent part of the KB and will detect inconsistency
- **Global**: Query `inconsistent_theory(E)` checks full KB consistency
- **Locally consistent queries**: `property_value(r, ind3, ind4, E)` and
  `instanceOf(x, ind4, E)` don't touch the inconsistent part

## Example Queries

```prolog
?- instanceOf(b, ind1, E).
% Locally inconsistent - will detect inconsistency

?- inconsistent_theory(E).
% Returns explanation for KB inconsistency

?- property_value(r, ind3, ind4, E).
% Locally consistent query

?- instanceOf(x, ind4, E).
% Locally consistent query
```

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:-use_module(library(trill)).

:- trill. % or :- trillp. or :- tornado.

/** <examples>

?- instanceOf(b,ind1,E). % locally inconsistent
?- inconsistent_theory(E).
E = [classAssertion(a, ind1), 
     classAssertion(complementOf(x), ind2),
     subClassOf(a, allValuesFrom(r, x)),
     propertyAssertion(r, ind1, ind2)
    ].
?- property_value(r,ind3,ind4,E). % locally consistent
?- instanceOf(x,ind4,E). % locally consistent


*/

% =============================================================================
% Axioms
% =============================================================================

% ind1 is of class a
classAssertion(a,ind1).

% Class a implies all r-fillers are of class x
subClassOf(a,allValuesFrom(r,x)).

% ind1 is related to ind2 via property r
propertyAssertion(r,ind1,ind2).

% Uncomment to create inconsistency: ind2 is not-x but must be x
%classAssertion(complementOf(x),ind2). %TODO uncomment

% Class hierarchy: a subClassOf b
subClassOf(a,b).

% Additional individuals for testing local consistency
propertyAssertion(u,ind3,ind4).
subPropertyOf(u,s).
subPropertyOf(s,t).
subPropertyOf(t,r).
classAssertion(a,ind3).