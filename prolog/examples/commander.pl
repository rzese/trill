/** <module> commander

This example demonstrates TRILL's reasoning with universal restrictions
(allValuesFrom) and equivalent classes.

## Knowledge Base Description

This is a simple military hierarchy example showing:
- Commander: Someone who commands only soldiers
- Guard: A type of soldier
- Equivalence between guard and soldier

## Ontology Structure

- john commands only guards
- Guards (pete, al) are soldiers (via equivalence)
- Anyone commanding only soldiers is a commander

## Inference

The query `instanceOf(commander, john, Expl)` should succeed because:
1. john commands only guards (via allValuesFrom(commands, guard))
2. guard is equivalent to soldier
3. Therefore, john commands only soldiers
4. Anyone commanding only soldiers is a commander

## Example Query

```prolog
?- instanceOf(commander, john, Expl).
% Returns explanation for why john is a commander
```

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:-use_module(library(trill)).

:- trill. % or :- trillp. or :- tornado.

/** <examples>

?- instanceOf(commander,john,Expl).

*/

% =============================================================================
% Axioms
% =============================================================================

% Anyone who commands only soldiers is a commander
subClassOf(allValuesFrom(commands,soldier),commander).

% Individuals pete and al are guards
classAssertion(guard,pete).
classAssertion(guard,al).

% john commands only guards
classAssertion(allValuesFrom(commands,guard),john).

% Guards are equivalent to soldiers
equivalentClasses([guard,soldier]).

% commands is a subproperty of commands1
subPropertyOf(commands,commands1).
