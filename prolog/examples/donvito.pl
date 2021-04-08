:-use_module(library(trill)).

:- init_trill.

/** <examples>

?- prob_instanceOf(goodPerson,donVito,Prob).

*/

classAssertion(cat, tom).
propertyAssertion(hasPet, donVito, tom).
classAssertion(cat, tom2).
propertyAssertion(hasPet, donVito, tom2).
subClassOf(cat, pet).
subClassOf(someValuesFrom(hasAnimal, pet), natureLover).
subClassOf(natureLover,goodPerson).
subPropertyOf(hasPet,hasAnimal).
 
annotationAssertion('disponte:probability',subClassOf(natureLover,goodPerson),literal('0.2')).
 
