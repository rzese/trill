:-use_module(library(trill)).

:- init_trill.

/** <examples>

?- instanceOf(commander,john,Expl).

*/
subClassOf(allValuesFrom(commands,soldier),commander).
classAssertion(guard,pete).
classAssertion(guard,al).
classAssertion(allValuesFrom(commands,guard),john).
equivalentClasses([guard,soldier]).

annotationAssertion('disponte:probability',classAssertion(guard,pete),literal('0.8')).
annotationAssertion('disponte:probability',subClassOf(allValuesFrom(commands,soldier),commander),literal('0.3')).
annotationAssertion('disponte:probability',equivalentClasses([guard,soldier]),literal('0.9')).