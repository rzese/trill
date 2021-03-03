:-use_module(library(trill)).

:- init_trill.

/*
An inconsistent KB representing the famous example from the literature on non-monotonic reasoning Nixon Example.
*/

/** <examples>

?- prob_instanceOf(complementOf(pacifist),nixon,Prob).
?- instanceOf(complementOf(pacifist),nixon,ListExpl).

*/

subClassOf(quaker,pacifist).
subClassOf(republican,complementOf(pacifist)).
subClassOf(president,republican).
subClassOf(president,quaker).

subClassOf(regular,president).
subClassOf(impeachment,complementOf(president)).
classAssertion(impeachment,nixon).
classAssertion(regular,nixon). 


annotationAssertion('disponte:probability',subClassOf(quaker,pacifist),literal('0.98')).
annotationAssertion('disponte:probability',subClassOf(republican,complementOf(pacifist)),literal('0.7')).
annotationAssertion('disponte:probability',subClassOf(president,republican),literal('0.5')).
annotationAssertion('disponte:probability',subClassOf(president,quaker),literal('0.5')).
annotationAssertion('disponte:probability',subClassOf(regular,president),literal('1.0')).
annotationAssertion('disponte:probability',subClassOf(impeachment,complementOf(president)),literal('0.9')).
