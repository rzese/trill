:-use_module(library(trill)).

%:- trill. % or :- trillp. or :- tornado.

/*
An inconsistent KB representing the classical examples about flying penguins.
*/

/** <examples>

?- prob_instanceOf(fly,pingu,Prob).
?- instanceOf(fly,pingu,ListExpl).

*/

subClassOf(bird,fly).
subClassOf(penguin,bird).
subClassOf(penguin,complementOf(fly)).
classAssertion(penguin,pingu).

annotationAssertion('disponte:probability',subClassOf(bird,fly),literal('0.999999999')).
%annotationAssertion('disponte:probability',subClassOf(penguin,complementOf(fly)),literal('0.9')).
 
