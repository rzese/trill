:- use_module(library(trill)).

:- trill.

classAssertion(t,a).
%classAssertion(complementOf(t),a).
classAssertion(k,a).
subClassOf(k,t).

propertyAssertion(r,a,z).
propertyAssertion(s,a,b).
propertyAssertion(r,b,z).

sameIndividual([a,b]).
sameIndividual([a,f]).
sameIndividual([b,c]).
sameIndividual([c,d]).
sameIndividual([d,e]).