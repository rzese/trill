:- use_module(library(trill)).

:- trill.

% instanceOf(final,x,Expl).
% add_axiom(propertyAssertion(r,x,y)).
% resume_query(Expl).

classAssertion(a,x).
subClassOf(a,b).
subClassOf(b,final).


classAssertion(c,y).
subClassOf(c,d).

subClassOf(intersectionOf([b,someValuesFrom(r,d)]),final).