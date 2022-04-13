:- use_module(library(trill)).


:- trill. % or :- trillp. or :- tornado.

classAssertion( smartphone, sm0815).

propertyAssertion( tp, a, b).
propertyAssertion( tp, b, c).
transitiveProperty(tp).
%symmetricProperty(tp).
%inverseProperties(tp,tpi).