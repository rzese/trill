:- use_module(library(trill)).


:- trill. % or :- trillp. or :- tornado.

propertyAssertion( tp, a, b).
propertyAssertion( tp, b, c).
transitiveProperty(tp).
symmetricProperty(tp).
inverseProperties(tp,tpi).