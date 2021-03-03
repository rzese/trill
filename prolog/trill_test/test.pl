

:- format(user_error,
	  'TRILL test suite.  To run all tests run ?- test.~n~n', []).
test:-
  use_module(library(trill_test/test_trill)),
  test_trill.
