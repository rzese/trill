/** <module> trill_test

This module provides testing utilities for the TRILL test suite.

## Overview

The trill_test module provides helper predicates for running and validating
TRILL tests. It supports:

1. Running queries with timing information
2. Comparing floating-point probabilities with epsilon tolerance
3. Comparing explanation sets regardless of order
4. Formula equivalence checking

## Main Predicates

### Test Execution
- run/1: Execute a query with timing, expecting success
- run_fail/1: Execute a query expecting failure

### Probability Comparison
- close_to/2: Check if value V is within epsilon of target T
- close_to/3: Check if value V is within specified epsilon E of target T

### Explanation Comparison
- same_expl/2: Check if two explanation lists contain the same explanations
- one_of/2: Check if an explanation is in a list of correct explanations

### Formula Testing
- test_formula/2: Test equivalence of two formulas

## Default Epsilon

The default epsilon for probability comparison is 0.09, suitable for
most probabilistic reasoning tests.

## Usage Example

```prolog
% Run a probability query and check the result
run((prob_instanceOf(class, ind, Prob), close_to(Prob, 0.5))).

% Run an explanation query and check the result
run((instanceOf(class, ind, Expl), one_of(Expl, [[ax1, ax2], [ax3, ax4]]))).
```

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:-module(trill_test,
  [close_to/2,close_to/3,run/1,run_fail/1]).

:- meta_predicate run(:).
:- meta_predicate run_fail(:).

/**
 * run(:Goal) is semidet
 *
 * Executes Goal with timing information.
 * Goal should be of the form (Query, Validation) where Query is the
 * TRILL query to execute and Validation checks the result.
 */
run(M:H):-
	copy_term(H,NH),
	numbervars(NH),
%	NH=(_Query,close_to('P',_Prob)),
	format("~p.~n",[NH]),
	(H=(G,R)),
	time(call(M:G)),!,
	format("\t~p.~n~n",[G]),
	call(R).

/**
 * run_fail(:Goal) is semidet
 *
 * Executes Goal expecting it to fail.
 * Succeeds if Goal fails, fails if Goal succeeds.
 */
run_fail(M:H):-
	copy_term(H,NH),
	numbervars(NH),
%	NH=(_Query,close_to('P',_Prob)),
	format("~p.~n",[NH]),
	time(call(M:H))->fail;true.

% Default epsilon for probability comparisons
epsilon(0.09).

/**
 * close_to(+Value, +Target) is semidet
 *
 * Checks if Value is within default epsilon of Target.
 */
close_to(V,T):-
	epsilon(E),
	TLow is T-E,
	THigh is T+E,
	TLow<V,
	V<THigh.

/**
 * close_to(+Value, +Target, +Epsilon) is semidet
 *
 * Checks if Value is within Epsilon of Target.
 */
close_to(V,T,E):-
	TLow is T-E,
	THigh is T+E,
	TLow<V,
	V<THigh.

/**
 * same_expl(+Expls, +CorrExpls) is semidet
 *
 * Checks if two lists of explanations contain the same explanations,
 * regardless of order within lists.
 */
same_expl(Expl, CorrExpl):-
	length(Expl,NE),
	length(CorrExpl,NE),
	same_expl_int(Expl, CorrExpl).

same_expl_int([],_CorrExpls).

same_expl_int([Expl|Expls],CorrExpls):-
  sort(Expl,ExplSort),
  member(X,CorrExpls),
  sort(X,ExplSort),!,
  same_expl_int(Expls,CorrExpls).

/**
 * one_of(+Expl, +CorrExpls) is semidet
 *
 * Checks if Expl matches any explanation in CorrExpls.
 */
one_of(Expl,CorrExpls):-
  sort(Expl,ExplSort),
  member(X,CorrExpls),
  sort(X,ExplSort),!.

/**
 * test_formula(+F1, +F2) is semidet
 *
 * Checks that F1 and F2 are not equivalent formulas.
 */
test_formula(F1,F2):-
  \+ trill:test(_,F1,F2),
  \+ trill:test(_,F2,F1).

