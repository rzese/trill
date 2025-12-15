/** <module> test

TRILL Test Suite - Main Entry Point

This module provides the main entry point for running the TRILL test suite.
The tests validate the core functionality of the TRILL probabilistic
description logic reasoner.

## Running Tests

To run all tests, execute:
```prolog
?- test.
```

## Test Organization

The test suite is organized into separate modules:
- test_trill: Tests for the standard TRILL algorithm
- test_trillp: Tests for TRILL^P (pinpointing formulas)
- test_tornado: Tests for TORNADO (BDD-based reasoning)

## Tested Knowledge Bases

The tests cover various example knowledge bases:
- BRCA (breast cancer risk factors)
- BioPAX (metabolic pathways)
- DBPedia (Wikipedia extract)
- Commander (universal restrictions)
- JohnEmployee (basic reasoning)
- PeoplePets (probabilistic reasoning)
- Vicodi (cultural heritage)
- Pizza (unsatisfiability detection)

## Example Tests

Each test typically checks:
1. Probabilistic query results (close_to/2 comparison)
2. Explanation structure (one_of/2 or same_expl/2 comparison)
3. Explanation count (aggregate_all)

@author Riccardo Zese
@license Artistic License 2.0
@copyright Riccardo Zese
*/

:- format(user_error,
	  'TRILL test suite.  To run all tests run ?- test.~n~n', []).

/**
 * test is det
 *
 * Runs the complete TRILL test suite.
 */
test:-
  use_module(library(trill_test/test_trill)),
  test_trill.
  %unload_file(library(trill_test/test_trill)),
  %use_module(library(trill_test/test_trill_prob)),
  %test_trill_prob,
  %unload_file(library(trill_test/test_trill_prob)),
  %use_module(library(trill_test/test_trillp)),
  %test_trillp,
  %unload_file(library(trill_test/test_trillp)),
  %use_module(library(trill_test/test_tornado)),
  %test_tornado.
