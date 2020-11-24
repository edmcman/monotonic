# Experiments using Monotonic tabling

This repo is a playground to study applying monotonic tabling in
practice. It is studied in the context of
[pharos](https://github.com/cmu-sei/pharos)

## Handle negation

Negation is clearly not monotonic. One of   the goals of this library is
to deal with negation.  We  do  this   by  changing  a  conjunction that
possibly holds negations into two monotonic derivations:

  - One producing a positive upperbound by removing all negations.
  - One representing the difference between the upperbound and the
    correct result by replacing all negated goals with goal itself.

For example, p(X) :- q(X), \+ r(X) is translated into

  - pos_p(X) :- q(X).
  - neg_p(X) :- q(X), r(X).

After doing so, we currently implement two ways to get the merged
result:

  - Represented as a rule p(X) :- pos_p(X), \+ neg_p(X).
  - Represetned as facts.  In this case the propagated results from
    the two monotonic tables are used to manage a set of facts (clauses)
    for p/1.
