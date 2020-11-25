:- use_module(monotonic).

:- dynamic (d1/1, d2/1) as monotonic.
:- monotonic t/1.

t(X) :- format('Expensive computation occurs here ~w~n', X), d1(X), not(d2(X)). %, format('done ~w~n', X).


test :-
    writeln('asserting'),
    assert(d1(1)),
    writeln('calling t'),
    t(_),
    writeln('asserting'),
    assert(d1(2)),
    assert(d2(1)),
    writeln('calling t, I do not think this should cause recomputation'),
    t(_).

:- test.

%!  l(Name)
%
%   List link clause as well as the positive and/or negative that exist.

l(Name) :-
    forall(current_predicate(Name, Head),
           (   functor(Head, Name, Arity),
               atom_concat(pos_, Name, Pos),
               atom_concat(neg_, Name, Neg),
               listing(Name/Arity),
               list_existing(Pos/Arity),
               list_existing(Neg/Arity)
          )).

list_existing(PI) :-
    current_predicate(PI),
    !,
    listing(PI).
list_existing(_).
