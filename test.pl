:- use_module(monotonic).

:- dynamic (q/1, r/1) as monotonic.

:- monotonic p/1.

p(X) :-
    q(X).

:- monotonic np/1.

np(X) :-
    q(X), \+ r(X).
