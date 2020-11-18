:- use_module(monotonic).

:- monotonic
    p/1.

:- dynamic (q/1, r/1) as monotonic.

p(X) :-
    q(X), \+ r(X).

