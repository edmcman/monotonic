:- module(monotonic,
          [ dnf/2                       % +NNF,-DNF
          ]).
:- use_module(library(prolog_code)).

table_monotonic(Head) :-
    findall((Head:-Body), gen_clause(Head, Body), Clauses).

gen_clause(Head, Body) :-
    functor(Head, Name, Arity),
    functor(Head0, Name, Arity),
    clause(Head0, Body0),
    (   is_most_general_term(Head0)
    ->  Head = Head0,
        Body = Body0
    ;   bind(1, Arity, Head, Head0, Bind),
        mkconj(Bind, Body0, Body)
    ).

bind(I, Arity, GenHead, Head, Bind) :-
    I =< Arity,
    !,
    arg(I, Head, A),
    arg(I, GenHead, GA),
    (   var(A)
    ->  A = GA,
        Bind0 = true
    ;   Bind0 = (GA=A)
    ),
    I2 is I+1,
    bind(I2, Arity, GenHead, Head, Bind1),
    mkconj(Bind0, Bind1, Bind).
bind(_, _, _, _, true).

head_unifications(Head, GenHead, Goal) :-
    functor(Head, _Name, Arity),
    head_unifications(1, Arity, Head, GenHead, Goal).

head_unifications(I, Arity, Head, GenHead, Goal) :-
    I =< Arity,
    (   arg(I, Head, Arg),
        var(Arg),
        arg(I2, Head, Arg2),
        I2 > I,
        contains_var(Arg, Arg2)
    ->  arg(I, GenHead, GenArg),
        Goal0 = (GenArg = Arg)
    ;   Goal0 = true
    ),
    I2 is I+1,
    head_unifications(I2, Arity, Head, GenHead, Goal1),
    mkconj(Goal0, Goal1, Goal).
head_unifications(_, _, _, _, true).

mono(A, _, A) :-
    var(A),
    !.
mono((A;B), Pos, (AP,BP)) :-
    !,
    mono_conj(A, Pos, AP),
    mono_conj(B, Pos, BP).
mono(A, Pos, AP) :-
    mono_conj(A, Pos, AP).

mono_conj(A, _, A) :-
    var(A),
    !.
mono_conj((A,B), Pos, Conj) :-
    mono_conj(A, Pos, AP),
    mono_conj(B, Pos, BP),
    mkconj(AP, BP, Conj).
mono_conj(not(_), pos, true) :-
    !.
mono_conj(not(A), neg, A) :-
    !.
mono_conj(A, _, A).


%!  dnf(+NNF, -DNF)
%
%   Convert a formula in NNF to Disjunctive Normal Form (DNF)

dnf((A0;B0), (A;B)) :-
    !,
    dnf(A0, A),
    dnf(B0, B).
dnf((A0,B0), DNF):-
    !,
    dnf(A0, A1),
    dnf(B0, B1),
    dnf1((A1,B1), DNF).
dnf(DNF, DNF).

dnf1((A0, (B;C)), (P;Q)) :-
    !,
    dnf1((A0,B), P),
    dnf1((A0,C), Q).
dnf1(((B;C), A0), (P,Q)) :-
    !,
    dnf1((A0,B), P),
    dnf1((A0,C), Q).
dnf1(DNF, DNF).
