/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        jan@swi-prolog.org
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2020, SWI-Prolog Solutions b.v.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(monotonic,
          [ (monotonic)/1,              % :Spec
            sink/2,                     % :Goal, :OnAnswer
            dnf/2,                      % +NNF,-DNF
            generalize_head/3,

            op(1150, fx, monotonic)
          ]).
:- use_module(library(prolog_code)).

:- meta_predicate sink(0,0).


/** <module> Handle negation using monotonic tabling

This library deals with  program   transformation  to  exploit monotonic
tabling in the presense of  negation.   The  idea  of the transformation
comes from Edward Schwartz.

Notes

  - Currently deals with predicates holding only a single clause.
  - Does not (yet) deal with (if->then;else)
  - Can we optimize expressions to minimize the intermediate tables?
    For example, if there is a leading monotonic conjunction before the
    part that holds negations we can create a seperate monotonic
    predicate for this that feeds the negated part.
  - We could (alternatively) materialize the final relation as a
    list of facts.  When is that a good idea?
  - How to deal with propagation triggers?  Can/should we handle
    these in batches?
*/

%!  monotonic(:Spec)
%
%   Declare  the  predicate  indicators   from    Spec   to   be  tabled
%   monotonically by splitting the predicate body   into  a positive and
%   negative monotonic predicate and define   a  predicate that combines
%   the two.

monotonic(Spec) :-
    throw(error(context_error(nodirective, monotonic(Spec)), _)).

expand_monotonic((:- monotonic(Spec)),
                 Clauses) :-
    phrase(expand_monotonic_decl(Spec), Clauses).
expand_monotonic(Head :- Body0,
                 [ (:- table (PosPI,NegPI) as monotonic),
                   (Head :- PosHead, \+ NegHead),
                   (PosHead :- PosBody),
                   (NegHead :- NegBody)
                 ]) :-
    prolog_load_context(module, M),
    current_predicate(M:'expand monotonic'/1),
    \+ predicate_property(M:'expand monotonic'(_), imported_from(_)),
    M:'expand monotonic'(Head),
    expand_goal(Body0, Body),
    prefix_head(Head, pos_, PosHead),
    prefix_head(Head, neg_, NegHead),
    pi_head(PosPI, PosHead),
    pi_head(NegPI, NegHead),
    mono(Body, pos, PosBody),
    mono(Body, neg, NegBody).

expand_monotonic_decl(Var) -->
    { var(Var),
      !,
      instantiation_error(Var)
    }.
expand_monotonic_decl((A,B)) -->
    !,
    expand_monotonic_decl(A),
    expand_monotonic_decl(B).
expand_monotonic_decl(PI) -->
    { pi_head(PI, Head) },
    [ 'expand monotonic'(Head) ].

user:term_expansion(In, Out) :-
    \+ current_prolog_flag(xref, true),
    expand_monotonic(In, Out).


%!  mono(+Body, +PosNeg, -MonoBody)
%
%   Given the body goal Body which may hold negations expressed using
%   not/1, create
%
%     - If PosNeg is `pos`: MonoBody is a body goal with all negations
%       omitted.  MonoBody represents a monotonic upper bound for the
%       answers of Body.
%     - If PosNeg is `neg`: MonoBody is a body goal where negations
%       have been replaced by the negated literal, i.e., not(X) is
%       replaced by `X`.  This provides a monotonic representation
%       for answers from the `pos` body that should be removed to
%       obtain the same set of answers as Body.

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
mono_conj(Not, pos, true) :-
    is_not(Not, _),
    !.
mono_conj(Not, neg, Pos) :-
    is_not(Not, Pos),
    !.
mono_conj(A, _, A).

is_not(not(X),  X).
is_not(\+(X),   X).
is_not(tnot(X), X).

%!  sink(:Goal, :OnAnswer)
%
%   Run forall(Goal, OnAnswer) for all answer   of Goal and run OnAnswer
%   for any new answer that arrives on Goal.

sink(Goal, OnAnswer) :-
    prefix_head(Goal, sink_, Sink),
    assert((Sink :- Goal, OnAnswer)),
    pi_head(PI, Sink),
    table(PI as monotonic),
    forall(Sink, true).

%!  generalize_head(+Callable, -General, -Goal) is det.
%
%   True when General is a   most  general term (is_most_general_term/1)
%   with the same name and arity  as   Callable  and  running Goal makes
%   General equivalent to Callable. Goal is   `true` or a conjunction of
%   unification (=/2) calls.

generalize_head(Term, General, Goal) :-
    atom(Term),
    !,
    General = Term,
    Goal = true.
generalize_head(Term, General, Goal) :-
    compound_name_arity(Term, Name, Arity),
    compound_name_arity(General, Name, Arity),
    unifiable(General, Term, Unifier),
    pre_bind(Unifier, Goal, General).

pre_bind([], true, _).
pre_bind([X=Y|T], Goal, General) :-
    X = Y,
    is_most_general_term(General),
    !,
    pre_bind(T, Goal, General).
pre_bind([G0|T], Goal, General) :-
    pre_bind(T, G1, General),
    mkconj(G0, G1, Goal).

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

%!  prefix_head(+HeadIn, +Prefix, -Head)
%
%   Prefix the head name for HeadIn using   Prefix  to create Head. Both
%   heads have the same arguments.

prefix_head(Head0, _, _) :-
    var(Head0),
    !,
    instantiation_error(Head0).
prefix_head(M:Head0, Prefix, M:Head) :-
    !,
    prefix_head(Head0, Prefix, Head).
prefix_head(Head0, Prefix, Head) :-
    atom(Head0),
    !,
    atom_concat(Prefix, Head0, Head).
prefix_head(Head0, Prefix, Head) :-
    compound_name_arguments(Head0, Name0, Args),
    atom_concat(Prefix, Name0, Name),
    compound_name_arguments(Head, Name, Args).
