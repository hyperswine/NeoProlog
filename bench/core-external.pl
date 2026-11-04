app([], L, L).
app([H|T], L, [H|R]) :- app(T, L, R).
nrev([], []).
nrev([H|T], R) :- nrev(T, RT), app(RT, [H], R).
range(N, N, [N]).
range(I, N, [I|T]) :- I < N, I1 is I + 1, range(I1, N, T).
loop(0).
loop(N) :- N > 0, N1 is N - 1, loop(N1).
bench_nrev(0).
bench_nrev(K) :- K > 0, range(1, 30, L), nrev(L, R),
  R == [30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1],
  K1 is K - 1, bench_nrev(K1).
fib(0, 0). fib(1, 1).
fib(N, F) :- N > 1, N1 is N - 1, N2 is N - 2, fib(N1, F1), fib(N2, F2), F is F1 + F2.
queens(N, Qs) :- range(1, N, Ns), perm(Ns, Qs), safe(Qs).
perm([], []).
perm(L, [H|T]) :- sel(H, L, R), perm(R, T).
sel(X, [X|T], T).
sel(X, [H|T], [H|R]) :- sel(X, T, R).
safe([]).
safe([Q|Qs]) :- noatt(Q, Qs, 1), safe(Qs).
noatt(_, [], _).
noatt(Q, [Q1|Qs], D) :- Q =\= Q1, D1 is Q1 - Q, D1 =\= D, D2 is Q - Q1, D2 =\= D, D3 is D + 1, noatt(Q, Qs, D3).

% Unification-heavy workloads (2026-11-04), written without cuts so every
% system runs the same search.
right_of(X, Y, [Y, X|_]).
right_of(X, Y, [_|T]) :- right_of(X, Y, T).
next_to(X, Y, L) :- right_of(X, Y, L).
next_to(X, Y, L) :- right_of(Y, X, L).
mem(X, [X|_]).
mem(X, [_|T]) :- mem(X, T).
zebra(Owner) :-
  Hs = [h(_, norwegian, _, _, _), _, h(_, _, _, milk, _), _, _],
  mem(h(red, english, _, _, _), Hs),
  mem(h(_, spanish, dog, _, _), Hs),
  mem(h(green, _, _, coffee, _), Hs),
  mem(h(_, ukrainian, _, tea, _), Hs),
  right_of(h(green, _, _, _, _), h(ivory, _, _, _, _), Hs),
  mem(h(_, _, snails, _, winstons), Hs),
  mem(h(yellow, _, _, _, kools), Hs),
  next_to(h(_, _, _, _, chesterfields), h(_, _, fox, _, _), Hs),
  next_to(h(_, _, _, _, kools), h(_, _, horse, _, _), Hs),
  mem(h(_, _, _, orange_juice, lucky_strikes), Hs),
  mem(h(_, japanese, _, _, parliaments), Hs),
  next_to(h(_, norwegian, _, _, _), h(blue, _, _, _, _), Hs),
  mem(h(_, Owner, zebra, _, _), Hs).
bench_zebra(0, O) :- zebra(O).
bench_zebra(K, O) :- K > 0, once(zebra(_)), K1 is K - 1, bench_zebra(K1, O).
d(add(U, V), X, add(DU, DV)) :- d(U, X, DU), d(V, X, DV).
d(sub(U, V), X, sub(DU, DV)) :- d(U, X, DU), d(V, X, DV).
d(times(U, V), X, add(times(DU, V), times(U, DV))) :- d(U, X, DU), d(V, X, DV).
d(quo(U, V), X, quo(sub(times(DU, V), times(U, DV)), pw(V, 2))) :- d(U, X, DU), d(V, X, DV).
d(pw(U, N), X, times(DU, times(N, pw(U, N1)))) :- integer(N), N1 is N - 1, d(U, X, DU).
d(neg(U), X, neg(DU)) :- d(U, X, DU).
d(ex(U), X, times(ex(U), DU)) :- d(U, X, DU).
d(ln(U), X, times(DU, quo(1, U))) :- d(U, X, DU).
d(X, X, 1).
d(C, X, 0) :- ground(C), \+ C == X.
expr1(add(add(pw(x, 3), times(4, pw(x, 2))), sub(times(7, x), 9))).
expr2(quo(times(ex(x), ln(add(x, 1))), add(pw(x, 2), 1))).
expr3(times(times(times(times(times(times(times(times(times(x, x), x), x), x), x), x), x), x), x)).
expr4(quo(quo(quo(quo(quo(quo(quo(quo(quo(x, x), x), x), x), x), x), x), x), x)).
deriv_all :- expr1(A), d(A, x, _), expr2(B), d(B, x, _), expr3(C), d(C, x, _), expr4(D), d(D, x, _).
bench_deriv(0).
bench_deriv(K) :- K > 0, once(deriv_all), K1 is K - 1, bench_deriv(K1).
remove(_, [], []).
remove(P, [I|Is], Nis) :- 0 is I mod P, remove(P, Is, Nis).
remove(P, [I|Is], [I|Nis]) :- X is I mod P, X =\= 0, remove(P, Is, Nis).
sieve([], []).
sieve([P|Xs], [P|Ys]) :- remove(P, Xs, Zs), sieve(Zs, Ys).
len([], 0).
len([_|T], N) :- len(T, M), N is M + 1.
primes(N, K) :- range(2, N, L), sieve(L, Ps), len(Ps, K).


% Current Core's loaded-query external comparison, 2026-10-18.
% The prefix of this file is a byte-for-byte copy of bench/bench.pl.
% Algorithms and inputs match bench/core-major.hs; reverse uses 100 repeats,
% unlike bench/run.py and the older runtime-compare.pl, which use 3000.

external_case('core-nrev', Result) :-
    once((bench_nrev(100), range(1, 30, L), nrev(L, Result))).
external_case('core-loop', Result) :- once((loop(90000), Result = 90000)).
external_case('core-fib', Result) :- once(fib(25, Result)).
external_case('core-queens', Result) :- once(queens(8, Result)).

external_valid('core-loop', [90000]).
external_valid('core-fib', [75025]).
external_valid('core-nrev', [Result]) :-
    Result == [30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1].
external_valid('core-queens', [Columns]) :-
    external_length(Columns, 8), external_queen_rows(Columns).

% The queens checker does not reuse generator perm/safe/noatt predicates.
external_length([], 0).
external_length([_|Tail], N) :- external_length(Tail, M), N is M + 1.
external_queen_rows([]).
external_queen_rows([Column|Tail]) :-
    integer(Column), Column >= 1, Column =< 8,
    external_queen_pairs(Column, Tail, 1), external_queen_rows(Tail).
external_queen_pairs(_, [], _).
external_queen_pairs(Column, [Other|Tail], Distance) :-
    integer(Other), Column =\= Other,
    Delta is abs(Column - Other), Delta =\= Distance,
    Next is Distance + 1, external_queen_pairs(Column, Tail, Next).

external_checked(Case, Results) :-
    findall(Result, external_case(Case, Result), Results),
    ground(Results), external_valid(Case, Results).
external_batch(0, _).
external_batch(N, Case) :- N > 0,
    external_checked(Case, _), Next is N - 1, external_batch(Next, Case).
external_name('core-nrev').
external_name('core-loop').
external_name('core-fib').
external_name('core-queens').
external_request(Case, N) :-
    integer(N), N > 0, N =< 1000000, external_name(Case).

external_output(Case, Results) :-
    write('INFERA_CORE_RESULT:'), write(Results), nl,
    write('INFERA_CORE_OK:'), write(Case), nl.

% SWI process_cputime is a floating seconds CPU counter including GC;
% walltime remains integer milliseconds. Avoid runtime, which excludes GC.
% The checked warmup and result output are outside the clock interval.
external_bench_swipl(Case, N) :-
    external_request(Case, N), external_checked(Case, _),
    statistics(process_cputime, C0), statistics(walltime, [W0,_]),
    external_batch(N, Case),
    statistics(process_cputime, C1), statistics(walltime, [W1,_]),
    Cpu is C1-C0, Wall is (W1-W0)/1000,
    Cpu > 0, Wall > 0,
    external_checked(Case, Results),
    write('INFERA_CORE_CPU_SECONDS:'), write(Cpu), nl,
    write('INFERA_CORE_WALL_SECONDS:'), write(Wall), nl,
    external_output(Case, Results).

% Root loads library(time) before invoking this Scryer entry point.
% Its single % CPU time line is the loaded CPU marker; there is no loaded
% wall-time observation. The Python parser normalizes and validates that line.
external_bench_scryer(Case, N) :-
    external_request(Case, N), external_checked(Case, _),
    time(external_batch(N, Case)),
    external_checked(Case, Results), external_output(Case, Results).
