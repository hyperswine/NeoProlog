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
