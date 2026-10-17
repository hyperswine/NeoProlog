% Loaded-runtime companion for machine-cache's split controls and core cases.
% bench/bench.pl supplies the core predicates; this file supplies independent
% result checks and batch execution. Every timed query is fully collected.

runtime_case('controls-arithmetic', Result) :- control_arithmetic(300, 0, Result).
runtime_case('controls-once', Result) :- control_once(300, 0, Result).
runtime_case('controls-not', Result) :- control_not(300, 0, Result).
runtime_case('controls-if', Result) :- control_if(300, 0, Result).
runtime_case(controls, Result) :- control_combined(300, 0, Result).
runtime_case('core-nrev', Result) :- once((bench_nrev(3000), range(1, 30, L), nrev(L, Result))).
runtime_case('core-loop', Result) :- once((loop(90000), Result = 90000)).
runtime_case('core-fib', Result) :- once(fib(25, Result)).
runtime_case('core-queens', Result) :- once(queens(8, Result)).

control_arithmetic(0, Acc, Acc).
control_arithmetic(N, Acc, Result) :- N > 0, Next is Acc + N,
    M is N - 1, control_arithmetic(M, Next, Result).
control_once(0, Acc, Acc).
control_once(N, Acc, Result) :- N > 0,
    once((Picked = N ; Picked = 0)), Next is Acc + Picked,
    M is N - 1, control_once(M, Next, Result).
control_not(0, Acc, Acc).
control_not(N, Acc, Result) :- N > 0, \+ (N < 0), Next is Acc + N,
    M is N - 1, control_not(M, Next, Result).
control_if(0, Acc, Acc).
control_if(N, Acc, Result) :- N > 0,
    (N > 150 -> Next is Acc + N ; Next is Acc + N),
    M is N - 1, control_if(M, Next, Result).
control_combined(0, Acc, Acc).
control_combined(N, Acc, Result) :- N > 0,
    once((Picked = N ; Picked = 0)), \+ (Picked < 0),
    (Picked > 0 -> Next is Acc + Picked ; Next = Acc),
    M is N - 1, control_combined(M, Next, Result).

runtime_valid('controls-arithmetic', [45150]).
runtime_valid('controls-once', [45150]).
runtime_valid('controls-not', [45150]).
runtime_valid('controls-if', [45150]).
runtime_valid(controls, [45150]).
runtime_valid('core-loop', [90000]).
runtime_valid('core-fib', [75025]).
runtime_valid('core-nrev', [Result]) :-
    Result == [30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1].
runtime_valid('core-queens', [Columns]) :-
    runtime_length(Columns, 8), runtime_queen_rows(Columns).

% Check bounds, pairwise column separation and diagonal separation directly.
% This does not call the generator's perm/2, safe/1 or noatt/3 predicates.
runtime_length([], 0).
runtime_length([_|Tail], N) :- runtime_length(Tail, M), N is M + 1.
runtime_queen_rows([]).
runtime_queen_rows([Column|Tail]) :-
    integer(Column), Column >= 1, Column =< 8,
    runtime_queen_pairs(Column, Tail, 1), runtime_queen_rows(Tail).
runtime_queen_pairs(_, [], _).
runtime_queen_pairs(Column, [Other|Tail], Distance) :-
    integer(Other), Column =\= Other,
    Delta is abs(Column - Other), Delta =\= Distance,
    Next is Distance + 1, runtime_queen_pairs(Column, Tail, Next).

runtime_checked(Case, Results) :-
    findall(Result, runtime_case(Case, Result), Results),
    ground(Results), runtime_valid(Case, Results).

runtime_batch(0, _).
runtime_batch(N, Case) :- N > 0, runtime_checked(Case, _),
    Next is N - 1, runtime_batch(Next, Case).

% The Python runner supplies engine-specific clock operations only after
% checking their availability. Its timed region calls this batch directly;
% warmup and final output/checking live outside the clock interval.
