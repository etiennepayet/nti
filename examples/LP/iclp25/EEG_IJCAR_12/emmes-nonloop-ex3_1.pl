%query: f(i).

% Adapted from:
% TPDB/TRS_Standard/EEG_IJCAR_12/emmes-nonloop-ex3_1

f(X) :-
    gt(X, 0),
    double(X, Y),
    f(Y).

gt(s(_), 0).
gt(s(X), s(Y)) :- gt(X, Y).

double(X, Y) :- doubleAkk(X, 0, Y).

doubleAkk(0, X, X).
doubleAkk(s(X), Y, Z) :- doubleAkk(X, s(s(Y)), Z).
