%query: f(i).

% Adapted from:
% TPDB/TRS_Standard/EEG_IJCAR_12/emmes-nonloop-ex7_3

f(X) :-
    len(X, L),
    len(cons(a, X), s(L)),
    append(X, cons(a, nil), Y),
    f(Y).

len(nil, 0).
len(cons(_, Y), s(L)) :- len(Y, L).

append(nil, Ys, Ys).
append(cons(X, Xs), Ys, cons(X, Zs)) :- append(Xs, Ys, Zs).