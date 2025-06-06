%query: g(i,i).

% Adapted from:
% TPDB/TRS_Standard/EEG_IJCAR_12/enger-nonloop-swapXY

g(X, Y) :-
    swap(X, Y),
    g(s(X), s(Y)).

swap(0, _).
swap(s(X), Y) :- swap(X, s(Y)).