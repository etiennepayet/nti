% The following mode does not terminate.
%query: p(i,i).
p(0, Y) :-
    p(s(Y), s(Y)).
p(s(X), Y) :- p(X, Y).
