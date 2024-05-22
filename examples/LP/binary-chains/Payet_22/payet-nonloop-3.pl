% The following mode does not terminate.
%query: p(i,i,i,i).
p(0, Y, g(_), U) :-
    p(s(Y), s(Y), g(1), U).
p(s(X), Y, Z, s(_)) :- p(X, Y, Z, s(2)).
