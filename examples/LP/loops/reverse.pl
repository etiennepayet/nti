% The following mode does not terminate.
%query: reverse(o,i).
% Hence every more general mode also does not terminate.
reverse(L,R) :- rev(L,[],R).

rev([],R,R).
rev([X|Xs],R0,R) :- rev(Xs,[X|R0],R).
