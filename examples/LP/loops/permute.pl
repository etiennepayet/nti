% The following mode does not terminate.
%query: permute(o,i).
% Hence every more general mode also does not terminate.
permute([],[]).
permute([X|Xs],[Y|Ys]) :- delete(Y,[X|Xs],Zs), permute(Zs,Ys).

delete(X,[X|Xs],Xs).
delete(Y,[X|Xs],[X|Ys]) :- delete(Y,Xs,Ys).
