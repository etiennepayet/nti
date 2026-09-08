% The following mode does not terminate.
%query: append(o,i,o).
% Hence every more general mode also does not terminate.
append([],Ys,Ys).
append([X|Xs],Ys,[X|Zs]) :- append(Xs,Ys,Zs).