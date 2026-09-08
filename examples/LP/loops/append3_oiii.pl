% The following mode does not terminate.
%query: append3(o,i,i,i).
% Hence every more general mode also does not terminate.
append3(Xs,Ys,Zs,Ts) :- append(Xs,Ys,Us), append(Us,Zs,Ts).

append([],Ys,Ys).
append([X|Xs],Ys,[X|Zs]) :- append(Xs,Ys,Zs).
