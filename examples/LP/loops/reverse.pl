% The mode rev(i,o,o) terminates, hence
% every less general mode also terminates.
% The following mode does not terminate.
%query: rev(o,i,i).
% Hence every more general mode also does not terminate.
rev([],R,R).
rev([X|Xs],R0,R) :- rev(Xs,[X|R0],R).

% The mode reverse(i,o) terminates, hence
% every less general mode also terminates.
% The following mode does not terminate.
%query: reverse(o,i).
% Hence every more general mode also does not terminate.
reverse(L,R) :- rev(L,[],R).
