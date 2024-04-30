mem(A, [B]).
mem(C, [D]) :- fail.
mem(E, [F | G]) :- mem(E, G).