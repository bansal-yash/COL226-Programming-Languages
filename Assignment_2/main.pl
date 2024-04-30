% search for the variable in G
search(X, [(X,Y)|_], Y) :- !.
search(X, [_|Tail], Y) :- search(X, Tail, Y), !.

% base cases
hastype(_, num(_), intT) :- !.
hastype(_, boolT(_), boolT) :- !.
hastype(_, intT(_), intT) :- !.
hastype(_, X, intT) :- number(X), !.
hastype(_, t, boolT) :- !.
hastype(_, f, boolT) :- !.
hastype(G, varT(X), Z) :- search(X, G, Z), !.

% inductive cases
hastype(G, plus(E1, E2), intT) :- hastype(G, E1, intT), hastype(G, E2, intT), !.
hastype(G, times(E1, E2), intT) :- hastype(G, E1, intT), hastype(G, E2, intT), !.
hastype(G, and(E1, E2), boolT) :- hastype(G, E1, boolT), hastype(G, E2, boolT), !.
hastype(G, or(E1, E2), boolT) :- hastype(G, E1, boolT), hastype(G, E2, boolT), !.
hastype(G, not(E1), boolT) :- hastype(G, E1, boolT), !.
hastype(G, eq(E1, E2), boolT) :- hastype(G, E1, intT), hastype(G, E2, intT), !.
hastype(G, eq(E1, E2), boolT) :- hastype(G, E1, boolT), hastype(G, E2, boolT), !.
hastype(G, gt(E1, E2), boolT) :- hastype(G, E1, intT), hastype(G, E2, intT), !.

hastype(G, X, Z) :- search(X, G, Z), !.