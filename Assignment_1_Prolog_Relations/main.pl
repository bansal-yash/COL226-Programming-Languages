% Part A :- Specification

% memebership
mem( X, []) :- fail.
mem( X, [X|Tail]).
mem( X, [Y|Tail]) :- mem( X, Tail).

% complement
mem( X, comp(S)) :- \+ mem( X, S).

% subset
subset( [], S).
subset( [X|Tail], S) :- mem( X, S), subset( Tail, S).

% Reflexive-Transitive closure
/* For any element (X,Y) to belong to reflexive - transitive closure of a relation, either it is (X,X) ( as it is reflexive), 
   or it itself belongs to the rel. If not, then there must exist some Z belongs to S such that (X,Z) belongs to relation 
   and (Z,Y) belongs to reflexive - transitive closure of the relation.
*/
mem( (X,X), ref-tran( Rel, S), Seen) :- mem( X, S).
mem( (X,Y), ref-tran( Rel, S), Seen) :- mem( (X,Y), Rel).
mem( (X,Y), ref-tran( Rel, S), Seen) :- \+ mem( (X,Y), Seen ), mem( (X,Z), Rel), mem( (Z,Y), ref-tran( Rel, S) , [ (X,Y)|Seen]).

/* Test cases for reflexive - transitive closure
   ?- mem( (1,2), ref-tran( [ (1,3), (1,4), (4,2) ], [1,2,3,4]) , []).
   true .

   ?- mem( (1,4), ref-tran( [ (1,2), (3,4), (1,3) ], [1,2,3,4]) , []).
   true .

   ?- mem( (1,4), ref-tran( [ (1,3), (3,4), (1,2) ], [1,2,3,4]) , []).
   true .

   ?- mem( (1,2), ref-tran( [ (1,3), (3,1) ], [1,2,3,5] ), [] ).
   false.

   ?- mem( (1,4), ref-tran( [ (1,2), (2,1), (2,3), (3,4) ], [1,2,3,4]) , []).
   true .
*/

% Reflexive-Symmetric-Transitive closure:- Equivalence closure
/* For any element (X,Y) to belong to equivalence closure of a relation, either it is (X,X) ( as it is reflexive), or it itself
   belongs to the rel, or (Y,X) belongs to the relation ( Due to iut being symmetric) . If not, then there must exist some Z belongs
   to S such that (X,Z) belongs to relation and (Z,Y) belongs to equivalence closure of the relation. Now, as the closure is symmetric,
   thus we check this property for all the 4 possible interchanges between these namely
   (X,Z), (Z,Y) or (X,Z), (Y,Z) or (Z,X), (Z,Y) or (Z,X) , (Y,Z)
*/
mem( (X,X), equivalence( Rel, S), Seen) :- mem( X, S).
mem( (X,Y), equivalence( Rel, S), Seen) :- mem( (X,Y), Rel).
mem( (X,Y), equivalence( Rel, S), Seen) :- mem( (Y,X), Rel).
mem( (X,Y), equivalence( Rel, S), Seen) :- \+ mem( (X,Y), Seen), mem( (X,Z), Rel), mem( (Z,Y), equivalence( Rel, S), [ (X,Y)|Seen]).
mem( (X,Y), equivalence( Rel, S), Seen) :- \+ mem( (X,Y), Seen), mem( (X,Z), Rel), mem( (Y,Z), equivalence( Rel, S), [ (X,Y)|Seen]).
mem( (X,Y), equivalence( Rel, S), Seen) :- \+ mem( (X,Y), Seen), mem( (Z,X), Rel), mem( (Z,Y), equivalence( Rel, S), [ (X,Y)|Seen]).
mem( (X,Y), equivalence( Rel, S), Seen) :- \+ mem( (X,Y), Seen), mem( (Z,X), Rel), mem( (Y,Z), equivalence( Rel, S), [ (X,Y)|Seen]).

/* Test cases for equivalence closure

   ?- mem( (1,1), equivalence( [ (1,2), (2,3), (1,5) ], [1,2,3,5] ), [] ).
   true .

   ?- mem( (1,2), equivalence( [ (1,3), (3,1) ], [1,2,3,5] ), [] ).
   false.

   ?- mem( (5,2), equivalence( [ (1,2), (2,3), (1,5) ], [1,2,3,5] ), [] ).
   true .

   ?- mem( (2,5), equivalence( [ (1,2), (2,3), (1,5) ], [1,2,3,5] ), [] ).
   true .

   ?- mem( (1,3), equivalence( [ (1,2), (2,3), (1,5) ], [1,2,3,5] ), [] ).
   true .
*/

%  Part B :- Implementation of sets as lists with no duplicates

% Delete member:- deletes the first occurence of the item
del( X, [], []).
del( X, [X|S], S).
del( X, [Y|S], [Y|Z]) :- del( X, S, Z).

% Remove duplicates
remdups( [], []).
remdups( [X|Tail], [X|Z]) :- del( X, Tail, Deleted), remdups( Deleted, Z).

% Union
unionI([], S2, S2).
unionI(S1, [], S1).
unionI([X|R], S2, [X|Z]) :- del(X, S2, S3),  unionI(R, S3, Z).

/* Test cases for Union :- 

    ?- unionI([],[],Z).
    Z = [].
    
    ?- unionI([1],[],Z).
    Z = [1].
    
    ?- unionI([],[2],Z).
    Z = [2].
    
    ?- unionI([1],[2],Z).
    Z = [1, 2].
    
    ?- unionI([1,4,2],[61,34,9],Z).
    Z = [1, 4, 2, 61, 34, 9].
    
    ?- unionI([1,2,3],[1,5,6,3],Z).
    Z = [1, 2, 3, 5, 6].
    
    ?- unionI([5,7,2,4],[7,3,4,1],Z).
    Z = [5, 7, 2, 4, 3, 1].
*/

% Append :- appends two lists without removing duplicates
append( [], L, L).
append( [X|R], L, [X|Z]) :- append(R, L, Z).

% mapcons :- cons the element X to each list in L1 to get L2
mapcons(X, [ ], [ ]).
mapcons(X, [Y|R], [ [X|Y] | Z ]) :- mapcons(X, R, Z).

% Power set
powerI([], [[]]).
powerI( [X|Tail], Z) :- powerI( Tail, S), mapcons( X, S, S1), append( S, S1, Z).

/* Test cases for Power set

   ?- powerI([],Z).
   Z = [[]].

   ?- powerI([4],Z).
   Z = [[],[4]].

   ?- powerI([2,6],Z).
   Z = [[],[6],[2],[2,6]].

   ?- powerI([5,7,2],Z).
   Z = [[],[2],[7],[7,2],[5],[5,2],[5,7],[5,7,2]].

   ?- powerI([5,2,2],Z).
   Z = [[],[2],[2],[2,2],[5],[5,2],[5,2],[5,2,2]].

   ?- powerI([5,7,2,1,9],Z).
   Z = [[],[9],[1],[1,9],[2],[2,9],[2,1],[2,1,9],[7],[7,9],[7,1],[7,1,9],[7,2],[7,2,9],[7,2,1],[7,2,1,9],
       [5],[5,9],[5,1],[5,1,9],[5,2],[5,2,9],[5,2,1],[5,2,1,9],[5,7],[5,7,9],[5,7,1],[5,7,1,9],[5,7,2],
       [5,7,2,9],[5,7,2,1],[5,7,2,1,9]].
*/

% Intersection
/*  For every element in the first set, it checks whether it is the member of the 
    second set. If yes, then it adds thats element to the required set, else it doesn't add.
*/
interI( [], S, []).
interI( S, [], []).
interI( [X|Tail], S, [X|Z]) :- mem( X, S), interI( Tail, S, Z). 
interI( [X|Tail], S, Z) :- \+ mem( X, S), interI( Tail, S, Z).

/* Test cases for Intersection

    ?- interI([],[],Z).
    Z = [].

    ?- interI([3],[],Z).
    Z = [].

    ?- interI([],[5],Z).
    Z = [].

    ?- interI([3],[5],Z).
    Z = [].

    ?- interI([1],[1],Z).
    Z = [1].

    ?- interI([2,1],[1],Z).
    Z = [1].

    ?- interI([5,7],[2],Z).
    Z = [].

    ?- interI([5,7,1,8,3],[2,5,3,9,13,15],Z).
    Z = [5, 3].
*/

% Set-difference
/* For each element in the first set, it check whether it is the element of the second set.
   If not, then only it adds that element to the required set, else it doesn't.
*/
diffI( [], S, []).
diffI( [X|Tail], S, [X|Z]) :- \+ mem( X, S), diffI( Tail, S, Z).
diffI( [X|Tail], S, Z) :- mem( X, S), diffI( Tail, S, Z).

/* Test cases for set difference

   ?- diffI([],[],Z).
   Z = [].

   ?- diffI([],[1,2],Z).
   Z = [].

   ?- diffI([1],[],Z).
   Z = [1].

   ?- diffI([1,3],[],Z).
   Z = [1,3].

   ?- diffI([1,3,5],[2,6],Z).
   Z = [1,3,5].

   ?- diffI([1,3,5],[5],Z).
   Z = [1,3].

   ?- diffI([1,3,5,7],[5,1],Z).
   Z = [3,7].

   ?- diffI([1,4,5,8],[5,1,9],Z).
   Z = [4,8].
*/

mapcons1(X, [ ], [ ]).
mapcons1(X, [Y|R], [ (X,Y) | Z ]) :- mapcons1(X, R, Z).
% mapcons1 is similar to mapcons, just it gives the result in the form of list of tuples, rather than list of lists.

% Cartesion product
/* For each element of the first set, it mapcons it to all the elements of the second set to form
   a list of tuples. Then this list of appended to the required output list.
*/
cartesianI( [], S, []).
cartesianI( [X|Tail], S, Z) :- cartesianI( Tail, S, L1), mapcons1( X, S, L2), append( L1, L2, Z).

/* Test cases for cartesian product

   ?- cartesianI([],[],Z).
   Z = [].

   ?- cartesianI([5],[],Z).
   Z = [].

   ?- cartesianI([],[7],Z).
   Z = [].

   ?- cartesianI([1],[7],Z).
   Z = [(1,7)].

   ?- cartesianI([1,4],[7],Z).
   Z = [(4,7),(1,7)].

   ?- cartesianI([1,4,7,3],[1,4,7,3],Z).
   Z = [(3,1),(3,4),(3,7),(3,3),(7,1),(7,4),(7,7),(7,3),(4,1),(4,4),(4,7),(4,3),(1,1),(1,4),(1,7),(1,3)].

   ?- cartesianI([1,4,7,3],[7,5],Z).
   Z = [(3,7),(3,5),(7,7),(7,5),(4,7),(4,5),(1,7),(1,5)].
*/

% Power set equality check

/*  equal :- check whether two sets are equal
    member_power :- check whether a given is a member of another set( of sets). For this, it checks the equality 
                   with all the sets of the set of sets.
    subset_power :- similar to the logic of specifying subsets of a set, this functions checks whether a
                    set of sets is a subset of another set of sets.
    powersetequal:- It finally checks whether the powersets formed by two sets are equal or not, using similar logic
                    as of specifying similarity of two sets. It takes two sets S1 and S2.
    checkequal :- takes two sets of sets and checks whether they both are equal

*/
equal( S1, S2) :- subset(S1,S2), subset(S2,S1).

member_power( X, []) :- fail.
member_power( X, [Y|P]) :- equal( X, Y).
member_power( X, [Y|P]) :- member_power( X, P).  

subset_power( [], P).
subset_power( [X|Tail], P) :- member_power( X, P), subset_power( Tail, P).  

powersetequal( S1, S2) :- powerI( S1, P1), powerI( S2, P2), subset_power( P1, P2), subset_power( P2, P1).
checkequal( P1, P2) :- subset_power( P1, P2), subset_power( P2, P1).

/* Test cases for power set equality

   ?- powersetequal([],[]).
   true.

   ?- powersetequal([1],[]).
   false.

   ?- powersetequal([1],[1]).
   true.

   ?- powersetequal([1],[1,2]).
   false.

   ?- powersetequal([2],[1]).
   false.

   ?- powersetequal([2,3,5],[3,5,2]).
   true.

   ?- powersetequal([2,3,5,7],[3,5,2,1]).
   false.

   ?- powersetequal([2,3,5,7,1],[7,3,5,2,1]).
   true.
*/