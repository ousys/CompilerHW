:- [library(clpfd)].

:- op(950,yf,;).
:- op(960,fx,if).
:- op(959,xfx,then).
:- op(958,xfx,else).
:- op(960,fx,while).
:- op(959,xfx,do).

ve(X,[]) :- integer(X),!.
ve(X,[X]) :- atom(X),!.
ve(E,L) :- E =.. [Op,A,B],
        member(Op,[+,-,*,/,rem,/\,\/,<,>,=<,>=,\=,==]),!,
        ve(A,L1), ve(B,L2),union(L1,L2,L3),L=L3.
ve(E,L) :- E =.. [Op,A],
        member(Op,[+,-,\]),!,ve(A,L).

vs(X=E,L) :- !, atom(X),ve(E,O),(not(member(X,O))->L=[X|O];L=O).
vs(if E then { S1 } else { S2 },L) :- !,ve(E,L1), vs(S1,L2), vs(S2,L4),union(L1,L2,L5),union(L4,L5,L3), L=L3.
vs(if E then { S },L) :- !,ve(E,L1), vs(S,L2),union(L1,L2,L3),L=L3.
vs(while E do { S },L) :- !,ve(E,L1), vs(S,L2),union(L1,L2,L3),L=L3.
vs(S1;S2,L) :- !,vs(S1,L1), vs(S2,L2),union(L1,L2,L3),L=L3.
vs(S;,L) :- !,vs(S,L).

var_list(P,Vars):-vs(P,Vars).
/*
:- Program =
    ( a = 240 ; b = 144 ; i = 0 ;
      while ( a \= b ) do {
          if ( b > a )
              then { b = b - a }
              else { a = a - b } ;
          i = i + 1 ;
      } ),var_list(Program,H).
      */


