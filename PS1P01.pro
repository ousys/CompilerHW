

:- [library(clpfd)].

:-dynamic(assig_num/1). /*dynamic database for counting*/

:- op(950,yf,;).
:- op(960,fx,if).
:- op(959,xfx,then).
:- op(958,xfx,else).
:- op(960,fx,while).
:- op(959,xfx,do).

/*
ve(X) :-
        term_to_atom(X,XA),
        atomic_list_concat(['in ve:',XA],Writable),
        writeln(Writable),fail.
*/
assig_num(0).

ve(X) :- integer(X),!.
ve(X) :- atom(X),!.
ve(E) :- E =.. [Op,A,B],
        member(Op,[+,-,*,/,rem,/\,\/,<,>,=<,>=,\=,==]),!,
        ve(A), ve(B).
ve(E) :- E =.. [Op,A],
        member(Op,[+,-,\]),!,ve(A).

vs(X=E) :- !, atom(X), ve(E),retract(assig_num(K)),M is K+1,asserta(assig_num(M)).
vs(if E then { S1 } else { S2 }) :- !,ve(E), vs(S1), vs(S2).
vs(if E then { S }) :- !,ve(E), vs(S).
vs(while E do { S }) :- !,ve(E), vs(S).
vs(S1;S2) :- !,vs(S1), vs(S2).
vs(S;) :- !,vs(S).

count_assig(P,N):-
	retract(assig_num(_)),
	asserta(assig_num(0)),
	vs(P),
	assig_num(X),
	N is X.

/*
:- Program =
    ( a = 240 ; b = 144 ; i = 0 ;
      while ( a \= b ) do {
          if ( b > a )
              then { b = b - a }
              else { a = a - b } ;
          i = i + 1 ;
      } ),
    count_assig(Program,N).
*/
