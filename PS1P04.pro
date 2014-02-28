/*
Main predict is indicated below: change_var_name/4
*/
:- [library(clpfd)].

:- op(950,yf,;).
:- op(960,fx,if).
:- op(959,xfx,then).
:- op(958,xfx,else).
:- op(960,fx,while).
:- op(959,xfx,do).

/*
vs/2, ve/2
vs(Expression,list_of_variables)
ve(Expression,list_of_variables)
convert1/4 convert/4
convert1(expression, OutputExpression, source_variable, target_variable)
convert1(expression, OutputExpression, source_variable, target_variable)
*/
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

convert1(X,X,_VA,_VX) :- integer(X),!.
convert1(X,NewP,VA,VX) :- atom(X),(X==VA->NewP=VX;NewP=X),!.
convert1(E,NewP,VA,VX) :- E =.. [Op,A,B],
        member(Op,[+,-,*,/,rem,/\,\/,<,>,=<,>=,\=,==]),!,
        convert1(A,N1,VA,VX), convert1(B,N2,VA,VX),NewP=..[Op,N1,N2].
convert1(E,NewP,VA,VX) :- E =.. [Op,A],
        member(Op,[+,-,\]),!,convert1(A,N1,VA,VX),NewP=..[Op,N1].

convert(X=E,NewP,VA,VX) :- !, atom(X),convert1(E,N1,VA,VX),(X==VA->NewP=(VX=N1);NewP=(X=N1)).
convert(if E then { S1 } else { S2 },NewP,VA,VX) :- !,convert1(E,N1,VA,VX),convert(S1,N2,VA,VX),convert(S2,N3,VA,VX),NewP=(if N1 then {N2} else {N3}).

convert(if E then { S },NewP,VA,VX) :- !,convert1(E,N1,VA,VX),convert(S,N2,VA,VX),NewP=(if N1 then {N2}).

convert(while E do { S },NewP,VA,VX) :- !,convert1(E,N1,VA,VX),convert(S,N2,VA,VX),NewP=(while N1 do {N2}).

convert(S1;S2,NewP,VA,VX) :- !,convert(S1,N1,VA,VX),convert(S2,N2,VA,VX),NewP=(N1;N2).
convert(S;,NewP,VA,VX) :- !,convert(S,N1,VA,VX),NewP=(N1;).

/*
Sample usage:

?-P = (
a = 240 ; b = 144 ; i = 0 ;
while ( a \= b ) do {
if ( b > a )
then { b = b - a }
else { a = a - b } ;
i = i + 1 ;
} ), change_var_name(P,NewP,a,x). % change a into x

*/
change_var_name(P,NewP,A,X):-vs(P,H),not(member(X,H)),convert(P,NewP,A,X).
