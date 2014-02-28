/*Ouyang Siyu(A0077453Y) PS1P05*/
/*Main usage is indicated at the bottom part*/

:- [library(clpfd)].

:- op(950,yf,;).
:- op(960,fx,if).
:- op(959,xfx,then).
:- op(958,xfx,else).
:- op(960,fx,while).
:- op(959,xfx,do).

ve(X,X) :- integer(X),!.
ve(X,X) :- atom(X),!.
ve(E,N) :- E =.. [Op,A,B],
        member(Op,[+,-,*,/,rem,/\,\/,<,>,=<,>=,\=,==]),!,
        ve(A,N1), ve(B,N2),N=..[Op,N1,N2].
ve(E,N) :- E =.. [Op,A],
        member(Op,[+,-,\]),!,ve(A,N1),N=..[Op,N1].

/*constant/1 to determine whether X is constant or not, since it is used together with ve or vs, it ignores operator*/

constant(X):-integer(X),!.
constant(E):-E=..[_,A,B],constant(A),constant(B),!.
constant(E):-E=..[_,A],!,constant(A).

vs(X=E,N) :- !, atom(X), ve(E,N1),N=(X=N1).
vs(if E then { S1 } else { S2 },N) :- !,ve(E,N1), vs(S1,N2), vs(S2,N3),
	 empty_assoc(Empty),
	( constant(E)-> (eval(E,Empty,Bval),(Bval#=1->N=(N2);N=(N3)));
           N = (if N1 then {N2} else {N3})).

vs(if E then { S },N) :- !,ve(E,N1), vs(S,N2),empty_assoc(Empty),
	( constant(E)-> (eval(E,Empty,Bval),(Bval#=1->N=(N2);N=(a=a)));
           N = (if N1 then {N2})).

vs(while E do { S },N) :- !,ve(E,N1), vs(S,N2),N=(while N1 do {N2}).
vs(S1;S2,N) :- !,vs(S1,N1), vs(S2,N2), N=(N1;N2).
vs(S;,N) :- !,vs(S,N1),N=(N1;).

/*eval to caculate the constant and helps make decision,also helps testing*/
eval(N,_,N) :- integer(N), !.
eval(X,Env,R) :- atom(X),!,get_assoc(X,Env,R).
eval(E,Env,R) :-
        E =.. [Op,A,B],
        member(Op,[+,-,*,/,rem,^]),!,
        eval(A,Env,RA), eval(B,Env,RB),
        Compute =.. [Op,RA,RB],
        R #= Compute.
eval(E,Env,R) :-
        E =.. [Op,A],
        member(Op,[+,-]),!,
        eval(A,Env,RA),
        Compute =.. [Op,RA],
        R #= Compute.
eval(E,Env,R) :-
        E =.. [Op,A,B],
        member(Op,[<,>,=<,>=,\=,==]),!,
        (   Op == (==) -> OpEv = (=) ; OpEv = Op ),
        eval(A,Env,RA), eval(B,Env,RB),
        atomic_concat('#',OpEv,HOp),
        Compute =.. [HOp,RA,RB],
        (   Compute -> R = 1 ; R = 0 ).
eval(E,Env,R) :-
        E =.. [Op,A],
        member(Op,[\]),!,
        eval(A,Env,RA),
        atomic_concat('#',Op,HOp),
        Compute =.. [HOp,RA],
        (   Compute -> R = 1 ; R = 0 ).

simplify_if(P,NewP):-vs(P,NewP).

/*
interp/3, get_var_values/3 is for testing purpose only, see the sample
at bottom for testing , all the code below is for testing ONLY.
*/
interp((X = Expr),Ein,Eout) :-
        atom(X),!,
        eval(Expr,Ein,R),
        put_assoc(X,Ein,R,Eout).

interp((S;),Ein,Eout) :- interp(S,Ein,Eout).

interp((S1;S2),Ein,Eout) :- interp(S1,Ein,Eaux), interp(S2,Eaux,Eout).

interp((if B then { S1 } else { S2 } ),Ein,Eout) :-
        eval(B,Ein,Bval),
        (   Bval #= 1
        ->  interp(S1,Ein,Eout)
        ;   interp(S2,Ein,Eout) ).

interp((if B then { S1 } ),Ein,Eout) :-
        eval(B,Ein,Bval),
        (   Bval #= 1
        ->  interp(S1,Ein,Eout)
        ;   Eout = Ein ).

interp((while B do { S }),Ein,Eout) :-
        interp(
            (if B then {
                      S ;
                      while B do { S }
                  }
            ),Ein,Eout).


get_var_values([],[],_).
get_var_values([X|XT],[V|VT],Assoc) :-
        get_assoc(X,Assoc,VX),
        term_to_atom((X=VX),V),
        get_var_values(XT,VT,Assoc).


/*
Sample usage with translation and testing
?-
P = (
a = 240 ; b = 144 ; i = 0 ;
while ( i < 6 ) do {
if (2+3+(2>1) < 1*1/1 )
then { b = b - a }
else { a = a - b } ;
i = i + 1 ;
} ), simplify_if(P,NewP),
    empty_assoc(Empty),
    interp(NewP,Empty,Out),
    get_var_values([a,b,i],Vals,Out),
    atomic_list_concat(Vals,' ',Writable),
    writeln(Writable).

*/

/*
Sample usage with translation only
?-
P = (
a = 240 ; b = 144 ; i = 0 ;
while ( i < 6 ) do {
if (2+3+(2>1) < 1*1/1 )
then { b = b - a }
else { a = a - b } ;
i = i + 1 ;
} ), simplify_if(P,NewP).
*/
