
:- [library(clpfd)].

:- op(950,yf,;).
:- op(960,fx,if).
:- op(959,xfx,then).
:- op(958,xfx,else).
:- op(960,fx,while).
:- op(959,xfx,do).

/*
  Main predict is indicated below as vs/2.
  ve(Expression, OutExpression),
  vs(Expression, OutExpression).
*/

ve(X,X) :- integer(X),!.
ve(X,X) :- atom(X),!.
ve(E,O) :- E =.. [Op,A,B],
        member(Op,[+,-,*,/,rem,/\,\/,<,>,=<,>=,\=,==]),!,
        ve(A,O1),ve(B,O2),O=..[Op,O1,O2].
ve(E,O) :- E =.. [Op,A],
        member(Op,[+,-,\]),!,ve(A,O1),O=..[Op,O1].

vs(X=E,O) :- !, atom(X),ve(E,O1),O=(X=O1).

/*if(a==b) then else can be changed to (a\=b), similar for other boolean operators.*/

vs(if E then { S1 } else { S2 },O) :-
	!, E =..[Op1,A,B],
         member(Op1,[<,>,=<,>=,\=,==]),
	( member(Op1,[==])
		->member(Op2,[\=]);true),
	( member(Op1,[\=])
		->member(Op2,[==]);true),
	( member(Op1,[>=])
		->member(Op2,[<]);true),
	( member(Op1,[=<])
		->member(Op2,[>]);true),
	( member(Op1,[>])
		->member(Op2,[=<]);true),
	( member(Op1,[<])
		->member(Op2,[>=]);true),
	E1 =..[Op1,user_never_usedvar1, user_never_usedvar2],
	E2 =..[Op2,user_never_usedvar1, user_never_usedvar2],
	vs(S1,O3),vs(S2,O4),
	O=(user_never_usedvar1 = A; user_never_usedvar2 = B;if E1 then {O3};if E2 then {O4}).

vs(if E then { S },O) :- !,ve(E,O1), vs(S,O2),
O = (if O1 then {O2}).

vs(while E do { S },O) :- !,ve(E,O1),vs(S,O2),
O = (while O1 do {O2} ).

vs(S1;S2,O) :- !,vs(S1,O1),vs(S2,O2),O=(O1;O2).
vs(S;,O) :- !,vs(S,O1),O=(O1;).


/* Below can be used for testing information for program*/
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
sample of usage of translation only :
?- Program =
    ( a = 240 ; b = 144 ; i = 0 ;
      while ( a \= b ) do {
          if ( b > a )
              then { b = b - a }
              else { a = a - b } ;
          i = i + 1 ;
      } ),
    vs(Program,L).
*/


/*
sample of usage of translation and testing:
?- Program =
    ( a = 240 ; b = 144 ; i = 0 ;
      while ( a \= b ) do {
          if ( b > a )
              then { b = b - a }
              else { a = a - b } ;
          i = i + 1 ;
      } ),
    vs(Program,L),
    empty_assoc(Empty),
    interp(L,Empty,Out),
    get_var_values([a,b,i],Vals,Out),
    atomic_list_concat(Vals,' ',Writable),
    writeln(Writable).
*/




