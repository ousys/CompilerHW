/*****************************************************************************
  CS4212 -- Compiler Design

        T O Y   C O M P I L E R   F O R   ''W H I L E''   L A N G U A G E

  This is a toy compiler for a 'while' language. It generates Pentium assembly
  output that can be assembled using gas, the assembler that comes with gcc,
  so as to produce executables, and thus test the correctness of the generated
  code. The compiler tries to optimize register usage, and given the non-uniform
  architecture of the Pentium, this leads to a very hairy code generator for
  expressions. However, the code generator for statements is relatively
  straightforward and by-the-book, and should be easy to follow.

  Main predicate: compile(Program,'file.s')

  Source language features:
     * unscoped integer variables (no need to declare, and all variables are global)
     * all arithmetic and bitwise operators supported
     * booleans encoded as 0 or 1
         - (0 < 1) evaluates to 1
         -  integers can be used where booleans are expected:  if (a+b) then...
         - when a+b is not 0, it is considered "true"
     * Prolog syntax for expressions: not equal is \=, negation is \, bitwise "and" is /\
     * statements are separated by semicolon
         - semicolon is not a terminator, does not need to be used in front of closing brace
     * assignments in usual form: Var = Expr
     * if statements
         - if Expr then { Statement1 ; ... ; Statement_n }
         - if Expr then {...} else {...}
     * while statements
         - while Expr do { Statement_1 ; ... ; Statement_n }
     * break statement allowed inside a while loop's body
     * switch-case statements
         - switch Expr of { 0 :: { ...code for 0...} ; 3 :: { ...code for 3..} ;
                            default :: { ...code for default... } }
         - case labels need to be in increasing order (but not necessarily consecutive)
         - 'default' label must exist, and must be last in list of cases.
         - value of 'Expr', and consequently the case labels, are limited to 0-255.
         - the code will yield 'segmentation fault' if a wider range of labels is used.

  Example source program:

     i = 1 ;
     while i < 100 do {
       switch i rem 8 of {
         2:: { c1 = c1 + i } ;
         4:: { c2 = c2 + i/2 } ;
         6:: { if c2 \= c1
                 then { c3 = (c3+1)*c3 }
                 else { c3 = (c3-1)*c2 } }
         default :: {
             j = 0 ;
             while j < i do {
               switch j of {
                 0 :: { if c0 >= 0 then { c0 = c0+1 } } ;
                 2 :: { c0 = c0 * c0 } ;
                 default :: { c0 = c0 + 2 ; }
               } ;
               j = j + 1
             }
         }
       } ;
       i = i + 1
     }

  Usage example given at the end of the file.

******************************************************************************/

:- [library(clpfd)]. % We need arithmetic
:- [library(lists)]. % We need 'union'

% operator declarations that allow the above program to be read as a Prolog term
:- op(1099,yf,;).
:- op(960,fx,if).
:- op(959,xfx,then).
:- op(958,xfx,else).
:- op(960,fx,while).
:- op(959,xfx,do).
:- op(960,fx,switch).
:- op(959,xfx,of).
:- op(970,xfx,::).
:- op(960,fx,switch).
:- op(959,xfx,of).
:- op(970,xfx,::).

% Improved version, capable of adding variable names
% to an array of strings, so that the runtime can
% print the value of all the variables at the end of
% program
% 1st arg: list of variable names collected from program
% 2nd arg: allocation of space for each variable
% 3rd arg: array of strings containing names of variables
% 4th arg: array of pointers to each of the strings
allocvars([],[],[],[]).
allocvars([V|VT],[D|DT],[N|NT],[P|PT]) :-
	atomic_list_concat(['\n',V,':\t\t .long 0'],D),
	atomic_list_concat(['\n',V,'_name:\t .asciz "',V,'"'],N),
	atomic_list_concat(['\n',V,'_ptr:\t .long ',V,'_name'],P),
	allocvars(VT,DT,NT,PT).

% Generate fresh labels for label placeholders
%  1st arg : list of label placeholders to be instantiated
%  2nd arg : integer suffix not yet used for a label before the call
%  3rd arg : integer suffix not yet used for a label after the call
%              -- essentially LabelSuffixOut #= LabelSuffixIn + length(1st_arg)
generateLabels([],LabelSuffix,LabelSuffix).
generateLabels([H|T],LabelSuffixIn,LabelSuffixOut) :-
    atomic_list_concat(['L',LabelSuffixIn],H),
    LabelSuffixAux #= LabelSuffixIn + 1,
    generateLabels(T,LabelSuffixAux,LabelSuffixOut).

% Replace register numbers with register names
%  1st arg : code template (list of atoms) with regs represented
%              as reg32(N) or reg8(N)
%  2nd arg : same code where each reg32(N) or reg8(N) has been replaced
%              with the corresponding register name
replace_regs([],[]).
replace_regs([reg32(N)|T],[A|TR]) :-
    member((N,A),
           [(0,'%eax'),(1,'%edx'),(2,'%ecx'),
            (3,'%ebx'),(4,'%esi'),(5,'%edi')]),!,
    replace_regs(T,TR).
replace_regs([reg8(N)|T],[A|TR]) :-
    member((N,A),
           [(0,'%al'),(1,'%dl'),(2,'%cl'),(3,'%bl')]),!,
    replace_regs(T,TR).
replace_regs([H|T],[H|TR]) :- replace_regs(T,TR).

% Further translations of register numbers into register
% names are required when inspecting the placeholder for
% the result of an expression. This predicate serves that
% purpose.
translate_regs(0,'%eax') :- !.
translate_regs(1,'%edx') :- !.
translate_regs(2,'%ecx') :- !.
translate_regs(3,'%ebx') :- !.
translate_regs(4,'%esi') :- !.
translate_regs(5,'%edi') :- !.

% 'combine_expr_code' is the main predicate performing register
% allocation for partial results of expressions. It tries to
% minimize register use, and avoid spilling results into memory.
%
% This predicate is called by the 'ce' (compile expression) predicate,
%  after it has generated code for the subexpressions of a binary
%  expression. This predicate generates a code template for the
%  current operator, allocating registers for partial results,
%  yet leaving the registers as underspecified (i.e. unbound) as
%  possible. However, these placeholders are constrained with operators
%  from the clpfd library to comply with the correctness requirements
%  of the generated code. The placeholders are concretized in a global
%  round of constraint solution search, performed via a call to 'label'
%  in the 'comp_expr' predicate.
%
%  This code is particularly complicated by the peculiarity of the
%  idivl instruction on the Pentium. In principle, whenever we have
%  an expression of the form (ELeft Op ERight), where Op is some
%  binary operator, we compile separately ELeft and ERight, and then
%  we bring the resulting codes into this predicates to be combined
%  into the code for the entire input expression. We need to consider
%  4 cases for each argument:
%      - the result of the expression is a constant
%      - the result of the expression is placed in a variable
%      - the result of the expression is placed in a register,
%        and we have a list of some other registers that needed
%        to be used throughout that expression's evaluation (which
%        means that we can't rely on those registers holding partial
%		 results from other expressions, since they will be
%		 overwritten).
%	   - the result of the expression is in (%eax,%edx), since the top
%	     level operator of that expression was a division or a remainder
%	     operation (which means that for the other 3 items above, the
%	     top level operation of either ELeft or ERight are not idivl).
%  We also have 3 cases for the operator Op:
%	   - The current operator Op is a binary arithmetic operator:
%			  +,-,*,/\,\/ -- differentiate between commutative and
%			                 non-commutative
%	   - The current Op is division or remainder: /, rem
%	   - The current Op is a boolean relational operator:
%	          <,>,=<,>=,==,\=
%
%	In principle, that means 3*4*4 cases. However, some of these
%	combinations of cases are handled together.
%
%  The arguments to 'combine_expr_code' are as follows:
%
%  1st & 2nd arg : representation of the result holder for the
%   (input)        left and right subexpressions. May have the
%                  following format:
%                  const(N)    : the result is the constant N
%                  id(X)       : the result is variable X
%                  [R1,R2,...] : the result is in register R1
%                                (which may be an unbound variable)
%                                and the rest of the list contains
%                                the registers that MUST be used
%                                (and therefore will be clobbered)
%                                throughout the evaluation of
%                                the subexpression at hand
%  3rd arg      : The operator for which code is being generated
%   (input)       Can be any of the following:
%                  +,-,*,/\,\/ : any pair of registers can be used as operands
%                  /,rem       : must use %eax,%edx, and another register
%                  <,=<,>,>=,==,\= : may have residual code so as to
%                                    allow compilation as regular arithmetic expr,
%                                    and also efficient code when appears as
%                                    if or while condition
% 4th & 5th arg : Code generated for the left and right subexpressions
%   (input)       (must be consistent with 1st and 2nd arg)
%
% 6th arg       : Resulting code for the current expression (return value)
% 7th arg       : Residual code, empty for all arithmetic expressions, but
%  (outputs)      non-empty for boolean expressions.
%	              The residual code places
%                 the boolean value in a register. This is not necessary
%                 if a boolean expr say x < y appears as an 'if' or 'while'
%                 condition, but it is necessary if we use it in an
%                 arithmetic expression, in the form (x<y)+1.
%                 Thus, the decision of whether the residual code should be
%                 appended to the currently generated code needs to be made
%                 one level above from the current call.
% 8th arg       : The result holder, with the same syntax as args 1 and 2.
%  (output)       The predicate will decide to either return directly a
%                 constant or variable, if possible (thus not using any
%                 of the registers, and allowing them to be used for other
%                 purposes). Or, it will return a list of registers (encoded
%                 as numbers, with the encoding given by predicate replace_regs).
%                 In that case, the first register in the list holds the
%                 result of the expression, and the rest of the registers
%                 will be used (and therefore, their values will be clobbered)
%                 throughout the evaluation, but once the result has been computed,
%                 will no longer hold any important value, and can be reused
%                 for in evaluations of other subexpressions.
combine_expr_code(const(N),const(M),Op,[],[],[],[],Result) :- % const opd, all arithmetic ops
                       % Expressions containing only constants are evaluated
                       % at compile time and do not generate any code
    member(Op,[+,-,*,/\,\/,/]),!,
	                   % 'Member' is used to classify the operator
    ResultExpr =.. [Op,N,M],
    ResultVal #= ResultExpr,   % For arithmetic expressions, use #= to compute the result
    Result = const(ResultVal). % at compile time. Return the result as a constant

combine_expr_code(const(N),const(M),Op,[],[],[],[],Result) :- % const opd, relational ops
                       % Expressions containing only constants are evaluated
                       % at compile time and do not generate any code
    member((Op,Opc),[(<,#<),(>,#>),(=<,#=<),(>=,#>=),(\=,#\=),(==,#=)]),!,
	                   % 'Member' is used to translate between Operator and its
					   % corresponding constraint operator.
    ResultExpr =.. [Opc,N,M],
    ResultVal #<==> ResultExpr, % For relational expressions, use #<==> to compute the
    Result = const(ResultVal).  % result at compile time. Return the result as a constant.

combine_expr_code(L,R,Op,[],[],Code,Residue,Result) :- % non-register opd, relational ops
                       % Subexpressions that do not need to be held in registers
                       % are expected to have generated empty code
    ( L = const(Tmp), R = id(Y), atomic_concat('$',Tmp,X) ;
      L = id(X), R = const(Tmp), atomic_concat('$',Tmp,Y) ;
	                   % Constants must have $ prepended in the assembly code
      L = id(X), R = id(Y) ),
					   % X and Y contain assembly language representations of
					   % the operands. 'Member' is used to translate between
					   % Operator and its corresponding OpCode.
    member((Op,I),[(<,setl),(=<,setle),(>,setg),(>=,setge),(\=,setne),(==,sete)]),!,
                       % For boolean expressions, a residue may be needed
                       % This is possible only with regs eax,edx,ecx,ebx
                       % The setXX instruction sets an 8-bit reg to 1 or 0
                       %   depending on whether the XX condition is true or false;
                       %   the corresponding 32-bit reg can hold the same result
                       %   if it has been zeroed first.
    Result = [Reg], Reg in 0..3,
                       % We allocate one register to hold the result of this operator,
                       % and we denote it by Reg. This register will not be explicitly
					   % specified, but allocated through constraint programming later,
                       % when the predicate 'label' is called for the entire
                       % code template, corresponding to the entire expression at hand.
                       % Thus, currently, Reg is an unbound variable, constrained
                       % to be between 0 and 3.
                       % The Result list is the list containing this register
    Code = [ '\n\t\t movl ',X,',',reg32(Reg),  % Load one operand into a register
             '\n\t\t cmpl ',Y,',',reg32(Reg) ],%   and compare with the other;
                                               %   result will be stored in condition flags
    Residue = [ '\n\t\t movl $0,',reg32(Reg),  % Zero the register first, and then
                '\n\t\t ',I,' ',reg8(Reg)    ].%   set the lower 8 bits to 0 or 1


combine_expr_code(L,R,Op,[],[],Code,[],Result) :- % non-register opds, arithmetic non-div ops
                       % Subexpressions that do not need to be held in registers
                       % are expected to have generated empty code
    ( L = const(Tmp), atomic_concat('$',Tmp,X), R = id(Y) ;
      L = id(X), R = const(Tmp), atomic_concat('$',Tmp,Y) ;
					   % Constants must have $ prepended to the name in assembly language
	                   % X and Y are assembly language representations of the partial results
					   % given in L and R.
      L = id(X), R = id(Y) ),
                       % Handling of arithmetic operators that can be performed
                       % using any registers. 'Member' is used to translate between
					   % Operator and its corresponding OpCode.
    member((Op,I),[(+,addl),(-,subl),(*,imull),(/\,andl),(\/,orl)]),!,
    Result = [Reg], Reg in 0..5,
                       % We allocate one register to hold the result of this operator,
                       % and we denote it by Reg. This register will not be explicitly
					   % specified, but allocated through constraint programming later,
                       % when the predicate 'label' is called for the entire
                       % code template, corresponding to the entire expression at hand.
                       % Thus, currently, Reg is an unbound variable, constrained
                       % to be between 0 and 5.
                       % The Result list is the list containing this register
    Code = [ '\n\t\t movl ',X,',',reg32(Reg),    % Load one operand into a register
             '\n\t\t ',I,' ',Y,',',reg32(Reg) ]. % and perform the operation I with the
                                                 % other operand.

combine_expr_code(L,R,Op,[],[],Code,[],Result) :- % non-register opds, Op is division or rem
                       % Subexpressions that do not need to be held in registers
                       % are expected to have generated empty code
    ( L = const(Tmp), atomic_concat('$',Tmp,X), R = id(Y) ;
      L = id(X), R = const(Tmp), atomic_concat('$',Tmp,Y) ;
					   % Constants must have $ prepended to the name in assembly language
	                   % X and Y are assembly language representations of the partial results
					   % given in L and R.
      L = id(X), R = id(Y) ),
                       % Handling of division and remainder operators. This is
                       % complicated because one operand, as well as the result
                       % must be in registers %edx:%eax. 'Member' is used to translate
					   % between Operator and its OpCode.
    member((Op,I),[(/,idivl),(rem,idivl)]),!,
                       % 0 = %eax, 1 = %edx
                       % For division, result will be [%eax,%edx,Reg]
                       % For reminder, result will be [%edx,%eax,Reg]

    (R = const(_) % if right operand is a constant, the AL representation is Y
      ->          % Then, prepare the operand for division/remainder by allocating
	              % some register Reg to hold the value Y, and then generating code
	              % that loads Y into Reg, so that division can be
				  % performed between %edx:%eax and Reg. The operand of idivl is not
	              % allowed to be a constant (damn weird, huh?)
		 CodeL = [ '\n\t\t movl ',Y,',',reg32(Reg) ], Reg in 0..5, Z = reg32(Reg),
	              % The result will be either %eax or %edx, depending on whether
	              % we are translating division or remainder. Variable Z is set
	              % to hold the operand of idivl, be it a register or a variable.
         (Op == / ->  Result = [0,1,Reg] ; Result = [1,0,Reg])

      ;           % Otherwise, R must be an identifier. In this case, idivl can
	              % take its operand directly from memory, therefore CodeL is empty.
				  %	Z is set to represent the AL operand to idivl, be it a
	              % register, or an identifier.
		 CodeL = [], (Op == / ->  Result = [0,1] ; Result = [1,0]), Z = Y ),
                       % In this code template, reg32(0) will be later replaced
                       % with %eax by replace_regs. Similar for reg32(1) --> %edx
	                   % Here, we have to constrain the registers tightly, since
	                   % idivl can only work with %eax and %edx

	% code implementing division, assuming I is the opcode for current operation
	% (can only be idivl in this case), and Z is the operand, either a variable or
	% a register.
    CodeOp = [ '\n\t\t movl ',X,',',reg32(0),        % load first opd into %eax
               '\n\t\t movl ',reg32(0),',',reg32(1), % copy %eax into %edx
               '\n\t\t shrl $31,',reg32(1),			 % %edx becomes sign extension of %eax
               '\n\t\t ',I,' ',Z ],                  % generate instruction performing Op
    all_distinct(Result),     % Set constraint that all allocated registers must be distinct
						      % The subsequent application of 'label' will comply
    append(CodeL,CodeOp,Code).% Finally, lay everything out into generated Code.

combine_expr_code(L,R,Op,CL,CR,Code,[],Result) :- % arithmetic Opr, one reg opd, one non-reg opd
                       % Code generation for the case when one subexpression
                       % is constant or a variable (i.e. doesn't need registers
                       % in its evaluation), and the other subexpression does
                       % need registers. The used registers list remains the same,
                       % as the result register of the subexpression that needs one
                       % can be reused to hold the result of the current expression.
    ( L = [Reg|_], ( R = const(Tmp),atomic_concat('$',Tmp,X) ; R = id(X)) ;
      (L = const(Tmp), atomic_concat('$',Tmp,X) ; L = id(X)), R = [Reg|_] ),
	                   % X and Reg are AL representations of operands
                       % handle operators that can be performed between any registers

	% Commutative operators may invert the order of Left and Right operands.
	% Non-commutative operators (-) must have register operands on the left
	%   -- this is tested at the same time with the translation Op -> OpCode
    member((Op,I,L),   % moreover, handle only commutative operators
           [(+,addl,_),(-,subl,[_|_]),(*,imull,_),(/\,andl,_),(\/,orl,_)]),!,
    ( L = [_|_] -> Result = L ; Result = R ),
    CodeOp = [ '\n\t\t ',I,' ',X,',',reg32(Reg) ], % code to perform operation between
    (CL = [] -> CS = CR ; CS = CL),                % result reg and const/var operand
    append([CS,CodeOp],Code).                      % order of operands NOT SIGNIFICANT

combine_expr_code(L,R,Op,CL,CR,Code,Residue,Result) :- % relational Opr, one reg opd, one non-reg
                       % One subexpression is const/variable, the other needs
                       % registers. This rule is for boolean operators.
    ( L = [Reg|_], ( R = const(Tmp), atomic_concat('$',Tmp,X) ; R = id(X)) ;
      (L = const(Tmp), atomic_concat('$',Tmp,X) ; L = id(X)), R = [Reg|_] ),
	                   % X and Reg are AL representations of L and R, or R and L
    member((Op,I),
           [(<,setl),(=<,setle),(>,setg),(>=,setge),(==,sete),(\=,setne)]),!,
                       % check if boolean operator, and set instruction for
                       % residual code

	% The result is the same list of registers as for the
	% operand represented in a register
    ( L = [_|_] -> Result = L ; Result = R ),

	(   CL = []        % Figure out the order of the operands. The one that comes in
	                   % with empty code is the non-reg one
                       % CS = code subexpression; whatever non-empty code comes from
		               %      arguments must be copied into generated code of the
	                   %      current expression.
	 ->	% If the right operand is in register, then CS must reference code from right
	    % Comparison is between X and Reg holding Result of Right (at&t reverses arg order)
	    CS = CR, CodeOp = [ '\n\t\t cmpl ',reg32(Reg),',',X ]
    ;   % Otherwise, the left operand must be in register, therefore CS must reference code of left
		% Comparison is in oposite order, between Reg and X
	    CS = CL, CodeOp = [ '\n\t\t cmpl ',X,',',reg32(Reg) ] ),
	% Lay out all the code in the generated Code.
    append([CS,CodeOp],Code),
    Reg in 0..3, % Constrain the registers to be {%eax,%edx,%ecx,%ebx}
	             % This is because in generating the residual code,
				 % the corresponding 8-bit reg must be used
				 % in transferring result of comparison into register, and %esi and %edi
				 % do not have corresponding 8-bit registers.
    Residue = [ '\n\t\t movl $0,',reg32(Reg), % residual code to use in expressions
                '\n\t\t ',I,' ',reg8(Reg) ].  % of the form 1 + (a<b).
    % NOTE: more aggressive optimization could be used here, since we can find out
    % whether the residual code would be needed or not. If residual code not needed,
    % registers can be relaxed to the entire set of 6.

combine_expr_code(L,R,Op,CL,[],Code,[],Result) :- % Op=div,rem ; Left = reg, Right = non-reg
                       % For division/remainder, left operand MUST use registers,
                       % because of the constraints imposed by the idivl instruction.
                       % This is the case when the right operand is const/variable.
    L = [_|_], ( R = const(Tmp), atomic_concat('$',Tmp,X) ; R = id(X)),
    member((Op,I), [(/,idivl),(rem,idivl)]),!,

	% Left subexpression may have used 1 or more registers, handle each case separately
	% A register may need to be allocated for right operand. A legal right operand will
	% be computed in Z, and the (possibly empty) code that sets up Z is generated into
	% CodeL.
    ( L = [0|T], select(1,T,Rest),
                       % If it used multiple registers, we try to make %edx one
                       % of the other used registers, and then reuse the registers
                       % in computing the entire expression (i.e. no new register is
                       % needed)
      (R = const(_) % differentiate between const and id; differentiate between / and rem
        -> ( select(Reg,Rest,RRest) ; RRest = Rest),
           (Op == / -> Result = [0,1,Reg|RRest] ; Result = [1,0,Reg|RRest]),
           CodeL = [ '\n\t\t movl ',X,',',reg32(Reg) ], Reg in 0..5, Z = reg32(Reg)
        ;  (Op == / -> Result = L ; Result = [1,0|Rest] ), CodeL = [], Z = X ) )
                       % If Op = /, then result in %eax; if remainder, result in %edx

    ; L = [0],         % If a single register was used, then it must be the case that
                       % this register is %eax, and %edx will be used also (it is
                       % clobbered by idivl, so it must be indicated as 'used').
      (R = const(_)
        -> CodeL = [ '\n\t\t movl ',X,',',reg32(Reg) ], Reg in 0..5, Z = reg32(Reg),
           (Op == / ->  Result = [0,1,Reg] ; Result = [1,0,Reg])
        ;  CodeL = [], (Op == / ->  Result = [0,1] ; Result = [1,0]), Z = X ),
                       % If Op = /, then result in %eax; if remainder, result in %edx

    % Code performing division/rem; Z is now the AL representation of right operand.
    CodeOp = [ '\n\t\t movl ',reg32(0),',',reg32(1), % copy %eax into %edx
               '\n\t\t shrl $31,',reg32(1),          % %edx is now sign extension of %eax
               '\n\t\t ',I,' ',Z ],                  % I = idivl, Z = right operand

	all_distinct(Result),           % Constrain all allocated registers to be distinct.
    append([CL,CodeL,CodeOp],Code). % Lay out the generated Code.

combine_expr_code(L,R,Op,[],CR,Code,[],Result) :- % Op = -, Left = non-reg, Right = reg
                       % The case when left subexpr is const/variable and
                       % right subexpression requires registers, for non-commutative
                       % operators --> may require an extra register
	                   % A similar rule for the same combination of arguments, but
					   % for commutative operators, was given above.
    (L = const(Tmp),atomic_concat('$',Tmp,X) ; L = id(X)), R = [Reg|_],
	                   % X and Reg are the AL representation of Left and Right results

    Op = -,!, I = subl,% minus is non-commutative

    ( R = [Reg,Reg1|Rest]         % If a single register is used in computing
      -> Result = [Reg1,Reg|Rest] % subexpression, then an extra register is required
      ;  Result = [Reg1,Reg] ),   % to compute current expression. Reg1 is either
								  % reused, or newly allocated, depending on the length
								  % of R (either 1 register or more).

    % Generate code to perform subtraction
    CodeOp = [ '\n\t\t movl ',X,',',reg32(Reg1), % order of operands is now SIGNIFICANT
               '\n\t\t ',I,' ',reg32(Reg),',',reg32(Reg1) ],

	Result ins 0..5, all_distinct(Result), % Constrain newly allocated registers.
    append([CR,CodeOp],Code).			   % Lay out the generated code

combine_expr_code(L,R,Op,[],CR,Code,[],Result) :- % Op = /,rem ; Left = non-reg, Right = reg
                       % Left operand is const/variable, and right operand requires
                       % registers. Operation is division/remainder
                       % May require an extra register
    (L = const(Tmp),atomic_concat('$',Tmp,X) ; L = id(X)), R = [H|T],
	                   % X is the AL representation of left operand.
					   % H is the register holding the right result
    member(Op,[/,rem]) ,!, I = idivl,

    ( H #\= 0, H #\= 1,  % easy case, right operand does not require %eax or %edx
                         % then, register holding result not clobbered by division/rem
                         % try to force %eax, %edx as used registers, but not holding
                         % result, since they will be used anyway by idivl --> leads
                         % to register use minimization
      (  select(0,T,R1), select(1,R1,Rest) % Try enforcing both %eax,%edx be used in R
       ; select(0,T,Rest)                  % If not possible, try only %eax
       ; select(1,T,Rest)				   % If not possible, try only %edx
       ; Rest = T ),                       % Failsafe, leave it as it is
                         % Result will be in %eax or %edx, depending on Op = / or Op = rem
      (Op == / -> Result = [0,1,H|Rest] ; Result = [1,0,H|Rest]),
                         % %eax and %edx can be used freely, since they do not hold
                         % anything important

      CodeOp = [ '\n\t\t movl ',X,',',reg32(0),        % Left operand must be moved into %eax
                 '\n\t\t movl ',reg32(0),',',reg32(1), % Sign extend %eax into %edx in usual way
                 '\n\t\t shrl $31,',reg32(1),
                 '\n\t\t ',I,' ',reg32(H) ]            % I = idivl, H is right operand

    ; (  select(0,T,Rest) % Tough case, result of right operand in either %eax or %edx
       ; select(1,T,Rest) % Try enforcing the use of both regs in code of right operand (may fail)
       ; Rest = T ),      % Failsafe case, all registers already concretized
                          % Check if new register is needed to save the result of
                          % right operand. Reg will either be an existing 'used'
                          % register (but not holding anything important, so that
                          % it can be used to hold a partial result) if possible, or a
                          % completely new, 'unused' register, if a 'used' one
                          % cannot be found.
    ( Rest = [] -> TRest = [] ; Rest = [Reg|TRest] ),
	                      % Reorder the used registers, and
	                      % add %eax and %edx if not in Result already
    (Op = / -> Result = [0,1,Reg|TRest] ; Result = [1,0,Reg|TRest]),
                          % The result of right operand will be saved from either
                          % %eax or %edx into Reg. Then, %eax and %edx can be used
                          % in the idivl operation.
      CodeOp = [ '\n\t\t movl ',reg32(H),',',reg32(Reg), % save %eax or %edx
                 '\n\t\t movl ',X,',',reg32(0),          % load %eax with left opd
                 '\n\t\t movl ',reg32(0),',',reg32(1),   % sign extend %eax into %edx
                 '\n\t\t shrl $31,',reg32(1),
                 '\n\t\t ',I,' ',reg32(Reg) ]            % divide by second, saved operand
    ),
    all_distinct(Result), % Most registers are still unbound,
                          % make sure they will be distinct when allocated
    append([CR,CodeOp],Code). % Lay out generated Code.

% The next 3 rules are the really gruesome ones. Both operands are in
% registers, and we distinguish between
%   -- arithmetic operators excluding division and rem,
%   -- division and rem
%   -- relational operators.
% Since both operands require registers, we must make sure that as many
% of the registers are reused, while not clobbering the result of one
% expression while we're computing the other one. Either or both of the
% left and right subexpressions might have idivl as the toplevel
% operator -- this complicates things tremendously, resulting in many
% extra cases.

combine_expr_code(L,R,Op,CL,CR,Code,Residue,Result) :-
                          % Both expressions require registers, and the operator
                          % is boolean. Here we would like to use as many common
                          % registers as possible, so as to minimize register use.
                          % Generating code for the subexpression that requires more
                          % registers first will lead to 1 register holding the
                          % subexpression result, and the remaining registers to
                          % be potentially reused in the code generation of the
                          % other subexpression. If both subexpressions require the
                          % same number of registers, then an extra register will be
                          % required.
                          % This rule is for boolean operators, and is simpler
                          % because the result is stored in the flags (any register
                          % can be used for the residual code).
    L = [HL|TL], R = [HR|TR], L ins 0..5, R ins 0..5, NewReg in 0..5,
	                      % Left and right results are both lists of unbound variables
						  % The first element holds the result, the other elements
						  % represent registers that MUST be used during the evaluation
						  % of that expression (and thus will be clobered in the process,
						  % so the compiler can't expect the original values in those
						  % registers to be preserved). We constrain these variables
						  % to numbers between 0 and 5, so they can be mapped into
						  % the Pentium registers later.
    member((Op,I),
           [(<,setl),(=<,setle),(>,setg),(>=,setge),(==,sete),(\=,setne)]),!,
	                      % Use	member to translate the operator into the corresponding opcode
    length(L,LgL), length(R,LgR),
                          % We distinguish 3 cases, based on the number of registers
						  % that are used in the code of each subexpression

    % first case, when both subexpressions require same no. regs --> extra reg needed
    ( LgL #= LgR
      ->    % happy subcase, the two result registers can be constrained to be different
	        % (this is not always possible, for instance, not in the case when toplevel
			%  operator of both sides is division, and the result from both sides must
			%  reside in %eax)
         (  HL #\= HR,    % enforce register reuse by making the right reg list
                          % a subset of the left tail + extra reg (denoted by '_')
			              % -- this is where constraint programming comes in really handy!!!
            permutation([_|TL],R), Result = [HL,HR|TR],
                          % current operation implemented as comparison, result in flags
            CodeOp = [ '\n\t\t cmpl ',reg32(HR),',',reg32(HL) ],
                          % Generated code made up of the left subexpression code,
                          % followed by right subexpression code, followed by
                          % current operator code.
            append([CL,CR,CodeOp],Code),
            HL in 0..3,   % Residue moves flag result into register, so as to allow
                          % compilation of expressions of the form 1+(a<b)
						  % Result of residue can only be placed in either %eax,%edx,%ecx,%ebx
			              % since only these registers have an 8-bit corresponding register
            Residue = [ '\n\t\t movl $0,',reg32(HL),
                        '\n\t\t ',I,' ',reg8(HL) ]

          ; % less happy subcase, the two result registers are the same
            % this can only happen if the top-level operators of the left
            % and right subexpressions are both division or both remainder
            % extra register is needed to save right result
            (HL #= 0 ; HL #=1), ( HR #= 0 ; HR #= 1 ),
                          % enforce register reuse, as above
            permutation(TL,TR), Result = [NewReg,HL|TL],
                          % Generated code obtained by laying out
                          % the left subexpr code, followed by saving
                          % the result from either %eax or %edx into
                          % a new register, followed by the code for
                          % right subexpr, followed by comparison between
                          % %eax or %edx (depending on whether current Op is / or rem)
                          % and the saved register.

			% Remember, here, HL and HR are actually the same. So, we lay out the code for
		    % left subexpression, then we need an instruction that saves HL into NewReg,
		    % which is a register not used in the code of the right subexpression. HL
		    % is about to be clobbered by the code of the right subexrpession, and without
		    % saving it into NewReg, we'd lose the result of the left side.
            append( [  CL,                                              % eval left expr
                       [ '\n\t\t movl ',reg32(HL),',',reg32(NewReg) ],  % save result into NewReg
                       CR,												% eval right expr
                       [ '\n\t\t cmpl ',reg32(HR),',',reg32(NewReg) ] ],% perform comparison
                       Code ) ), % The result is in fact the value of the processor's flags,
			                     % and the caller can directly generate a jXX instruction
			                     % based on the operator at the top level of the expression.

            NewReg in 0..3, % only 4 regs allow setXX instructions
                            % residual code transfers flag result into a register

            Residue = [ '\n\t\t movl $0,',reg32(NewReg), % The caller will check the context of the
                        '\n\t\t ',I,' ',reg8(NewReg) ]   % current expression. If say, expression
						                                 % (x < y) appears in the context 1+(x<y),
														 % then the residue needs to be appended to
														 % Code, so as to have the result of the
														 % current expression in a register

      % Second case, when right subexpr requires fewer regs than left
      % No new register needed; lay out code for left subexpr first, then for right
	  % This makes sense because after evaluating the left expression, which needs more registers,
	  % we end up with a list of registers that have been used, but do not hold anything
	  % important, and are in sufficient number to be used in evaluating the subexpression
	  % on the right side. Thus, the total number of registers used is max(LgR,LgL).

      ;  LgR #< LgL
         -> (  HL #\= HR, % Happy case, result registers different.
                          % Permutation constraint ensures register reuse, as above
			              % No need for a new register
               permutation(TL,TLP), append(R,_,TLP), Result = L,
               CodeOp = [ '\n\t\t cmpl ',reg32(HR),',',reg32(HL) ],
               append([CL,CR,CodeOp],Code),
               HL in 0..3,
               Residue = [ '\n\t\t movl $0,',reg32(HL),
                           '\n\t\t ',I,' ',reg8(HL) ]

             % less happy case, the two result registers are the same
             % this can only happen if the top-level operators of the left
             % and right subexpressions are both division or both remainder
             % extra register may be needed to save right result, when
             % len(Left) = len(Right)+1
             ; (HL #= 0 ; HL #=1), ( HR #= 0 ; HR #= 1 ),
                          % Enforce register reuse, as above
               permutation(TL,TLP),
               (  append(TR,[NewReg|_],TLP),!,select(NewReg,TL,TLRest)
                ; TR = TLP, TLRest = TL ),
                          % NewReg will be a new, 'unused' register, if
                          % a 'used' one cannot be found.
               Result = [NewReg,HL|TLRest],
                          % NewReg used to save left subexpr result while
                          % the right subexrp is computed. NewReg also holds
                          % final result
               append( [  CL,
                          [ '\n\t\t movl ',reg32(HL),',',reg32(NewReg) ],
                          CR,
                          [ '\n\t\t cmpl ',reg32(HR),',',reg32(NewReg) ] ],
                          Code ) ),
               NewReg in 0..3,
               Residue = [ '\n\t\t movl $0,',reg32(NewReg), % Residue as usual
                           '\n\t\t ',I,' ',reg8(NewReg) ]

         % third case, when left subexpr requires fewer regs than right
         ;  (  HL #\= HR, % happy case, result registers are different
                          % enforce register reuse
               permutation(TR,TRP), append(L,_,TRP),
               select(HL,R,Rest), Result = [HL|Rest],
               CodeOp = [ '\n\t\t cmpl ',reg32(HR),',',reg32(HL) ],
               % Result of right subexpr will be naturally untouched
               % during the computation of the left subexpr, because
               % of the register reuse constraint
               append([CR,CL,CodeOp],Code),
               HL in 0..3,
               Residue = [ '\n\t\t movl $0,',reg32(HL), % residue as usual
                           '\n\t\t ',I,' ',reg8(HL) ]

			% less happy case, the two result registers are the same
             ; (HL #= 0 ; HL #=1), ( HR #= 0 ; HR #= 1 ),
			   % attempt to enforce as much reuse as possible
			   % NewReg may end up being a completely new register
               permutation(TR,TRP),
               (  append(TL,[NewReg|_],TRP),!,select(NewReg,TR,TRRest)
                ; TL = TRP, TRRest = TR ),
                          % NewReg is a new, 'unused' register, only if a 'used'
                          % one cannot be found. NewReg will be used to save
                          % the result of the right subexpr while the left one
                          % is being computed.
			   Result = [HR,NewReg|TRRest]),
                          % Generated code obtained by laying out the right
                          % subexpr code, followed by a save of the result
                          % into the new register, followed by the left
                          % subexpr code, followed by the computation of
                          % the current operator --> result left in flags
               append( [  CR,
                          [ '\n\t\t movl ',reg32(HR),',',reg32(NewReg) ],
                          CL,
                          [ '\n\t\t cmpl ',reg32(NewReg),',',reg32(HL) ] ],
                          Code ),
               HL in 0..3,
               Residue = [ '\n\t\t movl $0,',reg32(HL),
                           '\n\t\t ',I,' ',reg8(HL) ] ),
               % enforce that all registers used in computing this expression be
               % distinct when subjected to labeling.
    all_distinct(Result). % Phew!!!

combine_expr_code(L,R,Op,CL,CR,Code,[],Result) :-
                          % Both expressions require registers, and the operator
                          % is arithmetic. Here we would like to use as many common
                          % registers as possible, so as to minimize register use.
                          % Generating code for the subexpression that requires more
                          % registers first will lead to 1 register holding the
                          % subexpression result, and the remaining registers to
                          % be potentially reused in the code generation of the
                          % other subexpression. If both subexpressions require the
                          % same number of registers, then an extra register will be
                          % required.
    L = [HL|TL], R = [HR|TR], L ins 0..5, R ins 0..5, NewReg in 0..5,
	                      % Left and right results are both lists of unbound variables
						  % The first element holds the result, the other elements
						  % represent registers that MUST be used during the evaluation
						  % of that expression (and thus will be clobered in the process,
						  % so the compiler can't expect the original values in those
						  % registers to be preserved). We constrain these variables
						  % to numbers between 0 and 5, so they can be mapped into
						  % the Pentium registers later.
    member((Op,I),[(+,addl),(-,subl),(*,imull),(/\,andl),(\/,orl)]),!,
	                      % Use	member to translate the operator into the corresponding opcode
    length(L,LgL), length(R,LgR),
                          % We distinguish 3 cases, based on the number of registers
						  % that are used in the code of each subexpression

    % first case, when both subexpressions require same no.
    % regs --> extra reg needed
    ( LgL #= LgR
            % happy case, the two result registers are different
      -> (  HL #\= HR,
                          % enforce register reuse by making the right reg list
                          % a subset of the left tail + extra reg (denoted by '_')
            permutation([_|TL],R), Result = [HL,HR|TR],
                          % current operation between the two result registers
            CodeOp = [ '\n\t\t ',I,' ',reg32(HR),',',reg32(HL) ],
                          % Generated code made up of the left subexpression code,
                          % followed by right subexpression code, followed by
                          % current operator code.
            append([CL,CR,CodeOp],Code)

            % less happy case, the two result registers are the same
            % this can only happen if the top-level operators of the left
            % and right subexpressions are both division or both remainder
            % extra register is needed to save right result
          ; (HL #= 0 ; HL #=1), ( HR #= 0 ; HR #= 1 ),
                          % enforce register reuse, as above
            permutation(TL,TR), Result = [NewReg,HL|TL], NewReg in 0..5,
                          % Generated code obtained by laying out
                          % the left subexpr code, followed by saving
                          % the result from either %eax or %edx into
                          % a new register, followed by the code for
                          % right subexpr, followed by instruction that
                          % performs the current operator between the
                          % result of right subexpr, and the result
                          % of left subexpr saved in NewReg. The overall
                          % result is kept in NewReg.
            append( [  CL,
                       [ '\n\t\t movl ',reg32(HL),',',reg32(NewReg) ],
                       CR,
                       [ '\n\t\t ',I,' ',reg32(HR),',',reg32(NewReg) ] ],
                       Code ) )
      % second case, when right subexpr requires fewer regs than left
      % no new register needed; lay out code for left subexpr first, then for right
      ;  LgR #< LgL
         -> (  HL #\= HR, % happy case, result registers different
                          % permutation constraint ensures register reuse, as above
               permutation(TL,TLP), append(R,_,TLP), Result = L,
               CodeOp = [ '\n\t\t ',I,' ',reg32(HR),',',reg32(HL) ],
               append([CL,CR,CodeOp],Code)

             % less happy case, the two result registers are the same
             % this can only happen if the top-level operators of the left
             % and right subexpressions are both division or both remainder
             % extra register may be needed to save right result, when
             % len(Left) = len(Right)+1
             ; (HL #= 0 ; HL #=1), ( HR #= 0 ; HR #= 1 ),
                          % Enforce register reuse, as above
               permutation(TL,TLP),
               (  append(TR,[NewReg|_],TLP),!,select(NewReg,TL,TLRest)
                ; TR = TLP, TLRest = TL ),
                          % NewReg will be a new, 'unused' register, if
                          % a 'used' one cannot be found.
               Result = [NewReg,HL|TLRest],
                          % NewReg used to save left subexpr result while
                          % the right subexrp is computed. NewReg also holds
                          % final result
               append( [  CL,
                          [ '\n\t\t movl ',reg32(HL),',',reg32(NewReg) ],
                          CR,
                          [ '\n\t\t ',I,' ',reg32(HR),',',reg32(NewReg) ] ],
                          Code ) )
         % third case, when left subexpr requires fewer regs than right
         ;  (  HL #\= HR, % happy case, result registers are different
                          % enforce register reuse
               permutation(TR,TRP), append(L,_,TRP),
               select(HL,R,Rest), Result = [HL|Rest],
               CodeOp = [ '\n\t\t ',I,' ',reg32(HR),',',reg32(HL) ],
               % Result of right subexpr will be naturally untouched
               % during the computation of the left subexpr, because
               % of the register reuse constraint
               append([CR,CL,CodeOp],Code)
             % less happy case, the two result registers are the same
             ; (HL #= 0 ; HL #=1), ( HR #= 0 ; HR #= 1 ),
               permutation(TR,TRP),
               (  append(TL,[NewReg|_],TRP),!,select(NewReg,TR,TRRest)
                ; TL = TRP, TRRest = TR ),
                          % NewReg is a new, 'unused' register, only if a 'used'
                          % one cannot be found. NewReg will be used to save
                          % the result of the right subexpr while the left one
                          % is being computed.
               Result = [HR,NewReg|TRRest]),
                          % Generated code obtained by laying out the right
                          % subexpr code, followed by a save of the result
                          % into the new register, followed by the left
                          % subexpr code, followed by the computation of
                          % the current operator
               append( [  CR,
                          [ '\n\t\t movl ',reg32(HR),',',reg32(NewReg) ],
                          CL,
                          [ '\n\t\t ',I,' ',reg32(NewReg),',',reg32(HL) ] ],
                          Code ) ),
    all_distinct(Result). % Phew!!! Phew!!!

combine_expr_code(L,R,Op,CL,CR,Code,[],Result) :-
                          % Both expressions require registers, and the operator
                          % is either division or remainder. Code generation is
                          % similar to the rule above, yet slightly
                          % more difficult due to the fact that the result of
                          % the left subexpression must end up in %eax
    L = [HL|TL], R = [HR|TR], L ins 0..5, R ins 0..5, NewReg in 0..5,
	                      % Left and right results are both lists of unbound variables
						  % The first element holds the result, the other elements
						  % represent registers that MUST be used during the evaluation
						  % of that expression (and thus will be clobered in the process,
						  % so the compiler can't expect the original values in those
						  % registers to be preserved). We constrain these variables
						  % to numbers between 0 and 5, so they can be mapped into
						  % the Pentium registers later.
    member((Op,I),[(/,idivl),(rem,idivl)]),!,
	                      % Use	member to translate the operator into the corresponding opcode
    length(L,LgL), length(R,LgR),
                          % We distinguish 3 cases, based on the number of registers
						  % that are used in the code of each subexpression

    % first case, left and right subexpressions require same no of regs
    ( LgL #= LgR
            % Enforce that left subexpr places result in %eax (preferred)
            % or in %edx (cannot be avoided if left top level opr is remainder)
            % happy case is that right subexpr puts result somewhere else
      -> (  ( HL #= 0 ; HL #= 1), HR #\= 0, HR #\= 1,
            Other #= 1 - HL,
            % enforce reuse of registers, and the use of %eax and %edx
            % in the right subexpr
            permutation([_|TR],L),
            (  select(0,R,R1), select(1,R1,R2)
             ; select(0,R,R2)
             ; select(1,R,R2)
             ; R2 = R ),
            (  Op == / ->  Result = [0,1|R2] ; Result = [1,0|R2] ),
            CodeOp = [ '\n\t\t movl ',reg32(HL),',',reg32(Other),
                       '\n\t\t shrl $31,',reg32(1),
                       '\n\t\t ',I,' ',reg32(HR) ],
            % lay out the right subexpr code first (using %eax and %edx for
            % temporary results if possible), and then left subexpr code,
            % and then place the division code
            append([CR,CL,CodeOp],Code)
            % Enforce that left subexpr places result in %eax (preferred)
            % or in %edx (cannot be avoided if left top level opr is remainder)
            % less happy case -> right subexpr places result in same register
            % An extra register is needed here to save result of right subexpr
          ; ( HL #= 0 #\/ HL #= 1 ), ( HR #= 0 #\/ HR #= 1 ),
            OtherL #= 1-HL,
            % enforce register reuse, and try reusing %eax and %edx in right subexpr
            permutation(L,R),
            (  select(0,R,R1), select(1,R1,R2)
             ; select(0,R,R2)
             ; select(1,R,R2)
             ; R2 = R ),
            % register order depends on operator
            (    Op == /
             ->  Result = [0,1,NewReg|R2]   % %eax, then %edx
             ;   Result = [1,0,NewReg|R2] ),% %edx, then %eax
            % Lay out resulting code with code for right subexpr first,
            % then save right result into new register, then copy
            % %eax into %edx or viceversa, and then sign extend %edx,
            % and then perform the division/remainder between %eax and
            % new register
            append( [  CR,
                       [ '\n\t\t movl ',reg32(HR),',',reg32(NewReg) ],
                       CL,
                       [ '\n\t\t movl ',reg32(HL),',',reg32(OtherL),
                         '\n\t\t shrl $31,',reg32(1),
                         '\n\t\t ',I,' ',reg32(NewReg) ] ],
                       Code ) )
      % second case, left subexpr requires more registers than left one
      ;  LgR #< LgL
               % Enforce result of left subexpr be available in either %eax or %edx
         -> (  ( HL #= 0 #\/ HL #= 1 ),
               OtherL #= 1 - HL,
               % Compute Save and Restore codes that may be inserted between
               % codes for left and right subexpressions to preserve partial
               % results
               % enforce register reuse
               permutation(L,LP),
               ( member(HL,R) % if reg of left result used in code of right subexpr
                              % (may be unavoidable due to / or rem)
                 -> (  append(R,[NewReg|_],LP),!,select(NewReg,TL,TLRest)
                              % right registers subset of left registers
                     ; R = LP, TLRest = TL ),
                              % find used or new register to save left result
                    ( select(OtherL,TLRest,TLRest2) ; TLRest2 = TLRest ),
                    ( (Op == /) % NewReg can be used to save result of left opd
                      ->  Result = [0,1,NewReg|TLRest2]
                      ;   Result = [1,0,NewReg|TLRest2] ),
                    % the save code saves partial result into new register
                    Save = [ '\n\t\t movl ',reg32(HL),',',reg32(NewReg) ],
                    ( HR #= 0     % right result in %eax
                      -> Restore = [ '\n\t\t xchg ',reg32(0),',',reg32(NewReg) ]
                      ;  HR #= 1  % right result in %edx
                                  % The corresponding restore code:
                         -> Restore = [ '\n\t\t movl ',reg32(NewReg),',',reg32(0),
                                        '\n\t\t movl ',reg32(1),',',reg32(NewReg) ]
                          ; Restore = [ '\n\t\t movl ',reg32(NewReg),',',reg32(0) ])
                 ;  append(R,_,LP), % reg of left result not used in code of
                                    % right subexpr --> nothing to save/restore
                    (select(OtherL,TL,TL2) ; TL2 = TL ),
                                    % make sure both %eax and %edx reused in
                                    % code of left subexpr
                    ( Op == /
                      ->  Result = [0,1|TL2]
                      ;   Result = [1,0|TL2] ),
                    Save = [], Restore = [] ), % nothing to save/restore
               ( ( HR #= 0 #\/ HR #= 1 )
                                    % repeat the test on where the right
                                    % subexpression result is stored to
                                    % generate the correct code for current operator
                 -> CodeOp = [ '\n\t\t movl ',reg32(0),',',reg32(1),
                               '\n\t\t shrl $31,',reg32(1),
                               '\n\t\t ',I,' ',reg32(NewReg) ]
                 ;  CodeOp = [ '\n\t\t movl ',reg32(0),',',reg32(1),
                               '\n\t\t shrl $31,',reg32(1),
                               '\n\t\t ',I,' ',reg32(HR) ] ),
               append([CL,Save,CR,Restore,CodeOp],Code) )
         % Third case, when right subexpr requires more registers than the left one
         % Here we lay out the code for right subexpr first, and we constrain
         % the result of left subexpr to be stored in %eax or %edx
         % We also constrain %eax and %edx to be reused in computation
         % of right subexpr, if possible. We also try to constrain the right
         % result register to not be used in the computation of left subexpr; if
         % that is not possible, then we save right result register into a
         % new register
         ;  (  ( HL #= 0 #\/ HL #= 1 ),
               OtherL #= 1 - HL,
               % Enforce register reuse
               permutation(R,RP),
               append(L,[NewReg|_],RP),select(NewReg,R,RRest),
               (  select(0,RRest,RR1),select(1,RR1,RR2)
                ; select(0,RRest,RR2)
                ; select(1,RRest,RR2)
                ; RR2 = RRest ),
               (  notmember(HR,L), % if true, no need to save right register
                  Save = [],
                  CodeOp = [ '\n\t\t movl ',reg32(HL),',',reg32(OtherL),
                             '\n\t\t shrl $31,',reg32(1),
                             '\n\t\t ',I,' ',reg32(HR) ] ,
                  ( Op == /
                    ->  Result = [0,1|RR2]
                    ;   Result = [1,0|RR2] )
                  % if member(HR,L), then need to find new register, and save
                ; Save = [ '\n\t\t movl ',reg32(HR),',',reg32(NewReg) ],
                  CodeOp = [ '\n\t\t movl ',reg32(HL),',',reg32(OtherL),
                             '\n\t\t shrl $31,',reg32(1),
                             '\n\t\t ',I,' ',reg32(NewReg) ] ),
                  ( Op == /
                    ->  Result = [0,1,NewReg|RR2]
                    ;   Result = [1,0,NewReg|RR2] ) ),
                 % There's no need to restore here, since %eax/%edx store result
               append([CR,Save,CL,CodeOp],Code) ),
    all_distinct(Result). % make sure all registers are distinct at labeling time.
% PHEW!!! PHEW!!! PHEW!!! PHEW!!! PHEW!!!

% predicate to check for lack of membership
% unlike \+ member(...), it does not fail when
% unbound variables are used
notmember(_,[]).
notmember(X,[Y|T]) :- X \== Y, notmember(X,T).

% Compiler of expressions
%  1st arg : program fragment to be translated
%  2nd arg : generated code for arg 1
%  3rd arg : attributes in
%  4th arg : attributes out
ce(N,Code,Ain,Aout) :- % generate code for an integer
    integer(N),!,
    get_assoc(context,Ain,Ctx),
    (   Ctx = expr
     -> put_assoc(expr_result,Ain,const(N),Aout),
        Code = [] % nothing to generate in expression context
     ;  put_assoc(expr_result,Ain,[0],Aout),
                  % code for the case where N appears in an 'if' or 'while' cond
        Code = [ '\n\t\t movl $',N,',%eax',
                 '\n\t\t cmpl %eax,$0' ] ).

ce(X,Code,Ain,Aout) :- % generate code for variable
    atom(X),!,
    get_assoc(vars,Ain,V,A1,NV),
    union(V,[X],NV),
                       % collect identifier so it can be printed by the runtime
    put_assoc(expr_result,A1,id(X),Aout),
                       % check context
    get_assoc(context,Ain,Ctx),
    (   Ctx = expr
     -> Code = []      % empty code in expression context
     ;  Code = [ '\n\t\t cmpl ',X,',$0' ] ).
                       % comparison code in 'if' or 'while' condition

ce(E,Code,Ain,Aout) :- % generate code for binary operator
    E =.. [Op,EL,ER],!,
    put_assoc(context,Ain,expr,A0), % request expression context
    ce(EL,CodeL,A0,A1),             % recursively compile left subexpr
    ce(ER,CodeR,A1,A2),             % recursively compile right subexpr
    get_assoc(expr_result,A1,ERL),  % combine the codes and registers
    get_assoc(expr_result,A2,ERR),  % getting code C, Residue, and regs in Result
    combine_expr_code(ERL,ERR,Op,CodeL,CodeR,C,Residue,Result),
    get_assoc(context,Ain,Ctx),
    (   Ctx == expr                 % Figure out if residual code needs to be
     -> append(C,Residue,Code)      % appended to currently generated code
     ;  (   notmember(Op,[<,=<,==,\=,>=,>])
         -> ( Result = [Temp|_],R = reg32(Temp) ; Result = id(R) ),
            append(C,['\n\t\t cmpl ',R,',$0'],Code)
         ;  Code = C ) ),
    put_assoc(expr_result,A2,Result,Aout).

ce(E,Code,Ain,Aout) :- % generate code for unary operator
    E =.. [Op,Es],!,   % can be either unary minus, or logical negation
    put_assoc(context,Ain,expr,A0),
    ce(Es,CodeS,A0,A1), % recursively compile argument of unary operator
    get_assoc(expr_result,A1,Regs),
    (   Op = (-)  % unary minus
     -> (   Regs = const(N)
         -> N1 #= (-N), Code = [], RegsOut = const(N1)
         ;  (   Regs = id(X)
             -> RegsOut = [NewReg],
                CodeOp = [ '\n\t\t movl ',X,',',reg32(NewReg),
                           '\n\t\t negl ',reg32(NewReg) ],
                Residue = []
             ;  Regs = [R|_], RegsOut = Regs,
                CodeOp = [ '\n\t\t negl ',reg32(R) ],
                Residue = [] ) )
     ;  (   Op = (\) % logical negation
         -> (   Regs = const(N)
             -> N1 #<==> (N #= 0) , Code = [], RegsOut = const(N1)
             ;  (   Regs = id(X)
                 -> RegsOut = [NewReg], NewReg in 0..3,
                    CodeOp = [ '\n\t\t movl ',X,',',reg32(NewReg),
                               '\n\t\t cmpl ',reg32(NewReg),',$0'],
                    Residue = [ '\n\t\t movl $0,',reg32(NewReg),
                                '\n\t\t sete ',reg8(NewReg)]
                 ;  Regs = [R|_], RegsOut = Regs, R in 0..3,
                    CodeOp =  [ '\n\t\t cmpl ',reg32(R),',$0' ],
                    Residue = [ '\n\t\t movl $0,',reg32(R),
                                '\n\t\t sete ',reg8(R) ] ) )
         ;  RegsOut = Regs, CodeOp = [] ) ),
    get_assoc(context,Ain,Ctx),
    (   Ctx == expr % Figure out if residual code needs to be appended
     -> append([CodeS,CodeOp,Residue],Code)
     ;  (   notmember(Op,[<,=<,==,\=,>=,>])
         -> ( RegsOut = [Temp|_],R = reg32(Temp) ; RegsOut = id(R) ),
            append([CodeS,CodeOp,['\n\t\t cmpl ',R,',$0']],Code)
         ;  append([CodeS,CodeOp],Code) ) ),
    put_assoc(expr_result,A1,RegsOut,Aout).

% Compile expression wrapper
% -- same arguments as 'ce'
% -- calls label(...) to perform the actual numeric allocation
% -- run 'replace_regs' to replace 'reg32(X)' constructs by the normal
%    register names
% -- result in CER is assembly language code that evaluates expr E
comp_expr(E,CER,Ain,Aout) :-
    ce(E,CE,Ain,Aout),
    get_assoc(expr_result,Aout,Result),
    (  Result = [_|_], Result ins 0..5, label(Result) ; true ),
    replace_regs(CE,CER).

	
% Compile statement -- implements while language
cs(break, Code,Ain,Aout) :- !,    % added in class, as example of adding
	Code = [ '\n\t\t jmp ',Lbl ], % new attributes
	get_assoc(labelsuffix,Ain,LabelSuffixIn,A,LabelSuffixOut),
	generateLabels([Lbl],LabelSuffixIn,LabelSuffixOut),
	put_assoc(break,A,Lbl,Aout).

cs((X=E),Code,Ain,Aout) :- !, atom(X), % assignment
    put_assoc(context,Ain,expr,A1),    % request expression context
    comp_expr(E,CE,A1,A2),             % compile right hand side
    get_assoc(vars,A2,V,Aout,NV), union(V,[X],NV),
                                       % collect all variable names so their values
                                       % can be later printed by the runtime

    % Check where the result of rhs is stored, and transfer it into
    % storage of variable X
    get_assoc(expr_result,A2,Result),
    (    Result = const(N) % if result is constant, load it into X
     ->  Cop = [ '\n\t\t movl $',N,',',X ]
     ;   (   Result = id(Y) % if result is a var, transfer value into X via %eax
          -> Cop = [ '\n\t\t movl ',Y,',%eax',
                     '\n\t\t movl %eax,',X ]
          ;  Result = [Reg|_],      % if result is in Reg, retrieve Reg's name
             member((Reg,RegName),  % and store Reg into X
                    [ (0,'%eax'),(1,'%edx'),(2,'%ecx'),
                      (3,'%ebx'),(4,'%esi'),(5,'%edi')]),!,
             Cop = [ '\n\t\t movl ',RegName,',',X ] ) ),
    append(CE,Cop,Code).

cs((if B then { S1 } else { S2 }), Code,Ain,Aout) :- !,
                            % For if-then-else statement, compile boolean
                            % condition first. Set context to 'stmt', so that
                            % residual code is not used.
    put_assoc(context,Ain,stmt,A1),
    comp_expr(B,CB,A1,A2),
                            % The result is in the flags, and the appropriate
                            % jump instruction must be used to select
    B =.. [Op|_],           % between 'then' and 'else' branches
    (   member((Op,I),[(<,jl),(=<,jle),(==,je),(\=,jne),(>,jg),(>=,jge)])
     -> true
     ;  I = jne ),          % code for 'then' branch appears below code for 'else'
    COpB = [ '\n\t\t ',I,' ',Lthen ],
    cs(S2,C2,A2,A3),        % generate code for 'else', and jump to skip the 'then'
    Cif1 = [ '\n\t\t jmp ',Lifend,
             '\n',Lthen,':' ],
                            % label for 'then' branch is 'Lthen:'
    cs(S1,C1,A3,A4),        % generate code for 'then' branch
    Cif2 = [ '\n',Lifend,':' ],
                            % 'Lifend:' is the label at end of 'if',
                            % target of jump placed after 'else'
    get_assoc(labelsuffix,A4,Kin,Aout,Kout),
    generateLabels([Lthen,Lifend],Kin,Kout),
                            % generate concrete labels for label placeholders
                            % and lay out the code
    append([CB,COpB,C2,Cif1,C1,Cif2],Code).

cs((if B then { S }), Code,Ain,Aout) :- !,
                            % Code for 'if-then', similar to the one above.
    put_assoc(context,Ain,stmt,A1),
    comp_expr(B,CB,A1,A2),
    B =.. [Op|_],           % The condition of the jump must now be negated
    (   member((Op,I),[(<,jge),(=<,jg),(==,jne),(\=,je),(>,jle),(>=,jl)])
     -> true
     ;  I = je ),
    COpB = [ '\n\t\t ',I,' ',Lifend ],
    cs(S,C,A2,A3),
    Cif = [ '\n',Lifend,':' ],
    get_assoc(labelsuffix,A3,Kin,Aout,Kout),
    generateLabels([Lifend],Kin,Kout),
    append([CB,COpB,C,Cif],Code).

cs((while B do { S }), Code,Ain,Aout) :- !,
                            % The while has the body first, and then the condition
                            % 'break' statement are allowed inside, so we must
                            % make sure that we accomodate only breaks issued
                            % from inside this loop's body. For this reason,
                            % previous 'break' labels will be saved here, and
                            % restored before returning.
    get_assoc(break,Ain,OrigBreak,A0,none),
                            % The local 'break' attribute currently set to 'none'.
                            % Will be checked again after generating code for the
                            % body. If 'break' attribute is changed, we are sure
                            % it comes from inside this loop's body.
    Cw1 = [ '\n\t\t jmp ',LCond ,
            '\n',LTop,':' ],
                            % Jump to while condition; generate label for looping
    cs(S,C,A0,A1),          % Then generate code for body
    Cw2 = [ '\n',LCond,':' ],
                            % Generate label 'LCond:' for bool condition
    put_assoc(context,A1,stmt,A2),
                            % Generate code for boolean condition, in
                            % 'stmt' context so that residual code is not used.
    comp_expr(B,CB,A2,A3),  % Results will be in the flags
    B =.. [Op|_],           % Appropriate conditional jump must be selected
    (   member((Op,I),[(<,jl),(=<,jle),(==,je),(\=,jne),(>,jg),(>=,jge)])
     -> true
     ;  I = jne ),
    COpB = [ '\n\t\t ',I,' ',LTop ], % Generate code for conditional jump
                                     % that repeats the loop. Loop is exited if
                                     % conditional jump not taken.
    get_assoc(labelsuffix,A3,Kin,A4,Kout),
    generateLabels([LTop,LCond],Kin,Kout),
                                     % Generate concrete label names
    get_assoc(break,A4,Break,Aout,OrigBreak),
                                     % If 'break' was encountered in the body,
                                     % then generate 'break' target outside
                                     % while loop. Also restore the original
                                     % break label, so that any enclosing 'while'
                                     % loop may have its own 'break' handled
                                     % correctly.
    ( Break = none -> Cbreak = [] ; Cbreak = ['\n',Break,':'] ),
                                     % Lay out the entire code.
    append([Cw1,C,Cw2,CB,COpB,Cbreak],Code).

cs((N::{S} ; Rest),Code,Ain,Aout) :- !,
    get_assoc(case_table_labels,Ain,(VL,LL),A1,([N|VL],[L|LL])),
    Ccase1 = [ '\n',L,':' ],
    cs(S,CS,A1,A2),
    get_assoc(label_case_end,A2,Lend),
    Ccase2 = [ '\n\t\t jmp ',Lend ],
    cs(Rest,CodeRest,A2,Aout),
    append([Ccase1,CS,Ccase2,CodeRest], Code).

cs((default::{S}),Code,Ain,Aout) :- !,
    get_assoc(case_table_labels,Ain,(VL,LL),A1,([default|VL],[L|LL])),
    Ccase1 = [ '\n',L,':' ],
    cs(S,CS,A1,Aout),
    append([Ccase1,CS], Code).

cs(switch E of { CaseList },Code,Ain,Aout) :-
    get_assoc(label_case_end,Ain,OldCaseLabel,A0,Lcaseend),
    get_assoc(case_table_labels,A0,OldCaseTableLabels,A1,([],[])),
    put_assoc(context,A1,expr,A2),
    comp_expr(E,CE,A2,A3),
    get_assoc(expr_result,A3,RE),
    (    RE = [Reg|_]
     ->  Cop = [],
         member((Reg,X),
                [ (0,'%eax'),(1,'%edx'),(2,'%ecx'),
                  (3,'%ebx'),(4,'%esi'),(5,'%edi')]),!
     ;   (   RE = id(Y) ; RE = const(Tmp), atomic_concat('$',Tmp,Y) ),!,
         Cop = [ '\n\t\t movl ',Y,',%eax' ], X = '%eax' ),
    CJ = [ '\n\t\t jmp * ',Lcasetab,'(,',X,',4)',
           '\n',Lcasetab,':' ],
    get_assoc(labelsuffix,A3,Lin,A4,Lout),
    generateLabels([Lcasetab,Lcaseend],Lin,Lout),
    cs(CaseList,CC,A4,A5),
    casetable(CodeCaseTab,A5,A6),
    CodeEnd = [ '\n',Lcaseend,':' ],
    put_assoc(label_case_end,A6,OldCaseLabel,A7),
    put_assoc(case_table_labels,A7,OldCaseTableLabels,Aout),
    append([CE,Cop,CJ,CodeCaseTab,CC,CodeEnd],Code).

cs((S1;S2),Code,Ain,Aout) :- !, % statement sequence
    cs(S1,C1,Ain,Aaux),         % append generated code, thread attributes
    cs(S2,C2,Aaux,Aout),
    append(C1,C2,Code).

cs((S;),Code,Ain,Aout) :- !, % statement terminated by semicolon
    cs(S,Code,Ain,Aout).     % compile S without semicolon

cs({S},Code,Ain,Aout) :- !, % statement enclosed in braces
    cs(S,Code,Ain,Aout).    % compile S without braces

casetable(Code,Ain,Aout) :-
    get_assoc(case_table_labels,Ain,(CTV,CTL),A1,none),
    get_assoc(labelsuffix,A1,Lin,Aout,Lout),
    generateLabels(CTL,Lin,Lout),
    CTV = [default|CTVT], CTL = [DefaultLabel|CTLT],
    reverse(CTVT,VR), reverse(CTLT,LR),
    casetable_helper(VR,LR,CodeL,0,DefaultLabel),
    append(CodeL,Code).

casetable_helper([],[],[],256,_) :- !.
casetable_helper([],[],[C|CT],N,DL) :-
    N < 256, !,
    C = [ '\n\t\t .long ',DL ],
    N1 #= N+1,
    casetable_helper([],[],CT,N1,DL).
casetable_helper([VH|VT],[LH|LT],[CH|CT],N,DL) :-
    N < VH, !,
    CH = [ '\n\t\t .long ',DL ],
    N1 #= N+1,
    casetable_helper([VH|VT],[LH|LT],CT,N1,DL).
casetable_helper([N|VT],[LH|LT],[CH|CT],N,DL) :-
    CH = [ '\n\t\t .long ',LH ],
    N1 #= N+1,
    casetable_helper(VT,LT,CT,N1,DL).

% Main predicate
%  1st arg : Program to be compiled
%  2nd arg : File for output
% The generated file has to be compiled together with runtime-stmt.c
% to produce a valid executable. Should work on Linux, Mac, and Cygwin.
compile(P,File) :-
	tell(File),                              % open output file
	empty_assoc(Empty),                      % initialize attribute dict
    put_assoc(break,Empty,none,A0),
    put_assoc(label_case_end,A0,none,A1),
    put_assoc(case_table_labels,A1,([],[]),A2),
	put_assoc(labelsuffix,A2,0,A3),          % add initial label counter
	put_assoc(vars,A3,[],A4),                % add initial list of vars
	cs(P,Code,A4,A5),!,                      % Compile program P into Code
	                                         %  -- Code is now a list of atoms
                                             %     that must be concatenated to get
                                             %     something printable
	Pre = [ '\n\t\t .text',                  % Sandwich Code between Pre and Post
		'\n\t\t .globl _entry',              %  -- sets up compiled code as
		'\n_entry:',                         %     procedure 'start' that can be
	        '\n\t\t pushl %ebp',             %     called from runtime.c
		'\n\t\t movl %esp,%ebp'],
	Post = ['\n\t\t movl %ebp,%esp',
		'\n\t\t popl %ebp',
		'\n\t\t ret'],
	append([Pre,Code,Post],All),             % The actual sandwiching happens here
	atomic_list_concat(All,AllWritable),     % Now concat and get writable atom
	writeln(AllWritable),                    % Print it into output file
        get_assoc(vars,A5,VarList),          % Create data declarations for all vars
	allocvars(VarList,VarCode,VarNames,VarPtrs),
	atomic_list_concat(VarCode,WritableVars),
                                             % Write declarations to output file
	write('\n\t\t .data\n\t\t .globl __var_area\n__var_area:\n'),
	write(WritableVars),
	                                         % Create array of strings representing
                                             % variable names, so that vars can
                                             % be printed nicely from the runtime
	atomic_list_concat(VarNames,WritableVarList),
	write('\n\n\t\t .globl __var_name_area\n__var_name_area:\n'),
	write(WritableVarList),
	                                         % Create array of pointers to strings
                                             % so that runtime code doesn't need
                                             % to be changed every time we compile
	atomic_list_concat(VarPtrs,WritableVarPtrs),
	write('\n\n\t\t .globl __var_ptr_area\n__var_ptr_area:\n'),
	write(WritableVarPtrs),
	write('\n\n__end_var_ptr_area:\t .long 0\n'),
	told. % close output file

:- Program = (
     i = 1 ;
     while i < 100 do {
       switch i rem 8 of {
         2:: { c1 = c1 + i } ;
         4:: { c2 = c2 + i/2 } ;
         6:: { c3 = (c3+1)*c3 } ;
         default :: {
             j = 0 ;
             while j < i do {
               switch j of {
                 0 :: { c0 = c0+1  } ;
                 2 :: { c0 = c0 * c0 } ;
                 default :: { c0 = c0 + 2 ; }
               } ;
               j = j + 1
             }
         }
       } ;
       i = i + 1
     }
   ), compile(Program,'test0.s').

:- writeln('Test program "test0.s" generated.').

/* The following is the equivalent C program. It can be run
   so as to check that the output is the same.

   int main() {
     int i = 1, c1=0, c2=0, c3=0, c0 = 0, j = 0 ;
     while (i < 100) {
       switch (i % 8) {
         case 2 : { c1 = c1 + i ; break ; } ;
         case 4 : { c2 = c2 + i/2 ; break ; } ;
         case 6 : { c3 = (c3+1)*c3 ; break ;} ;
         default : {
             j = 0 ;
             while (j < i) {
               switch (j) {
                 case 0 : { c0 = c0+1 ; break ;  } ;
                 case 2 : { c0 = c0 * c0 ; break ;} ;
                 default : { c0 = c0 + 2 ; break ; }
               } ;
               j = j + 1 ;
             }
         }
       } ;
       i = i + 1 ;
     }
     printf("i = %d\n",i);
     printf("j = %d\n",j);
     printf("c0 = %d\n",c0);
     printf("c1 = %d\n",c1);
     printf("c2 = %d\n",c2);
     printf("c3 = %d\n",c3);
  }

*/

/* runtime-stmt.c -- C file that we need to link in to obtain
                     executables from our toy compiler's output

        #include <stdlib.h>
        #include <stdio.h>

        // name of function in the generated code
        int entry() asm("_entry") ;

        // array holding all variable storage
        extern int var_area[] asm("__var_area") ;

        // array holding pointers to variable names
        //   -- variable var_area[i] has name varnameptr[i]
        extern char *varnameptr[] asm("__var_ptr_area");

        int main() {
            int i = 0, result ;

            // call the function and collec its return value
            //  -- eax can be always used to return a value if needed
            result = entry() ;

            // print the result; only significant if eax has been set
            // to return something meaningful
            printf("Result = %d\n",result) ;

            // print all the variables used in the generated code
            while(varnameptr[i] != NULL) {
                printf("%s = %d\n",varnameptr[i],var_area[i]) ;
                i++ ;
            }
        }
*/

/* The following is the test0.s file generated in the test given above.
   It can be compiled on Linux or Mac with:

          gcc -m32 -o test0 test0.s runtime-stmt.c

   And on Cygwin with:

          gcc -m32 -o test0.exe test0.s runtime-stmt.c


		 .text
		 .globl _entry
_entry:
		 pushl %ebp
		 movl %esp,%ebp
		 movl $1,i
		 jmp L14
L13:
		 movl $8,%ecx
		 movl i,%eax
		 movl %eax,%edx
		 shrl $31,%edx
		 idivl %ecx
		 jmp * L0(,%edx,4)
L0:
		 .long L9
		 .long L9
		 .long L12
		 .long L9
		 .long L11
		 .long L9
		 .long L10
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
		 .long L9
L12:
		 movl c1,%eax
		 addl i,%eax
		 movl %eax,c1
		 jmp L1
L11:
		 movl $2,%ecx
		 movl i,%eax
		 movl %eax,%edx
		 shrl $31,%edx
		 idivl %ecx
		 addl c2,%eax
		 movl %eax,c2
		 jmp L1
L10:
		 movl c3,%eax
		 addl $1,%eax
		 imull c3,%eax
		 movl %eax,c3
		 jmp L1
L9:
		 movl $0,j
		 jmp L8
L7:
		 movl j,%eax
		 jmp * L2(,%eax,4)
L2:
		 .long L6
		 .long L4
		 .long L5
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
		 .long L4
L6:
		 movl c0,%eax
		 addl $1,%eax
		 movl %eax,c0
		 jmp L3
L5:
		 movl c0,%eax
		 imull c0,%eax
		 movl %eax,c0
		 jmp L3
L4:
		 movl c0,%eax
		 addl $2,%eax
		 movl %eax,c0
L3:
		 movl j,%eax
		 addl $1,%eax
		 movl %eax,j
L8:
		 movl j,%eax
		 cmpl i,%eax
		 jl L7
L1:
		 movl i,%eax
		 addl $1,%eax
		 movl %eax,i
L14:
		 movl i,%eax
		 cmpl $100,%eax
		 jl L13
		 movl %ebp,%esp
		 popl %ebp
		 ret

		 .data
		 .globl __var_area
__var_area:

c1:		 .long 0
c2:		 .long 0
c3:		 .long 0
c0:		 .long 0
j:		 .long 0
i:		 .long 0

		 .globl __var_name_area
__var_name_area:

c1_name:	 .asciz "c1"
c2_name:	 .asciz "c2"
c3_name:	 .asciz "c3"
c0_name:	 .asciz "c0"
j_name:	 .asciz "j"
i_name:	 .asciz "i"

		 .globl __var_ptr_area
__var_ptr_area:

c1_ptr:	 .long c1_name
c2_ptr:	 .long c2_name
c3_ptr:	 .long c3_name
c0_ptr:	 .long c0_name
j_ptr:	 .long j_name
i_ptr:	 .long i_name

__end_var_ptr_area:	 .long 0

*/
