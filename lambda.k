require "substitution.k"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX

/** SYNTAX **
We extend the simply-typed lambda calculus with dependent types
`(forall x : t) s` and a syntax for defining inductive types like nat, bool,
and `vec a n` lists of length `n`.

In dependently typed languages, types are values and values may appear in
types. Hence we put them all in the same syntactic category but distinguish
a special category for neutral terms like identifiers and lambda expressions;
this is useful for defining the semantics below.

Note that the simple function type `a -> b` is shorthand for the dependent
function type `(forall _ : a) b` where `b` does not depend on the value of
the domain.
**/

  /* Regular lambda syntax */

  syntax Val ::= Id
               | "lambda" Id "." Exp           [binder]
               | "type" // The type of types
               | "(" "forall " Id ":" Exp ")" Exp   [binder(1 -> 3)]
               | Exp "->" Exp [right]
               | Val Val [strict, left]  // Netural terms like `vec nat (suc zero)`

  syntax Id ::= "$x"
  rule T1:Exp -> T2:Exp => (forall $x : T1) T2 [macro]

  syntax Exp ::= "(" Exp ")"                   [bracket]
               | Exp Exp                       [strict, left]
               | Val
               | "let" Id "=" Exp "in" Exp
               | Exp ":" Exp
  syntax Exps ::= List{Exp,";"}

  syntax Exp ::= "data" Id ":" Exp "{" Exps "}" Exp

  syntax Exp ::= "match" Exp "with" Bindings
  syntax Binding ::= Exp "=" Exp
  syntax Bindings ::= List{Binding,"|"}

  syntax priorities ___LAMBDA-SYNTAX
                  > _->__LAMBDA-SYNTAX
                  > (forall_:_)__LAMBDA-SYNTAX
                  > _:__LAMBDA-SYNTAX
                  > let_=_in__LAMBDA-SYNTAX
                  > lambda_.__LAMBDA-SYNTAX
                  > data_:_{_}__LAMBDA-SYNTAX

endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION

  syntax KVariable ::= Id
  syntax KResult ::= Val

/** CONFIGURATION **
The configuration is essentially the same as that in simply typed programming.
I added a cell `ctors` that associates types with their constructors; this is
needed to define eliminators for inductive types.
**/

  configuration 
    <T color="yellow">
      <k color="green"> check($PGM:Exp) </k>
      <tenv color="blue"> .Map </tenv>
      <ctors color="purple"> .Map </ctors>
    </T>

/** Some useful stuff **/

  syntax Exp ::= 
      typeCheck(Exp, Exp) // Check that arg2 is the type of arg1
    | check(Exp)          // Check the insides of the expression
    | setTEnv(Map)        // Update the type context
    | getType(Exp)        // Infer the expression's type
    | Map "|-" Exp        // Shorthand for temporarily updating the ctx
    | Exp "==" Exp        [strict]    // Compare expressions by normalizing
    | applyType(Exp, Exp) [strict(1)] // Apply arg2 to dependent fun type arg1

  rule <k> check(let X:Id = M:Exp in N:Exp) 
    => check(N[M/X]) //Gamma[X <- getType(M)] |- check(N)
    ...</k>
       <tenv> Gamma </tenv>

  rule check(data D:Id : T:Exp { Cs:Exps } Etc:Exp) 
    => data D : T { Cs } check(Etc)

  rule check(E:Exp) => getType(E) requires notDecl(E)


  rule <k> G:Map |- E:Exp => E ...</k>
       <tenv> G:Map </tenv>
  rule <k> G':Map |- E:Exp => setTEnv(G') ~> E ~> setTEnv(G)...</k>
       <tenv> G:Map </tenv> [owise]


  // Evaluation semantics for values; needed for normalization
  rule (lambda X:Id . M) N => M[N/X]
  rule E:Exp : T:Exp => E
  rule let X:Id = E1:Exp in E2:Exp => E2[E1/X]


/** NORMALIZATION **
Typechecking a dependently typed program requires normalization, for example to
see that `vec nat (1 + 1)` meets the spec for `vec nat 2`. Lambda expressions
and dependent types are compared up to alpha-equivalence and values are
compared syntactically. Since `_==_` is strict in both its arguments,
substitution may take place during checking.
**/

  // Alpha-equivalence checking is done by substituting the same variable
  rule (lambda X:Id . M) == (lambda Y:Id . N) 
    => M == (N[X/Y])

  rule ((forall X:Id : A:Exp) B:Exp) == ((forall Y:Id : A':Exp) B':Exp)
    => (A == A') ~> (B == (B'[X/Y]))

  rule X:Id == X:Id => .  // It's slightly better for dbugging to keep failures stuck
  rule type == type => .
  rule V:Val == V => .


/** TYPE INFERENCE **
Type inference is defined for every syntactic expression except lambda because
the most general type of a lambda expression is undecidable.  We expect the
programmer to supply an annotation for each lambda expression, so that getting
the type amounts to checking it against the annotation.

Notice that in a dependently typed language, all expressions (even types like
int, bool, and type) have a type. The type of a type is usually called a
"kind".

The key differences here from a simply typed language are:
- Checking that a dependent function type `(x : a) -> b` is well-formed
  requires assuming `x : a` and checking that `b` is well-formed. This is
  because `b` may contain `x` inside it.
- Getting the type of an application requires evaluation at compile time!
  Since the codomain of `(x : a) -> b` depends on the argument, we
  substitute `N` for `x` in `b`. But we won't evaluate it until the type 
  checking phase...
**/

  rule getType(type) => type

  // Check annotation
  rule getType(E:Exp : T:Exp)
    => typeCheck(T, type) 
    ~> typeCheck(E, T) 
    ~> T

  // Lookup
  rule <k> getType(X:Id) => T:Exp ...</k> <tenv>... X |-> T ...</tenv>

  // Well-formedness
  rule <k> getType((forall X:Id : A:Exp) B:Exp) 
     => Gamma         |- typeCheck(A, type)
     ~> Gamma[X <- A] |- typeCheck(B, type)
     ~> type 
    ...</k> 
       <tenv> Gamma </tenv>

  // Dependent function application
  rule getType(M:Exp N:Exp) => applyType(getType(M), N)
  rule applyType((forall X:Id : A:Exp) B:Exp, N:Exp) => typeCheck(N, A) ~> B[N/X]


/** TYPE CHECKING **
Here's the important bit!

Typechecking a lambda expression `lambda x . M` is just like the simply typed
case, except that we do alpha-renaming to make sure that the `x` in the
expression is the same as the `x` in the type of `M`.

The real power of dependent types is that we can normalize types to compare
them. Hence if `Vec a n` is the type of arrays of length `n` containing
elements of type `a`, we can check that `Vec a (1+1)` satisfies the
specification `Vec a 2`.

For example, suppose we have the concatenation function

  _::_ : (n : int) -> (m : int) -> Vec a n -> Vec a m -> Vec a (n + m)

Then we can typecheck

  let xs = [1]    : Vec int 1
      ys = [2, 3] : Vec int 2
  in (xs :: ys)   : Vec int 3  // Or even `Vec (if true then int else bool) (5 - 2)`

**/


  rule <k> typeCheck(lambda X:Id . E:Exp, (forall Y:Id : A:Exp) B:Exp) => 
           Gamma[X <- A] |- typeCheck(E, B[X/Y]) // Alpha-renaming
       ...</k> 
       <tenv> Gamma </tenv>

  rule <k> typeCheck(let X:Id = M:Exp in N:Exp, B:Exp) 
        => typeCheck(N[M/X], B)
       ...</k> 
       <tenv> Gamma:Map </tenv>

  // Key rule: we can typecheck by inferring a type and then normalizing both
  rule typeCheck(E:Exp, T:Exp) => getType(E) == T
    requires notBool isLambda(E)


/** INDUCTIVE TYPES **
We won't check things like strict positivity and ensuring that constructors do
not reference other constructors, all of which may cause non-termination. The
point is to get some basic dependently typed code working.

The programmer should ensure that data declarations always produce `type` and
that constructors only produce fully instantiated instances of that data. E.g.
a constructor should produce `Vec A n` rather than `Vec A`.
**/
  syntax Exp ::= declareCtors(Id, Exps)

  rule <k> data D:Id : T:Exp { Cs:Exps } Etc:Exp
    => typeCheck(T, type)
    ~> setTEnv(Gamma[D <- T])
    ~> declareCtors(D, Cs)
    ~> Etc
       ...</k> 
       <tenv> Gamma </tenv>
       <ctors> Ctors => Ctors[D <- .List] </ctors>

  rule <k> declareCtors( D:Id, (C:Id : T:Exp) ; More:Exps )
    => typeCheck(T, type)
    ~> setTEnv(Gamma[C <- T])
    ~> declareCtors( D, More )
       ...</k> 
       <tenv> Gamma </tenv>
       <ctors>... D |-> _:List (.List => ListItem(C)) ...</ctors>

  rule declareCtors(_, .Exps) => .


/** ETC **/

  syntax Bool ::= isLambda(Exp) [function]
                | notDecl(Exp) [function]
                | checkProduces(Exp, Exp) [function]
  rule isLambda(lambda X:Id . E:Exp) => true
  rule isLambda(let X:Id = M:Exp in N:Exp) => true
  rule isLambda(E:Exp) => false [owise]
 
  rule notDecl(let _ = _ in _) => false
  rule notDecl(data _ : _ { _ } _) => false
  rule notDecl(_:Exp) => true [owise]

  rule <k> setTEnv(G) => . ... </k> <tenv> _ => G </tenv>
endmodule
