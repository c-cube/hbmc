

%\documentclass{sigplanconf}
\documentclass{llncs}
%include polycode.fmt

% The following \documentclass options may be useful:

% preprint      Remove this option only once the paper is in final form.
% 10pt          To set in 10-point type instead of 9-point.
% 11pt          To set in 11-point type instead of 9-point.
% authoryear    To obtain author/year citation style instead of numeric.

\usepackage{tikz}
\usepackage{pgfplots}
\usepackage{pgfplotstable}
\usepackage{amsmath}
\usepackage{xcolor}
\usepackage{graphicx}
\usepackage{textcomp}
\usepackage{verbatim}
\usepackage[final]{microtype}
\usepackage{url}

\newcommand{\hbmc}[0]{\textsc{hbmc}}
\newcommand{\comm}[1]{\marginpar{\footnotesize #1}}
\newcommand{\ifthenelse}{|if|-|then|-|else|}
%format § = $
%format noot = "not"

\begin{document}

%%sigplan
%\special{papersize=8.5in,11in}
%\setlength{\pdfpageheight}{\paperheight}
%\setlength{\pdfpagewidth}{\paperwidth}
%
%\conferenceinfo{ICFP '15}{September, 2015, Vancouver, Canada}
%\copyrightyear{2015}
%\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
%\doi{nnnnnnn.nnnnnnn}
%
%% Uncomment one of the following two, if you are not going for the
%% traditional copyright transfer agreement.
%
%\exclusivelicense                % ACM gets exclusive license to publish,
%                                 % you retain copyright
%
%\permissiontopublish             % ACM gets nonexclusive license to publish
%                                 % (paid open-access papers,
%                                 % short abstracts)
%
%\titlebanner{DRAFT}        % These are ignored unless
%\preprintfooter{}   % 'preprint' option specified.

\title{SAT-based Bounded Model Checking\\for Functional Programs}
\titlerunning{DRAFT SAT-based Bounded Model Checking\\for Functional Programs}

\author{Koen Claessen \and Dan Ros{\'e}n}
%
\authorrunning{Koen Claessen et al.}

\institute{Department of Computer Science and Engineering, Chalmers University of Technology
\email{\{koen,danr\}@@chalmers.se}
}

\maketitle

\begin{abstract}
We present a new symbolic evaluation method for functional programs that generates input to a SAT-solver. The result is a Bounded Model Checking (BMC) method for functional programs that can find concrete inputs that cause the program to produce certain outputs, or show the inexistence of such inputs under certain bounds. SAT-solvers have long been used for BMC on hardware and low-level software. This paper presents the first method for SAT-based BMC for high-level programs containing algebraic datatypes and unlimited recursion. Our method works {\em incrementally}, i.e. it increases bounds on inputs until it finds a solution. We also present a novel optimization, namely {\em function call merging}, that can greatly reduce the complexity of symbolic evaluation for recursive functions over datatypes with multiple recursive constructors.
\end{abstract}

\keywords
bounded model checking, SAT, symbolic evaluation

% ------------------------------------------------------------------------------

\section{Introduction}

At the end of the 1990s, SAT-based Bounded Model Checking (BMC \cite{bmc}) was
introduced as an alternative to BDD-based (Binary Decision Diagrams) hardware model checking. BMC
revolutionized the field; SAT-solvers by means of BMC provided a scalable and
efficient search method for finding bugs. A BMC tool enumerates a depth
bound~$d$, starting from 0 upwards, and tries to find a counter example of
length~$d$, using a SAT-solver. Deep bug finding was one thing BDD-based
methods were not good at. Since then, BMC techniques have also found their way
into software model checkers. One example is the C model checker CBMC
\cite{cbmc}. BMC techniques work well for software that is low-level (reasoning
about bits, words, and arrays), and not well at all for software with
higher-level features (pointers, recursive datastructures).

Our aim in this paper is to take the first step towards bringing the power of
SAT-based BMC to a high-level functional programming language, with algebraic
datatypes and recursion. We built a tool dubbed \hbmc{}, for the Haskell Bounded Model Checker,
which \hbmc{} works by taking an
existentially quantified formula, and it tries to prove
it by finding an assignment of concrete values that makes it hold.
This makes it possible to use \hbmc{} for synthesis of desired
values, such as finding solutions to search problems, inverses
to functions, solutions to puzzles and finding test data
that satisfies certain constraints.
Naturally, this can also be used for property testing:
trying to falsify a universally quantified conjecture.
An assigment is then a counterexample
to why the property does not hold. Applications of this is
to find errors in programs (or in the specifications!).

We built \hbmc{} on top of only a SAT solver. \comm{comment on why only sat}
No SMT-techniques, such as uninterpreted functions or data
types, were used. However, it is easy to change the SAT solver that is used
in this article to leverage other useful theories from SMT such as
integer linear arithmetic or bit vectors. In this work we focus solely
on how to represent algebraic datatypes, and we encode them propositionally.

From a high-level perspective, \hbmc{} evaluates the program symbolically,
and the symbolic constraints are encoded into a propositional formula
that is sent to a SAT-solver. By representing expandable input data,
\hbmc{} first starts out by assuming that none of the input is going to
be used. Unless the property is trivial, the solver will report that there
is no counter-example, but by examining the conflict clause (also known
as the unsatisfiable core), it will give a suggestion on which part of
the input that needs to be expanded. Now, we will search for an assigment
in this larger search space, and the process continues until we find
a counterexample, or in some cases that we highlight later, the unsatisfiable
core will be empty and thus no counterexample exists.

There exist alternatives to using a SAT-solver to find assigments and
counterexample. For example,
QuickCheck \cite{quickcheck} is a tool for random property-based testing that
has been shown to be quite effective at finding bugs in programs. However, to
find intricate bugs, often a lot of work has to be spent on test data
generators, and a lot of insight is required. A dedicated search procedure
could alleviate some of that work. Also, random testing would not work at all
for finding solutions to search problems, or inverting a function.

%format ==> = "\Longrightarrow"

%format :-> = ":\rightarrow"

To make things more concrete, we will look at a small example,
namely a type-checker for simply typed lambda calculus.
The function |tc| takes an environment |env|, an expression |e| where
variables refer to types in the environment by de Bruijn-indicies
and where the application constructor has the cut type explicitly specified,
and a type |t|, and returns whether or not |e| has the type |e| in the |env|:

> tc :: [Type] -> Expr -> Type -> Bool
> tc  env  (App f x tx)  t           = tc env f (tx :-> t) && tc env x tx
> tc  env  (Lam e)       (tx :-> t)  = tc (tx:env) e t
> tc  env  (Lam e)       _           = False
> tc  env  (Var x)       t           =  case env `atIndex` x of
>                                         Just tx  -> tx == t
>                                         Nothing  -> False

As an example of \hbmc{} finding an assignment, we write a top level declaration,
|compose|, which asks for an expression |e| that has the type of function composition
in the empty environment:

> compose e = question (tc [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)))

(the datatype for types contains the three base types |A|, |B| and |C|).
Now, we can run \hbmc{} on this, which in half a second reports:

\begin{verbatim}
e: Lam (Lam (Lam (App (Var (S (S Z))) (App (Var (S Z)) (Var Z) A) B)))
\end{verbatim}

Which is the representation of |(\ f g x -> f (g x))|, as expected.
The same property can be written as a QuickCheck, by replacing
|question| with |noot|: saying that for all expressions |e|, they do not
have the type of function composition.
But it would be very hard to find this value by random testing.
The situation could be improved upon by writing a custom generator that always
generates well-typed data, but this is not such an attractive option
as it is a difficult problem in itself \cite{PalkaLambdaTerms2011}.

There already exist dedicated search procedures for inputs that lead to certain
\comm{Should we refer to smten here too?}
outputs. Most notably, there are a number of tools (such as Reach \cite{reach},
Lazy SmallCheck \cite{lazysc}, and Agsy \cite{agsy}) that employ a backtracking
technique called {\em lazy narrowing} to search for inputs. These tools are
much better than random testing at finding intricate inputs, but they rely
on laziness to be able to abort unfruitful computations early.
but they have one
big shortcoming: they employ a depth-limitation on the input. In order to use
these tools, a maximum search depth has to be specified (or the tool itself can
enumerate larger and larger depths). Increasing the maximum depth of a set of
terms affects the size of the search space exponentially. For example, Lazy
SmallCheck times out for instances of the type-checking example |compose| when the depth gets
larger than 5, because there are just too many cases to check.
The |tc| predicate is just too strict
(even when as many parallell connectives as possible are used), and the
counterexample is at a too big depth to be able to be found by this techinque.

This paper contains the following contributions:

\begin{itemize}
\item We show how to express values of arbitrary datatypes symbolically in a SAT-solver.
      (Section X)

\item Furthermore, these datatypes are ``expandable'', allowing the system to be run
      without a depth or size restriction (Section X)

\item We show how to use the conflict clause of the SAT-solver to choose an unevaluated
      point in the program to expand (Section X)

\item We describe how we can handle non-terminating programs (Section X)

\item We present how memoization helps in this setting and how it can be used
      to do ``non-local'' reasoning (Section X)

\item We show a new techinque how to merge function calls to remove
      exponential blowup that can happen in symbolic evaluation (Section X)

\item We present a thorough evaluation with other techniques.
      This also includes a new tool that instruments a program with
      parallell boolean connectives to be used with LazySmallCheck (Section X)

\item \textbf{Old list of contributions:}

\item We present a monadic DSL for constraint generation that can be used
to program with a SAT-solver. (Section 3)

\item We show how to express values of arbitrary datatypes symbolically in a SAT-solver. (Section 3)

\item We show programs containing recursive functions over datatypes can be symbolically executed, resulting in a SAT-problem. (Section 4)

\item We show how we can battle certain kinds of exponential blow-up that naturally happen in symbolic evaluation, by means of memoization and a novel program transformation. (Section 4)

\item We show to perform bounded model checking {\em incrementally} for growing input sizes, by making use of feedback from the SAT-solver. (Section 5)
\end{itemize}
We also show a number of different examples, and experimental evaluations on these examples (Section \ref{examples}).
\comm{We could also expand the introduction and have examples here, and then refer back to them
in the evaluation section}

The tool is available at \url{http://github.com/danr/hbmc},
and available on hackage and thus installable with \verb!cabal install hbmc!.

% ------------------------------------------------------------------------------

%\begin{comment}
\section{Symbolic datatypes}
\label{ite}

This section gives some background and motivation to the techniques we use later in the paper,
by introducing symbolic values and approaches how to do if-then-else on them.

The programming language FL, part of the formal verification system Forte \cite{forte} is an ML-like language with one particular distinguishing feature: symbolic booleans. FL has a primitive function with the following type%\footnote{Throughout the paper, we use Haskell notation for our examples, even though the examples may not actually be written in the Haskell language.}:
\begin{code}
var :: String -> Bool
\end{code}
The idea behind |var| is that it creates a symbolic boolean value with the given name. It is possible to use the normal boolean operators (|(&&)|, |(not)|, |(==)|, etc.) on these symbolic booleans, and the result is then computed as a normalized boolean formula in terms of the variables created by |var|. The implementation of FL uses BDDs \cite{bdd} for this.

%format BoolSym = "\mathit{Bool}^\dagger"
What happens when we use \ifthenelse{} with these symbolic booleans to choose between, for example, two given lists? This is unfortunately disallowed in FL, and leads to a run-time error. The Haskell library Duck Logic \cite{duck-logic} provided a similar feature to FL, but used the type system to avoid mixing symbolic booleans with regular Haskell values, by making symbolic booleans |BoolSym| a different type from regular |Bool|.

This paper aims to lift this restriction, and allow for all values in the program to be symbolic.
The problem presented by an expression such as:
\begin{code}
if var "a" then [1] else []
\end{code}
is that at symbolic evaluation time, we cannot decide which constructor to return. One of our main ideas in this paper is to transform algebraic datatypes with several constructors, for example:
\begin{code}
data List a = Nil | Cons a (List a)
\end{code}
into a algebraic datatype with only one constructor which is the ``superposition state'' of all possible constructors, that contains enough symbolic boolean variables to decide which constructor we actually have, plus a ``superposition'' of all possible arguments. Here is what we could do for lists:
%format ListSym = "\mathit{List}^\dagger"
%format FalseSym = "\mathit{false}^\dagger"
%format TrueSym = "\mathit{true}^\dagger"
\begin{code}
data ListSym a = NilCons BoolSym (Maybe (a, ListSym a))

nil :: ListSym a
nil = NilCons FalseSym Nothing

cons :: a -> ListSym a -> ListSym a
cons x xs = NilCons TrueSym (Just (x, xs))
\end{code}
Here, |Maybe| is the regular Haskell datatype, not the symbolic datatype. A symbolic list is thus always built using the |NilCons| constructor. The first argument (a symbolic bool) indicates which constructor we are using (|FalseSym| for |Nil|, |TrueSym| for |Cons|), and the second argument contains the arguments to the |Cons| constructor (which are only used in the case when we actually have a |Cons| constructor).

An extra datatype invariant has to be respected. For |ListSym| it is that whenever it is possible for the constructor to be |True|, the second argument cannot be |Nothing|.

What have we gained from this? It is now possible to implement \ifthenelse{} on lists, in terms of \ifthenelse{} on symbolic booleans and list elements. Here is the implementation:
%format c1
%format c2
%format ma1
%format ma2
\begin{code}
if b then NilCons c1 ma1 else NilCons c2 ma2 =
  NilCons  (if b then c1   else c2)
           (if b then ma1  else ma2)
\end{code}
We also need \ifthenelse{} on the regular |Maybe| type, which in a symbolic setting is only used to indicate the presence or absence of constructor arguments:
%format a1
%format a2
\begin{code}
if b then Nothing  else ma2      = ma2
if b then ma1      else Nothing  = ma1
if b then Just a1  else Just a2  =
  Just (if b then a1 else a2)
\end{code}
If one branch does not have arguments, we choose the other side. If both branches have arguments, we choose between them.

How can we do |case|-expressions on these symbolic lists? It turns out having \ifthenelse{} on the result type is enough. If we have a |case|-expression:
\begin{code}
case xs of
  Nil        -> a
  Cons y ys  -> f (y,ys)
\end{code}
we can translate it to work on symbolic lists as follows:
\begin{code}
let NilCons c ma = xs in
  if c then f (fromJust ma) else a
\end{code}
In this way, the user can use boolean variables to create a symbolic input to a program, for example representing all lists up to a particular length, containing elements up to a particular size, and run the program. The output will be another symbolic expression, about which we can ask questions. For example, if we want to do property checking, the output will be a symbolic boolean, and we can ask if it can ever be |FalseSym|.

In the remainder of the paper we will use the main idea described in this section, with a number of changes. Firstly, we are going to use a SAT-solver instead of BDDs. Also, we want to create inputs to the program {\em incrementally}, without deciding up-front how large the inputs should be.
For these reasons, we move from an {\em expression-based} view (using \ifthenelse{}) to a {\em constraint-based} view.

% ------------------------------------------------------------------------------

%\end{comment}
\section{A DSL for generating constraints}
\label{dsl}

In this section, we present a small DSL, the constraint monad, that we will use later for generating constraints to a SAT-solver. We also show, by means of examples, how it can be used to encode algebraic datatypes symbolically.
\comm{
Reviewer:
The notion of the constraint monad appears inside both (and also in Kuncak
et. al's Comfusys, a precursor to the LEON work).
}

\subsection{The Constraint monad}

We start by explaining the API of the monad we use to generate constraints. We make use of an abstract type |Prop|, that represents propositional logic formulas. (The type |Prop| plays the same role as the type |BoolSym| above.)
%format /\ = "\wedge"
%format \/ = "\vee"
%format ==> = "\Rightarrow"
%format <=> = "\Leftrightarrow"
%format nt = "\neg"
\begin{code}
type Prop

(/\), (\/), (==>), (<=>)  :: Prop -> Prop -> Prop
(nt)                      :: Prop -> Prop
true, false               :: Prop
\end{code}
Note however that there is no way to create a variable with a given name of type |Prop|. Variable creation happens inside the constraints generating monad |C|, using the function |newVar|:
\begin{code}
type C a
instance Monad C  -- defines |return :: a -> C a|,
                  -- |(>>) :: C a -> C a -> C a|, and
                  -- |(>>=) :: C a -> (a -> C b) -> C b|.

newVar  :: C Prop
insist  :: Prop -> C ()
when    :: Prop -> C () -> C ()
\end{code}
We can use the function |insist| to state that a given proposition has to hold. In this way, we generate constraints.
On its own, |insist| enjoys a few laws:
%format === = "\Longleftrightarrow"
\begin{code}
insist true        === return ()
insist false >> m  === insist false
m >> insist false  === insist false
\end{code}
These are logical equivalences, i.e.\ the expressions on the left and right hand side may generate syntactically different sets of constraints, but they are logically equivalent.

The function |when| provides a way of keeping track of local assumptions. The expression |when a m| generates all constraints that are generated by |m|, but they will only hold conditionally under |a|.
The following logical equivalences hold for |when|:
\begin{code}
when a (insist b)     ===  insist (a ==> b)
when false m          ===  return ()
when a (when b m)     ===  when (a /\ b) m
when a m >> when b m  ===  when (a \/ b) m
when a m >> when a n  ===  when a (m >> n)
\end{code}

|C| can be thought of as a reader monad in the environment condition (hereafter called the {\em context}), a writer monad in the constraints, and a state monad in variable identifiers. In reality, it is implemented on top of a SAT-solver (in our case, we are using MiniSat \cite{minisat}). The function |newVar| simply creates a new variable in the solver, |insist| generates clauses from a given proposition and the environment condition, and |when| conjoins its proposition argument with the current environment condition to generate the environment for its second argument.

\subsection{Finite choice}

In order to help us define the translation from algebraic datatypes to monadic constraint generating code, we introduce the following abstraction. The type |Fin a| represents a symbolic choice between finitely many concrete values of type |a|.
\begin{code}
newtype Fin a = Fin [(Prop,a)]

newFin :: Eq a => [a] -> C (Fin a)
newFin xs = do  ps <- sequence [ newVal | x <- nub xs ]
                insist (exactlyOne ps)
                return (Fin (ps `zip` nub xs))

one :: a -> Fin a
one x = Fin [(true,x)]

is :: Eq a => Fin a -> a -> Prop
Fin pxs `is` x = head ([p | (p,y) <- pxs, x == y] ++ [false])
\end{code}
The function |newFin| creates a suitable number of new variables, uses a proposition function |exactlyOne| that creates a formula expressing that exactly one of its arguments is true, and returns |Fin a| value which relates the values from |xs| to the corresponding propositional variables. The function |one| creates a |Fin a| with only one option. The function |is| selects the proposition belonging to the given value.

\subsection{Incrementality}

\comm{Really need to show the solve-loop, too!!}
Before we show the symbolic encoding of datatypes in the constraint generation setting, we need to introduce one more auxiliary type. Since we are going to create symbolic inputs to programs {\em incrementally}, i.e.\ without knowing on beforehand how large they should be, we introduce the type |Delay|\footnote{As we shall see in Section \ref{sec:solving}, the story is slightly more complicated than this, but we present a simplified version here for presentation purposes.}.
\begin{code}
type Delay a

delay  :: C a -> C (Delay a)
done   :: a -> Delay a
force  :: Delay a -> C a
wait   :: Delay a -> (a -> C ()) -> C ()
\end{code}
Using the function |delay|, we can created a delayed computation of type |Delay a|, which will be executed at most once. For convenience, the function |done| also creates a delayed computation, but one which is already done.
Using |force|, we can make a delayed computation happen. Using |wait|, we can make code wait for a delayed computation to happen, and react to it by executing its second argument.

The way |Delay| is implemented is the standard way lazy thunks are implemented in an imperative setting, using |IORef|s, as follows:
\begin{code}
data Delay a  =  Done a
              |  Delay (IORef (Either (C ()) a))
\end{code}
A |Delay| is either an already evaluated value, or a mutable reference filled with either a constraint generator that, when run, will fill the reference with a value, or a value.

In order to use references in the |C|-monad, we lift the standard |IORef| functions into the |C|-monad:
\begin{code}
newRef    :: a -> C (IORef a)
readRef   :: IORef a -> C a
writeRef  :: IORef a -> a -> C ()
\end{code}
In Section \ref{sec:input}, a more detailed implementation of |Delay|s is given. In the next subsection, we will see how |Delay| is used.

\subsection{Symbolic datatypes}

In the previous section, we saw how we could make an algebraic datatype symbolic by creating one constructor that is the ``superposition'' of all constructors, with arguments (1) a symbolic value indicating which constructor we have, and (2) the union of all possible arguments to the constructors.

In this subsection, we show how to do this in our constraint-based setting, by example, and using a different datatype, namely of arithmetic expressions:
\begin{code}
data Expr a  =  Var a
             |  Add (Expr a) (Expr a)
             |  Mul (Expr a) (Expr a)
             |  Neg (Expr a)
\end{code}
The first thing we need to do to create a symbolic version of this datatype
is to make a new datatype representing the choice of constructors:
\begin{code}
data ExprL = Var | Add | Mul | Neg deriving ( Eq )
\end{code}
The second thing we do is to merge all constructor arguments into one symbolic constructor:
%format ExprSym = "\mathit{Expr}^\dagger"
\begin{code}
data Arg a    = X | An a

data ExprC s  = Expr (Fin ExprL)  (Arg a)
                                  (Arg (ExprSym a))
                                  (Arg (ExprSym a))
\end{code}
The new constructor |Expr| has one argument of type |Fin ExprL| that indicates (symbolically) which constructor we are using. The other arguments are the (multi-set) union of all arguments that are used by any of the original constructors. We use the type |Arg|, which is isomorphic to the Haskell |Maybe| type to indicate that some arguments may not always be present.
In the merged constructor |Expr|, we reuse argument positions as much as possible; for example the first arguments of |Add|, |Mul|, and |Minus| are all represented by one argument of the symbolic |Expr| constructor.

We are enforcing a datatype invariant that guarantees that an |Arg| argument is not |X| when it is possible that the constructor has the corresponding argument.

Finally, we define the actual type of symbolic expressions, by using the |Delay| type:
\begin{code}
type ExprSym a = Delay (ExprC a)
\end{code}
A symbolic expression is thus an object that can potentially create a choice of constructors, plus the choice of arguments, which in turn can be symbolic expressions again.

All recursive types have to use the |Delay| constructor, because in general we cannot know in advance what the size is. With |Delay|, we can delay this decision until later, when we see what happens when we evaluate the program.

For convenience, we create the following helper functions that represent the old constructor functions:
\begin{code}
var       :: a -> ExprSym a
add, mul  :: ExprSym a -> ExprSym a -> ExprSym a
neg       :: ExprSym a -> ExprSym a

var x    = done (Expr (one Var) (An a)  X       X)
add a b  = done (Expr (one Add) X       (An a)  (An b))
mul a b  = done (Expr (one Add) X       (An a)  (An b))
neg a    = done (Expr (one Neg) X       (An a)  X)
\end{code}
%format TypeSym = "\mathit{Type}^\dagger"
In general, to make a symbolic version of an algebraic datatype |Type|, we create three new types: |TypeL|, which enumerates all constructor functions from |Type|; |TypeC|, which has one argument of type |Fin TypeL| and moreover the union of all constructor arguments tagged with |Arg|, and |TypeSym|, which is just |Delay TypeC|. Note that this construction also works for mutally recursive datatypes.

We have seen how to construct concrete values in these symbolic datatypes. What is left is to show how to do case analysis on symbolic datatypes, how to construct symbolic values, and how to state equality between them. This is presented in the next two subsections.

\subsection{Case expressions on symbolic datatypes}

In a regular case analysis, three things happen: (1) the scrutinee is evaluated, (2) the constructor is examined to make a choice between branches, and (3) the arguments of the constructor are bound in the correct branch.

On symbolic datatypes, we split case analysis in three parts as well. However, our case analysis is {\em passive}; it does not demand any evaluation, instead it will wait until another part of the program defines the scrutinee, and then generate constraints.

To examine which constructor we have, we introduce the following helper functions:
\begin{code}
isVar, isAdd, isMul, isNeg :: ExprC a -> Prop
isVar  (Expr c _ _ _)  = c `is` Var
isAdd  (Expr c _ _ _)  = c `is` Add
isMul  (Expr c _ _ _)  = c `is` Mul
isNeg  (Expr c _ _ _)  = c `is` Neg
\end{code}
And to project out relevant arguments, we use the following projection functions:
%format sel1
%format sel2
%format sel3
\begin{code}
sel1 :: ExprC a -> a
sel2 :: ExprC a -> ExprSym a
sel3 :: ExprC a -> ExprSym a

sel1 (Expr _ (An x) _ _)  = x
sel2 (Expr _ _ (An a) _)  = a
sel3 (Expr _ _ _ (An b))  = b
\end{code}
Note that the $\mathit{sel}_i$ functions are partial; we should not use them when the corresponding arguments do not exist.
Now, to express a case expression of the following form on a symbolic datatype:
%format P1
%format P2
%format P3
%format P4
%format //- = "\!"
\begin{code}
case e of
  Var x    -> P1//-[x]
  Add a b  -> P2//-[a,b]
  Mul a b  -> P3//-[a,b]
  Neg a    -> P4//-[a]
\end{code}
We write the following:
\begin{code}
wait e § \ec ->
  do  when (isVar ec)  §  P1//-[sel1 ec]
      when (isAdd ec)  §  P2//-[sel2 ec,sel3 ec]
      when (isMul ec)  §  P3//-[sel2 ec,sel3 ec]
      when (isNeg ec)  §  P4//-[sel2 ec]
\end{code}
First, we wait for the scrutinee to be defined, then we generate 4 sets of constraints, one for each constructor.

\subsection{Creating symbolic values}

We have seen how we can create concrete symbolic values (using |var|, |add|, |mul|, and |neg|), but not how to create values with symbolic variables in them.

Creating these kinds of values turns out to be so useful that we introduce a type class for them:
\begin{code}
class Symbolic a where
  new :: C a
\end{code}
Here are some instances of types we have seen before:
\begin{code}
instance Symbolic Prop where
  new = newVal

instance Symbolic a => Symbolic (Arg a) where
  new = An `fmap` new

instance Symbolic a => Symbolic (Delay a) where
  new = delay new
\end{code}
We already know how to generate symbolic |Prop|s. When generating a completely general symbolic |Arg|, it has to exist (it cannot be |X|). Generating a symbolic |Delay| just delays the generation of its contents, which is how we get incrementality. Generating a symbolic tuple means generating symbolic elements.

When we make a new symbolic datatype |TypeSym|, we have to make an instance of |Symbolic| for its constructor type |TypeC|. Here is what it looks like for |ExprC|:
\begin{code}
instance Symbolic a => Symbolic (ExprC a) where
  new =  do  c <- newFin [Var,Add,Mul,Neg]
             liftM3 (Expr c) new new new
\end{code}
With the instance above, we also have |new :: C ExprSym| to our disposal.

\subsection{Copying symbolic values} \label{sec:copy}

The last operation on symbolic types we need is {\em copying}. Copying is needed when we want to generate constraints that define a symbolic value |y| in terms of a given value |x|. Copying is also used a lot, and therefore we introduce a type class:
%format >>> = "\rhd"
\begin{code}
class Copy a where
  (>>>) :: a -> a -> C ()
\end{code}
The expression |x >>> y| copies |x| into |y|; it defines |y| as |x| under the current environment condition.

Here are some instances of types we have seen before:
\begin{code}
instance Copy Prop where
  p >>> q = insist (p <=> q)

instance Eq a => Copy (Fin a) where
  Fin pxs >>> v = sequence_
    [ insist (p ==> (v `is` x)) | (p,x) <- pxs ]

instance Copy a => Copy (Delay a) where
  s >>> t = wait s § \x -> do  y <- force t
                               x >>> y
\end{code}
For |Prop|, copying is just logical equivalence. For finite values |Fin a|, we let the propositions in the left argument imply the corresponding propositions in the right argument. This is enough because all propositions in a |Fin a| are mutually exclusive.

For |Delay a|, we wait until |s| gets defined, and as soon as this happens, we make sure |t| is defined (if it wasn't already), and copy the contents of |s| to the contents of |t|.

At this stage, it may be interesting to look at an example of a combination of |new| and |>>>|. Consider the following two |C|-expressions:
%format ¤ = "\phantom"
%format /// = "\;\;\;"
%format quad = "\quad"
%format //  = "\;"
\begin{code}
do  y <- new  ///  ===  /// do x >>> z
    x >>> y
    y >>> z
\end{code}
Both logically mean the same thing, if |y| is not used anywhere else. The left hand side creates a new |y|, copies |x| into |y| and also copies |y| into |z|. The first copy constraint has the effect of always making sure that |y| is logically equivalent to |x| under the current environment condition. As soon as any |Delay| in |x| becomes defined, which may happen after these constraints have been generated, |y| will follow suit. And whenever |y| expands a |Delay|, |z| will follow suit. So the effect of the left hand side is the same as the right hand side.

To enable copying on symbolic datatypes |TypeSym| we need to make an instance for their corresponding |TypeC|. Here is what this looks like for |ExprC|:
%format x1
%format x2
%format b1
%format b2
\begin{code}
instance Copy a => Copy (ExprC a) where
  Expr c1 x1 a1 b1 >>> Expr c2 x2 a2 b2 =
    do  c1 >>> c2
        when (isVar c1)  §  do x1 >>> x2
        when (isAdd c1)  §  do a1 >>> a2; b1 >>> b2
        when (isMul c1)  §  do a1 >>> a2; b1 >>> b2
        when (isNeg c1)  §  do a1 >>> a2
\end{code}
We can see that copying runs the same recursive call to |>>>| multiple times in different branches. However, we should not be calling these branches, because in one general symbolic call to the above function, {\em all} ``branches'' will be executed! This means that the same recursive call will be executed several times, leading to an exponential blow-up. In Section \ref{sec:memo} we will see how to deal with this.

% ------------------------------------------------------------------------------

\section{Translating programs into constraints}

%format (sym (x)) = "\mathit{" x "}^\dagger"
%format pSym = "\mathit{p}^\dagger"
%format ASym = "\mathit{A}^\dagger"
%format BSym = "\mathit{B}^\dagger"
In this section, we explain how we can translate a program |p :: A -> B| in a simple functional programming language into a monadic program |sym p :: sym A -> C (sym B)| in Haskell, such that when |pSym| is run on symbolic input, it generates constraints in a SAT-solver that correspond to the behavior of |p|.

For now, we assume that the datatypes and programs we deal with are first-order. We also assume that all definitions are total, i.e.\ terminating and non-crashing. We will later have a discussion on how these restrictions can be lifted.
\comm{termination/crash restriction}

\subsection{The language}

%format x1
%format xn = "\mathit{x}_n"
%format e1
%format en = "\mathit{e}_n"
%format s1
%format sn = "\mathit{s}_n"
%format K1
%format Kn = "\mathit{K}_n"

%format (transr (e)) = "\llbracket" e "\rrbracket\!\!\!\Rightarrow\!\!\!"
%format (transc (e)) = "\llbracket" e "\rrbracket\!\!\!\Rightarrow_c\!\!\!"
%format (trans (e))  = "\llbracket" e "\rrbracket"

%format isK1 = "\mathit{isK}_1"
%format isKn = "\mathit{isK}_n"


We start by presenting the syntax of the language we translate. This language is very restricted syntactically, but it is easy to see that more expressive languages can be translated into this language.

The language is presented in Figure~\ref{fig:lang}.
Function definitions |d| and recursion can only happen on top-level ({\em local} recursive function definitions are not allowed). A program is a sequence of definitions |d|.
Expressions are separated into two categories: {\em simple} expressions |s|, and regular expressions |e|. Simple expressions are constructor applications, selector functions, or variables. Regular expressions are let-expressions with a function application, case-expressions, or simple expressions.

Function application can only happen inside a let-definition and only with simple expressions as arguments. Case-expressions can only match on constructors, the program has to use explicit selector functions to project out the arguments.

\begin{figure}[h]
\centering
\begin{code}
s ::=  K s1 ... sn
    |  sel s
    |  x

e ::=  s
    |  case s of
         K1 -> e1
         ...
         Kn -> en
    |  let x = f s1 ... sn in e

d ::= f x1 ... xn = e
\end{code}
\caption{The restricted intermediate language.\label{fig:lang}}
\end{figure}


As an example, consider the definition of the standard Haskell function |(++)|:
\begin{code}
(++) :: [a] -> [a] -> [a]
[]      ++ ys  = ys
(x:xs)  ++ ys  = x : (xs ++ ys)
\end{code}
In our restricted language, this function definition looks like:
\begin{code}
xs ++ ys =  case xs of
              Nil   ->  ys
              Cons  ->  let vs = sel2 xs ++ ys
                        in Cons (sel1 xs) vs
\end{code}

\subsection{Basic translation}

%format SIMP = "\textsc{Simp}"
%format CASE = "\textsc{Case}"
%format LET  = "\textsc{Let}"
%format DEF  = "\textsc{Def}"
%format MEMODEF  = "\textsc{Memo-Def}"

The translation revolves around the basic translation for expressions, denoted |transr e r|, where |e| is a (simple or regular) expression, and |r| is a variable. We write |transr e r| for the monadic computation that generate constraints that copy the symbolic value of the expression |e| into the symbolic value |r|.

We present the translation rules in Figure~\ref{fig:trans}.
Rule |SIMP| translations simple expressions. This is simple, because no monadic code needs to be generated; we have pure functions for concrete data constructors and pure functions for selectors. Thus we can
simply copy the value of the simple expression into |r|.
Rule |CASE| translates case-expressions. We use |wait| to wait for the result to become defined, and then generate code for all branches. This code, and the constraints it generates, will only be run when the result is defined.
Rule |LET|: to translate let-expressions, we use the standard monadic transformation.
The translated function is called.
And to translate functions, rule |DEF| is used: it creates a new symbolic value |y| for the result, translates |e| into |y|, and returns |y|.

\begin{figure}[h]
\centering
\fbox{|transr(e) r|}
\begin{code}
(SIMP)  ///  transr s r                ///  =  /// s >>> r

(CASE)  ///  transr (case s of         ///  =  ///  wait s § \cs ->
        ///            K1 -> e1        ///  ¤  ///  ///   do  when (isK1 cs)  ((transr e1 r))
        ///            ...             ///  ¤  ///            ...
        ///            Kn -> en //) r  ///  ¤  ///            when (isKn cs)  ((transr en r))

(LET)   ///  transr (let x = f s1 ... sn in e//) r /// = /// do  x <- sym f s1 ... sn
                                                                 transr e r

\end{code}

\fbox{|trans(d)|}
\begin{code}

(DEF)  ///   trans (f x1 ... xn = e) /// = /// sym f x1 ... xn = do  y <- new
                                                                     transr e y
                                                                     return y
\end{code}
\caption{Translation rules to a constraint-generating program.\label{fig:trans}}
\end{figure}





\subsection{A translated example}

Applying our translation to this function and using symbolic lists, yields the following code:
%format ++? = ++"\!^\dagger"
%format ==? = =="^\dagger"
\begin{code}
(++?) :: Symbolic a => ListSym a -> ListSym a -> C (ListSym a)
xs ++? ys = do  zs <- new
                wait xs § \cxs ->
                  when (isNil cxs) §
                    do  ys >>> zs
                  when (isCons cxs) §
                    do  vs <- sel2 cxs ++ ys
                        cons (sel1 cxs) vs >>> zs
\end{code}
An example property that we may use to find a counter example to may be
|xs ++ ys == ys ++ xs|. Translated, this will look like this:
\begin{code}
appendCommutative xs ys =
  do  vs  <-  xs ++? ys
      ws  <-  ys ++? xs
      b   <-  vs ==? ws
      insist (nt b)
\end{code}
We use the symbolic version |(==?)| of |(==)| that is generated by our translation. When we run the above computation, constraints will be generated that are going to search for inputs |xs| and |ys| such that |xs++ys == ys++xs| is false.
\comm{Polymorphism?}
\comm{we don't really explain how to translate properties!}

\subsection{Memoization} \label{sec:memo}

\comm{
Furthermore,
the notion of memoizing is quite classical; solvers go to great lengths to use
it to share sub-terms (c.f. hash-consing in Greg Nelson's thesis).
}

When performing symbolic evaluation, it is very common that functions get applied to the same arguments more than once. This is much more so compared to running a program on concrete values. A reason for this is that in symbolic evaluation, {\em all} branches of every case expression are potentially executed. If two or more branches contain a function application with the same arguments (something that is even more likely to happen when using selector functions), a concrete run will only execute one of them, but a symbolic run will execute all of them. A concrete example of this happens in datatype instances of the function |(>>>)| (see Section \ref{sec:copy}).

An easy solution to this problem is to use memoization. We apply memoization in two ways.

First, for translated top-level function calls that return a result, we keep a memo table that remembers to which symbolic arguments a function has been applied. If the given arguments has not been seen yet, a fresh symbolic result value |r| is created using |new|, and the function body |e| is run {\em in a fresh context} |c|. The reason we run |e| in a fresh context is that we may reuse the result |r| from many different future contexts. In order to use the result |r| from any context, we need to make the context |c| true first (by using |insist|). After storing |c| and |r| in |f|'s memo table, we return |r|. If we have already seen the arguments, we simply return the previously computed result, after making sure to imply the context in which it was created.

We transle a definition |f x1 ... xn = e| with memoization enabled in this way:
\begin{code}
(MEMODEF)  quad  (sym (f)) x1 ... xn =
                   do  mcy <- lookMemo_f x1 ... xn
                       case mcy of
                            Nothing     -> do  c <- new
                                               y <- new
                                               storeMemo_f x1 ... xn (c,y)
                                               with c ((transr e y))
                                               insist c
                                               return y
                            Just (c,y)  -> do  insist c
                                               return y
\end{code}
The functions |lookMemo_f| and |storeMemo_f| perform lookup and storage in |f|'s memo table, respectively. The function |with| locally sets the context for its second argument.

Second, we also memoize the copy function |(>>>)|. This function is not a function that returns a result, but it generates constraints instead. However, we treat |(>>>)| as if it were a top-level function returning |()|, and memoize it in the same way.

Memoization can have big consequences for the performance of constraint generation and solving, as shown in the experimental evaluation.
%We allow memoization to be turned on and off manually for each top-level function.
Memoization is enabled by default on all recursive functions.
We always memoize |(>>>)| on |Delay|.

\subsection{Symbolic merging of function calls}

\comm{
Reviewer:
 The function call merging optimization, while effective, is known in
  the first-order symbolic execution world.  See for example the
  description of encoding paths in "Enhancing symbolic execution with
  Veritesting", section	2.3.  That paper cites "Avoiding exponential
  explosion: Generating compact verification conditions" by Flanagan
  and Saxe and "Efficient weakest preconditions" by Leino.  The	paper
  should probably weaken the claims of novelty and compare it to
  existing approaches.
  }

Consider the following program:
\begin{code}
f e =  case e of
         Var v    -> v
         Add a b  -> f a
         Mul a b  -> f b
         Neg a    -> f a
\end{code}
In the previous subsection, we explained that all branches of a case expression have to be explored when performing symbolic evaluation. This is obviously bad when there exist identical function calls that occur in multiple branches. But it is also bad when there are multiple branches that contain a call to the same function |f|, even when those calls do not have the same arguments. A run of |f| on concrete values would take linear time in the depth $k$ of the argument expression. A naive symbolic run of |f| would take time proportional to $3^k$! After applying memoization, this is reduced to $2^k$. However, we would like to get as closely to linear in $k$ as possible.

Consider the following transformed version of the above program, after applying standard program transformations.
%format undefined = "\bot"
\begin{code}
f e =  let y = f (  case e of
                      Var v    -> undefined
                      Add a b  -> a
                      Mul a b  -> b
                      Neg a    -> a )
       in  case e of
             Var v    -> v
             Add a b  -> y
             Mul a b  -> y
             Neg a    -> y
\end{code}
This program behaves the same as the original program (at least in a lazy semantics), but now it only makes one recursive call, {\em even when we symbolically evaluate it}. The trick is to share one generalized call to |f| between all 3 places that need to call |f|. We can do this, because those 3 places never really need to call |f| at the same time; for any concrete input, we can only be in one branch at a time. Thus, we have {\em merged} three calls to |f| into one call.

Our translator can generate constraint producing code that applies the same idea as the above program transformation, but directly expressed in constraint generation code. In order for this to happen, the user has to manually annotate calls to |f| with a special labelling construct |@|:
\comm{Update this and remove the labelling construct
Describe that we can have lets binding case-constructs
}
\begin{code}
f e =  case e of
         Var v    -> v
         Add a b  -> (f a)@ 1
         Mul a b  -> (f b)@ 1
         Neg a    -> (f a)@ 1
\end{code}
The generated constraint producing code will look like this:
%format fSym = "\mathit{f}^\dagger"
\begin{code}
fSym e = do  r <- new
             wait e § \ce ->
               do  c <- new
                   x <- new
                   y <- with c § fSym x

                   when (isVar ce) §  do  sel1 ce >>> r
                   when (isAdd ce) §  do  insist c
                                          sel2 ce >>> x
                                          y >>> r
                   when (isMul ce) §  do  insist c
                                          sel3 ce >>> x
                                          y >>> r
                   when (isNeg ce) §  do  insist c
                                          sel2 ce >>> x
                                          y >>> r
\end{code}
The above function first waits for its argument to be defined, and then creates a fresh context |c| and a fresh input |x|, and then it evaluates |fSym| with the input |x| in the context |c|. Then, the normal part of the case expression progresses, but instead of calling |fSym|, the branches simply use |insist| to make sure the context of the merged call is set, and copy the argument they need into |x|. This guarantees that |y| gets the correct value. An interesting thing to notice is that, because we are generating constraints and not evaluating values,

Note that in the above code, because |(>>>)| is memoized, the call |y >>> r| only gets performed once although it appears in the code three times, and |sel2 ce >>> x| also gets performed only once although it appears twice.

Our experimental evaluation also shows the importance of merging function calls in case branches. Automatically knowing when and where to apply the labels of function calls that should be merged is future work.

\subsection{Other optimizations}

We perform a few other optimizations in our translation. Two of them are described here.

Not all algebraic datatypes need to use |Delay|. In principle, for any finite type we do not need to use |Delay| because we know the (maximum) size of the elements on beforehand. In our translator, we decided to not use |Delay| for enumeration types (e.g.\ |BoolSym|).

For definitions that consist of a simple expression |s|, we can translate as follows:
\comm{this is actually not on}
\begin{code}
trans (f x1 ... xn = s) /// = /// f x1 ... xn = do  return s
\end{code}
This avoids the creation of an unnecessary helper value using |new|.

% ------------------------------------------------------------------------------

\section{Solving the constraints} \label{sec:solving}

In the previous two sections, we have seen how to generate constraints in the |C| monad, and how to translate functional programs into constraint producing programs. However, we have not talked about how to actually generate symbolic inputs to programs, and how to use the SAT-solver to find solutions to these constraints. In order to do this, we have to make part of the code we have shown so far slightly more complicated.

\subsection{Inputs and internal points} \label{sec:input}

In a symbolic program, there are two kinds of symbolic expressions: inputs and internal points. They are dealt with in two fundamentally different ways. Inputs are expressions that are created outside of the program, and that are controlled by the solver. If the solver determines that a certain input should be made bigger by expanding one of its delays, it can do so, and the program will react to this, by triggering constraint generators that are waiting for these delays to appear. These triggers may in turn define other delays (by using |>>>|), and a cascade of constraint generators will be set in motion. So, inputs are set on the outside, and internal points react to their stimuli.

We would like to make this difference explicit by introducing two functions to create symbolic expressions: one called |new| for internal points, and one called |newInput| for inputs. To implement this, we introduce a new datatype of |Mode|s, with which symbolic expressions can be labelled.
\begin{code}
data Mode = Input | Internal
\end{code}
The most important place where the label should occur is when we create a |Delay|. We make the following changes:
%format mdo = "\mathbf{mdo}"
\begin{code}
data Delay a  =  Done a
              |  Delay Mode (IORef (Either (C ()) a))

delay :: Mode -> C a -> C (Delay a)
delay m c =
  mdo  ref <-  newRef § Left §
                 do  a <- c
                     writeRef ref (Right a)
       return (Delay m ref)
\end{code}
The function |delay| gets an extra |Mode| argument, which indicates what kind of delay we are creating.

Whenever we create any new symbolic value, we need to be explicit about what kind of value we are creating. We therefore change the |Symbolic| class accordingly:
\begin{code}
class Symbolic a where
  newMode :: Mode -> C a

new, newInput :: Symbolic a => C a
new       = newMode Internal
newInput  = newMode Input
\end{code}
The function |new| now always creates internal points, where as the new function |newInput| creates new inputs.

The mode information needs to be propagated through all calls of |newMode|:
\begin{code}
instance Symbolic Prop where
  newMode _ = newVal

instance Symbolic a => Symbolic (Arg a) where
  newMode m = An `fmap` newMode m

instance Symbolic a => Symbolic (Delay a) where
  newMode m = delay m (newMode m)

instance Symbolic a => Symbolic (ExprC a) where
  newMode m =  do  c <- newFin [Var,Add,Mul,Neg]
                   liftM3  (Expr c) (newMode m)
                           (newMode m) (newMode m)
\end{code}
What is now the different between delays that belong to inputs and delays that belong to internal points? Well, if the program decides to do a |wait| on an internal point, then the algorithm that controls the expansion of the input delays does not need to know this. Internal points are only expanded by the program. But if the program decides to do a |wait| on an input delay, the algorithm that controls the expansion needs to know about it, because now this delay is a candidate for expansion later on.

To implement this, we introduce one more function to the |C| monad:
\begin{code}
enqueue :: Delay a -> C ()
\end{code}
We augment |C| to also be a state monad in a queue of pairs of contexts and delays. The function |enqueue| takes a delay and adds it to this queue together with the current context.

The function |enqueue| is called by the function |wait| when it blocks on an input delay:
\begin{code}
wait :: Delay a -> (a -> C ()) -> C ()
wait (Done x)         k = k x
wait d@(Delay m ref)  k =
  do  ecx <- readRef ref
      case ecx of
        Left cx  -> do  c <- ask
                        writeRef ref § Left §
                          do  cx
                              Right x <- readRef ref
                              with c § k x
                        case m of
                          Input     -> enqueue d
                          Internal  -> return ()

        Right x  -> do  k x
\end{code}
When a |C| computation terminates and has generated constraints, we can look at the internal queue and see exactly which parts of the inputs (input delays) are requested by which parts of the program (contexts), and in which order this happened.

\subsection{Solving and expanding}

\comm{Make this clearer}
The main loop we use in our solving algorithm works as follows. We start by creating a SAT-solver, and
running the main |C|-computation. This will produce a number of constraints in the SAT-solver. It will also produce a queue $Q$ of pairs of contexts and unexpanded input delays.
\comm{Compare this by only using a queue, and expanding even when it is not strictly required}

We then enter our main loop.

The first step in the loop is to find out whether or not there exists an actual solution to the current constraints. The insight we employ here is that a real solution (i.e.\ one that corresponds to an actual run of the program) cannot enter any of the contexts that are currently in the queue. This is because those contexts all have pending input delays: case expressions that have not been triggered yet. In other words, the constraints belonging to those contexts are not finished yet; there may yet be more to come. So, when looking for a real solution, we ask the SAT-solver to find a solution to all constraints generated so far, under the assumption that all of the contexts that appear in the queue $Q$ are false. If we find a solution, we can from the model produced by the SAT-solver read off the actual values of the input that satisfy the constraints.

If we do not find a solution, it may be because we still had to expand one of the contexts in the queue $Q$. So, we have to pick an element from the queue, for which we are going to expand the corresponding |Delay|. The simplest choice we can make here is just to pick the first element from the queue, expand the delay contained in it, remove all occurrences of that delay in the queue $Q$, and repeat the main loop. If we do this, we get a completely fair expansion, which leads to an algorithm that is both sound and complete. Soundness here means that any found solution actually corresponds to a real run of the program, and completeness means that we are guaranteed to find a solution if there exists one.

But we can do better. The SAT-solver is able to give feedback about our question of finding a solution under the assumption that all contexts in the queue $Q$ are false. When the answer is no, we also get a {\em subset} of the assumptions for which the SAT-solver has discovered that there is no solution (this subset is called the {\em assumption conflict set} \cite{minisat}, or sometimes an {\em unsatisfiable core}). Typically, the assumption conflict set is much smaller than the original assumption set. An improved expansion strategy picks a context to expand from the assumption conflict set. It turns out that if always we pick the context from the conflict set that is closest to the front of the queue $Q$, then we also get a sound and complete expansion strategy.

Why is this better? There may be lots of contexts that are waiting for an input to be expanded, but the SAT-solver has already seen that there is no reason to expand those contexts, because making those contexts true would violate a precondition for example. The assumption conflict set is a direct way for the solver to tell us: ``If you want to find a solution, you should make one of these propositions true''. We then pick the proposition from that set that leads to the most fair expansion strategy.

To see why this strategy is complete, consider the case where the full constraint set has a solution $s$, but we are not finding it because we are expanding the wrong delays. In that case, there must after a while exist a finite, non-empty set $S$ of delays in $Q$ that should be expanded in order to reach the desired solution, but that are never chosen when we do choose to expand a delay. (If this does not happen, we will find the solution eventually.) The first observation we make is that for every conflict set that is found, at least one element from $S$ must be a part of it. (If not, this would imply that $s$ was not a solution after all.) Since the expansion strategy does not pick points from $S$ to expand, it picks points that lie closer to the front of the queue instead. But it cannot pick such points infinitely often; eventually the points in $S$ must be the ones closest to the head.

In our experimental evaluation we show that this expansion strategy very often defines just the right constructors in the input in order to find the counter example, even for large examples. We thus avoid having to pick a depth-limit up-front, and even avoid reasoning about depth altogether.

An additional bonus of using the assumption conflict set is that when that set is empty, it is guaranteed that no solution can be found, ever, and the search can terminate. This typically happens if the user constrained the input using size and/or depth constraints, but it can happen in other cases as well.

\subsection{Dealing with non-termination}
\label{postpone}

So far, we have assumed that all functions terminate. However, it turns out that this restriction is unnecessary; there is a simple trick we can employ to deal with functions that may not terminate: For possibly non-terminating functions, we use a special function |postpone|:
\begin{code}
postpone :: C () -> C ()
postpone m =  do  x <- newInput
                  wait x § \ () -> m
\end{code}
This function takes a constraint generator as an argument, and postpones it for later execution, by simply constructing a new {\em input} to the program, and blocking in that input. The result is that the expansion of the input in the current context now lies in the expansion $Q$, and it is guaranteed that it will be picked some time in the future, if the solver deems the current context part of a promising path to a solution.

For possibly non-terminating functions |f|, |postpone| is used in the following way:
\begin{code}
trans (f x1 ... xn = e) /// = /// sym(f) x1 ... xn = do  y <- new
                                                         postpone ((transr e y))
                                                         return y
\end{code}
The generation of constraints for the body |e| of |f| is postponed until a later time.

It is good that we have postpone; sometimes, even though our input program clearly terminates, the transformed symbolic program may not terminate. This can happen when the static sizes of symbolic arguments to recursive functions do not shrink, whereas they would shrink in any concrete case. An example is the function |merge| after merging recursive function calls, as explained in the experimental evaluation section. The function |postpone| also works in those cases.

Thus, we use |postpone| on any function which is not structurally recursive {\em after} transformation into a symbolic program.

\comm{New text}
The true story is this:
If we assume that the input program is terminating for all inputs,
we can guarantee that we will find the counter-example (given sufficient memory and time).
This is the same assumption that CVC4 does, and it is a totally reasonable assumption.
So our program is well-behaved on terminating programs.

However, if the input program is not terminating, then the function axioms can still
be consistent, and our tool can still be used beneficially.
An example is |f x = f x|, which is not a contradiction. Our tool will just
enqueue f ocassionally but be able to say anything about what |f x| is.
If the axioms are inconsistent due to non-termination, as in |f x = not (f x)|, then
we cannot make any guarantees that we will find this inconsistency. In the function above,
with memozation enabled (which it will be by default, since |f| is a recursive function)
we will get some value |y| that is equal to |not y|, a contradiction! However, if
memoization is turned off, or if memoization does not apply, then our tool won't be able
to see that there is a contradiction and instead search for (and maybe report) a counterexample
in another part of the program.

Comment:
It can be beneficial to have |postpone|s even on functions that are obviously terminating.
The reason is that it can sometimes be seen that expanding a function further won't lead
to a counterexample. And the less functions are expanded, the fewer constraints are produced.

% ------------------------------------------------------------------------------

\section{Experimental Evaluation}
\label{examples}

In this section, we compare different settings of our tool
and with other similar tools, to be able to show the claims
made in the introduction.

We do three different experiments:
\begin{enumerate}
\item as a quantitative analysis we compare the runtimes to
show that there are no counterexamples up to some depth |d| to true properties
with LazySmallCheck\cite{lazysc} and with smten\cite{smten}.
We also compare running our tool by generating symbolic data up-front up to some depth,
or to incrementally expand it until it reaches some depth.

\item a qualitative evaluation of challenge benchmarks that have
counterexamples, also against some other tools (CVC4 \cite{cvc4models}, and
Feat \cite{feat}).

\item to show the importance of memoization and function call merging,
we compare our tool with and without these settings on some programs
\end{enumerate}



In this section, we would like to compare our tool to
\comm{restart}
similar tools that can also find values with a certain property
(such as being a counter-example to a conjecture).
We have identified two approaches to evaluate such tools:
One way to evaluate such tools are to use a benchmark suite
with satisfiable properties.

This approach has some drawbacks, in particular: (1) tools can get ``lucky'',
and find an assignment quickly (this especially applies to randomised testing),
(2) there is an unsettling arbitrariness of what benchmarks to use
(introduce random mutations to make buggy programs,
introduce artificial limits like that the input must have some certain size,
try to excavate buggy programs from version controlled code)

Another approach is to use conjectures that are true,
which have no counterexample, and see how long time it takes for
the tools to report that there is no conterexample.
Since we use recursive data types, the search space is infinite,
so there will have to be a bound, for instance depth or size.
(Otherwise a tools like our will forever (except in favourable cases)!)
We modified our tool to be able to make such an evaluation:
there is a flag for specifying the maximum depth of the input data.
The implementation is simple: when the symbolic data has reached
the specified depth, a delayed value is not used, but rather an
inaccessible delay that cannot be expanded. This will eventually
make the queue of points to expand empty, and then it can be concluded
that no counterexample exist within the depth.

Of course, this is using the tools for the wrong purpose.
The right tool is to use an inductive prover that could prove
that there are no counterexamples, regardless of length.
So we emphasize that this is just a way to be able to evaluate
how well it would work when there actually are counterexamples to find.

With this in place, we can easily compare our tool with
the most similar tools, namely LazySmallCheck\cite{lazysc},
which operates by depth by default, and with smten\cite{smten},
which allows the user specify search spaces in a DSL. We simply
generate the code that makes a search space up to some depth.
\comm{smten could get merged spaces}
Care was taken so that LazySmallCheck uses as many parallel connectives as possible.

\paragraph{Experimental set-up} The experiments were run on a 2013 laptop computer
with an Intel Xeon E3-1200 v2 processor and the processes were allowed 7 GB of RAM.
We used the latest versions of the tools: smten 4.1.0.0, LazySmallCheck 0.6,
\verb!cvc4-2015-08-18-x86_64-linux-opt!.

\subsection{Exhausting a search space up to some depth}
We use the TIP benchmarks\cite{tip_problems},
some of the benchmarks sort integer lists, and some of them
have a polymorphic quantification of the property.
For these kind of problems, we make a new versions, where
we replace the type or the sortable with a unary representation of natural numbers.
We remove those that use integer {\em arithmetic}, and higher-order-functions\footnote{
Most of the higher-order constructs are removable by specialization.
Quantification over functions in the properties only occurs in a few benchmarks.
We aim to be able to lift this restriction of our tool to the final version of the paper.
}. This is to only compare data-types, and to get all tools to
have the same interpretation of depth.
This yields some ~400 benchmarks.
We run them on increasing depths.
Here is a table of the number of solved problems within 60s:


Preliminary results with timeout of 1s:





\begin{figure}[h]

\centering
\begin{tabular}{l || r || r || r || r || r || r || r || r || r || r || r || r || r || r  || r}
tool              & 3  & 4  & 5  & 6  & 7  & 8  & 9  & 10 & 15 & 20 & 30 & 50 & 100 & 200 & 1000 \\
\hline
\hline
hbmc & 328 & 295 & 282 & 249 & 220 & 202 & 194 & 187 & 136 & 119 & 96 & 78 & 49 & 41 & 26 \\
\hline
LSC  & 350 & 339 & 316 & 296 & 278 & 199 & 166 & 163 & 151 & 132 & 127 & 109 & 99 & 65 & 50 \\
\hline
smten & 282 & 267 & 253 & 235 & 213 & 197 & 188 & 169 & 152 & 127 & 102 & 86 & 54 & 42 & 6 \\
\end{tabular}
\caption{
Number of benchmarks shown to not contain any conterexample up to various depths, within a timeout of 60s.
\label{tab:depth}
}
\end{figure}

10s:

lazysc 398 386 362 342 332 305 296 284 201 167 167 164 162 159 159 159 151 151 150 150 132 129 127 127 127 110 108 105 98 90 72 61 61 61 61 61 61

smten  319 312 288 272 258 244 233 221 203 190 179 171 170 167 163 159 157 156 154 153 127 114 102 101  96  92  86  82 54 48 39 39 39 39 38 38 37

hbmc   394 363 335 316 290 281 264 238 218 204 202 197 194 191 188 181 176 167 164 159 126 106  98  93  87  83  81  80 58 48 45 44 43 41 40 37 32

hbmc u 394 363 337 324 296 287 268 243 227 209 202 199 196 192 191 187 180 175 172 171 141 115  98  86  79  77  75  72 52 48 45 45 44 40 36 35 35

Here are scatter plots:

... plots plots ...

\subsubsection{Interpretation}


There are some examples where the intermediate symbolic
values get too big, for instance the regular expression examples.
Here, it is just simply faster to exhaustively run the programs
(a'la SC or LSC).
Interpreting the program symbolically is slower than
evaluating the program, so LSC typically performs faster unless
there is some exponential blowup that our tool can avoid
symbolically.
From the results, it can be seen that our tool is able to
exhaustively search larger search spaces than LSC, so
one could hypothesise that this tool is better at finding
big counterexample. (And the next section strengthens this
hypothesis).
Another case is when memoisation enables us to see that two values are equal,
and only needs the result from the computation, but not the actual
computation.
(see \verb!isaplanner/prop_75!)
The property talks about the function |count|, defined as:

> count :: Nat -> [Nat] -> Nat
> count n []     = Z
> count n (x:xs) = if n = = x then S (count n xs) else count n xs

The property is:

> plus (count n xs) (count n [m]) = count n (m:xs)

However, our tool can see that there is no counterexample, even without
expanding the definition of |==|. To see why, memoisation will give names
to |n == xi| for all |xi| in the list |xs| and in |m|. Then, the SAT solver
effectively case splits on the result of the comparison, and propagates
the information symbolically through |count| and |plus|.
This has the effect that |n| and the elements of the list are not expanded,
only the list |xs| is.

What is it we cannot see with memoization? Consider this (contrived) fragment of code:

> if x == y then f x ++ f y else []

Here |f x| and |f y| will be equal as |x| and |y| are. But the lookup in the memoization
table does not know about the current context's equalities. So there is some room
for improvement here.
It should be noted that Leon should be able to achieve this through its use of
uninterpreted functions and SMT congruence reasing.

% (declare-datatypes (a)
%   ((list (nil) (cons (head a) (tail (list a))))))
% (declare-datatypes () ((Nat (Z) (S (p Nat)))))
% (define-fun-rec
%   plus
%     ((x Nat) (y Nat)) Nat
%     (match x
%       (case Z y)
%       (case (S z) (S (plus z y)))))
% (define-fun-rec
%   equal
%     ((x Nat) (y Nat)) Bool
%     (match x
%       (case Z
%         (match y
%           (case Z true)
%           (case (S z) false)))
%       (case (S x2)
%         (match y
%           (case Z false)
%           (case (S y2) (equal x2 y2))))))
% (define-fun-rec
%   count
%     ((x Nat) (y (list Nat))) Nat
%     (match y
%       (case nil Z)
%       (case (cons z ys)
%         (ite (equal x z) (S (count x ys)) (count x ys)))))
% (assert-not
%   (forall ((n Nat) (m Nat) (xs (list Nat)))
%     (= (plus (count n xs) (count n (cons m (as nil (list Nat)))))
%       (count n (cons m xs)))))
% (check-sat)

These are some scribbles about the old evaluation:
\begin{itemize}
\item Lazy SmallCheck performs very well on sorting examples where
      the structure of the sorted lists can be determined lazily
      without looking at the elements.
      On the other hand, hbmc performs better on
      stricter sorts like insertion sort, bubble sort
      or merge sort which first identifies sublists which are ascending
      and descending.
      The problems about sorting come in two flavors, one
      where it is given that |length xs = n && length ys = n|,
      and one when only |length xs = n| is given, and hbmc
      performs well even when only one of them is given.
\item Problems with very small counter-examples are quickly found
      by both Lazy SmallCheck and feat: the overhead of symbolic
      execution can sometimes be high here even though the
      counterexample is small. Some examples of these is finding
      small regular expressions of some property: evaulating
      the regular expression reckogniser symbolically is quite expensive.
\item hbmc shines when a lot of the search space can be carved
      away, (but not necessarily by a lazy predicate), and
      the counterexample is at a certain depth.
      Some of the examples in the bench mark suite that hbmc
      can only do are:
      \begin{itemize}
        \item synthesise lambda expressions in normal form by inverting a type checker
              (however, these are not so big so feat can find the smaller ones, too)
              (inferring the types of these is easy for LazySC, but feat does not
              always make it. hbmc is good at inferring)
        \item find a fixed point combinator in combinatory calculus
              (all but one of these are too big even for feat)
        \item find a turing machine with certain properties
        \item find propositional formula with certain properties
        \item find balanced search trees
      \end{itemize}
\end{itemize}

\subsection{Satisfiable problems}
We took some we were interested in, so this section does not
want to claim as much scientific rigour as the last section.

\begin{itemize}
\item typechecker for simply typed lambda calculus
      (with and without products)
\item combinatory calculus
\item synthesising turing-machines
\item grammars
\item nqueens
\item edit distance
\item the ferry problem
\item wolf, sheep, cabbage
\item combinators
\item grammars
\item sudoku
\item scale
\item regexp
\item tic-tac-toe
\item group assignments under wishful thinking constraints
\item the send-more-money puzzle
\end{itemize}

\subsection{The importance of function call merging}
We could take some true property, like merge commutative, and increase the depth

\begin{comment}
\section{Examples and Experiments}
\label{examples}

In this section we aim to describe how our system works in practice by
looking at some examples. All experiments were run on
a laptop with a Intel Xeon E3-1200 processor.

\subsection{Generating sorted lists}

Assume that we are given a predicate about unique and sorted lists,
that all elements are pairwise larger than the next:
\begin{code}
unqsorted  ::  [Nat] -> Bool
unqsorted (x:y:xs)  =  x < y && unqsorted (y:xs)
unqsorted _         =  True
\end{code}
\noindent
Now we can investigate the expansion strategy based on the assumption conflict set, by asking for |xs|
such that |unqsorted xs| and |length xs > n|, given some bound |n|.
Our tool can output a trace showing how the incremental values
have been expanded so far.  With |n=2|, the trace looks like this:
\begin{verbatim}
xs: _
xs: Lst__
xs: Lst_(Lst__)
xs: Lst_(Lst_(Lst__))
xs: Lst_(Lst_(Lst_(Lst__)))
xs: Lst_(Lst(Nat_)(Lst_(Lst__)))
xs: Lst_(Lst(Nat_)(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat_)(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat(Nat_))(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat(Nat_))(Lst(Nat(Nat_))(Lst__)))
xs= [Z,S Z,S (S Delayed_Nat)]
\end{verbatim}
All but the last lines describe a partial view of the value.
Delayed values are represented with a @_@, and other values
with their type constructor and the arguments. The
value @xs@ is first expanded to contain sufficiently many
elements, namely three, and
then the natural numbers start to be expanded. Note that
in this case only the necessary values are evaluated.
This can in general not be guaranteed.

The same expansion behaviour happens also when increasing
the list length, |n|. The run time is also low, generating
a sorted list of length at least 25 takes a little less than
a second, and the list |[0..24]| is indeed obtained.

% Can also generate reverese and qrev lists, can generate
% sorted lists with |sort xs=xs|.... Later we will look at the more difficult
% |sort xs=sort ys|. Sorting stuff

\subsubsection{Terminating without counterexample}

Sometimes it can be noticed that there is no counterexample regardless how the
program is expanded.  The simplest property when this happens is perhaps asking
for an |x| such that |x < Z|. The standard definition of |(<)| returns |False|
for any |y < Z|, so there is a contradiction in this context. This is also the
same context that the incremental value in |x| is waiting for, but since this is
unsatisfiable, it will never be expanded.

Let's return to the previous example with asking for an |xs|, such that
|unqsorted xs| and |length xs > n|, but with  the new constraint that |all (< n)
xs|.  So the list must be sorted, but the upper bounds on the data are only
local: namely that each element should be below |n|. We do not give an upper bound on the length of the list.
The other constraint is a lower bound on the list: that it should at least have length |n|.

When executing this, first the |length| constraint forces the program to expand
to make the list at least that long.  Then the |unsorted| predicate will make
sure that all the elements are pairwise ordered. This will make the first
element to be at least |Z|, the one after that at least |S Z| and so un until
the |n|th element. But then we will eventually enter the situation outlined
above and the |n|th element cannot expand any more, and the system terminates
cleanly with saying:
\begin{verbatim}
Contradiction!
No value found.
\end{verbatim}
\noindent
and thus efficiently proving the property (for a specific choice of |n|, not for all |n|.) This is perhaps surprising, because no explicit upper bound on the length of the list was given.

We can use boolean predicates in general to give all kinds of bounds on inputs, for instance depth. If the predicates bound the input sufficiently much, the tool is guaranteed to terminate.

% \subsubsection{Limitations of termination discovery}
%
% Our system is not an inductive prover and will not terminate on
%
% \begin{code}
% nub xs = y:y:ys
% \end{code}
%
% \noindent
% (Note that it does not help even if the element type is finite.)
%
% nor on:
%
% \begin{code}
% unqsorted (rev xs) && all (< n) xs && length xs > n
% \end{code}
%
% \noindent
% it keeps expanding the tail of the list, hoping for something....
%
% \subsubsection{Discussion about contracts checking a'la Leon}
%
% ....

\subsection{Merging the calls in merge}
\label{merge}

%format x_1
%format x_2
%format x_3
%format x_n
%format y_1
%format y_2
%format y_3
%format y_m

% The section discusses some optimisations that can be done
% to functions with more that one recursive call.
% The topic is this implementation of merge sort:
%
% \begin{code}
% msort      :: [Nat] -> [Nat]
% msort []   = []
% msort [x]  = [x]
% msort xs   = merge (msort (evens xs)) (msort (odds xs))
%
% Here, |evens, odds :: [Nat] -> [Nat]| picks ut the elements
% at the even and the odd positions, respectively.


This example about the function |merge| from merge sort aims to highlight how important
merging of function calls can be. We use
the following standard definition of |merge| that merges two lists,
returning a sorted list of the inputs:
\begin{code}
merge :: [Nat] -> [Nat] -> [Nat]
merge []      ys      = ys
merge xs      []      = xs
merge (x:xs)  (y:ys)  | x <= y     = x:merge xs (y:ys)
                      | otherwise  = y:merge (x:xs) ys
\end{code}
Evaluating merge on symbolic lists is expensive since |merge|
performs two recursive calls, leading to an exponential behaviour.
One first observation
of the situation reveals that evaluating this expression:

> merge [x_1, x_2, ..., x_n] [y_1, y_2, ..., y_m]

makes these two calls:

> merge [x_1, x_2, ..., x_n]  [y_2, ..., y_m]
> merge [x_2, ..., x_n]       [y_1, y_2, ..., y_m]

However, both of these will make the following call:

> merge [x_2, ..., x_n] [y_2, ..., y_m]

We can avoid to twice calculate this, by
memoizing the function |merge|. This leads to quadratic behavior of the symbolic evaluator.

Another observation is that the two recursive calls in |merge|
can be merged into one:
\begin{code}
merge' :: [Nat] -> [Nat] -> [Nat]
merge' []      ys      = ys
merge' xs      []      = xs
merge' (x:xs)  (y:ys)  | x <= y     = x:(merge' xs (y:ys))@1
                       | otherwise  = y:(merge' (x:xs) ys)@1
\end{code}
After merging those two function calls, the function |merge'| will make a
\emph{linear} number of calls instead of \emph{quadratic} for the memoized version, and
\emph{exponential} for the unmemoized version.

We experimentally evaluated the performance of these three versions
(without any optimizations, with memoization, and with merged calls)
by increasing a length bound |n|, and asking to find |xs|, |ys| satisfying:

> xs /= ys && msort xs == msort ys && length xs >= n

In words: two different lists that are permutations of each other,
via a |msort| function that calls the different versions of |merge|.

The results are in Figure \ref{inj}. The merged function is
significantly better: allowing to go up to lists over size 20 within
reasonable time instead of size 10. We hypothesise that this is
due to the fact that we can move the exponential behavior to the
SAT solver rather than in the size of the SAT problem.

The memoized version performs slightly better than the unmemoized
one. We also compare our runtimes to Leon\cite{leon} and LazySmallCheck\cite{lazysc}.

% The runtime is considerably better for the |merge'| version, and the memoised
% version of |merge| is considerably better than the unmemoised version.
% The runtimes are compared to Leon and LazySmallCheck.

% We also applied the |merge| to |merge'| transformation
% by hand for them, but this did not improve their runtime.

\begin{figure} \centering{
\includegraphics[scale=0.60]{inj.pdf}}
\caption{
Run time to find |xs|, |ys| such that |xs /= ys|
and |msort xs == msort ys| with a |length| constraint on |xs|.
We compare our tool with different settings (\emph{merged}, \emph{memo}, \emph{unopt})
as described in Section \ref{merge}.
and with LazySmallCheck\cite{lazysc} and Leon\cite{leon}.
\label{inj}
}
\end{figure}

The original |merge| function is structurally recursive,
but this property is destroyed when symbolically
merging to |merge'|. The symbolic values that are
fed to the recursive calls are not smaller: for instance,
the first one is |if x <= y then xs else x:xs| which
is as big as the input |x:xs|. We overcome this
introduced non-termination by introducing a |postpone|
as described in Section \ref{postpone}.

\subsection{Expressions from a type checker}

We will here consider a standard type-checker for
simply typed lambda calculus. It answers whether
a given expression has a given type, in an environment:

> tc :: [Type] -> Expr -> Type -> Bool
> tc  env  (App f x tx)  t           = tc env f (tx :-> t) && tc env x tx
> tc  env  (Lam e)       (tx :-> t)  = tc (tx:env) e t
> tc  env  (Lam e)       _           = False
> tc  env  (Var x)       t           =  case env `index` x of
>                                         Just tx  -> tx == t
>                                         Nothing  -> False

By inverting this function, we can use it
to infer the type of a given expression,
or even synthesise programs of a given type!
For instance, we can get the S combinator
by asking for an |e| such that:

> tc [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C)

Upon which our tool answers this term, when pretty-printed:
\begin{code}
\x y z -> ((((\v w -> w) z) x) z) (y z)
\end{code}
This takes about 7 seconds, but as can be seen above,
it contains redexes. Interestingly, we can
avoid getting redexes \emph{and} reduce the search space by
by adding a recursive predicate
|nf :: Expr -> Bool|
that checks that there is no unreduced
lambda in the expression. Now, we ask
for the same as above, and that |nf e|.
With this modification, finding the s combinator,
in normal form, takes less a fraction of a second.
Comparison with and without normal form and
with LazySmallCheck can be found in Table \ref{typetable}\footnote{We also ran Leon on this example but it timed out.}.

Constraining the data in this way allows
cutting away big parts of the search space (only normal
forms). The context where the expression is not in normal
form will become inconsistent due to the predicate,
and no delayed computations are evaluated from inconsistent
contexts. This would not be the case if we up from decided on how
big our symbolic values were. So here we see a direct benefit from
incrementally expanding the program.

Both the code for the type checker and the
normal form predicate contains calls that
can be merged in the fashion as the merge
sort. Without merging these calls, finding the normal
form of the S combinator takes about a second,
and 30 seconds without the normal form predicate.

\begin{table}
\begin{center}
\textit{
\begin{tabular}{l r r}
\em Type & \em Our & \em LazySC \\
\hline
|w    ::(a->a->b)->a->b|         & 1.0s &  - \\
|(.)  ::(b->c)->(a->b)->a->c|    & 6.7s &  - \\
|s    ::(a->b->c)->(a->b)->a->c| & 7.6s &  - \\
|w| in normal form   & $<$0.1s &     0.9s \\
|(.)| in normal form   & $<$0.1s &  - \\
|s| in normal form    & 0.1s &  - \\
\end{tabular}
}
\end{center}
\caption{Using the type checker to synthesise
expressions. LazySmallCheck was given a 300s
time limit for each depth 6, 7 and 8, timeout
is denoted with -.
}
\label{typetable}
\end{table}%

% \begin{code}
% data Expr = App Expr Expr Type | Lam Expr | Var Nat
%
% data Type = Type :-> Type | A | B | C
% tc  env  (App f x tx)  t           = tc env f (tx :-> t)
%                                    && tc env x tx
% tc  env  (Lam e)       (tx :-> t)  = tc (tx:env) e t
% tc  env  (Lam e)       _           = False
% tc  env  (Var x)       t           =  case env `index` x of
%                                         Just tx  -> tx == t
%                                         Nothing  -> False
% \end{code}
%
% \begin{code}
% nf :: Expr -> Bool
% nf (App (Lam _) _ _) = False
% nf (App f x _)       = nf f && nf x
% nf (Lam e)           = nf e
% nf (Var _)           = True
% \end{code}

\subsection{Regular expressions}
\label{regexp}

%format :+: = ":\!\!+\!\!:"
%format :&: = ":\!\&\!:"
%format :>: = ":>:"
%format .>. = ".\!>\!\!."

%format Meps = "\epsilon"
%format (repp (p) (i) (j)) = p "\!\{" i "," j "\}"
%format (reppp (p) (i) (j)) = "(" p ")\!\{" i "," j "\}"
%format (maxx (i) (j)) = i "\cap" j
%format (minn (i) (j)) = i "\cup" j
%format Mempset = "\emptyset"

We used a regular expression library
to falsify some plausible looking laws. The library has the following api:

% We will call the main one |prop_repeat|:
%
% > Meps `notElem` p && s `elem` repp p i j & repp p i' j' ==> s `elem` repp p (maxx i i') (minn j j')
%
% Here, |repp p i j| means repeat the regular expression |p| from |i| to |j| times.
% If |i > j|, then this regular expression does not recognize any string.
% Conjunction of regular expressions is denoted by |&|.
%
% This property is false for |i = 0|, |j = 1|, |i' = j' = 2|, |p = a+aa| and |s = aa|,
% since |reppp (a+aa) (maxx 0 2) (minn 1 2) = reppp (a+aa) 2 1 = Mempset|.


> data RE a  = a :>: a  | a :+: a  | a :&: a
>            | Star a   | Eps      | Nil       | Atom Token

> step  ::  RE -> Token -> RE
> eps   ::  RE -> Bool
> rec   ::  RE -> [Token] -> Bool
> rep   ::  RE -> Nat -> Nat -> RE

The |step| function does Brzozowski differentiation, |eps|
answers if the expression contains the empty string, |rec|
answers if the word is recognised, and |rep p i j|
repeats a regular expression sequentially from |i| to |j| times.

We can now ask our system for variables satisfying:

> prop_repeat:  not (eps p) &&
>               rec s (rep p i j :&: rep p i' j') &&
>               not (rec (rep p (max i i') (min j j')) s)

whereupon we get the following counterexample in about 30 seconds:

% p:  (R(R(R__(T))(R__(T))(T))(R__(T))(T))
% i:  (Nat(Nat(Nat_)))
% i': (Nat(Nat(Nat_)))
% j:  (Nat(Nat(Nat_)))
% j': (Nat(Nat(Nat_)))
% s:  (List(T)(List(T)(List(T)_)))

\begin{verbatim}
p:  (Atom A :>: Atom A) :+: Atom A
i:  S (S Z)
i': S Z
j:  S (S Z)
j': S Z
s:  [A,A]
\end{verbatim}

This is a counterexample since
|rep p (max i i') (min j j')| = |rep p 2 1|, which recognizes
no string, but |rep p [A,A]| does hold.

We list our and LazySmallCheck's run times on
|prop_repeat| above and on two seemingly simpler
properties, namely:
\begin{code}
prop_conj:  not (eps p) && rec (p :&: (p :>: p)) s
prop_iter:  i /= j && not (eps p) && rec (iter i p :&: iter j p) s
\end{code}
The last property uses a function |iter :: Nat -> RE -> RE| which
repeats a regular expression a given number of times. The results are found
in Table \ref{regexptable}.
\begin{table}[]
\begin{center}
\textit{
\begin{tabular}{l r r }
\em Conjecture & \em Our tool & \em LazySC \\
\hline
|prop_conj|   & 27.2s &  0.6s \\
|prop_iter|   &  6.6s & 17.4s \\
|prop_repeat| & 35.7s & 103s  \\
\end{tabular}
}
\end{center}
\caption{Run times of finding counterexamples
to regular expression conjectures. The properties
are defined in Section \ref{regexp}.}
\label{regexptable}
\end{table}%
If we look more closely at the implementation of the regular expression library
we find that the calls are duplicated across the branches.
For instance, the |eps| function looks like this:
\begin{code}
eps Eps          = True
eps (p  :+:  q)  = eps p || eps q
eps (p  :&:  q)  = eps p && eps q
eps (p  :>:  q)  = eps p && eps q
eps (Star _)     = True
eps _            = False
\end{code}
Here, we could collapse all the calls |eps p| as described
in the section above, but it is actually enough to just
memoize them as they are exactly the same. (The same holds for |eps q|).
The recursive call structure of the |step| function follows
the same pattern as for |eps| and memoization is enough there as well.

% \begin{code}
% step  :: RE Token -> Token -> RE Token
% step  (Atom a)   x  = if a == x then Eps else Nil
% step  (p :+: q)  x  =  step p x :+:  step q x
% step  (p :&: q)  x  =  step p x :&:  step q x
% step  (p :>: q)  x  =  (step p x :>: q) :+:
%                        if eps p then step q x else Nil
% step  (Star p)   x  =  step p x :>: Star p
% step  _          x  = Nil
% \end{code}
%
% The previous code uses the predicate |eps :: R a -> Bool|
% which answers if a regular expression recognizes
% the empty string. We can now define the recognizer |rec|
% for an input word:
%
% \begin{code}
% rec :: RE Token -> [Token] -> Bool
% rec p []      = eps p
% rec p (x:xs)  = rec (step p x) xs
% \end{code}
%
% The first example we look at is
% relating conjunction of regular expressions |(:&:)|
% and sequential composition |(:>:)|:
%
% > not (eps p) && rec (p :&: (p :>: p)) s
%
% On this example, we get a counterexample after 28
% seconds, having explored the right part of the
% expression, but the list a little too far:
%
% \begin{verbatim}
% p: (R(R(R__(T))_(T))(R__(T))(T))
% s: (List(T)(List(T)(List(T)(List(T)_))))
%
% Counterexample!
% p: Star (Atom B) :>: Atom B
% s: Cons B (Cons B Nil)
% \end{verbatim}
%
% The second  property we looked at
% involves iterates a regular expression
% with |iter| a number of times:
%
% \begin{code}
% iter :: Nat -> R a -> R a
% iter Z     _ = Eps
% iter (S n) r = r :>: iter n r
% \end{code}
%
% The property is now is trying to find such an expression
% |p|, a word |s| and two numbers |i| and |j| such that:
%
% > i /= j && not (eps p) && rec (iter i p :&: iter j p) s
%
% On this example we explore this:
%
% \begin{verbatim}
% i: (Nat(Nat(Nat_)))
% j: (Nat(Nat(Nat_)))
% p: (R(R(R__(T))_(T))(R__(T))(T))
% s: (List(T)(List(T)(List(T)_)))
%
% Counterexample!
% i: S (S Z)
% j: S Z
% p: Star (Atom A) :>: Atom A
% s: Cons A (Cons A Nil)
% \end{verbatim}
%
% Given this:
%
% \begin{code}
% subtract1 :: Nat -> Nat
% subtract1 Z      = Z
% subtract1 (S x)  = x
%
% rep :: R T -> Nat -> Nat -> R T
% rep p i      (S j)  = (cond (isZero i) :+: p)
%                     :>: rep p (subtract1 i) j
% rep p Z      Z      = Eps
% rep p (S _)  Z      = Nil
% \end{code}
%
% Prove this:
%
% > not (eps p)  && rec (rep p i j :&: rep p i' j') s
% >              && not (rec (rep p (i `max` i') (j `min` j')))
%
% This is what we get:
%
% \begin{verbatim}
% p8: (R(R(R__(T))(R__(T))(T))(R__(T))(T))
% i0: (Nat(Nat(Nat_)))
% i': (Nat(Nat(Nat_)))
% j0: (Nat(Nat(Nat_)))
% j': (Nat(Nat(Nat_)))
% s: (List(T)(List(T)(List(T)_)))
%
% == Try solve with 74 waits ==
% Counterexample!
% p8: (Atom A :>: Atom A) :+: Atom A
% i0: S (S Z)
% i': S Z
% j0: S (S Z)
% j': S Z
% s: Cons A (Cons A Nil)
% \end{verbatim}

% \subsection{Ambiguity detection}
%
% Showing stuff, inverse.
%
% \subsection{Integration from Differentiation}
% Deriving expressions, inverse.

\subsection{Synthesising Turing machines}
\label{turing}

Another example we considered was a simulator
of Turing machines. The tape symbols are
either empty (|O|), or |A| or |B|:

> data A = O | A | B

The actions are either halting or moving
right or left and entering a new state represented with a |Nat|:

> data Action = Lft Nat | Rgt Nat | Stp

The machine is then a function from the state (a |Nat|), and
the symbol at the tape head |A|, to a symbol to be written
and a new head:

> type Q' = (Nat,A) -> (A,Action)

but we (currently) don't support functions, so we represent this
tabulated in a list instead:

> type Q      = [((Nat,A),(A,Action))]

A configuration of the machine is a state, and a zipper
of the tape head: the reversed list of the symbols to
the left, and the current symbol consed on to the symbols to the right:

> type Configuration  = (Nat,[A],[A])

The |step| function advances the machine one step, which
either terminates with the final tape, or
ends up in a  new configuration.

> step :: Q -> Configuration -> Either [A] Configuration

The |steps| function runs |step| repeatedly
until the machine terminates.

> steps  :: Q -> Configuration -> [A]

This function may of course not terminate, so
the translated functions needs to insert a |postpone|,
as described above.

The entire machine can be run from a starting
tape, by stepping it from the starting state |Zero| with |run|:

> run         :: Q -> [A] -> [A]
> run q tape  = steps q (Zero,[],tape)

We used our system to find Turing machines given a list of expected inserts the first symbol on the tape into the (sorted) rest of the symbols:

> run q [A]            == [A] &&
> run q [B,A,A,A,A,B]  == [A,A,A,A,B,B]

Asking to find such a |q|, we get this result in about thirty seconds:
\begin{code}
[  ((Succ Zero,         A),  (B,  Stp)),
   ((Succ (Succ Zero),  A),  (A,  Rgt (Succ (Succ Zero)))),
   ((Zero,              B),  (A,  Rgt (Succ (Succ Zero)))),
   ((Succ (Succ Zero),  B),  (B,  Lft (Succ Zero))),
   ((Zero,              A),  (A,  Stp)) ]
\end{code}
This machine contains a loop in state two, which is enters
upon reading an inital |B| (which is replaced with an |A|).
It then uses state two to skip by all the |A|s until
it comes to a |B|, where it backtracks, and replaces
the last |A| it found with a |B|. If the tape starts with
|A| the program terminates immediately.

In the above example we found by experimentation that
it was necessary to have no less than four A in the example,
otherwise it the returned machine would "cheat" and instead
of creating a loop, just count.

In this example it is crucial to use |postpone| to
be able to handle the possibly non-terminating |steps| function.
In systems like Reach \cite{reach}, it is possible
to limit the expansion of the program on the number of unrollings
of recursive functions. Our method with |postpone| does exactly
this, but there is no need to decide beforehand how many
unrollings are needed.
\comm{This dravel about postpone is repeated at too many places!}


% ------------------------------------------------------------------------------

% \section{Experimental evaluation}
%
% And again, there is the merge sort times.
%
% Regexp was evaluated against leon and
% lazy small check. leon timed out on all of them
%
% We evaluated the type checker against
% lazy small check with a timeout of 300s.
%
% Turing machines were evaluated...
% LSC timed out.

%
% Compare some examples against Leon.
%
% Compare some examples against Lazy SmallCheck.
%
% Compare with/without memoization and with/without merging function calls.
%
% Compare with/without conflict minimization?
%
% Show timings of the above examples.

% ------------------------------------------------------------------------------

\end{comment}

\section{Related Work}

One source of inspiration for this work is Leon\cite{leon},
which uses an encoding from functional programs to
uninterpreted functions in a SMT solver. Their focus is mainly
on proving properties (stated as contracts)
rather than finding counterexamples, which they see as a beneficial side effect.
Using uninterpreted
functions in a SMT solver helps to derive equivalences between values
that have not yet been fully expanded.
Leon has the plus that it can do "non-local" reasoning akin to
what we can sometimes achive through memoization. However,
they also allow pre- and post-connditions (which allows them to
prove propetries at the same time). To be able to do this reliably,
the prover really needs to have {\em names} for each thing, and
then congruence reasoning on top of that is really elegant.

Another similar tool to both Leon and ours is Smten\cite{smten}.
They also compile Haskell to a SAT/SMT-based query, given
functions that explain how the search space looks like.
One of their goals is, just like us, to enable SAT-based (and SMT-based)
search for users with little experience in the area.
They interpret the by syntactic transformations and simplifications
on the search space and the program together. This constructs a query
for the SMT solver. This enables them to do
symbolic if-then-else on programs.
They heuristically determine when computation does not seem to terminate: in this case they
can approximate the formula with a guard. This is a bit similar to
how we deal with incrementality.
By putting the design of the search space to the end
user, it is possible to get the same collapsing of
datatypes effect that we use.
This is the default in our work, as well as
collapsing function calls.
We also use the conflict clause to determine where to
expand the program.
They start expanding the program
and if they heuristically detect that it is long-running (by a timeout?) they
make some parts opaque, to be filled in later.
They don't seem to be using a conflict clause.
In this work, we try to make it very clear how to use the conflict clause
in a simple way to expand the program incrementally.

QuickCheck\cite{quickcheck} is an embedded DSL for finding
counterexamples for Haskell by using randomized testing.
A potential drawback of random testing is that one
has to write generators of random values suitable
for the domain. This becomes especially important in
the presence of preconditions, where the generator can
essentially become the inverse of the predicate.

One way to avoid the generator problem is to enumerate
input values for testing. This is the approach taken in
SmallCheck\cite{smallcheck} which
enumerates values on depth, and can also handle nested quantifiers.
Feat\cite{feat} instead enumerates values based on size.
Using size instead of depth as measure can sometimes be
beneficial as it grows slower, allowing for greater granularity.

By evaluating tagged undefined values (in a lazy language),
it can be observed which parts of the input are actually
demanded by the program. The forced parts of the value
can be refined with concrete values and then repeated.
This technique is called lazy narrowing, and is
used in Curry \cite{curry}, the theorem prover Agsy\cite{agsy}, and the systems Reach\cite{reach} and Lazy SmallCheck\cite{lazysc}.
The backtracking
techniques to stop exploring an unfruitful path
varies between different systems. Reach has two
modes, limiting the search space by predetermined
depth either of the input values or the function call recursion.
LazySmallCheck combines the ideas from SmallCheck and Reach to do lazy narrowing
on the depth of the values as a DSL in Haskell.

The evaluation section shows that LazySmallCheck is very effective:
and it is perhaps surprising that just laziness can be so powerful
to satisfy properties. (This relies on maximal use of parallal connectives, though).
LazySmallCheck is implemented as a library in Haskell, on just a few hundred lines or so.

Methods for finding models for SMT with quantified uninterpreted functions
exist \cite{GeMoura,ReyEtAl-CADE-13}.
When knowing what axioms are (recursive) function definitions
(as we assume), it is possible to unroll these incrementally to use the
techniques above \cite{cvc4models}
(assuming they are well-founded).

Finding models to uninterpreted functions in SMT-LIB
Looking at the problem as finding a model to recursive function
definitions in the presence of an assertion has been done \cite{cvc4models}.

The tool Target \cite{TypeTargetedTesting} uses an SMT solver
to exhaustively search for counterexamples written as
refinement types. This is a restricted format, but shows
that an SMT solver can prune off big parts of the search space.
One very interesting aspect of this work is that they use
an SMT solver to find data that satisfies the preconditions,
but then evaluate the program to see if the postconditions were met.
If not, we have a counterexample, if not, an axiom is laid down
to prevent the SMT solver to suggest the data again. And then the
process is repeated. So in a sense it is a hybrid approach.
Our approach is to do the evaluation of the program symbolically as well.
This can be benificial when the postcondition also constrains what
parts of the program can be expanded.

Finally, it should be noted that there are several libraries
to access SAT and SMT solvers in functional languages. Perhaps the most
well-known for Haskell is SBV\cite{sbv}.
However their |if-then-else| function |ite| is implemented by calling the
function |symbolcMerge| in the |Mergeable| typeclass, which throws an exception
if the constructors do not match up.

We use the function-call merging optimisation to reduce
exponential size of the SAT problem to linear in the number of calls.
This is similar to avoiding exponential blowup in the weakest-precondition
calculus \cite{Flanagan01avoidingexponential}. In particular, they
address the problem with sequenced non-deterministic choices, which
is similar to how |case|-constructs are non-deterministic in the symbolic
evaluation of our programs.

Another strand of related work is concolic execution: a combination of
concrete and symbolic execution (hence the name).
The idea is to evaluate the program on some random concrete value,
but while logging all the path conditions that led us there.
If there was no crash or assertion failure from this value,
a constraint solver - typically an SMT solver - tries to find an
assignment that makes some other path true. This enables such solvers
to explore relevant parts of the search space.
Traditionally, this has mainly been used for imperative programs,
in toos like PEX \cite{PEX2008}, KLEE \cite{KLEE2008} and SAGE (?).
This has been applied to functional programming, in particular
Erlang\cite{ConcTestingFP2015}, but lacks a thorough evaluation.
\comm{What to write about this?}

\comm{Missing:

HO stuff

Constraint programming

Liquid types. HALO. (and other contracts checkers)

EasyCheck (Curry enumeration)

Catch
}

% ------------------------------------------------------------------------------

\section{Discussion and Future Work}

In the beginning of the paper, we made three assumptions about the language we are dealing with: (1) programs terminate, (2) programs don't crash, and (3) programs are first-order. We managed to lift restriction (1) by means of using |postpone|, as explained in Section \ref{postpone}. For possibly non-terminating programs, the semantics of our language is lazy, and our counter examples are sound w.r.t. partial correctness.

Restriction (2) can be lifted also, but this is not shown in the paper. We can introduce an
extra constructor to each data type that corresponds to a program crash. Every case should
propagate program crashes. If we employ this technique, it will be possible to ask
for values yielding crashes instead of returning |True| or |False|.

Restriction (3) can also be lifted. Already we can translate higher-order functions, by simply calling argument functions when they are applied. We can also synthesize functions if we represent them as a look-up table. The Turing machine example from the previous section shows the feasibility of this approach.
Systematically, the values of a higher
order function in our setting would be a datatype that is either a lookup table plus a default
value, or a closure of a concrete function occurring in the program.

We first sketched out a translation based on \ifthenelse{} in Section \ref{ite},
but abandoned it for using |>>>| to be able to make incremental |new| (in Section \ref{dsl}.
It is our current belief after working with this for some time that it is
not possible to implement incrementality in the \ifthenelse{} setting.

In the Reach\cite{reach} setting, it is possible to annotate a target
expression. We think this is a very convenient way of specifying all kinds of properties, and
want to incorporate this feature in our tool as well.

Currently, we rely on the user to manually annotate function calls and
data constructor arguments to be merged, and explicitly say
which function calls to memoize. This burden should be removed
by appropriate default and automatic heuristics.

One interesting step is to incorporate integer reasoning from SMT
solvers. We have already done this in one of our prototype implementations.
However, it is unclear what should happen when performing recursion over such integers.
Any function doing this, even if it is structurally recursive, would need to be guarded
by an occurrence of |postpone|, otherwise the constraint generation may not terminate.
It would also be interesting to see what our gain could be from other theories, in particular those for
equality and uninterpreted functions.

% ------------------------------------------------------------------------------

\section{Conclusions}

We have decided to tackle a hard problem (finding program inputs that lead to certain program outputs) in a new way (using a SAT-solver) and a new setting (functional programs with algebraic datatypes). The first remark we can make is that it is surprising that it can be done at all: we can generate constraints about general high-level programs, in terms of a logic for a finite number of binary choices, in a sound and complete way.

We use the conflict set of the SAT-solver to decide how to expand the input incrementally until a suitable input is found. Our experiments have shown that this actually works rather well, very often just the right constructors are chosen. We also apply memoization and function call merging to battle exponential blow-up, and have experimentally shown that both of these have a positive effect, with function call merging being vital for certain problems to even succeed.

Our method works well for cases where the generation of the SAT-problem does not blow up. It can outperform other methods in cases where one gains something from the extra combinatorial search power. The method does not work well when the input expansion chooses the wrong thing to expand, or when the expansion needs too many steps to reach the correct input shape. We have not encountered any problem that turned out to be too hard for the SAT-solver itself; most SAT calls terminate almost immediately (even for large problems), and very few calls take more than, say, a second.

\paragraph{Acknowledgements} We thank anonymous reviewers for helpful feedback on an earlier version of this article.

% ------------------------------------------------------------------------------

%\appendix
%\section{Appendix Title}

% We recommend abbrvnat bibliography style.

%\bibliographystyle{abbrvnat}
\bibliographystyle{plain}
\bibliography{Paper}

% The bibliography should be embedded for final submission.

%\begin{thebibliography}{}
%\softraggedright

%\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
%P. Q. Smith, and X. Y. Jones. ...reference text...

%\end{thebibliography}


\end{document}

