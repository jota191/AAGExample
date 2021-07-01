
\section{Grammar specification}
\label{sec:grammarspecification}

The abstract syntax of our expression language is given by the
following grammar:

<  expr    ->  Int_val
<  expr    ->  String_var
<  expr    ->  expr_l + expr_r

\noindent
where |Int| and |String| are terminals corresponding to integer values
and variable names, respectively. Both are said to be \emph{children}
in their productions.  In the third production there are two children
|expr_l| and |expr_r|, both occurrences of the non-terminal
|expr|. They have different names (the indexes l and r) so that we can
refer to each one unambiguously.


\subsection{Grammar implementation in AspectAG}

We declare the syntax of the expression language in the {\tt Expr.Syn}
module. As in every Haskell module part of a bigger system we must
declare the module giving it a name, and a list of module imports (at
least the \AspectAG library modules in this case). Usually the user
also declares a set of pragmas, like the set of extensions to use.

%if False

> {-# LANGUAGE TypeFamilies, FlexibleContexts, ScopedTypeVariables,
>              NoMonomorphismRestriction, ImplicitParams, ExtendedDefaultRules,
>              UnicodeSyntax, DataKinds, TypeApplications, PartialTypeSignatures,
>              AllowAmbiguousTypes, RankNTypes, ScopedTypeVariables,
>              TypeSynonymInstances, FlexibleInstances, TemplateHaskell,
>              MultiParamTypeClasses, TypeOperators
> #-}

> module Expr.Syn where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> import Data.Proxy -- ocultar, should be exported by AspectAG

%endif

From now on we will omit module declarations. Module dependencies are
showed in [TODO: un grafo de dependencia de modulos en algún lugar
  estaría bien, anexo? sobre todo en Matefun es necesario, porque son
  un montón]


The {\tt Language.Grammars.AspectAG} module contains all the
constructs of our EDSL. The {\tt Language.Grammars.AspectAG} module
contains some useful Template Haskell
\cite{Sheard:2002:TMH:636517.636528} utilities to generate some
boilerplate for us. It is relevant to note that \AspectAG can be used
alone with no Template Haskell requirement. \AspectAG modules can be
plain Haskell modules with no preprocessing.

To declare a grammar in \AspectAG we need to declare all the
ingredients: terminals, nonterminals, productions and children. Since
our goal is to use all this information in compile time, the
information will live in types. At value level, all this objects are
trivial, used only to be passed as arguments. In our EDSL they are of
type |Label|, which is similar to the well known |Proxy| type.

In \AspectAG the grammar specified in section
\ref{sec:grammarspecification} is declared as follows.  First, we
declare the non-terminal for expressions:

> type Nt_Expr = 'NT "Expr"
> nt_Expr = Label @ Nt_Expr


Non-terminals are defined by introducing a name (like |"Expr"|) at the
type level by using a promoted string literal (which has kind
|Symbol|). We use the \texttt{TypeApplications} extension of GHC to
associate the type information to the label. We will make extensive
use of this extension. Productions are also identified by a name and
they are related to a non-terminal, the one at the Left hand side.


> type P_Val  = 'Prd "Val" Nt_Expr
> p_Val       = Label @ P_Val
> type P_Var  = 'Prd "Var" Nt_Expr
> p_Var       = Label @ P_Var
> type P_Add  = 'Prd "Add" Nt_Expr
> p_Add       = Label @ P_Add

The last ingredient of the grammar declaration is given by the
introduction of the children that occur in the productions.

> ch_Add_l    = Label  @ ('Chi "Add_l"    P_Add (NonTerminal  Nt_Expr))
> ch_Add_r    = Label  @ ('Chi "Add_r"    P_Add (NonTerminal  Nt_Expr))
> ch_Val_val  = Label  @ ('Chi "Val_val"  P_Val (Terminal     Integer))
> ch_Var_var  = Label  @ ('Chi "Var_var"  P_Var (Terminal     [Char]))

Each child has a name, is tied to a production and can be either a
non-terminal or a terminal. in the latter case we include the type of
values it denotes


\subsection{Embedding actual terms}

Summing up the information just provided, we can see that our grammar
declaration indirectly contains all the information that take part in
the Haskell datatype representation of its abstract syntax tree:

> data Expr
>  = Add {l :: Expr, r :: Expr} |
>    Var {var :: String} |
>    Val {val :: Integer}
>     deriving (Show, Eq, Read)

By defining this datatype we have a way to deep embedd terms of the
expression language in Haskell. Then we can consume these trees
according to some semantics specification. There is yet no relation
between labels previously defined and the datatype |Expr|. This
relation is given by the semantic functions. The following piece of
code correspond to the semantic function for the expression language:


> sem_Expr asp (Add l r)
>  = knitAspect p_Add asp  $    ch_Add_l .=. sem_Expr asp l
>                          .*.  ch_Add_r .=. sem_Expr asp r
>                          .*.  emptyGenRec
> sem_Expr asp (Var var)
>  = knitAspect p_Var asp   $   ch_Var_var .=. sem_Lit var
>                           .*.  emptyGenRec
> sem_Expr asp (Val val)
>  = knitAspect p_Val asp   $   ch_Val_val .=. sem_Lit val
>                           .*.  emptyGenRec


The semantic function takes an \emph{aspect} |asp| (the semantics
definition) and an expression represented by a tree of type |Expr| and
builds a function from Attributions (inherited attributes, and
environment) to Attributions (synthesized attributes, the
computation). It is not explicit from the definition that a function
is actually built, to understand it, consider that |knitAspect| takes
four arguments. Details of how |knitAspect| is implemented are given
in section [REF], but the relation between labels defined with
\AspectAG constructs and the specified grammar (and the |Expr|
datatype) are now explicit. For instance, in the first clause, where
we are consuming an addition, we say that it corresponds to the
|p_Add| production (in the first argument of |knitAspect|), and that
|l| and |r| correspond to |ch_l| and |ch_r| and that they will be be
processed recursively with the same semantic function.

The grammar definition is now complete. If the user prefers, there is
a way to define it in a way more similar to a EBNF notation. All the
previous code as it is can be generated by template Haskell splices.
Template Haskell splices are special expressions that evaluates at
compile time to generate Haskell source code at that point of the
program.

For the labels:

< (addNont "Expr")
< (addProd "Val" ''NtExpr  [  ("val",  Ter     ''Integer)])
< (addProd "Var" ''NtExpr  [  ("var",  Ter     ''String)])
< (addProd "Add" ''NtExpr  [  ("l",    NonTer  ''NtExpr),
<                             ("r",    NonTer  ''NtExpr)])


To derive the |Expr| datatype and the semantic functions, we can use
respectively:

< (closeNT NtExpr)
< (mkSemFunc NtExpr)

To extend the definition of the grammar in \AspectAG adding new
productions we can add suitable labels. This can be even in a new
module as we will do in section [REF] in the module {\tt ASTExt}. But
this approach has an issue. The grammar as a collection of labels is
open, but when we build a Haskell data type such as |Expr|, since
Haskell data types are closed, there is no way to extend it.


The solution we present in \cite{iflaag} is to make an updated
``copy'' of |Expr| and |sem_Expr| in {\tt ASTExt} with the new
constructors or, by hand or by calling the |closeNT| and |mkSemFunc|
splices there. Using qualified names there is no ambiguity: |AST.Expr|
is the datatype for the original grammar. |ASTExt.Expr| is the
extended datatype.

This duplication is not nice. Someone could argue that our approach to
tackle the expression problem is avoiding recompilation by actually
rewriting the compiled code. This is partially true, but still this
approach has something to give us. Firstly, semantics definitions will
be reusable for both versions of the grammar. As we shall see later in
section [REF] rules to compute aspects are tied (by their type) to a
production. They can be used in any grammar where that production
exists. Secondly, using Template Haskell splices this duplication is
hidden to the programmer, offering a solution similar to libraries
like uuagc \cite{uuagc}.

Still, we can push in this direction, as we will see in the next
section.

\subsection{A deforestated approach}

To avoid the code duplication that we discussed above, there are some
solutions. One is to use actual extensble algebraic datatypes. Vanilla
Haskell does not support them, but there are ways to mimmick them
[REF, REF]. Unfortunately these encodings are heavyweight, generating
complex types. \AspectAG is already implemented using advanced type
level programming, adding more complexity to types does not seems to
be wise.

The alternative is not to use datatypes at all, building terms of the
expression language using a shallow embedding. The semantic function
|sem_Expr| is defined as a traversal over the abstract syntax tree
tying the \AspectAG constructs to the datatype. It is a general
interpreter parametrised on the semantics |asp|. Using a shallow
embedding we can define expressions directly in terms of semantic
functions.

First, consider the following alternative semantic functions
definition:

> sem_Expr_Add' asp sl sr =
>  knitAspect p_Add asp $
>  ch_Add_l   .=. sl  .*.
>  ch_Add_r  .=. sr  .*. emptyGenRec

> sem_Expr_Val' asp val =
>   knitAspect p_Val asp $
>   ch_Val_val  .=. sem_Lit @Integer val .*. emptyGenRec

> sem_Expr_Var' asp var =
>   knitAspect p_Var asp $
>   ch_Var_var  .=. sem_Lit @String var .*. emptyGenRec

Instead of pattern matching over |Expr|, we define a function for each
production. Nonterminal subexpressions like in the |sem_Expr_Add|
function are given themselves as semantic functions. 

The expression {\tt 4 + x} that was expressed as
|Add (Val 4)(Var "x")| before can be now implemented as:

< e = \asp -> sem_Expr_Add' asp  (sem_Expr_Val' asp 4)
<                                (sem_Expr_Var' asp "x")

Now, to add a new production to our expression language we can add the
suitable labels and the new semantic function. Even if |e| was
precompiled and the new production was defined in another module, |e|
is an expression of the extended language.

Perhaps the reader is worried about the verbosity of the new
representation for terms. We can hide the argument |asp| with a reader
monad, or use a fixed one when we are working with concrete
semantics. We can then build smart constructors to actually write the
term in a readable way such as |add (vl 4)(vr "x")|.

Unfortunately, when implementing \emph{embedded} languages using
\AspectAG there is a subtle flaw with this approach. It is not
unavoidable, but it requires a lot of implementation work. We will
discuss this in [ref to implementation].


%if False

> sem_Expr_Add asp sl sr =
>  knit Proxy asp $
>  ch_Add_l  .=. sl  .*.
>  ch_Add_r  .=. sr  .*. emptyGenRec

> sem_Expr_Val asp val =
>   knit Proxy asp $
>   ch_Val_val  .=. sem_Lit @Integer val .*. emptyGenRec

> sem_Expr_Var asp var =
>   knit Proxy asp $
>   ch_Var_var  .=. sem_Lit @String var .*. emptyGenRec

%endif
