%if False

> {-# LANGUAGE
>              TypeFamilies,
>              FlexibleContexts,
>              ScopedTypeVariables,
>              NoMonomorphismRestriction,
>              ImplicitParams,
>              ExtendedDefaultRules,
>              UnicodeSyntax,
>              DataKinds,
>              TypeApplications,
>              PartialTypeSignatures,
>              AllowAmbiguousTypes,
>              RankNTypes,
>              ScopedTypeVariables,
>              TypeSynonymInstances,
>              FlexibleInstances,
>              TemplateHaskell,
>              MultiParamTypeClasses,
>              TypeOperators
> #-}

%endif

\section{Syntactic Extension}
\label{sec:syntacticextension}

In the previous section we showed how to extend a language with new
semantics in \AspectAG, but that is not a great accomplishment since
the host language is already purely functional.

Now we show how the user of the library can extend the syntax of the
language. Suppose that we want to add a new syntactic construct:
funtion calls. We add a new production to the expression language:

|expr -> fname(expr)|

An expression can be a function application, consisting in a function
name and an argument expression. We implement this
in a new module {\tt ExprExt.Syn}.

%if False

> module ExprExt.Syn where
> import Expr.Syn hiding (Expr(..),sem_Expr)
> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

%endif

We declare the required labels as follows:

> type P_Call  = 'Prd "Call" Nt_Expr
> p_Call       = Label @ P_Call
> ch_Call_fun  = Label @ ('Chi "Call_fun" P_Call (Terminal String))
> ch_Call_arg  = Label @ ('Chi "Call_arg" P_Call (NonTerminal Nt_Expr))

We add a production label |p_Call|. The |"Call"| production is a
rewrite rule for the non terminal |Nt_Expr|. It has two children.  The
|ch_Call_fun| child is a terminal of type |String|, representing the
name of the applyed function. The |ch_Call_arg| child is a non
terminal, the argument expression.

Recall that we can add the production using the Template Haskell
splices:

< $(addProd "Call" ''Nt_Expr  [ ("fun",  Ter ''String),
<                               ("arg",  NonTer ''Nt_Expr)])

We can also reify the grammar in scope as a Haskell data type using a
splice with |closeNT|, and generate the semantic functions with a
splice with |mksemFunc|.

< (closeNT ''NtExpr)
< (mkSemFunc ''NtExpr)

The derived data type is a new copy of the |Expr.Syn.Expr| data type,
with the new constructor.

> data Expr
>  = Add   {l :: Expr, r :: Expr} |
>    Var   {var :: String}  |
>    Val   {val :: Integer} |
>    Call  {fun :: String, arg :: Expr}
>     deriving (Show, Eq, Read)

