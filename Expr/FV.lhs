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

\section{Semantics Extension}
\label{sec:semanticsextension}

Our approach allows the users to define alternative semantics or
extending already defined ones in a simple and modular way. For
instance suppose that we want to collect the free variables (i.e. all
variables, there are no binders in our expression language) occuring
in an expression, in the order they occur (they can occur many times,
appearing many times in the result).

Let us define this new interpretation in a new module called {\tt
  Expr.FV}. It depends on the {\tt Expr.Syn} module but it is
completely independent of the {\tt Expr.Eval } module.


%if False

> module Expr.FV where

> import Expr.Syn
> import Language.Grammars.AspectAG
> import Data.List

%endif

Now, let us define an attribute to collect the variables:

> fv = Label @ ('Att "fv" [String])

We define the aspect with the rules to compute |fv|:

> asp_fv  =
>        syndefM fv p_Add ((++) <$> at ch_Add_l fv <*> at ch_Add_r fv)
>   .+:  syndefM fv p_Var ((:[]) <$> ter ch_Var_var)
>   .+:  syndefM fv p_Val (pure [])
>   .+:  emptyAspect

In this case we defined and combined all rules in the same
expression. In the |p_Add| production we concatenate variables
occuring in each child. In the |p_Var| expression we obtain the
terminal representing the variable and wrap it in a singleton list. In
the case of the |p_Val| production we simply return the empty list.


Again, we can implement a traverse to collec all free variables of an
expression applying the defined aspect to the semantic funcion:

> freeVars e = sem_Expr asp_fv e emptyAtt #. fv

[otra sección?]
We can also modify semantics in a modular way. Suppose that, instead
of collecting all variable occurences, we only want to collect the
first one (i.e. get all occuring variables in their occuring order).
We can take the |asp_fv| aspect and modify the rule for
the |p_Add| expression as follows:

> asp_fv' =
>        synmodM fv p_Add (Data.List.union <$> at ch_l fv <*> at ch_r fv)
>   .+:  asp_fv

Note that this redefinition of the semantics can be defined in a new
module (in this case depending on {\tt Expr.Sem} since |asp_fv| must
be imported) with no need to recompile the original one.
