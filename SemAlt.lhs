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

\section{Semantic Extension: Adding and Modifying attributes}

Our approach allows the users to define alternative semantics or
extending already defined ones in a simple and modular way. This can
be done without modifying previous modules and without recompiling
them. In this section we show how this can be done.

Let us define a new module {\tt SemAlt}.

> module SemAlt where

And let us include the \AspectAG library.

> import Language.Grammars.AspectAG

And our previously defined grammar:

> import AST

We do not include the {\tt Sem} module since we will define orthogonal
semantics here.

Instead of implementing operational semantics here, what we want to do
is to collect all the occurences of free variables in an expression,
from left to right. We define an attribute |vars| for that purpose.


> vars = Label @ ('Att "vars" [String])

Now, let us define the aspect |asp_vars| to compute the |vars| attribute:

> asp_vars
>   =    syn vars p_Add ((++) <$> at ch_l vars <*> at ch_r vars)
>   .+:  syn vars p_Val (pure [])
>   .+:  syn vars p_Var ((:[]) <$> ter ch_var)
>   .+:  emptyAspect

This time we combined all rules on the fly. We used the |syn|
combinator that is an alias to |syndefM|. To materialize this
semantics definition in a haskell function we can define the
|freeVars| function as follows:

> freeVars e = sem_Expr asp_vars e emptyAtt #. vars

Note that we are using the "forestated" approach here.
