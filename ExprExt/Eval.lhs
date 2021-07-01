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

%if False

> module ExprExt.Eval where
> import ExprExt.Syn
> import Expr.Syn hiding (Expr(..),sem_Expr)
> import Expr.Eval
> import Data.Map as M
> import Language.Grammars.AspectAG

%endif

We finish the declaration here. Now its time to add semantics to the
extended language. The following code is part of a new module {\tt
  ExprExt.Eval}. We extend the evaluation semantics for function
calls. There is no way to define functions yet, so assume that there
is a set of known builtin functions. It makes sense to make them
avaiable in an environment at a given scope, so it could be extended
with new definitions in a future extension.

To minimize the complexity of the running example we keep it simple
here. Consider an environment of functions named by Strings. We use a
call by value regime, so functions compute integers from integers.

Let us define an inherited attribute to pass this environment:

> fenv = Label @ ('Att "fenv" (M.Map String (Integer -> Integer)))

We must pass this environment from parents to children in each non
terminal. For instance we can implement the rule for the left argument
of the sum as:

< add_fenv_l = inhdefM fenv p_Add ch_Add_l (at lhs env)

Note that this is almost the same definition as in |add_env_l| in
section \ref{sec:semanticsdefinition}.  We are only passing the
attribute untouched from the parent to the children. One big advantage
of use the AG System as an EDSL is that we could abstract this easily
as a Haskell function, and then build a rule such that for any
argument given. We can for instance, build a function that given an
attribute, builds an aspect with rules that copy that attribute in
each recursive definition. Even more, we could do that and use
|inhmodM| exactly in that special production where the environment is
touched. We will see examples in our case study.  We must also note
that this pattern -passing information from top-down untouched- is
very common when deveoloping using Attribute Grammars: they are called
copy rules in the literature. The \AspectAG library has a builtin
construct |copyAtChi| that builds the copy rule given an attribute and
a child. It also adds an implicit |traceRule| application to have
readable type errors later.

Then, we can define the rules to copy the environment in the following
way:

> add_fenv_l = copyAtChi fenv ch_Add_l
> add_fenv_r = copyAtChi fenv ch_Add_r

For the new production |p_Call|, we also need to copy the environment
in the function argument child.

> add_fenv_arg = copyAtChi fenv ch_Call_arg

We also need to define rules for the previously defined attributes
|eval| and |env| in the new production. Let us combine both rules at
once with the |(.+.)| operator, that combines a pair of rules for a
given production.

> call_evalenv_arg =
>   copyAtChi env ch_Call_arg .+.
>   (syndefM eval p_Call (
>    do fe    <- at lhs fenv
>       fn    <- ter ch_Call_fun
>       argv  <- at ch_Call_arg eval
>       case M.lookup fn fe of
>         Just f   -> return (f argv)
>   ))

For the |env| attribute we use a copy rule. To compute the value of
the |eval| attribute we get the inherited function environment, and
the function name (that is a terminal). We look at the synthesized
|eval| attribute at the argument children and apply the
function. Again we do not care about undefined functions for now.


Finally we can write the new evaluator for the expression language as:

> type FEnv = M.Map String (Integer -> Integer)
> evaluator :: Expr -> (Env, FEnv) -> Integer
> evaluator exp (envi, fenvi) =
>   sem_Expr asp_sem' exp (env =. envi *. fenv =. fenvi *. emptyAtt) #. eval
>   where
>     asp_sem'  =    add_fenv_l
>               .+:  add_fenv_r
>               .+:  add_fenv_arg
>               .+:  call_evalenv_arg
>               .+:  asp_sem


%if False

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

> sem_Expr asp (Call f e) =
>  knitAspect p_Call asp  $   ch_Call_fun .=. sem_Lit f
>                         .*. ch_Call_arg .=. sem_Expr asp e
>                         .*. emptyGenRec

%endif
