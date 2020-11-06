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

> module Sem where
> import AST
> import Language.Grammars.AspectAG

> eval :: Label ('Att "eval" Int); eval = Label
> env  :: Label ('Att "env" [(String, Int)]); env = Label


> add_eval  =
>   syndefM eval p_Add $
>   (+) <$> at ch_l eval <*> at ch_r eval

> val_eval  =
>   syndefM eval p_Val $ ter @Int ch_val

> var_eval  =
>   syndefM eval p_Var (
>   do env  <- at lhs env
>      x    <- ter ch_var
>      case Prelude.lookup x env of
>        Just e -> return e
>   )

> add_env_l =
>   inhdefM env p_Add ch_l (at lhs env)

> add_env_r =
>   inhdefM env p_Add ch_r (at lhs env)

> asp_eval = add_eval .+: val_eval .+: var_eval
>            .+: add_env_l .+: add_env_r .+: emptyAspect

> evaluator :: Expr -> [(String,Int)] -> Int
> evaluator exp envi
>  = sem_Expr asp_eval exp (env =. envi *. emptyAtt) #. eval


3 + x, deforestated

> asp_eval' = add_eval .+: val_eval
>            .+: add_env_l .+: add_env_r .+: emptyAspect

> vl e v = sem_Expr_Val asp_eval' v (env =. e *. emptyAtt) #. eval 

 > vr = sem_Expr_Var asp_eval
 > add = sem_Expr_Add asp_eval

 > e1 = vl 3 `add` vr "x"
