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


> module MF.Expr.Compile where
> import MF.Expr.Syn
> import ExprExt.Syn

> import Expr.Syn hiding
>  (ch_Val_val, P_Val, Expr(..), p_Val, sem_Expr_Var, sem_Expr_Val)

> import MF.Core.Syn hiding (p_Var, p_Val)
> import Language.Grammars.AspectAG
> import Data.Proxy 

> import MF.Terminals

Compile Expressions to core language

> scomp :: forall v op . Values op v => Label ('Att "compile" (CTerm op v))
> scomp = Label

> scomp_var = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_Var (CVar <$> ter ch_Var_var)

> scomp_val = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_Val (CVal
>     <$> ter (ch_Val_val :: Label ('Chi "Val_val" P_Val ('Right ('T v)))))

> scomp_op = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_Op (COp <$> at ch_Op_l (scomp @ v)
>     <*> ter (ch_Op_op :: Label ('Chi "Op_op" P_Op ('Right ('T (Val2Op v)))))
>                             <*> at ch_Op_r (scomp @ v))

> scomp_call = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_Call ( do
>     f    <- ter ch_Call_fun
>     carg <- at ch_Call_arg (scomp @ v)
>     return $ CApp (CVar f) carg
>   )


 3 + dup x

> proxyVal = Proxy @Val
> test1 = sem_Expr_Op (scomp_op proxyVal) (sem_Expr_Val (scomp_val proxyVal) (I 3))
>          MF.Terminals.Add
>         (sem_Expr_Call (scomp_call proxyVal) "dup"
>                  (sem_Expr_Var (scomp_var proxyVal) "x")) emptyAtt #. (scomp @Val)



inherited, to test: like compilation, but in each litera leaf we put
the length of the path from the root to it.

> stest :: forall v op . Values op v => Label ('Att "stest" (CTerm op v))
> stest = Label

> itest :: Label ('Att "itest" Integer)
> itest = Label

> stest_var = \(Proxy :: Proxy v) ->
>   syn (stest @ v) p_Var (CVal . I <$> at lhs itest)

> stest_val = \(Proxy :: Proxy v) ->
>   syn (stest @ v) p_Val (CVal . I <$> at lhs itest)

> stest_op = \(Proxy :: Proxy v) ->
>   (syn (stest @ v) p_Op (COp <$> at ch_Op_l (stest @ v)
>     <*> ter (ch_Op_op :: Label ('Chi "Op_op" P_Op ('Right ('T (Val2Op v)))))
>                             <*> at ch_Op_r (stest @ v))
>   ) .+.
>   (inh itest p_Op ch_Op_l ((+1) <$> at lhs itest))
>     .+.
>   (inh itest p_Op ch_Op_r ((+1) <$> at lhs itest))

> stest_call = \(Proxy :: Proxy v) ->
>   syn (stest @ v) p_Call ( do
>     return $ CVal $ I 0
>   )
