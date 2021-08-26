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
>              TypeOperators, DatatypeContexts, FunctionalDependencies
> #-}

%endif

> module MF.Core.Eval where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> import Data.Proxy
> import MF.Core.Syn

> import Data.Map as M
> import Data.Ord

> import MF.Terminals.Values

Let us build substitutions

Our goal is to get a program with the following type

< subst :: String -> CTerm op v -> CTerm op v -> CTerm op v 
             var     term to put    term to transf  result


 > asp_core_env att =
 >       copyAtChi att ch_COp_l
 >  .+:  copyAtChi att ch_COp_r
 >  .+:  copyAtChi att ch_CComp_l
 >  .+:  copyAtChi att ch_CComp_r
 >  .+:  copyAtChi att ch_CLam_body
 >  .+:  copyAtChi att ch_CApp_l
 >  .+:  copyAtChi att ch_CApp_r
 >  .+:  emptyRuleAtPrd p_CVar
 >  .+:  emptyRuleAtPrd p_CVal
 >  .+:  emptyAspect
 
> asp_core_env att =
>       inhdefM att p_COp   ch_COp_l (at lhs att)
>  .+:  inhdefM att p_COp   ch_COp_r (at lhs att)
>  .+:  inhdefM att p_CComp ch_CComp_l (at lhs att)
>  .+:  inhdefM att p_CComp ch_CComp_r (at lhs att)
>  .+:  inhdefM att p_CLam  ch_CLam_body (at lhs att)
>  .+:  inhdefM att p_CApp  ch_CApp_l (at lhs att)
>  .+:  inhdefM att p_CApp  ch_CApp_r (at lhs att)
>  .+:  emptyRuleAtPrd p_CVar
>  .+:  emptyRuleAtPrd p_CVal
>  .+:  emptyAspect

> asp_core_env' att =
>       inhdefM att p_COp   ch_COp_l (at lhs att)
>  .+:  inhdefM att p_COp   ch_COp_r (at lhs att)
>  .+:  inhdefM att p_CComp ch_CComp_l (at lhs att)
>  .+:  inhdefM att p_CComp ch_CComp_r (at lhs att)
>  .+:  inhdefM att p_CApp  ch_CApp_l (at lhs att)
>  .+:  inhdefM att p_CApp  ch_CApp_r (at lhs att)
>  .+:  emptyRuleAtPrd p_CVar
>  .+:  emptyRuleAtPrd p_CVal
>  .+:  emptyAspect


> ivar = Label @('Att "ivar" String)
> asp_ivar = asp_core_env ivar

> isubst :: forall v op . Values op v => Label ('Att "isubst" (Maybe (CTerm op v)))
> isubst = Label
> asp_isubst = \(Proxy :: Proxy v) ->
>   inhdefM (isubst @ v) p_CLam ch_CLam_body (
>   do t <- at lhs (isubst @v)
>      x <- ter ch_CLam_binder
>      x' <- at lhs ivar
>      if x == x' then return Nothing else return t
>    )
>    .+: asp_core_env' (isubst @v)

> asp_subst =
>   synmodM (self @Val) p_CVar (
>    do x   <- at lhs ivar
>       x'  <- ter ch_CVar_var
>       t   <- at lhs (isubst @Val)--
>       case t of
>         Nothing  -> return (CVar x')
>         Just t'  ->
>           if x == x' then return t' else return (CVar x')
>     )
>    .+: asp_core_id (Proxy @Val)


> subst :: String -> CTerm Op Val -> CTerm Op Val -> CTerm Op Val
> subst x t e = sem_CTerm (asp_ivar .:+: asp_subst .:+: asp_isubst (Proxy @Val))
>    e (ivar .=. x .*. isubst .=. Just t .*. emptyAtt) #. (self @Val)


> fenv :: forall v op . Label ('Att "fenv" (M.Map String (CTerm op v)))
> fenv = Label

> asp_core_fenv = \(Proxy :: Proxy v) -> asp_core_env (fenv @v)

> redu :: forall v op. Values op v => Label ('Att "redu" (CTerm op v))
> redu = Label

> asp_redu = \(Proxy :: Proxy v) ->
>       syn (redu @ v) p_CVal  (CVal <$>  ter  ch_CVal_val)
>  .+:  syn (redu @ v) p_CVar  (CVar <$>  ter  ch_CVar_var)
>  .+:  syn (redu @ v) p_CLam  (CLam <$>  ter  ch_CLam_binder
>                                    <*>  at   ch_CLam_body (redu @v))
>  .+:  syn (redu @ v) p_CApp ( do
>       l   <- at ch_CApp_l (self @ v)
>       l'  <- at ch_CApp_l (redu @ v)
>       r   <- at ch_CApp_r (self @ v)
>       fe  <- at lhs (fenv @ v)
>       case l of
>         CLam x t -> return $ subst x r t
>         CVar x   -> case M.lookup x fe of
>                       Just f  -> return $ CApp f r
>                       Nothing -> return $ CApp l r
>         _        -> return $ CApp l' r --  introduces a bug
>      )
>  .+: syn (redu @ v) p_COp ( do
>       l  <- at ch_COp_l (redu @v)
>       r  <- at ch_COp_r (redu @v)
>       op <- ter ch_COp_op
>       case (l, r) of
>         (CVal l', CVal r') -> return (CVal $ ap op l' r')
>         (l,r) -> return $ COp l op r
>      )
>  .+: syn (redu @ v) p_CComp ( do
>       l  <- at ch_CComp_l (redu @v)
>       r  <- at ch_CComp_r (redu @v)
>       op <- ter ch_CComp_op
>       case (l, r) of
>         (CVal l', CVal r') ->
>           case (cmp op l') r' of
>             True  -> return (CLam "T" (CLam "F" (CVar "T")))
>             False -> return (CLam "T" (CLam "F" (CVar "F")))
>         _ -> return (CComp l op r)
>   )
>  .+: emptyAspect


> step :: M.Map String (CTerm Op Val) -> CTerm Op Val -> CTerm Op Val
> step funs expr = sem_CTerm
>       (asp_redu (Proxy @Val) .:+:
>        asp_core_fenv (Proxy @Val) .:+:
>        asp_core_id (Proxy @Val)
>       ) expr (fenv .=. funs .*. emptyAtt) #. (redu @Val)

> steps 0 e ex = ex
> steps n e ex = steps (n-1) e (step e ex)


> reduce :: M.Map String (CTerm Op Val) -> CTerm Op Val -> CTerm Op Val
> reduce e ex =
>   let ex' = step e ex
>   in if ex == ex' then ex else reduce e ex'
> reduceNC = reduce $ fromList []


