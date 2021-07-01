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

> module MF.Core.PP where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> import Data.Proxy
> import MF.Core.Syn
> import MF.Core.Eval -- test

> import Data.Map as M
> import Data.Ord

> import MF.Terminals

> spp = Label @('Att "spp" String)
> asp_spp = \(Proxy :: Proxy v) -> 
>        syn spp p_CVal (show @v <$> ter ch_CVal_val)
>   .+:  syn spp p_CVar (ter ch_CVar_var)
>   .+:  syn spp p_CLam ( do
>          x <- ter ch_CLam_binder
>          t <- at ch_CLam_body spp
>          return $ "λ " ++ x ++ " → " ++ t
>        )
>   .+: syn spp p_CApp ( do
>          l <- at ch_CApp_l spp
>          r <- at ch_CApp_r spp
>          return $ "" ++ l ++ "(" ++ r ++")"
>        )
>   .+: syn spp p_COp ( do
>          l   <- at ch_COp_l spp
>          (op :: Val2Op v)  <- ter ch_COp_op
>          r   <- at ch_COp_r spp
>          return $ "(" ++ l ++ show op ++ r ++ ")" 
>        )
>   .+: syn spp p_CComp ( do
>          l   <- at ch_CComp_l spp
>          op  <- ter ch_CComp_op
>          r   <- at ch_CComp_r spp
>          return $ "(" ++ l ++ show op ++ r ++ ")" 
>        )
>   .+: emptyAspect

> printCore :: CTerm Op Val -> String
> printCore e = sem_CTerm (asp_spp (Proxy @Val)) e emptyAtt #. spp
