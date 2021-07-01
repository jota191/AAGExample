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

> module MF.Function.Compile where
> import MF.Expr.Syn
> import MF.Expr.Compile
> 
> import Expr.Syn
> import MF.Function.Syn

> import MF.Core.Syn

> import Language.Grammars.AspectAG
> import Data.Ord
> import Data.Proxy

> import MF.Terminals ---

> import qualified Data.Map as M

> scomp_eif = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_EIf (
>   ap3 <$> pure ite <*> at ch_EIf_cond (scomp @ v)
>                    <*> at ch_EIf_if (scomp @ v)
>                    <*> at ch_EIf_else (scomp @ v)
>   )

> scomp_eor = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_EOr (at ch_EOr_or (scomp @ v))

> scomp_top = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_Top (return tt)

> scomp_neg = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_Neg (CApp neg <$> at ch_Neg_e (scomp @ v))

> scomp_and = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_And (ap2 <$> pure conj
>                              <*> at ch_And_l (scomp @v)
>                              <*> at ch_And_r (scomp @v))

> scomp_comp = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_Comp (CComp  <$> at ch_Comp_l (scomp @ v)
>                                  <*> ter ch_Comp_op
>                                  <*> at ch_Comp_r (scomp @ v))

> scomp_ecu = \(Proxy :: Proxy v) ->
>   syn (scomp @ v) p_Ecu (do
>      vars <- ter ch_Ecu_vars
>      body <- at ch_Ecu_body (scomp @ v)
>      return $ foldr CLam body vars
>   )


> sfcomp :: forall v op . Values op v
>   => Label ('Att "fcompile" (String, CTerm op v))
> sfcomp = Label

> sfcomp_fdef = \(Proxy :: Proxy v) ->
>   syn (sfcomp @ v) p_FDef
>       $ (,) <$> ter ch_FDef_name <*> at ch_FDef_ecu (scomp @ v)


> spcomp :: forall v op . Values op v
>   => Label ('Att "fcompile" (M.Map String (CTerm op v)))
> spcomp = Label

> spcomp_nil = \(Proxy :: Proxy v) ->
>   syn (spcomp @ v) p_ProgramNil (return M.empty)

> spcomp_snoc = \(Proxy :: Proxy v) ->
>   syn (spcomp @ v) p_ProgramSnoc (do
>    fenv <-  at ch_ProgramCons_init (spcomp @v)
>    (f, ecu) <- at ch_ProgramCons_init (sfcomp @v)
>    return $ M.insert f ecu fenv
>   )
