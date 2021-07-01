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


> module MF.Core.Syn where

> import Expr.Syn hiding (P_Val, Add)

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> import Data.Proxy
> import Data.Ord

> import MF.Terminals

> type Nt_Core = 'NT "Core"
> nt_Core = Label @Nt_Core


> type P_COp  = 'Prd "COp" Nt_Core
> p_COp       = Label @P_COp
> ch_COp_l    = Label @('Chi "COp_l" P_COp (NonTerminal Nt_Core))
> ch_COp_r    = Label @('Chi "COp_r" P_COp (NonTerminal Nt_Core))
> ch_COp_op   = Label :: forall op. Label ('Chi "COp_op" P_COp (Terminal op))

> type P_CVal = 'Prd "CVal" Nt_Core
> p_CVal       = Label @P_CVal
> ch_CVal_val  = Label :: forall v . Label ('Chi "CVal_val" P_CVal (Terminal v))

> type P_CVar = 'Prd "CVar" Nt_Core
> p_CVar       = Label @P_CVar
> ch_CVar_var  = Label @ ('Chi "CVar_var" P_CVar (Terminal String))

> type P_CComp  = 'Prd "CComp" Nt_Core
> p_CComp       = Label @P_CComp
> ch_CComp_l    = Label @('Chi "CComp_l" P_CComp (NonTerminal Nt_Core))
> ch_CComp_r    = Label @('Chi "CComp_r" P_CComp (NonTerminal Nt_Core))
> ch_CComp_op   = Label @ ('Chi "CComp_op" P_CComp (Terminal Ordering))

> type P_CLam = 'Prd "CLam" Nt_Core
> p_CLam = Label @ P_CLam
> ch_CLam_binder = Label @('Chi "CLam_binder" P_CLam (Terminal String)) 
> ch_CLam_body   = Label @('Chi "CLam_body" P_CLam (NonTerminal Nt_Core)) 

> type P_CApp = 'Prd "CApp" Nt_Core
> p_CApp = Label @ P_CApp
> ch_CApp_l = Label @('Chi "CApp_l" P_CApp (NonTerminal Nt_Core))
> ch_CApp_r = Label @('Chi "CApp_r" P_CApp (NonTerminal Nt_Core))


TODO: ordenar producciones todas iguales

> data CTerm op v
>   = CVal v
>   | CVar String
>   | CLam String (CTerm op v)
>   | CApp (CTerm op v)(CTerm op v)
>   | COp (CTerm op v) op (CTerm op v)
>   | CComp (CTerm op v) Ordering (CTerm op v)
>   deriving (Eq, Show)

> sem_CTerm asp (COp l op r :: CTerm op v) =
>   knitAspect p_COp asp (
>         ch_COp_l  .=. sem_CTerm asp l
>    .*.  (ch_COp_op :: Label('Chi "COp_op" P_COp ('Right ('T op)))) .=. sem_Lit @op op
>    .*.  ch_COp_r  .=. sem_CTerm asp r
>    .*.  emptyGenRec
>   )

> sem_CTerm asp (CComp l op r) =
>   knitAspect p_CComp asp (
>         ch_CComp_l  .=. sem_CTerm asp l
>    .*.  ch_CComp_op .=. sem_Lit op
>    .*.  ch_CComp_r  .=. sem_CTerm asp r
>    .*.  emptyGenRec
>   )

> sem_CTerm asp (CVal v :: CTerm op v) =
>   knitAspect p_CVal asp (
>    (ch_CVal_val :: Label('Chi "CVal_val" P_CVal ('Right ('T v))))
>              .=. sem_Lit @v v .*. emptyGenRec)

> sem_CTerm asp (CVar v) =
>   knitAspect p_CVar asp (ch_CVar_var .=. sem_Lit v .*. emptyGenRec)

> sem_CTerm asp (CApp l r) =
>   knitAspect p_CApp asp (
>         ch_CApp_l  .=. sem_CTerm asp l
>    .*.  ch_CApp_r  .=. sem_CTerm asp r
>    .*.  emptyGenRec
>   )

> sem_CTerm asp (CLam x e) =
>   knitAspect p_CLam asp (
>         ch_CLam_binder  .=. sem_Lit x
>    .*.  ch_CLam_body    .=. sem_CTerm asp e
>    .*.  emptyGenRec
>   )


> self :: forall v op . Values op v => Label ('Att "self" (CTerm op v))
> self = Label
> asp_core_id = \(p :: Proxy v) -> 
>       syn (self @ v) p_COp (COp <$> at ch_COp_l (self @v)
>                                <*> ter ch_COp_op
>                                <*> at ch_COp_r (self @ v))
>   .+: syn (self @v) p_CComp (CComp <$> at ch_CComp_l (self @v)
>                                   <*> ter ch_CComp_op
>                                  <*> at ch_CComp_r (self @v))
>   .+: syn (self @v) p_CVal (CVal <$> ter ch_CVal_val)
>   .+: syn (self @v) p_CVar (CVar <$> ter ch_CVar_var)
>   .+: syn (self @v) p_CLam (CLam <$> ter ch_CLam_binder
>                                 <*> at ch_CLam_body (self @v))
>   .+: syn (self @v) p_CApp (CApp <$> at ch_CApp_l (self @ v)
>                                 <*> at ch_CApp_r (self @v))
>   .+: emptyAspect

> cterm_id :: Values op v => CTerm op v -> CTerm op v
> cterm_id (e :: CTerm op v)
>   = sem_CTerm (asp_core_id (Proxy @v)) e emptyAtt #. (self @v)


examples:

> ap3 f a b c = CApp (CApp (CApp f a) b) c
> ap2 f a b = CApp (CApp f a) b

> tt = CLam "T" $ CLam "F" $ CVar "T"
> ff = CLam "T" $ CLam "F" $ CVar "F"

> ite = CLam "C" $ CLam "T" $ CLam "E" $
>     CApp (CApp (CVar "C")(CVar "T")) (CVar "E")

> neg = CLam "E" $ CLam "T" $ CLam "F"
>   $ ap2 (CVar "E")(CVar "F")(CVar "T")

> conj = CLam "L" $ CLam "R" $
>   ap3 ite (CVar "L")(CVar "R") ff


> fac = CLam "n" $ ap3 ite (CComp (CVar "n") LT (CVal $ I 1))
>                          (CVal $ I 1)
>                          (COp (CVar "n") Times (CApp (CVar "fac")
>                                                (COp (CVar "n") Add
>                                                     (CVal $ I (-1)))))


> tup2 =CLam "X" $ CLam "Y" $ CLam "T"
>      $ ap2 (CVar "T")(CVar "X") (CVar "Y") 
> swap = CLam "x" $ CLam "y" $ ap2 tup2 (CVar "x")(CVar "y")
