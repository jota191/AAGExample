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

> module MF.Expr.Syn where
> import Expr.Syn hiding (P_Val)

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> $(addProd "Op" ''Nt_Expr [("l", NonTer ''Nt_Expr),
>                           ("op", Poly),
>                           ("r", NonTer ''Nt_Expr) 
>                           ])


> $(addProd "Val" ''Nt_Expr [("val", Poly)])


> data Expr val op =
>   Op (Expr val op) op (Expr val op)
