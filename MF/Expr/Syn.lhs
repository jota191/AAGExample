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

> module MF.Expr.Syn
>    where
> import Expr.Syn hiding (ch_Val_val, P_Val, Expr(..), p_Val, sem_Expr_Val)
> import ExprExt.Syn

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> import Data.Proxy

> type P_Val = 'Prd "Val" Nt_Expr
> p_Val       = Label @P_Val
> ch_Val_val  = Label :: forall v . Label ('Chi "Val_val" P_Val (Terminal v))

> type P_Op  = 'Prd "Op" Nt_Expr
> p_Op       = Label @P_Op
> ch_Op_l    = Label @('Chi "Op_l" P_Op (NonTerminal Nt_Expr))
> ch_Op_r    = Label @('Chi "Op_r" P_Op (NonTerminal Nt_Expr))
> ch_Op_op   = Label :: forall op. Label ('Chi "Op_op" P_Op (Terminal op))

> sem_Expr_Val asp (v :: v) =
>   knit Proxy asp (
>     (ch_Val_val :: Label('Chi "Val_val" P_Val ('Right ('T v))))
>      .=. sem_Lit @v v .*. emptyGenRec)

> sem_Expr_Var asp (x :: String) =
>   knit Proxy asp (
>      ch_Var_var .=. sem_Lit x .*. emptyGenRec
>    )

> sem_Expr_Op asp sl (op :: op) sr =
>   knit Proxy asp (
>     ch_Op_l .=. sl .*.
>     (ch_Op_op :: Label ('Chi "Op_op" P_Op ('Right ('T op))))
>           .=. sem_Lit @op op .*.
>     ch_Op_r .=. sr .*. emptyGenRec
>    )

> sem_Expr_Call asp f se =
>   knit Proxy asp (
>     ch_Call_fun .=. sem_Lit @String f .*.
>     ch_Call_arg .=. se .*. emptyGenRec
>    )


