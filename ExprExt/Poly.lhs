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

> import Language.Grammars.AspectAG
> import Expr.Syn

%endif

\section{Polymorphism in \AspectAG}
\label{sec:polymorphism}

In the previous sections we showed how the expression problem can be
tackled using \AspectAG. How the expression problem is tackled is a
good measurement of modularity, but not the only one we are interested
in. Functional programming provides tools to achieve modularity such
as higher order functions and lazy evaluation \cite{citeulike:494117}.
Polymorphism is obviously another useful feature to modularize
programs since it adds the possibility to code a function once to
manipulate many data structures. As a DSL embedded in Haskell
\AspectAG can exploit the benefits of polymorphic, higher order
functional programming. We briefly discussed in the previous sections
a couple of examples of how to use lazy evaluation (partial functions
in attribute definitions that will not crash) and polymorphism (the
|copyAtChi| template). But since \AspectAG as a language used to
create languages it is a natural to wonder if the generated language
can be polymorphic or if we can produce higher order functions from
the application of semantic functions.

For instance, consider the |Data.List| module in GHC's base
library. It is an EDSL used to manipulate lists, and most functions in
it are polymorphic and higher order. Can we program functions in
|Data.List| using \AspectAG? In fact a subset of them (arbitrarily
chosed by the author) are included in an example program in the
\AspectAG package distribution.

When using \AspectAG to build abstract syntax for compilers (i.e. not
embedded languages) there are are also good reasons to make the
generated abstract syntax polymorphic. One could paremetrize the
abstract syntax tree by its binders to use higher order syntax tree
approaches [REF]. Or one could build extensible data types using trees
that grow [ref]. There is another useful use that we will extensively
exploit in the case study presented later. It is to parametrize the
language over its terminals. This is exactly the same we do in the
|List| DSL over the type of the contained elements.

To show the benefits of parametrization over terminals let us come
back to the expression language. Suppose that we want to add the
possibility to manipulate real numbers instead of integers. We can
drop the |p_Val| production as it is and introduce an alternative, say
|p_ValR|, with the correct type. Unfortunately our semantics for the
|eval| and |env| attributes will no longer be reusable since they have
the |Integer| type attached. We can define a new pair of attributes,
and define rules to compute them, but note that those rules will be
written exactly the same way as for |eval| and |env|. For |eval| we
would take the terminal on |p_Val|, sum the recursive denotations in
|p_Add|, lookup the environment in |p_Var|. For |env| we use copy
rules. Polymorphism in attributes can avoid this duplication.

If we want to manipulate both real numbers and integers things will
get more complicated. |p_Val| and |p_ValR| productions can coexist,
but the rule to compute |eval| on the |p_Add| production will be ill
typed (even using the polymorphic addition). The issue can be solved
computing the evaluation as a sum type and combining it in a suitable
way in the case of addition, although this does not scale if adding more
productions.

If we want to add more types of numbers to the expression language we
can add more productions. Computing rules for the |eval| attribute
will be similar in each terminal production, injecting the leaf value
in the sum value we are computing. This repetition can be avoided. We
can think in the expression language as a way to build variables,
additions, and values of some abstract type. We can push the
responsability of how values are handled to the abstract type.

This will be clear if we implement it. Consider the |Nt_Expr| non
terminal and the |p_Add| and |p_Var| productions as they are defined
already. We build an alternative production for values, |p_ValP| that
contains a polymorphic terminal:

> type P_ValP = ('Prd "ValP" Nt_Expr)
> p_ValP  = Label @ P_ValP
> ch_ValP_val :: forall v . Label ('Chi "val" P_ValP (Terminal v))
> ch_ValP_val = Label

Note that actually the |p_Val| label could be reused, the children
definition is the one thet differs with respect to the definition in
section \ref{sec:grammarspecification}. We make polymorphic the type
of the value contained in the child.

Now we define a polymorphic attribute |evalP|, abstracting the type in
the same way.

> evalP :: forall v. Label ('Att "evalP" v)
> evalP = Label

Now we define an interface for the abstract type of our values. We
call it |Number| and whatever it is, the type implementing the
interface must support support addition. We do it with a type
class.

> class Number a where
>   add :: v -> v -> v

To document types better we can have this class as a constraint in the
polymorphic type |v| of |evalP| and |ch_ValP_val|, but it is not
necessary at all. Now we define semantics for the |evalP| attribute.

> add_evalP = \(Proxy :: Proxy v) ->
>  syndefM (evalP @v) p_Add 
>     $    add
>     <$>  at ch_Add_l (evalP @v)
>     <*>  at ch_Add_r (evalP @v)

> val_evalP = \(Proxy :: Proxy v) ->
>   syndefM (eval @v) p_Val (ter (ch_Val_val @v))

Those definitions are very similar to the ones in section
\ref{sec:semanticsdefinition}. The difference is that we added a
|Proxy| parameter with the type of values and applyed that type to all
polymorphic labels. That |Proxy| argument solves a subtle technical
issue. As we will see in section [REF] \AspectAG structures are
implemented with extensible records. When a record contains
polymorphic values and we look up fields (either with polymorphic or
monomorphic) values variables may not unify. Even if we could deduce
they do, GHC inference algorithm may not, and type inference may get
stuck. The solution is to pass the type explicitly and force
unification early.

With this approach there are no relevant differences in the semantic
functions definition or with data type definitions. As an example we
can show the type that we would generate with the forestated approach:

> data Expr a
>  = Add  {l :: Expr a, r :: Expr a} |
>    Var  {var :: String} |
>    Val  {val :: a}
>     deriving (Show, Eq, Read)

We can show that we can get what we had befoire. If we
implement the instance of |Number| for the type |Integer| we get the
same language defined in section \ref{sec:grammarspecification}. The
evaluator looks like:

> evaluator :: Expr Integer -> Env Integer -> Integer
> evaluator exp envi =
>  sem_Expr  (asp_sem (Proxy @Integer)) exp
>            ((envP @Integer) =. envi *. emptyAtt) #. (eval @Integer)

where |asp_sem| is built by a combinator similar to (.:+:) (actually
the same, since in the current \AspectAG implementation it is
polymorphic) that combines polymorphic rule definitions (it passes
the proxy taken to every rule). We omitted the the definition of the
attribute |envP| and the rules to compute it, since it is
straightforward and does not offer any new insight.

The news is that we also got a family of languages, for every type
implementing the |Number| interface. If we want to combine |Integer|s,
real numbers (say, represented as |Double|) and unary naturals, we can:

< data MyNum = I Integer | R Dobuble | N Nat
< data Nat = Z | S Nat

< instance Number MyNum where
<   add = ...

How they are combined when added up will depend on the implementation
of the |add| method.

Finally we must note that we do not lose any expresivity with
polymorphic attributes. The language can still be extended with new
productions. If we need more functions to combine elements of the type
of terminals (suppose, for instance if we add a production to model
other operation than addition) we wan implement a subclass of
|Number|.
