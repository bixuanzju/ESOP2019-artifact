{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}


module SEDEL.Source.Desugar
  ( desugar
  , desugarExpr
  , desugarTmBind
  , normalizeTmDecl
  , expandType
  ) where

import Protolude
import Unbound.Generics.LocallyNameless

import SEDEL.Environment
import SEDEL.Source.Syntax
import SEDEL.Util

desugar :: [SDecl] -> [SDecl]
desugar = map go
  where
    go :: SDecl -> SDecl
    go (DefDecl decl) = DefDecl $ desugarTmBind decl
    go ty = ty

desugarTmBind :: TmBind -> TmBind
desugarTmBind b = b {bindRhs = desugarExpr (bindRhs b)}

desugarExpr :: Expr -> Expr
desugarExpr = runFreshM . go
  where

    go :: Fresh m => Expr -> m Expr

    -- Interesting cases
    go (AnonyTrait t) = return $ desugarTrait t

    go (DRec' b) =
      let (l, e) = normalizeTmDecl (desugarTmBind b)
      in return $ DRec l e

    -- Routine
    go (Anno e t) = do
      e' <- go e
      return $ Anno e' t
    go (App e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ App e1' e2'
    go (Lam t) = do
      (n, body) <- unbind t
      body' <- go body
      return $ Lam (bind n body')

    go (Letrec t) = do
      ((n, pt), (e, body)) <- unbind t
      bind' <- go e
      body' <- go body
      return $ Letrec (bind (n, pt) (bind', body'))

    go (DLam b) = do
      ((n, t), body) <- unbind b
      body' <- go body
      return $ DLam (bind (n, t) body')
    go (TApp e t) = do
      e' <- go e
      return $ TApp e' t
    go (DRec l e) = do
      e' <- go e
      return $ DRec l e'
    go (Acc e l) = do
      e' <- go e
      return $ Acc e' l
    go (Remove e l t) = do
      e' <- go e
      return $ Remove e' l t
    go (Merge e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ Merge e1' e2'
    go (PrimOp op e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ PrimOp op e1' e2'
    go (If e1 e2 e3) = do
      e1' <- go e1
      e2' <- go e2
      e3' <- go e3
      return $ If e1' e2' e3'
    go (LamA b) = do
      ((n, t), body) <- unbind b
      body' <- go body
      return $ LamA (bind (n, t) body')
    go (Pos p e) = do
      e' <- go e
      return (Pos p e')
    go e = return e



{- | Desugar trait


trait [self : C] inherits b & c {...}

~>

\ (self : C) . let super = b(self) ,, c(self) in super \ {...} ,, {...}


If there are any overridden methods, remove them from super


Limitation:

Don't use the same name for both overridden and non-overridden methods, even if
they have different types, otherwise the behaviour is unpredictable.


-}
desugarTrait :: Trait -> Expr
desugarTrait trait = expr
  where
    (expr, _) =
      normalize
        []
        [ ( s2n self
          , Just st)
        ]
        -- when no inherits, there is no super in scope
        (maybe
           body
           (\arg -> elet "super" arg (Merge superExpr body))
           (foldl1May Merge inherits))
        ret
    (self, st) = selfType trait
    inherits =
      map
        (\t ->
           case desugarExpr t of
             Pos p (Remove e l t') -> Pos p (Remove (App e (evar self)) l t')
             -- hack for trait excluding
             t' -> App t' (evar self))
        (traitSuper trait)
    body = mkRecds (map (normalizeTmDecl . desugarTmBind) (traitBody trait))
    overrides = map bindName (filter isOverride (traitBody trait))
    -- remove overridden methods from super
    superExpr = foldr (\l tt -> Remove tt l Nothing) (evar "super") overrides
    ret = retType trait



-- After parsing, earlier declarations appear first in the list
-- Substitute away all type declarations
-- resolveDecls :: [SDecl] -> [TmBind]
-- resolveDecls decls = map (substs substPairs) [decl | (DefDecl decl) <- decls]
--   where
--     tydecls =
--       foldl'
--         (\ds t -> substs (toSubst ds) t : ds)
--         []
--         [decl | decl@TypeDecl {} <- decls]
--     substPairs = toSubst tydecls
--     toSubst ds = [(s2n n, t) | TypeDecl (TypeBind n _ t) <- ds]

{- |


(1): Translate

f [(A, T1), (B, T2)] [(x, A), (y, B)] = e

to

(f, /\ A*T1. B*T2. \x : A .\y : B . e)


(2): Translate

f [(A, T1), (B, T2)] [(x, A), (y, B)] C = e

to

(f, letrec f : forall (A * T1) (B * T2) . A -> B -> C = /\ A*T1. B*T2. \x y . e in f)


-}


normalizeTmDecl :: TmBind -> (RawName, Expr)
normalizeTmDecl decl =
  ( bindName decl
  , maybe ex (\t -> eletr (bindName decl) t ex (evar (bindName decl))) typ)
  where
    (ex, typ) =
      normalize
        (bindTyParams decl)
        (bindParams decl)
        (bindRhs decl)
        (bindRhsTyAscription decl)

{- |

Note: Make sure everything is desugarred before normalizing

Normalize

[(A, T1), (B, T2)] [(x, A), (y, B)] C e

to

\/ A*T1. B*T2. A -> B -> C

and

/\ A*T1. B*T2. \x.\y.e

-}
normalize :: [(TyName, SType)] -> [(TmName, Maybe SType)] -> Expr -> Maybe SType -> (Expr, Maybe SType)
normalize tyParams params e ret = (body, tbody)
  where
    tbody =
      maybe
        Nothing
        (\arr' ->
           Just
             (foldr (\(n, s) tm -> DForall (bind (n, Embed s) tm)) arr' tyParams))
        arr
    arr =
      maybe
        Nothing
        (\t ->
           foldrM
             (\(_, x) y -> maybe Nothing (\x' -> Just $ Arr x' y) x)
             t
             params)
        ret
    body = foldr (\(n, s) tm -> DLam (bind (n, Embed s) tm)) fun tyParams
    fun =
      foldr
        (\(n, t) tm ->
           maybe (Lam (bind n tm)) (\t' -> LamA (bind (n, Embed t') tm)) t)
        (maybe e (Anno e) ret)
        params


-- | Recursively expand all type synonyms. The given type must be well-kinded.
expandType :: Ctx -> SType -> SType
expandType ctx ty = runFreshM (go ctx ty)
  where
    go :: Ctx -> SType -> FreshM SType
    -- Interesting cases:
    go d (TVar a) =
      case lookupTVarSynMaybe d a of
        Nothing -> return $ TVar a
        Just t -> go d t
    go d (OpAbs b) = do
      ((x, Embed k), t) <- unbind b
      t' <- go (extendTVarCtx x k d) t
      return $ OpAbs (bind (x, embed k) t')
    go d typ@(OpApp t1 t2) =
      go d t1 >>= \case
        OpAbs b -> do
          t2' <- go d t2
          ((x, Embed _), t) <- unbind b
          go d (subst x t2' t)
        _ -> return typ
    go _ NumT = return NumT
    go _ BoolT = return BoolT
    go _ StringT = return StringT
    go d (Arr t1 t2) = do
      t1' <- go d t1
      t2' <- go d t2
      return $ Arr t1' t2'
    go d (And t1 t2) = do
      t1' <- go d t1
      t2' <- go d t2
      return $ And t1' t2'
    go d (DForall b) = do
      ((a, Embed t1), t2) <- unbind b
      t1' <- go d t1
      t2' <- go d t2
      return $ DForall (bind (a, embed t1') t2')
    go d (SRecT l t) = do
      t' <- go d t
      return $ SRecT l t'
    go _ TopT = return TopT
    go _ BotT = return BotT
