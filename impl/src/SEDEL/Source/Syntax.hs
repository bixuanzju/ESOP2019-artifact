{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses, TemplateHaskell, FlexibleInstances #-}

module SEDEL.Source.Syntax where

import           Data.Maybe (fromMaybe)
import           Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics (Generic)
import           Text.Megaparsec
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.TH

import           SEDEL.Common


-- | Modules
data Module = Module
  { moduleEntries :: [SDecl]
  , mainExpr      :: SDecl
  } deriving (Show, Generic)

-- | Declarations other than traits
data SDecl
  = DefDecl TmBind
  | TypeDecl TypeBind
  deriving (Show, Generic)

type RawName = String

data Trait = TraitDef
  { selfType      :: (RawName, SType)
  , traitSuper    :: [Expr]
  , retType       :: Maybe SType
  , traitBody     :: [TmBind]
  } deriving (Show, Generic)


-- f A1,...,An (x1: t1) ... (xn: tn): t = e
-- If t is provided, then e can mention f
data TmBind = TmBind
  { bindName            :: RawName                   -- f
  , bindTyParams        :: [(TyName, SType)]          -- A1, ..., An
  , bindParams          :: [(TmName, Maybe SType)]    -- x1: t1, ..., xn: tn
  , bindRhs             :: Expr                      -- e
  , bindRhsTyAscription :: Maybe SType                -- t
  , isOverride          :: Bool
  } deriving (Show, Generic)

-- type T[A1, ..., An] = t
data TypeBind = TypeBind
  { typeBindName   :: RawName            -- T
  , typeBindParams :: [(TyName, Kind)]   -- A1, ..., An
  , typeBindRhs    :: SType               -- t
  } deriving (Show, Generic)


type TmName = Name Expr
type TyName = Name SType

-- Expression
data Expr = Anno Expr SType
          | Var TmName
          | App Expr Expr
          | Lam (Bind TmName Expr)
          | Letrec (Bind (TmName, Embed (Maybe SType)) (Expr, Expr))
            -- ^ let expression, possibly recursive
          | DLam (Bind (TyName, Embed SType) Expr)
          | TApp Expr SType
          | DRec Label Expr
          | Acc Expr Label
          | Remove Expr Label (Maybe SType)
          | Merge Expr Expr
          | LitV Double
          | BoolV Bool
          | StrV String
          | PrimOp Operation Expr Expr
          | If Expr Expr Expr
          | Top
          -- practical matters for surface language
          | Pos SourcePos Expr
          -- ^ marked source position, for error messages
          | LamA (Bind (TmName, Embed SType) Expr)
          -- ^ Not exposed to users, for internal use
          | Bot
          -- The following should disappear after desugaring
          | AnonyTrait Trait
          | DRec' TmBind
  deriving (Show, Generic)

type Label = String
data SType = NumT
          | BoolT
          | StringT
          | Arr SType SType
          | And SType SType
          | TVar TyName
          | DForall (Bind (TyName, Embed SType) SType)
          | SRecT Label SType
          | TopT
          | BotT
          | OpAbs (Bind (TyName, Embed Kind) SType)
          -- ^ SType-level abstraction: "type T A = t" becomes "type T = \A : *. t",
          | OpApp SType SType
          -- ^ SType-level application: t1 t2

  deriving (Show, Generic)

-- Kinds k := * | k -> k
data Kind = Star | KArrow Kind Kind deriving (Eq, Show, Generic)


instance Pretty (Name a) where
    pretty v = Pretty.pretty (name2String v)


-- Unbound library instances

$(makeClosedAlpha ''SourcePos)

instance Alpha SType
instance Alpha Expr
instance Alpha Trait
instance Alpha SDecl
instance Alpha TmBind
instance Alpha TypeBind
instance Alpha Kind


instance Subst b SourcePos where
  subst _ _ = id
  substs _ = id

instance Subst Expr SType
instance Subst Expr Kind
instance Subst Expr ArithOp
instance Subst Expr LogicalOp
instance Subst Expr Operation
instance Subst Expr CompOp
instance Subst Expr Trait
instance Subst Expr SDecl
instance Subst Expr TmBind
instance Subst Expr TypeBind

instance Subst Expr Expr where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst SType Expr
instance Subst SType Trait
instance Subst SType Operation
instance Subst SType LogicalOp
instance Subst SType CompOp
instance Subst SType ArithOp
instance Subst SType SDecl
instance Subst SType TmBind
instance Subst SType TypeBind
instance Subst SType Kind


instance Subst SType SType where
  isvar (TVar v) = Just (SubstName v)
  isvar _ = Nothing


-- | Partial inverse of Pos
unPosExpr :: Expr -> Maybe SourcePos
unPosExpr (Pos p _) = Just p
unPosExpr _         = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: Expr -> Maybe SourcePos
unPosDeep = unPosExpr

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Expr -> SourcePos
unPosFlaky t =
  fromMaybe (SourcePos "unknown location" (mkPos 0) (mkPos 0)) (unPosDeep t)
