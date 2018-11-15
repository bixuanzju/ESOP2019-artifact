{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}

module SEDEL.Target.Eval (evaluate) where

import           Control.Monad.Except
import           Data.IORef
import qualified Data.Map.Strict as M
import           Unbound.Generics.LocallyNameless

import           SEDEL.Target.Syntax
import           SEDEL.Common

-- call-by-need environment
type Env = M.Map UName Thunk

type EvalM a = FreshMT (ExceptT String IO) a

newtype Thunk = Thunk { force :: EvalM Value }

instance Show Thunk where
  show _ = "<Thunk>"

mkThunk :: EvalM Value -> EvalM Thunk
mkThunk ev = do
  ref <- liftIO $ newIORef Nothing
  return $
    Thunk $ do
      mv <- liftIO $ readIORef ref
      case mv of
        Nothing -> do
          v <- ev
          liftIO $ writeIORef ref (Just v)
          return v
        Just v -> return v



data Value
  = VLit !Double
  | VBool !Bool
  | VStr !String
  | VPair !Thunk !Thunk
  | VUnit
  | VLam !(Thunk -> EvalM Value)

instance Show Value where
  show (VLit n) = show n
  show (VBool True) = "true"
  show (VBool False) = "false"
  show (VPair _ _) = "<Pair>"
  show VUnit = "()"
  show (VStr s) = show s
  show (VLam _) = "<Lambda>"


runEvalM :: EvalM a -> IO (Either String a)
runEvalM = runExceptT . runFreshMT


evaluate :: UExpr -> IO (Either String Value)
evaluate e = runEvalM (eval M.empty e)

-- | Lazy evaluation
eval :: Env -> UExpr -> EvalM Value
eval env (UVar n) = lookupValue env n >>= force
eval env (UApp f x) = do
  f' <- eval env f
  x' <- mkThunk (eval env x)
  evalApp f' x'
eval env (ULam b) = do
  (n, e) <- unbind b
  return $ VLam $ \x -> eval (M.insert n x env) e
eval env (ULet b) = mdo
  (n, (e1, e2)) <- unbind b
  e1' <- mkThunk (eval (M.insert n e1' env) e1)
  eval (M.insert n e1' env) e2
eval env (UPair e1 e2) = do
  e1' <- mkThunk (eval env e1)
  e2' <- mkThunk (eval env e2)
  return $ VPair e1' e2'
eval env (UP1 e) = do
  e' <- eval env e
  evalP1 e'
eval env (UP2 e) = do
  e' <- eval env e
  evalP2 e'
eval _ (ULitV n) = return (VLit n)
eval _ (UBoolV n) = return (VBool n)
eval _ (UStrV n) = return (VStr n)
eval _ UUnit = return VUnit
eval env (UPrimOp op e1 e2) = do
  e1' <- eval env e1
  e2' <- eval env e2
  evalOp op e1' e2'
eval env (UIf e1 e2 e3) = do
  e1' <- eval env e1
  case e1' of
    VBool b ->
      if b
        then eval env e2
        else eval env e3
    v -> throwError $ "Expected a Boolean, but got: " ++ show v
eval env (UToString e) = do
  e' <- eval env e
  return (VStr (show e'))
eval env (USqrt e) = do
  e' <- eval env e
  case e' of
    VLit n -> return $ VLit (sqrt n)
    v -> throwError $ "Expected a number, but got: " ++ show v
eval _ Bot = throwError "Damn it, it's an infinite loop!"



evalApp :: Value -> Thunk -> EvalM Value
evalApp (VLam f) t  = f t
evalApp v _ = throwError $ "Expected a function, but got: " ++ show v


evalP1 :: Value -> EvalM Value
evalP1 (VPair v1 _)   = force v1
evalP1 v = throwError $ "Expected a pair, but got: " ++ show v


evalP2 :: Value -> EvalM Value
evalP2 (VPair _ v2)   = force v2
evalP2 v = throwError $ "Expected a pair, but got: " ++ show v

evalOp :: Operation -> Value -> Value -> EvalM Value
evalOp (Arith Add) (VLit x) (VLit y) = return $ VLit $ x + y
evalOp (Arith Sub) (VLit x) (VLit y) = return $ VLit $ x - y
evalOp (Arith Mul) (VLit x) (VLit y) = return $ VLit $ x * y
evalOp (Arith Div) (VLit x) (VLit y) = return $ VLit $ x / y
evalOp (Comp Equ) (VLit x) (VLit y) = return $ VBool $ x == y
evalOp (Comp Equ) (VStr x) (VStr y) = return $ VBool $ x == y
evalOp (Comp Equ) (VBool x) (VBool y) = return $ VBool $ x == y
evalOp (Comp Lt) (VLit x) (VLit y) = return $ VBool $ x < y
evalOp (Comp Gt) (VLit x) (VLit y) = return $ VBool $ x > y
evalOp (Comp Neq) (VLit x) (VLit y) = return $ VBool $ x /= y
evalOp (Comp Neq) (VStr x) (VStr y) = return $ VBool $ x /= y
evalOp (Comp Neq) (VBool x) (VBool y) = return $ VBool $ x /= y
evalOp (Logical LAnd) (VBool x) (VBool y) = return $ VBool $ x && y
evalOp (Logical LOr) (VBool x) (VBool y) = return $ VBool $ x || y
evalOp Append (VStr x) (VStr y) = return $ VStr $ x ++ y
evalOp _ _ _ = throwError "Impossible happened in evalOp"

lookupValue :: Env -> UName -> EvalM Thunk
lookupValue env n = maybe err return $ M.lookup n env
  where
    err = throwError $ "Not found: " ++ show (name2String n)
