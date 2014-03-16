#!/usr/bin/runhaskell
{-# LANGUAGE TemplateHaskell, RankNTypes, QuasiQuotes #-}

import Data.Map as Map hiding (map)
import Data.Monoid
import Data.Functor
import Control.Applicative hiding ((<|>), many)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Lens hiding (noneOf)
import Control.Arrow hiding (left, right)
import Text.Parsec
import Text.Parsec.Numbers
import System.IO
import System.Environment
import System.Directory

-- types and instances

data Purity = Pure | Impure deriving (Show, Ord, Eq)
type Env = (Purity, Map String LispVal)
type LispM = StateT Env (EitherT String IO) LispVal
type LGet a = Getting (First a) LispVal a

data LispVal  = LispNum     Double |
                LispBool    Bool |
                LispSym     String |
                LispList    [LispVal] |
                LispWIPFunc {_lwfunc :: LispFunc} |
                LispWFunc   {_lwfunc :: LispFunc} |
                LispWFexpr  {_lwfunc :: LispFunc} |
                LispWVmacro {_lwfunc :: LispFunc} |
                LispWMacro  {_lwfunc :: LispFunc} deriving (Eq, Ord)
data LispFunc = LispFunc    {_closure :: Env, _pnames :: [String],
                            _body :: LispVal} |
                HaskellFunc {_name :: String,
                             _func :: [LispVal] -> LispM}

instance Show LispVal where
  show (LispBool b)    = show b
  show (LispNum n)     = show n
  show (LispSym s)     = s
  show (LispList l)    = "(" ++ unwords (map show l) ++ ")"
  show (LispWIPFunc f) = lfShow "impure function" f
  show (LispWFunc f)   = lfShow "function"        f
  show (LispWFexpr f)  = lfShow "fexpr"           f
  show (LispWVmacro f) = lfShow "vacro"           f
  show (LispWMacro f)  = lfShow "macro"           f

lfShow :: String -> LispFunc -> String
lfShow fType (LispFunc _ pnames _) =
  "[" ++ fType ++ " of " ++ show (LispList $ map LispSym pnames) ++ "]"
lfShow fType (HaskellFunc name _) =
  "[wrapped Haskell " ++ fType ++ " " ++ name ++ "]"

instance Show LispFunc where
  show = lfShow "function"

instance Eq LispFunc where
  (LispFunc a1 a2 a3) == (LispFunc b1 b2 b3)
    = (a1, a2, a3) == (b1, b2, b3)
  (HaskellFunc name1 _) == (HaskellFunc name2 _) = name1 == name2

instance Ord LispFunc where
  compare (LispFunc a1 a2 a3) (LispFunc b1 b2 b3) =
    compare (a1, a2, a3) (b1, b2, b3)

makePrisms ''LispVal
makeLenses ''LispVal
makePrisms ''LispFunc
makeLenses ''LispFunc

elookup k = Map.lookup k . snd
einsert k a = _2 %~ insert k a
eunion (ctx, m1) (_, m2) = (ctx, m1 `union` m2)
purify, impurify :: Env -> Env
purify   = _1 .~ Pure
impurify = _1 .~ Impure

-- main impl

eval :: LispVal -> LispM
eval (LispSym s)    = StateT $ \env ->
  case elookup s env of
    Just v  -> right (v, env)
    Nothing -> left $ "undefined variable: " ++ s
eval (LispList l@(f:a)) = apply f a
eval other              = return other

apply :: LispVal -> [LispVal] -> LispM
apply = sApply eval

neApply :: LispVal -> [LispVal] -> LispM
neApply = sApply return

sApply :: (LispVal -> LispM) -> LispVal -> [LispVal] -> LispM
sApply eval f a = do
  ef  <- eval f
  env <- get
  let purity = fst env
  case ef of
    LispWIPFunc f' ->
      case purity of
        Pure   -> lift $ left $
          "impure function " ++ show ef ++ " called in a pure context"
        Impure -> mapM eval a >>= uwApply Impure f' ef
    LispWFunc   f' -> mapM eval a >>= uwApply Pure f' ef
    LispWFexpr  f' -> uwApply Pure f' ef a
    LispWVmacro f' -> mapM eval a >>= uwApply Pure f' ef >>= eval
    LispWMacro  f' -> uwApply Pure f' ef a >>= eval
    _             -> lift $ left $ "not a function: " ++ show ef

uwApply :: Purity -> LispFunc -> LispVal -> [LispVal] -> LispM
uwApply purity f@(LispFunc closure pnames body) this args
 | length pnames /= length args =
     lift $ left $ "wrong number of arguments: expected " ++
       show (LispList $ map LispSym pnames) ++ "; got: " ++
       show (LispList args)
 | otherwise =
     let argEnv    = (Pure, fromList $ zip pnames args)
         mergedEnv = einsert "this" this $ argEnv `eunion` closure
         purityEnv = set _1 purity mergedEnv
     in do
       cur <- get
       put purityEnv
       res <- eval body
       put cur
       return res
uwApply _ (HaskellFunc _ func) _ args = func args

-- lifting

type LConv a = a -> LispM

gb :: AReview' LispVal a -> LConv a
gb p v = return $ p # v

liftL :: (a -> b) -> LGet a -> LConv b -> String -> LispFunc
liftL func param1 resultC name =
  HaskellFunc name $ \args ->
    case args of
      [arg1] ->
        case func <$> arg1 ^? param1 of
          Just v  -> resultC v
          Nothing -> lift $ left $
            "invalid argument types to " ++ name ++
              ": got " ++ show (LispList args)
      _ -> lift $ left $ "wrong number of arguments to " ++ name ++
        ": expected 1; got " ++ show (LispList args)

liftL2 :: (a -> b -> c) -> LGet a -> LGet b -> LConv c -> String -> LispFunc
liftL2 func param1 param2 resultC name =
  HaskellFunc name $ \args ->
    case args of
      [arg1, arg2] ->
        case func <$> arg1 ^? param1 <*> arg2 ^? param2 of
          Just v  -> resultC v
          Nothing -> lift $ left $
            "invalid argument types to " ++ name ++
              ": got " ++ show (LispList args)
      _ -> lift $ left $ "wrong number of arguments to " ++ name ++
        ": expected 2; got " ++ show (LispList args)

liftL3 :: (a -> b -> c -> d) -> LGet a -> LGet b -> LGet c -> LConv d -> String -> LispFunc
liftL3 func param1 param2 param3 resultC name =
  HaskellFunc name $ \args ->
    case args of
      [arg1, arg2, arg3] ->
        case func <$> arg1 ^? param1 <*> arg2 ^? param2 <*> arg3 ^? param3 of
          Just v  -> resultC v
          Nothing -> lift $ left $
            "invalid argument types to " ++ name ++
              ": got " ++ show (LispList args)
      _ -> lift $ left $ "wrong number of arguments to " ++ name ++
        ": expected 3; got " ++ show (LispList args)

-- builtins

createEnv :: (LispFunc -> LispVal) -> [(String, String -> LispFunc)] -> Env
createEnv c ps =
    (Impure, fromList $ map (fst &&& c . convert) $ ps)
  where convert (name, partial) = partial name

builtinFuncs =
  createEnv LispWFunc [("progn", HaskellFunc ?? return . last),
                       ("eval",  liftL eval id id),
                       ("apply", liftL2 neApply id _LispList id),
                       ("list", HaskellFunc ?? return . LispList),
                       ("cons", liftL2 (:) id _LispList $ gb _LispList),
                       ("concat", liftL2 (++)
                         _LispList _LispList $ gb _LispList),
                       ("append", liftL2 (flip (++) . pure)
                         id _LispList $ gb _LispList),
                       ("car",  liftL safeHead _LispList $ gb id),
                       ("cdr",  liftL safeTail _LispList $ gb _LispList),
                       ("impure", liftL id
                         (lwfunc . _LispFunc) $
                         gb (_LispWIPFunc . _LispFunc)),
                       ("func",   liftL id
                         (lwfunc . _LispFunc) $
                         gb (_LispWFunc . _LispFunc)),
                       ("fexpr",  liftL id
                         (lwfunc . _LispFunc) $
                         gb (_LispWFexpr . _LispFunc)),
                       ("vmacro", liftL id
                         (lwfunc . _LispFunc) $
                         gb (_LispWVmacro . _LispFunc)),
                       ("macro",  liftL id
                         (lwfunc . _LispFunc) $
                         gb (_LispWMacro . _LispFunc)),
                       ("add",  liftL2 (+) _LispNum _LispNum $ gb _LispNum),
                       ("sub",  liftL2 (-) _LispNum _LispNum $ gb _LispNum),
                       ("mul",  liftL2 (*) _LispNum _LispNum $ gb _LispNum),
                       ("div",  liftL2 (/) _LispNum _LispNum $ gb _LispNum),
                       ("eq",  liftL2 (==) id id $ gb _LispBool),
                       ("gt",  liftL2 (>) _LispNum _LispNum $ gb _LispBool),
                       ("lt",  liftL2 (<) _LispNum _LispNum $ gb _LispBool),
                       ("bool", liftL lispToBool id $ gb _LispBool),
                       ("and", liftL2 (&&)
                         _LispBool _LispBool $ gb _LispBool),
                       ("or", liftL2 (||)
                         _LispBool _LispBool $ gb _LispBool),
                       ("not", liftL not _LispBool $ gb _LispBool),
                       ("read", liftL lispRead _LispSym id),
                       ("is-num",  liftL (has _LispNum)  id $ gb _LispBool),
                       ("is-bool", liftL (has _LispBool) id $ gb _LispBool),
                       ("is-sym",  liftL (has _LispSym)  id $ gb _LispBool),
                       ("is-list", liftL (has _LispList) id $ gb _LispBool),
                       ("is-func", liftL (has lwfunc)    id $ gb _LispBool),
                       ("try", liftL3 lispTry id id id id)]
builtinFexprs =
  createEnv LispWFexpr [("quote", liftL id id $ gb id),
                        ("define", liftL2 define _LispSym id id),
                        ("lambda", liftL2 lambda
                          (_LispList . below _LispSym) id id),
                        ("if", liftL3 lispIf id id id id)]
builtinIPFuncs =
  createEnv LispWIPFunc [("puts", liftL (lispPrint putStrLn)
                           id $ lift . lift),
                         ("print", liftL (lispPrint putStr)
                           id $ lift . lift),
                         ("gets", HaskellFunc ?? lift . lift . lispGets),
                         ("read-file", liftL lispReadFile _LispSym id)]
defaultEnv = builtinIPFuncs `eunion` builtinFuncs `eunion` builtinFexprs

lispTry :: LispVal -> LispVal -> LispVal -> LispM
lispTry proc succ catch = do
  env <- get
  let io = runEitherT $ runStateT (neApply proc []) env
  res <- lift $ lift io
  case res of
    Left err       -> neApply catch [LispSym err]
    Right (v, env) -> put env >> neApply succ [v]

lispReadFile :: String -> LispM
lispReadFile fn = do
  exists <- lift $ lift $ doesFileExist fn
  if exists
    then do
      code <- lift $ lift $ readFile fn
      lift $ right $ LispSym code
    else lift $ left $ "no such file: " ++ fn

lispRead :: String -> LispM
lispRead s =
  case parseTerm "(read)" s of
    Right v -> return v
    Left  e -> lift $ left $ show e

lispGets :: [LispVal] -> IO LispVal
lispGets prompt = do
  putStr $ unwords (map show prompt) ++ " "
  LispSym <$> getLine

lispPrint :: (String -> IO a) -> LispVal -> IO LispVal
lispPrint p = (LispList [] <$) . p . show

safeHead :: [LispVal] -> LispVal
safeHead [] = LispList []
safeHead (x:xs) = x

safeTail :: [a] -> [a]
safeTail [] = []
safeTail (x:xs) = xs

define :: String -> LispVal -> LispM
define "this" _ = lift $ left "can't assign to 'this'"
define name v   = eval v >>= StateT . assign
  where assign ev env = right (ev, einsert name ev env)

lispIf :: LispVal -> LispVal -> LispVal -> LispM
lispIf cond then' else' = do
  econd <- eval cond
  eval (if lispToBool econd
    then then'
    else else')

lispToBool :: LispVal -> Bool
lispToBool v =
  case v of
    LispBool False -> False
    LispNum 0      -> False
    LispList []    -> False
    _              -> True

lambda :: [String] -> LispVal -> LispM
lambda pnames body = do
  closure <- get
  return $ LispWFunc $ LispFunc closure pnames body

-- parsing

prefixes = fromList [('\'', "quote"),
                         ('`', "quasiquote"),
                         (',', "dequote")]
termP = do
  quoted <- optionMaybe $ oneOf $ keys prefixes
  spaces
  case quoted of
    Just pre -> do
      inner <- termP
      return $ LispList [LispSym $ prefixes ! pre, inner]
    Nothing  -> numP <|> boolP <|> symP <|> listP

numP = LispNum <$> Text.Parsec.Numbers.parseFloat

boolP =
  try (string "True" >> return (LispBool True)) <|>
    try (string "False" >> return (LispBool False))

symP = rawSymP <|> quotedSymP
rawSymP = LispSym <$> liftA2 (:) first (many rest)
  where first = letter <|> oneOf "-_"
        rest  = alphaNum <|> oneOf "-_"
quotedSymP =
  LispSym <$> between (char '"') (char '"') (many1 $ noneOf "\"")

listP = do
  char '('
  items <- termP `sepEndBy` spaces
  char ')'
  return $ LispList items

parseTerm :: String -> String -> Either ParseError LispVal
parseTerm = parse termP

-- io

repl :: Env -> IO ()
repl env = do
  putStr "bLisp> "
  code <- getLine
  v <- exec env "(repl)" code
  case v of
    Just (res, newEnv) -> putStrLn ("=> " ++ show res) >> repl newEnv
    Nothing -> repl env

exec :: Env -> String -> String -> IO (Maybe (LispVal, Env))
exec env source code =
  case parseTerm source code of
    Left err   -> print err >> return Nothing
    Right expr -> do
      let prog = runEitherT $ runStateT (eval expr) env
      pres <- prog
      case pres of
        Left err -> putStrLn ("*** - " ++ err) >> return Nothing
        Right (res, newEnv) -> return $ Just (res, newEnv)

main = do
  hSetBuffering stdout NoBuffering
  stdlib <- readFile "stdlib.bl"
  Just (_, env) <- exec defaultEnv "stdlib.bl" stdlib
  args <- getArgs
  case args of
    fn:_ -> do
      code <- readFile fn
      () <$ exec env fn code
    []   -> do
      putStrLn "Welcome to bLisp!"
      repl env

