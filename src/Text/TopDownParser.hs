{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- |
-- Grammar combinators for parsing full CFG.
-- The original idea was proposed by R.A. Frost et al.'s Top-down parsing
--
-- This code is a porting of an implementation used in FliPpr
-- https://bitbucket.org/kztk/flippr/src/master/Text/TDGrammar.hs
--
-- Some of codes are just borrowed from
-- http://cs.uwindsor.ca/~richard/PUBLICATIONS/Demonstration.hs (dead-link)
module Text.TopDownParser (
  Grammar,
  char,
  satisfy,
  memoize,
  currentPosition,
  fullParse,
  fullParseGen,
) where

import Control.Applicative
import Control.Monad (foldM)
import Control.Monad.ST (ST, runST)
import Data.Dynamic (Dynamic, Typeable, fromDynamic, toDyn)
import Data.IntMap (IntMap)
import qualified Data.IntMap as I
import Data.IntSet (IntSet)
import qualified Data.IntSet as S
import Data.Kind (Type)
import Data.Maybe (fromJust, fromMaybe)
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef)

-- import Debug.Trace (trace)

type Key = Int
type KeyMap = IntMap
type Pos = Int

-- Tag for Efficient Ordering and Comparison
data Tag s m c a
  = Tag
      {-# UNPACK #-} !Pos -- Next position used as sorting key
      (InputBuffer s m c)
      [c]
      a

instance (Show c) => Show (Tag s m c a) where
  show (Tag p ib str _) = "Tag " <> show p <> " " <> show ib <> " " <> show str <> " <result>"

data St = Err !Int !Int | Ok
  deriving stock Show

instance Semigroup St where
  Ok <> _ = Ok
  Err _ _ <> Ok = Ok
  Err l1 c1 <> Err l2 c2
    | l1 > l2 = Err l1 c1
    | l1 < l2 = Err l2 c2
    | otherwise = Err l1 (max c1 c2)

instance Monoid St where
  mempty = Err 0 0

data E s m c a = E !St [Tag s m c (m a)]
  deriving stock Show

singletonE :: (Applicative m) => InputBuffer s m c -> [c] -> a -> E s m c a
singletonE ib str r =
  E Ok [Tag (position ib) ib str (pure r)]

instance (Functor m) => Functor (E s m c) where
  fmap f (E s ls) = E s [Tag p ib str (fmap f rs) | Tag p ib str rs <- ls]

emptyE :: (Int, Int) -> E s m c a
emptyE (l, c) = E (Err l c) []

mergeE :: (Alternative m) => E s m c a -> E s m c a -> E s m c a
mergeE (E s1 a) (E s2 b) = E (s1 <> s2) $ sortedMerge a b

sortedMerge :: (Alternative m) => [Tag s m c (m a)] -> [Tag s m c (m a)] -> [Tag s m c (m a)]
sortedMerge [] bs = bs
sortedMerge as [] = as
sortedMerge as@(ia@(Tag i ii s a) : at) bs@(jb@(Tag j _jj _t b) : bt) =
  case i `compare` j of
    LT -> ia : sortedMerge at bs
    EQ -> Tag i ii s (a <|> b) : sortedMerge at bt
    GT -> jb : sortedMerge as bt

type CurtailingNTs = IntSet
type UpResult s m c a = (CurtailingNTs, E s m c a)

type KeyContext = [(Key, Int)] -- Key & Counter pairs

data Stored s m c
  = Stored
  { storedCuts :: !CurtailingNTs
  , storedResults :: !(E s m c Dynamic)
  , storedContext :: !KeyContext
  }

type Memo s m c = KeyMap (Stored s m c)

data InputBuffer s m c = InputBuffer
  { _restString :: String
  , memoRefs :: [STRef s (Memo s m c)]
  , position :: !Pos
  , lineCount :: !Int
  , columnCount :: !Int
  , restLength :: !Int
  }

instance Show (InputBuffer s m c) where
  show (InputBuffer _ _ p l c r) = show (p, l, c, r)

data Grammar (m :: Type -> Type) c a where
  ParseEmpty :: Grammar m c a
  ParsePure :: a -> Grammar m c a
  ParseSatisfy :: (c -> Bool) -> Grammar m c c
  --  ParseText :: [c] -> Grammar m c [c]
  ParseAlt :: Grammar m c a -> Grammar m c a -> Grammar m c a
  ParseSeq :: Grammar m c (a -> b) -> Grammar m c a -> Grammar m c b
  ParseMemo :: (Typeable a) => Key -> Grammar m c a -> Grammar m c a
  ParseParsed :: Grammar m c a -> Grammar m c [c]
  ParsePosition :: Grammar m c (Int, Int, Int)

instance Functor (Grammar m c) where
  fmap f = ParseSeq (ParsePure f)

instance Applicative (Grammar m c) where
  pure = ParsePure
  f <*> x = ParseSeq f x

instance Alternative (Grammar m c) where
  empty = ParseEmpty
  (<|>) = ParseAlt

  many = error "Don't use `many` for Grammar."
  some = error "Don't use `some` for Grammar."

-- text :: [c] -> Grammar m c [c]
-- text = ParseText

char :: (Eq c) => c -> Grammar m c c
char c = ParseSatisfy (== c)

memoize :: (Typeable a, Enum k) => k -> Grammar m c a -> Grammar m c a
memoize k = ParseMemo (fromEnum k)

satisfy :: (c -> Bool) -> Grammar m c c
satisfy = ParseSatisfy

-- parsedString :: Grammar m c a -> Grammar m c [c]
-- parsedString = ParseParsed

currentPosition :: Grammar m c (Int, Int, Int)
currentPosition = ParsePosition

-------------------------------
emptyCuts :: IntSet
emptyCuts = S.empty

data Flag = End | Middle

noSolution :: (Int, Int) -> (IntSet, E s m c a)
noSolution (l, c) = (emptyCuts, emptyE (l, c))

parseErr :: InputBuffer s m c -> (IntSet, E s m c a)
parseErr ib = parseErr' (lineCount ib, columnCount ib)

parseErr' :: (Int, Int) -> (IntSet, E s m c a)
parseErr' (l, c) = noSolution (l, c)

errorE :: InputBuffer s m c -> E s m c a
errorE ib = errorE' (lineCount ib, columnCount ib)

errorE' :: (Int, Int) -> E s m c a
errorE' (l, c) = emptyE (l, c)

nextLC :: (Int, Int) -> Char -> (Int, Int)
nextLC (l, _) '\n' = (l + 1, 0)
nextLC (l, c) _ = (l, c + 1)

-- nextLCs :: (Int, Int) -> String -> (Int, Int)
-- nextLCs (l, c) str = foldl (nextLC) (l, c) str

-- showStatus :: E s m c a -> String
-- showStatus (E s _) = show s

--------------------------------------------------------------------------

type Parser s m c a =
  (Alternative m, Functor m) =>
  KeyContext
  -> InputBuffer s m c
  -> ST s (UpResult s m c a)

parse :: Flag -> Grammar m Char a -> Parser s m Char a
parse _ ParseEmpty _context ib = return $ parseErr ib
parse _ (ParsePure res) _context ib = pure (emptyCuts, singletonE ib [] res)
parse flg (ParseSatisfy predicate) _context (InputBuffer rest memos pos lc cc rlen) = case flg of
  End -> case rest of
    [x]
      | predicate x ->
          let (!lc', !cc') = nextLC (lc, cc) x
              nextIB = InputBuffer [] [] (pos + rlen) lc' cc' 0
          in  pure (emptyCuts, singletonE nextIB [x] x)
    _ ->
      pure $ parseErr' (lc, cc)
  Middle -> case rest of
    x : xs
      | predicate x ->
          let (!lc', !cc') = nextLC (lc, cc) x
              nextIB = InputBuffer xs (tail memos) (pos + 1) lc' cc' (rlen - 1)
          in  pure (emptyCuts, singletonE nextIB [x] x)
    _ ->
      pure $ parseErr' (lc, cc)
parse f (ParseAlt p q) context ib = do
  (cut1, r1) <- parse f p context ib
  (cut2, r2) <- parse f q context ib
  pure (S.union cut1 cut2, mergeE r1 r2)
parse f (ParseSeq p q) context ib = do
  (cut, E e pResults) <- parse Middle p context ib
  let joinForFirst (Tag nextPos nextIB s ps) = do
        let nullP = position ib == nextPos
        let newContext
              | nullP = context
              | otherwise = []
        (newCuts, E e' qResults) <- parse f q newContext nextIB
        let outCuts
              | nullP = newCuts `S.union` cut
              | otherwise = cut
        pure (outCuts, E e' [Tag j jb (s ++ t) (ps <*> qs) | Tag j jb t qs <- qResults])
      joinForRest prevResults (Tag _ nextIB s ps) = do
        (_, E e' qResults) <- parse f q [] nextIB
        pure $
          E e' [Tag j jb (s ++ t) (ps <*> qs) | Tag j jb t qs <- qResults]
            `mergeE` prevResults
  case pResults of
    [] -> pure (cut, E e [])
    r : rs -> do
      (outCuts, firstRes) <- joinForFirst r
      outResults <- foldM joinForRest firstRes rs
      pure (outCuts, outResults)
parse f (ParseMemo etag p) context ib = do
  let memoRef = head $ memoRefs ib
  mTable <- readSTRef memoRef
  case lookupT key context mTable of
    Just res ->
      pure res
    Nothing
      | funcCount context > restLength ib ->
          pure (S.singleton key, errorE ib)
      | otherwise -> do
          let newDownContext = incContext key context
          (upCuts, results) <- parse f p newDownContext ib
          let !toStore =
                Stored
                  upCuts
                  (fmap toDyn results)
                  (pruneContext upCuts context)
          modifySTRef' memoRef (update toStore)
          return (upCuts, results)
  where
    key = case f of
      Middle -> 2 * etag
      End -> 2 * etag + 1
    funcCount cs = fromMaybe 0 (lookup key cs)
    update = I.insert key
parse f (ParseParsed p) context ib = do
  (cut, E s pResults) <- parse f p context ib
  pure (cut, E s $ map h pResults)
  where
    h (Tag p' ib' s _) = Tag p' ib' s (pure s)
parse _ ParsePosition _context ib =
  pure (emptyCuts, singletonE ib "" (position ib, lineCount ib, columnCount ib))

pruneContext :: IntSet -> [(S.Key, t)] -> [(S.Key, t)]
pruneContext rs _
  | S.null rs = []
pruneContext rs ctxt =
  [nc | nc@(n, _) <- ctxt, n `S.member` rs]

incContext :: S.Key -> [(S.Key, Int)] -> [(S.Key, Int)]
incContext name [] = [(name, 1)]
incContext name (nc@(n, c) : ncs)
  | n == name = (n, c + 1) : ncs
  | otherwise = nc : incContext name ncs

lookupT ::
  (Functor m, Typeable a) =>
  Key
  -> KeyContext
  -> KeyMap (Stored s m c)
  -> Maybe (UpResult s m c a)
lookupT key current mTable =
  do
    memo <- I.lookup key mTable
    let cuts = storedCuts memo
    let results = fromDyn' <$> storedResults memo
    if S.null cuts
      then
        return (cuts, results)
      else
        if canReuse current (storedContext memo)
          then
            Just (cuts, results)
          else
            Nothing
  where
    fromDyn' = fromJust . fromDynamic

    canReuse :: KeyContext -> KeyContext -> Bool
    canReuse curr stored =
      and
        [ or
          [ cc >= sc
          | (cn, cc) <- curr
          , sn == cn
          ]
        | (sn, sc) <- stored
        ]

fullParseGen :: (Alternative m) => Grammar m Char a -> [Char] -> Either (Int, Int) (m a)
fullParseGen p string = runST $ do
  refs <- mapM (\_ -> newSTRef I.empty) (undefined : string)
  let !len = length string
  let ib0 = InputBuffer string refs 0 0 0 len
  (_, E s results) <- parse End p [] ib0
  case s of
    Ok ->
      case [rs | Tag i _ _ rs <- results, i == len] of
        fullResults@(_ : _) ->
          pure $ Right $ asum fullResults
        _ ->
          -- Case: `results` only contains early successes.
          pure $ Left $ maximum [(lineCount ib, columnCount ib) | Tag _ ib _ _ <- results]
    Err l c ->
      pure $ Left (l, c)

fullParse :: Grammar [] Char a -> String -> Either (Int, Int) [a]
fullParse = fullParseGen