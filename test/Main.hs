{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import Control.Applicative

import Control.Monad (forM, forM_)
import Data.Char (isDigit, ord)
import Data.Either
import Data.Word (Word8)
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxSize, prop)
import Text.TopDownParser

dyck :: Grammar m Char Int
dyck =
  memoize (0 :: Int) $
    ( (\_ x _ y -> max x y)
        <$> char '('
        <*> fmap (+ 1) dyck
        <*> char ')'
        <*> dyck
    )
      <|> pure (0 :: Int)

digit :: Grammar m Char Int
digit = (\n -> ord n - ord '0') <$> satisfy isDigit

number :: Grammar m Char Int
number =
  memoize 1 $
    ((\x y -> 10 * x + y) <$> number <*> digit)
      <|> digit

plus :: Grammar m Char ()
plus =
  memoize 0 $
    ((\_ _ _ -> ()) <$> plus <*> char '+' <*> plus)
      <|> (() <$ number)

catalan :: (Integral i) => [i]
catalan = 1 : zipWith f [1 ..] catalan
  where
    f n cn' = (4 * n - 2) * cn' `div` (n + 1)

spec :: Spec
spec = do
  describe "fullParse dyck" $ do
    it "accepts balanced parens" $
      fullParse dyck "()(())" `shouldBe` Right [2]
    it "rejects unrecognized chars" $
      fullParse dyck "abcd" `shouldSatisfy` isLeft
    it "rejects unblanced parens" $
      fullParse dyck "(()))()" `shouldSatisfy` isLeft
  describe "fullParse number" $ do
    it "can parse '1234'" $
      fullParse number "1234" `shouldBe` Right [1234]
  describe "fullParse plus" $ do
    it "can parse '1+1'" $
      fullParse plus "1+1" `shouldSatisfy` isRight
    forM_ [4 .. 10] $ \(n :: Word8) -> do
      let sn = "1" ++ concat (replicate (fromIntegral n) "+1")
          cn = (catalan !! fromIntegral n) :: Int
      it ("returns " ++ show cn ++ " results for " ++ show sn) $
        fullParse plus sn `shouldBe` Right (replicate cn ())

-- it "behaves for example as" $ example $ do
--   print $ fullParse dyck "(()))()"

main :: IO ()
main = hspec $ do
  spec
