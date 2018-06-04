{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module Generate.Lambda.Builder
  ( exprToBuilder
  , Expr(..)
  )
  where

-- Based on the language-ecmascript package.
-- https://hackage.haskell.org/package/language-ecmascript
-- They did the hard work of reading the spec to figure out
-- how all the types should fit together.

import Data.ByteString.Builder as B
import Data.Monoid ((<>))
import qualified Generate.Lambda.Name as Name
import Generate.Lambda.Name (Name)



-- EXPRESSIONS

data Expr =
  = App Expr Expr Line
  | Lam Name Expr
  | Var Name
  | Def Name Expr Expr
  | Let Name Expr Expr
  | Str Builder
  | Dec Double
  | Int Int

data Line = NewLine | SameLine

-- FUNCTIONS

exprToBuilder :: Expr -> Builder
exprToBuilder expr =
  fromExpr "" expr


fromExpr :: Builder -> Expr -> Builder
fromExpr indent expression =
  let 
    newIndent =
      if newLine expression
        then indent <> "\t"
        else indent

    separator =
      if newLine expression
        then "\n"
        else ""

  in   
    case expression of
      Def name expr inExpr ->
        "@" <> name 
            <> fromExpr newIndent  expr 
            <> separator
            <> fromExpr indent  inExpr

      Let name expr inExpr ->
        ":" <> name 
            <> fromExpr newIndent expr
            <> separator
            <> fromExpr indent  inExpr

      App func expr line ->
        "/" <> fromExpr newIndent func
            <> separator
            <> fromExpr newIndent func

      Lam name expr ->
        "#" <> name
            <> separator
            <> fromExpr newIndent expr

      Var name ->
        name
          
      Str string ->
        "'" <> string <> "'"

      Dec n ->
        B.doubleDec n

      Int n ->
        B.intDec n

-- HELPERS  

newLine :: Expr -> Bool
newLine expression = 
  case expression of
    App _ _ SameLine -> 
      False 
    Lam _ (Lam _ _) -> 
      False
    _ -> 
      True