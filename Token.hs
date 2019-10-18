{- Author: Lisa Hou & Umme Tanjuma Haque
   File: Token.hs

   Defines lexical tokens for Tiger
-}

{-# LANGUAGE DeriveGeneric, DeriveAnyClass, EmptyDataDeriving #-}

module Tiger.Token where

import Control.DeepSeq ( NFData )
import GHC.Generics    ( Generic )

data Token
  = ID String
   | STR String
   | INTGR Integer
   | COMMA
   | COLON
   | SEMICOLON
   | LPAREN
   | RPAREN
   | LBRACK
   | RBRACK
   | LBRACE
   | RBRACE
   | DOT
   | PLUS
   | MINUS
   | TIMES
   | DIVIDE
   | EQUALT
   | NEQUALT
   | LESSTHAN
   | LESSTHANEQ
   | GREATERTHAN
   | GREATERTHANEQ
   | AND
   | OR
   | ASSIGN
   | ARRAY
   | IF
   | THEN
   | ELSE
   | WHILE
   | FOR
   | TO
   | DO
   | LET
   | IN
   | END
   | OF
   | BREAK
   | NIL
   | FUNCTION
   | VAR String
   | TYPE
 deriving (Show, Eq, Generic, NFData)
