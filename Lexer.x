-- -*- mode: haskell -*-

{
{- Author: <Lisa H. & Tanjuma H.>
   File: Lexer.x

   A lexer file for Tiger.
-}

{-# OPTIONS_GHC -W -Wno-unused-top-binds #-}

module Tiger.Lexer ( lexTiger ) where

import Tiger.Token  ( Token(..) )

import Data.Char    ( isSpace, isDigit, chr )
}

%wrapper "basic"

-- Add definitions for character sets and regular expressions here:

$digit      = 0-9
$Letter        = [A-Za-z_]
$LetterOrDigit = [0-9$Letter]
@Identifier    = $Letter($LetterOrDigit | _ )*
@Strng = \" [^ \"]* \"

$AnyChar = [.\n]

@CommentElement    = ($AnyChar # \*) | \*+ ($AnyChar # \/)
@CommentTerminator = \*+ \/
@CommentTail       = @CommentElement* @CommentTerminator

@TraditionalComment = "/*" @CommentTail


@Comment        =  @TraditionalComment

Tiger :-

-- Add lexing rules here:
$white                                                           ;
@Comment                                                         ;
","                                                              { \_ -> COMMA}
":"                                                              { \_ -> COLON}
";"                                                              { \_ -> SEMICOLON}
"("                                                              { \_ -> LPAREN}
")"                                                              { \_ -> RPAREN}
"["                                                              { \_ -> LBRACK}
"]"                                                              { \_ -> RBRACK}
"{"                                                              { \_ -> LBRACE}
"}"                                                              { \_ -> RBRACE}
"."                                                              { \_ -> DOT}
"+"                                                              { \_ -> PLUS}
"-"                                                              { \_ -> MINUS}
"*"                                                              { \_ -> TIMES}
"/"                                                              { \_ -> DIVIDE}
"="                                                              { \_ -> EQUALT}
"<>"                                                             { \_ -> NEQUALT}
"<"                                                              { \_ -> LESSTHAN}
"<="                                                             { \_ -> LESSTHANEQ}
">"                                                              { \_ -> GREATERTHAN}
">="                                                             { \_ -> GREATERTHANEQ}
"&"                                                              { \_ -> AND}
"|"                                                              { \_ -> OR}
":="                                                             { \_ -> ASSIGN}
array                                                            { \_ -> ARRAY}
if                                                               { \_ -> IF}
then                                                             { \_ -> THEN}
else                                                             { \_ -> ELSE}
while                                                            { \_ -> WHILE}
for                                                              { \_ -> FOR}
to                                                               { \_ -> TO}
do                                                               { \_ -> DO}
let                                                              { \_ -> LET}
in                                                               { \_ -> IN}
end                                                              { \_ -> END}
of                                                               { \_ -> OF}
break                                                            { \_ -> BREAK}
nil                                                              { \_ -> NIL}
function                                                         { \_ -> FUNCTION}
type                                                             { \_ -> TYPE}
var                                                              { \s -> VAR s}
@Identifier                                                      { \s -> ID s}
@Strng                                                           { \s -> STR (toHaskellString s)}
[$digit]+                                                        { \s -> INTGR (read s)}

{

lexTiger :: String -> [Token]
lexTiger = alexScanTokens


unquote :: String -> String
unquote (_:xs) = init xs
unquote [] = []

toHaskellString :: String -> String
toHaskellString str = do
  let unquotstr = unquote str
  go unquotstr

go :: String -> String
go [] = []
go [x] = [x]
go ('\\': xs) = processEsc xs
go (x:xs) = x : (go xs)

            --[]
            --[p] where p is not one of {'*', '\\', 't', 'n'}
            --[p, _] where p is not one of {'*', '\\', 't', 'n'}

processEsc :: String -> String
processEsc [] = []
processEsc [x] = [x]
processEsc ('n' : xs) = '\n' : go xs
processEsc ('t' : xs) = '\t' : go xs
processEsc ('\\' : xs) = '\\' : go xs
processEsc ('*' : xs) = '*' : go xs
processEsc (x:y:z:xs) = do
  if (isDigit x) && (isDigit y) && (isDigit z)
    then do
      let code = getIntCode (charToInt x) (charToInt y) (charToInt z)
      let newchar = chr code
      newchar : go xs
  else x:y:z:(go xs)
processEsc [_,_] = error "Illegal string input"

charToInt :: Char -> Int
charToInt c | '0' <= c && c <= '9' = fromEnum c - fromEnum '0'
            | otherwise = -1

getIntCode :: Int -> Int -> Int -> Int
getIntCode a b c = a*100 + b*10 + c


}
