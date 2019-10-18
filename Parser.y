-- -*- mode: haskell -*-

{
{- Author: <Your name here>
   File: Parser.y

   A parser for the Tiger language.
-}

module Tiger.Parser ( parse ) where

import Tiger.Token ( Token(..) )
import qualified Tiger.Syntax as S

}

--%expect 0             -- expect 0 conflicts in this grammar
                      -- comment this line out to allow happy to run
%name parse           -- exported function will be called parse
%tokentype { Token }  -- input is list of tokens
%error     { (error . show) }   -- what to do in event of emergency

-- Declare all terminals with a %token declaration:
%token
  ID                        {ID $$}
  STR                       {STR $$}
  INTEGER                   {INTGR $$}
  COMMA                     {COMMA}
  COLON                     {COLON}
  SEMICOLON                 {SEMICOLON}
  LPAREN                    {LPAREN}
  RPAREN                    {RPAREN}
  LBRACK                    {LBRACK}
  RBRACK                    {RBRACK}
  LBRACE                    {LBRACE}
  RBRACE                    {RBRACE}
  DOT                       {DOT}
  PLUS                      {PLUS}
  MINUS                     {MINUS}
  TIMES                     {TIMES}
  DIVIDE                    {DIVIDE}
  EQUALT                    {EQUALT}
  NEQUALT                   {NEQUALT}
  LESSTHAN                  {LESSTHAN}
  LESSTHANEQ                {LESSTHANEQ}
  GREATERTHAN               {GREATERTHAN}
  GREATERTHANEQ             {GREATERTHANEQ}
  AND                       {AND}
  OR                        {OR}
  ASSIGN                    {ASSIGN}
  ARRAY                     {ARRAY}
  IF                        {IF}
  THEN                      {THEN}
  ELSE                      {ELSE}
  WHILE                     {WHILE}
  FOR                       {FOR}
  TO                        {TO}
  DO                        {DO}
  LET                       {LET}
  IN                        {IN}
  END                       {END}
  OF                        {OF}
  BREAK                     {BREAK}
  NIL                       {NIL}
  FUNCTION                  {FUNCTION}
  VAR                       {VAR $$}
  TYPE                      {TYPE}

%right    OF
%nonassoc DO
%nonassoc ELSE
%nonassoc ASSIGN
%left     OR AND
%nonassoc EQUALT NEQUALT LESSTHAN LESSTHANEQ GREATERTHAN GREATERTHANEQ
%left     PLUS MINUS
%left     TIMES DIVIDE
%left     NEG

%%

-- Expressions. (These come first because an overall Tiger program is an expression.)
program  : exp                                                  {$1}

exp      : lval                                                 {S.Lvalue $1}
         | NIL                                                  {S.Nil}
         | LPAREN sequencing RPAREN                             {S.Seq $2}
         | liter                                                {S.Literal $1}
         | MINUS exp %prec NEG                                  {S.Negate $2}
         | ID LPAREN args RPAREN                                {S.Call $1 $3 }
         | exp PLUS exp                                         {S.Binary $1 S.Plus $3}
         | exp MINUS exp                                        {S.Binary $1 S.Minus $3}
         | exp TIMES exp                                        {S.Binary $1 S.Times $3}
         | exp DIVIDE exp                                       {S.Binary $1 S.Divides $3}
         | exp EQUALT exp                                       {S.Binary $1 S.Equals $3}
         | exp NEQUALT exp                                      {S.Binary $1 S.NotEquals $3}
         | exp LESSTHAN exp                                     {S.Binary $1 S.Less $3}
         | exp LESSTHANEQ exp                                   {S.Binary $1 S.LessEquals $3}
         | exp GREATERTHAN exp                                  {S.Binary $1 S.Greater $3}
         | exp GREATERTHANEQ exp                                {S.Binary $1 S.GreaterEquals $3}
         | exp AND exp                                          {S.Binary $1 S.LogicalAnd $3}
         | exp OR exp                                           {S.Binary $1 S.LogicalOr $3}
         | ID LBRACE rcd RBRACE                                 {S.NewRecord $1 $3}
         | ID LBRACK exp RBRACK OF exp                          {S.NewArray $1 $3 $6}
         | lval ASSIGN exp                                      {S.Assign $1 $3}
         | IF exp THEN exp ELSE exp                             {S.If $2 $4 (Just $6)}
         | IF exp THEN exp                                      {S.If $2 $4 (Nothing)}
         | WHILE exp DO exp                                     {S.While $2 $4}
         | FOR ID ASSIGN exp TO exp DO exp                      {S.For $2 $4 $6 $8}
         | BREAK                                                {S.Break}
         | LPAREN RPAREN                                        { S.Seq [] }
         | LET decs IN seqlet END                             {S.Let $2 $4}


lval     : ID                                                   {S.VarLV $1}
         | ID DOT ID                                            {S.FieldLV (S.VarLV $1) $3 }
         | lval DOT ID                                          {S.FieldLV $1 $3}
         | lval LBRACK exp RBRACK                               {S.ArrayLV $1 $3}
         | ID LBRACK exp RBRACK                                 {S.ArrayLV (S.VarLV $1) $3}


sequencing : exp SEMICOLON exp sequence1                        {$1 : $3 : $4}
           | exp                                               {[$1]}

sequence1 : SEMICOLON exp sequence1                             {$2 : $3}
          | {- empty -}                                         {[]}

liter    : INTEGER                                              {S.IntLit $1}
         | STR                                                  {S.StringLit $1}


args     : exp args_rest                                        {$1 : $2}
         | {- empty -}                                          {[]}

args_rest: COMMA exp args_rest                                  {$2 : $3}
         | {- empty -}                                          {[]}


rcd      : ID EQUALT exp rcd1                                   { ($1, $3) : $4 }
         | {- empty -}                                          {[]}

rcd1     :COMMA ID EQUALT exp rcd1                              { ($2, $4) : $5 }
         | {-empty-}                                            {[]}

seqlet  : exp seqletrest                                        {$1 : $2}
          | {- empty -}                                         {[]}
seqletrest : SEMICOLON exp seqletrest                           { $2 : $3 }
           | {- empty -}                                        { [] }

decs     : dec1 decs                                            {$1 : $2}
         | {- empty -}                                          {[]}

dec1 : typedecl                                                 {S.TypeD $1}
     | vardecl                                                  {S.VarD  $1}
     | fundecl                                                  {S.FunD  $1}

typedecl : TYPE ID EQUALT typ                                  {S.TD $2 $4}

typ      : ID                                                  {S.Named $1}
         | LBRACE typefields RBRACE                            {S.Struct $2}
         | ARRAY OF ID                                         {S.Array $3}


typefields : ID COLON ID typefield1                             { (S.TF $1 $3) : $4 }
           | {-empty-}                                          {[]}


typefield1 : COMMA ID COLON ID  typefield1                      { (S.TF $2 $4) : $5 }
           | {-empty-}                                         {[]}

vardecl : VAR ID ASSIGN exp                                         {S.PlainVar $2 $4}
        | VAR ID COLON ID ASSIGN exp                                {S.AnnotVar $2 $4 $6}

fundecl : FUNCTION ID LPAREN typefields RPAREN EQUALT exp           {S.Proc $2 $4 $7}
        | FUNCTION ID LPAREN typefields RPAREN COLON ID EQUALT exp  {S.Fun $2 $4 $7 $9 }

{
concatseq  expr (exprs) = (expr:exprs)

maketuple a b = (a, b)
}
