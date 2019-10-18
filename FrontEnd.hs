{- Author: Richard Eisenberg, inspired by Steve Zdancewic
Lisa H & Tanjuma H
   File: FrontEnd.hs

   Compiles Tiger to LLVM.
-}

{-# LANGUAGE OverloadedLists #-}

module FrontEnd where

import Tiger.Syntax as T
import LLVM.Lite    as L

import CS350.CompileM    ( CompileM, compileError )
import CS350.Panic
import CS350.Renderable  ( Renderable(..) )
import CS350.Unique      ( newUniqueString, Unique, newUnique )

import Control.Monad     ( when, zipWithM_, unless, replicateM )
import Control.Monad.Extra  ( mconcatMapM , concatMapM)
import Data.Bits         ( toIntegralSized )
import Data.Char         ( ord )
import Data.Foldable     ( toList )
import Data.Int          ( Int16 )
import Data.List         ( unzip4, zipWith4, genericLength, zipWith5 )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Sequence     ( Seq(..), empty, (|>), (<|), (><), fromList )
import Data.Tuple.Extra  ( fst3 )
import Text.Printf       ( printf )


-- Overview -----------------------------------------------------------------

{- The job of the frontend is to translate Tiger's abstract syntax into
   the LLVM IR, implementing the source language semantics in terms of
   the target language constructs.

   Because the LLVM IR is typed, the frontend must also propagate
   enough type information so that we can generate appropriate type
   annotations at the LLVM level.
-}

-- Instruction Streams ------------------------------------------------------

{- The compiler emits code by generating a stream of instructions interleaved
   with declarations that should be hoisted to the global scope.

   The result of each translation function (typically) includes a stream.     -}
data Element
  = L Label                 -- Block labels
  | I Local Instruction     -- LL IR instruction
  | T Terminator           -- Block terminators
  | H Hoisted               -- A global declaration in LLVM
  deriving Show

data Hoisted
  = HGlobal (Named GlobalDecl)    -- Global declaration
  | HTy (Named L.Ty)              -- Type declaration
  | HFun (Named FunDecl)          -- Function declaration
  deriving Show

-- A Stream is a Sequence of Elements. We use Sequence instead of ordinary
-- lists because Sequences are more efficient for appending together.
-- You may happily pretend that a Seq is just a list -- only some function names
-- are different. Look online for Data.Sequence to see the relevant functions.
-- Note that the `mconcat` function is useful for concatenating Seqs.
type Stream = Seq Element

-- This is occasionally useful for debugging.
instance Renderable Element where
  render (L lbl)      = printf "L: %s" lbl
  render (I uid insn) = printf "I: %%%s = %s" uid (render insn)
  render (T t)        = printf "T: %s" (render t)
  render (H h)        = printf "H: %s" (render h)

instance Renderable Hoisted where
  render (HGlobal gbl)   = render gbl
  render (HTy ty)        = render ty
  render (HFun fun)      = render fun

-- Convert an instruction stream into a control flow graph and a list
-- of hoisted declarations.
buildCfg :: Stream -> (Cfg, [Hoisted])
buildCfg stream = ( Cfg { entry = entry_block
                        , blocks = labeled_blocks }
                  , entry_hoisted ++ more_hoisted )
  where
    (entry_block, entry_hoisted, lbl_stream) = get_entry_block stream
    (labeled_blocks, more_hoisted)           = get_labeled_blocks lbl_stream

    get_entry_block    = go_block empty []

    get_labeled_blocks (L lbl :<| es) = ((lbl, block) : other_blocks, globs ++ other_globs)
      where
        (block, globs, stream)      = go_block empty [] es
        (other_blocks, other_globs) = get_labeled_blocks stream

    get_labeled_blocks (H h :<| es)  = (blocks, h : other_hs)
      where
        (blocks, other_hs) = get_labeled_blocks es

    get_labeled_blocks (e :<| _)     = panic $ "Unexpected element: " ++ render e
    get_labeled_blocks Empty         = ([], [])

    go_block :: Seq (Local, L.Instruction)  -- accumulator for instructions
             -> [Hoisted]                   -- accumulator for hoisted definitions
                                            -- (order does not matter)
             -> Stream -> (Block, [Hoisted], Stream)
      -- returns the block, the hoisted globals, and the remainder of the
      -- stream
    go_block _     _     (L lbl :<| _)       = panic $ "Label in middle of block: " ++ lbl
    go_block insns globs (I uid insn :<| es) = go_block (insns |> (uid, insn)) globs es
    go_block insns globs (T term :<| es)     = ( Bl { instructions = toList insns, terminator = term }
                                               , globs
                                               , es )
    go_block insns globs (H h :<| es)        = go_block insns (h : globs) es
    go_block _     _     Empty               = panic "Unterminated block"

-- Helper functions -----------------------------------------------------

-- Make an appropriate L.GlobalInit for a given type.
mkGlobalInit :: Type -> GlobalInit
mkGlobalInit (IBuiltIn TigerInt)    = IntGI 0
mkGlobalInit (IBuiltIn TigerString) = NullGI

-- generalization of zipWithM in Control.Monad
zipWith3M :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWith3M f (x : xs) (y : ys) (z : zs) = do
  result <- f x y z
  results <- zipWith3M f xs ys zs
  pure (result : results)
zipWith3M _ _ _ _ = pure []

-- Checking types -----------------------------------------------------------

{- Both Tiger and LLVM are *typed* languages. In the process of converting a
   Tiger program to LLVM, we must carefully track the types of definitions in
   Tiger so that we can produce well-typed LLVM. Along the way, we can also
   *type-check* the Tiger program to make sure that it is indeed well-typed.
   (After all, an ill-typed Tiger program can hardly be expected to produce
   a well-typed LLVM program.) The functions in this section do this type-
   checking.

-}

-- internal representation of types within the type-checker
-- distinct from Tiger types because users can redefine Tiger
-- type names. The "I" prefixes denote "Internal"
data Type
  = IBuiltIn BuiltInTy
  -- you will neeed to add more to compile types
  deriving Eq

instance Renderable Type where
  render (IBuiltIn b) = render b

-- convenient abbreviations
tigerInt :: Type
tigerInt = IBuiltIn TigerInt

tigerString :: Type
tigerString = IBuiltIn TigerString

-- Ensure that the given type is equivalent to "int". If it isn't, issue
-- a compiler error.
checkIntType :: Type -> CompileM ()
checkIntType (IBuiltIn TigerInt) = pure ()
checkIntType ty = compileError $ "Expected an int, but got " ++ render ty

-- Ensure that the given result is really Nothing
checkVoidResult :: Maybe (Type, x) -> CompileM ()
checkVoidResult Nothing = pure ()
checkVoidResult (Just (ty, _))
  = compileError $ "Expected no value, but got something of type " ++ render ty

--get tiger type from Maybe tuple
getType :: Maybe (Type, x) -> CompileM Type
getType (Just (t, x)) = pure t
getType Nothing = compileError "Input is Nothing."

-- Ensure that the two given types are the same.
checkTypesEqual :: Type -> Type -> CompileM ()
checkTypesEqual ty1 ty2
  | ty1 == ty2   -- shortcut if they're identical already
  = pure ()
  | otherwise
  = compileError $ "Type error. Mismatch between " ++ render ty1 ++ " and " ++ render ty2


  -- Given two maybe tuples, ensure that the two given types are the same.
checkOpTypesEqual :: Maybe (Type, L.Operand) -> Maybe (Type, L.Operand) -> CompileM ()
checkOpTypesEqual Nothing Nothing = pure ()
checkOpTypesEqual (Just (ty1, _)) (Just (ty2, _)) = do
  if ty1 == ty2
    then pure ()
  else compileError $ "Type error. Mismatch between operand types."
checkOpTypesEqual _ _ = compileError $ "Type error. Mismatch between operand types."

getOps :: Maybe (Type, L.Operand) -> Maybe (Type, L.Operand) -> CompileM (L.Operand, L.Operand)
getOps Nothing Nothing = compileError $ "Type error. Both inputs must be Just values."
getOps (Just (_, o1)) (Just (_, o2)) = pure (o1, o2)



-- Contexts -----------------------------------------------------------------

{- We once again need to track a *compilation context*, which contains
   information needed in order to produce LLVM code from Tiger. This context
   gets modified when the Tiger code brings more definitions into scope.
-}

data Context = Ctx { ctx_vars :: M.Map T.VarId (Type, L.Operand)
                      -- map Tiger variable names to their types and LL operands
                   , ctx_types :: M.Map T.TypeId Type
                      -- map Tiger type names to types
                   , ctx_break :: Maybe L.Label
                      -- if we're in a loop, contains the label to jump to when
                      -- 'break'ing
                   , ctx_toplevel :: Bool
                      -- True if we're outside of every function; false if we're
                      -- inside a function
                   , ctx_funs :: M.Map T.FunId (L.Global, Maybe Type, [Type])
                      -- map Tiger function names to the LL name, the return
                      -- type (if there is one) and a list of argument types
                   }

-- Get the type and operand associated with a Tiger variable.
-- Issues an error if the variable name is unknown.
lookupVar :: Context -> VarId -> CompileM (Type, L.Operand)
lookupVar (Ctx { ctx_vars = vars }) var
  | Just result <- M.lookup var vars = pure result
  | otherwise                        = compileError $ "Unbound variable " ++ var

-- Given a Type, gets the corresponding LLVM type.
lookupType :: Context -> Maybe Type -> CompileM L.Ty
lookupType _ Nothing = pure L.Void
lookupType _ (Just (IBuiltIn TigerInt)) = pure I16
lookupType _ (Just (IBuiltIn TigerString)) = pure pstring

-- Given a Maybe (Type, L.Operand), gets the corresponding LLVM type.
lookupOpType :: Maybe (Type, L.Operand) -> CompileM L.Ty
lookupOpType Nothing = pure L.Void
lookupOpType (Just ((IBuiltIn TigerInt), _)) = pure I16
lookupOpType (Just ((IBuiltIn TigerString), _)) = pure pstring

-- Look up a TypeId to get a Type
lookupTypeId :: Context -> T.TypeId -> CompileM Type
lookupTypeId (Ctx { ctx_types = types }) typeid
  | Just ty <- M.lookup typeid types = pure ty
  | otherwise                        = compileError $ "Unknown type: " ++ typeid

-- Get the label that corresponds to breaking out of the innermost loop.
-- Fails if we are not in a loop.
lookupBreakLabel :: Context -> CompileM L.Label
lookupBreakLabel (Ctx { ctx_break = Just lbl }) = pure lbl
lookupBreakLabel (Ctx { ctx_break = Nothing  })
  = compileError "Use of 'break' outside of a loop"

-- Are we outside of any function?
isTopLevel :: Context -> Bool
isTopLevel = ctx_toplevel

-- Get the LLVM name of a function, along with the types the function
-- returns and expects.
lookupFunction :: Context -> T.FunId -> CompileM (L.Global, Maybe Type, [Type])
lookupFunction (Ctx { ctx_funs = funs }) fun
  | Just result <- M.lookup fun funs = pure result
  | otherwise                        = compileError $ "Unknown function: " ++ fun

bindVariable :: Context -> Type -> T.VarId -> L.Operand -> Context
bindVariable ctx@(Ctx { ctx_vars = vars }) ty var op
  = ctx { ctx_vars = M.insert var (ty, op) vars }

bindFunctions :: Context -> [(T.FunId, [TyField], Maybe T.TypeId)] -> [L.Global]
              -> CompileM Context
bindFunctions ctx@(Ctx { ctx_funs = funs }) ((tiger_name, arg_fields, m_ret_id) : new_funs)
                                            (ll_name : ll_funs) = do
  arg_typs <- mapM tyfield_to_type arg_fields
  m_ret_ty <- case m_ret_id of
                Nothing -> pure Nothing
                Just id -> do ret_ty <- lookupTypeId ctx id
                              pure (Just ret_ty)
  let ctx1 = ctx { ctx_funs = M.insert tiger_name (ll_name, m_ret_ty, arg_typs) funs }
  bindFunctions ctx1 new_funs ll_funs

  where
    tyfield_to_type (TF _ id) = lookupTypeId ctx id

bindFunctions ctx _ _ = pure ctx  -- the lists are empty

bindBreakLabel :: Context -> L.Label -> Context
bindBreakLabel ctx lbl = ctx { ctx_break = Just lbl }

unbindBreakLabel :: Context -> Context
unbindBreakLabel ctx = ctx { ctx_break = Nothing }

setNotTopLevel :: Context -> Context
setNotTopLevel ctx = ctx { ctx_toplevel = False }

-- Prelude ------------------------------------------------------------------

{- Every compiler has some set of predefined constructs. This is sometimes called
   a "prelude". Our prelude items are defined in this section.
-}

stdlibFuns :: M.Map T.FunId (L.Global, Maybe Type, [Type])
stdlibFuns = M.fromList [ print, flush, getchar, ord, chr
                        , size, substring, concat, not, exit, print_int]
  where
    print     = ("print",     ("tiger_print",     Nothing,          [tigerString]))
    flush     = ("flush",     ("tiger_flush",     Nothing,          []))
    getchar   = ("getchar",   ("tiger_getchar",   Just tigerString, []))
    ord       = ("ord",       ("tiger_ord",       Just tigerInt,    [tigerString]))
    chr       = ("chr",       ("tiger_chr",       Just tigerString, [tigerInt]))
    size      = ("size",      ("tiger_size",      Just tigerInt,    [tigerString]))
    substring = ("substring", ("tiger_substring", Just tigerString, [tigerString, tigerInt, tigerInt]))
    concat    = ("concat",    ("concat",          Just tigerString, [tigerString, tigerString]))
    not       = ("not",       ("tiger_not",       Just tigerInt,    [tigerInt]))
    exit      = ("exit",      ("tiger_exit",      Nothing,          [tigerInt]))

    -- not in standard, but very useful
    print_int = ("print_int", ("tiger_print_int", Nothing,          [tigerInt]))

initialContext :: Context
initialContext = Ctx { ctx_vars = M.empty
                     , ctx_types = M.fromList [ ("int", tigerInt)
                                              , ("string", tigerString) ]
                     , ctx_break = Nothing
                     , ctx_toplevel = True
                     , ctx_funs = stdlibFuns
                     }

-- These external functions should be declared for every LLVM program.
externals :: CompileM [L.Named L.FunTy]
externals = do
  ll_decls <- mapM to_ll_decl (M.elems stdlibFuns)
  pure $ [ N { name = "malloc", decl = FunTy (L.Ptr I16) [I16] }
         , N { name = "tstrcmp", decl = FunTy I16 [pstring, pstring] } ] ++
         ll_decls
  where
    to_ll_decl (ll_name, m_ret_type, arg_types) = do
      ll_ret_ty <- lookupType initialContext m_ret_type
      ll_arg_tys <- mapM (lookupType initialContext . Just) arg_types
      pure (N { name = ll_name
              , decl = FunTy ll_ret_ty ll_arg_tys })

-- Compiling Types ----------------------------------------------------------

{- Definitions around linking Tiger types to LLVM types. This section must
   expand considerably to support type definitions.
-}

int :: L.Ty
int = I16

string :: L.Ty
string = L.Struct [I16, L.Array 0 I16]

pstring :: L.Ty
pstring = Ptr string

-- LL IR helper functions ---------------------------------------------------

{- Generate a fresh identifier based on a given string.  Because Tiger
   identifiers cannot begin with _, the resulting string is guaranteed
   not to clash with another source language construct.
-}
newId :: String -> CompileM String
newId name = newUniqueString ('_' : name)

-- This convenience function produces an Element for an instruction, generating
-- a new LLVM local name along the way.
newInstruction :: L.Instruction -> CompileM (Element, L.Operand)
newInstruction insn = do
  local <- newId "local"
  pure (I local insn, LocalId local)

-- Allocate memory in the heap. The returned operand has the type given
-- (which must be a pointer type), and the size of the memory is indicated
-- in the given operand. (This is *not* need in HW05.)
malloc :: L.Ty -> L.Operand -> CompileM (Stream, L.Operand)
malloc ll_ty size_op = do
  (malloc_insn, malloc_op)
    <- newInstruction (L.Call (L.Ptr I16) (GlobalId "malloc")
                              [(I16, size_op)])
  (cast_insn, cast_op)
    <- newInstruction (Bitcast (L.Ptr I16) malloc_op ll_ty)

  pure ([malloc_insn, cast_insn], cast_op)

-- Compare two strings, pointers to which are stored in the operands given. (That
-- is, both operands should have type 'pstring'.)
-- The returned operand is an I16; it is a value
-- less than 0 iff the first string is less than the second (lexicographically),
-- equal to 0 iff the first string equals the second, and
-- greater than 0 iff the first string is greater than the second
tstrcmp :: L.Operand -> L.Operand -> CompileM (Stream, L.Operand)
tstrcmp lhs rhs = do
  (tstrcmp_insn, result)
    <- newInstruction (L.Call I16 (GlobalId "tstrcmp")
                              [(pstring, lhs), (pstring, rhs)])
  pure ([tstrcmp_insn], result)

-- Compile a declaration block ----------------------------------------------

{- According to the definition of Tiger, declarations come in three forms:
   variable declarations, type declarations, and function declarations.
   The latter two of these can be mutually recursive, meaning that two
   definitions might each refer to the other. To account for this, we view
   both type declarations and function declarations as groups; according
   to the spec, a mutually recursive group of type/function declarations
   must not have any intervening declarations of another sort. Accordingly,
   when we spot a type or function declaration, we must search forward for
   all such declarations, accumulate them into a list, and process them
   all at once.

   No such special treatmnt is necessary for variable declarations, which
   may not be recursive in Tiger.

   Because declarations bring new constructs into scope, the
   compileDeclarations function returns a new Context, extended to include
   the new constructs. It also returns a Stream that contains the type
   declarations, along with the variable declarations and function declarations.

   Special care must be taken around variable declarations. If these are
   at top-level, we want to make sure that the variables are accessible in
   all functions -- that is, they must be compiled into LLVM globals.
   If a variable declaration is not at top-level, it can just be alloca'd
   in the current function's stack, as we do not support nested function
   declarations.
-}

compileDeclarations :: Context -> [T.Dec] -> CompileM (Stream, Context)
compileDeclarations ctx (VarD vd : rest) = do
  (s1, lhs, rhs_ty, rhs_op) <- compileVarDec ctx vd
  ll_ty <- lookupType ctx (Just rhs_ty)
  (alloca, lhs_op) <- if isTopLevel ctx
    then do global_name <- newId lhs
            let global_init = mkGlobalInit rhs_ty
                glob = N { name = global_name
                         , decl = GD { globalType = ll_ty
                                     , globalInit = global_init }}
            pure (H (HGlobal glob), GlobalId global_name)

    else newInstruction (Alloca ll_ty)

  (store, _) <- newInstruction (Store ll_ty rhs_op lhs_op)
  let ctx1 = bindVariable ctx rhs_ty lhs lhs_op
  (s2, ctx2) <- compileDeclarations ctx1 rest -- use ctx1 because the new
                                              -- var is in scope in the rest

  pure (s1 >< alloca <| store <| s2, ctx2)

compileDeclarations ctx (TypeD td : rest) =
  compileTypeDeclarations ctx [td] rest

compileDeclarations ctx (FunD fd : rest) =
  compileFunDeclarations ctx [fd] rest

compileDeclarations ctx [] = pure (empty, ctx)

-- Compiling a VarDec produces:
--  1) a stream that computes the value assigned to the variable
--  2) the name of the Tiger variable
--  3) the type of the Tiger variable
--  4) the LLVM operand storing the initial value of the Tiger variable
compileVarDec :: Context -> VarDec -> CompileM (Stream, T.VarId, Type, L.Operand)
compileVarDec ctxt vdec = case vdec of
  (PlainVar vid exp1) -> do
    (s, r) <- compileExp ctxt exp1
    case r of
      Just (t, o) -> pure (s, vid, t, o)
      _           -> compileError "DOES NOT PRODUCE A VALUE"
  (AnnotVar vid tid exp1) -> do
    typ    <- lookupTypeId ctxt tid
    (s, r) <- compileExp ctxt exp1
    case r of
      Just (t, o) -> do
        checkTypesEqual t typ
        pure (s, vid, typ, o)
      _   -> compileError "DOES NOT PRODUCE A VALUE"




-- Compiling a type declaration accumulates all type declarations
-- into one group and adds them to the context. Then, this context
-- is used to compile the remaining declarations.
compileTypeDeclarations :: Context -> [TyDec] -> [T.Dec] -> CompileM (Stream, Context)
compileTypeDeclarations ctx _ decls = compileDeclarations ctx decls   -- ignore types for now

-- Compiling a function declaration accumulates all function declarations
-- into one group and then compiles them. It then compiles the remaining
-- declarations in the list of declarations under the new context.
compileFunDeclarations :: Context -> [FunDec] -> [T.Dec] -> CompileM (Stream, Context)
compileFunDeclarations ctx fun_decs (FunD fd : decls)
  = compileFunDeclarations ctx (fd : fun_decs) decls
compileFunDeclarations ctx fun_decs decls = do
  let xs = getFunlist fun_decs
  globlob <- makeLLVMnames fun_decs
  newctxt <- bindFunctions ctx xs globlob
  let params = concatMap (\(_,tyfield,_) -> [tyfield]) xs
  tigerparamtypes <- concatMapM (\tfs -> do let tys = concatMap (\(TF _ ty) -> [ty]) tfs
                                            pure [tys]) params
  paramtypes <- concatMapM (\tigertypeIDs -> do
                              tgtypes <- concatMapM (\id -> do result <- lookupTypeId newctxt id
                                                               pure [result]) tigertypeIDs
                              llty    <- mconcatMapM (\ty -> do result <- lookupType newctxt (Just ty)
                                                                pure [result]) tgtypes
                              pure [llty]) tigerparamtypes

  let decswithbod = concatMap (\f -> case f of
                                      Proc funid tfs exp  ->  [(funid, tfs, Nothing, exp)]
                                      T.Fun funid tfs tid exp ->  [(funid, tfs, Just tid, exp)]) fun_decs

  cmplfuns <- mconcatMapM (\y -> compileFuns (setNotTopLevel newctxt) y) decswithbod
  ftyps <- concatMapM (\(_,_,tid,_) -> do
    case tid of
      Nothing -> pure [Void]
      Just ty -> do tigtype <- lookupTypeId newctxt ty
                    llvmTy <- lookupType newctxt (Just tigtype)
                    pure [llvmTy]) decswithbod
  let (funstr, alcls) = unzip cmplfuns
      functionCfgs = concatMap (\y -> [buildCfg y]) funstr
      (cfgz, llvmHoist) = unzip functionCfgs
      hoistedd = concatMap (\s -> s) llvmHoist
      finalehoist = concatMap (\hi -> [H hi]) hoistedd
      namedtdecs = zipWith5 (\g t l c a -> H (HFun (N { name = g, decl = FD {functionType = FunTy t a, functionParams = l, functionCfg = c}}))) globlob ftyps alcls cfgz paramtypes
  (streamx, dectxt) <- compileDeclarations newctxt decls
  pure ( fromList (finalehoist ++ namedtdecs) >< streamx, dectxt)


--cfd helper funcs
getFunlist :: [FunDec] -> [(T.FunId, [TyField], Maybe T.TypeId)]
getFunlist [] =  []
getFunlist [x] = case x of
  (T.Proc funid tfs exp) ->  [(funid, tfs, Nothing)]
  (T.Fun funid tfs tid exp) ->  [(funid, tfs, Just tid)]
getFunlist (x:xs) = case x of
  (T.Proc funid tfs exp) -> do
    let rest = getFunlist xs
    ([(funid, tfs, Nothing)] ++ rest)
  (T.Fun funid tfs tid exp) -> do
    let rest = getFunlist xs
    ([(funid, tfs, Just tid)] ++ rest)



makeLLVMnames :: [FunDec] -> CompileM [L.Global]
makeLLVMnames fundecs = concatMapM (\y -> do nid <- newId "FUNCTION"
                                             pure ([nid])) fundecs
-- [] = []
--makeLLVMnames [(f, _, _)] = [(newId f)]
-- makeLLVMnames [(f, _ , _): ys] = ((newId f) : makeLLVMnames ys )

complArg :: Context -> [TyField] -> [L.Local] -> CompileM (Stream, [L.Local], Context)
complArg ctxt [] _ = pure ([], [], ctxt)
complArg ctxt tyfields@((TF fieldID tyID) : tfx)  alcls = do
  paramname <- newId fieldID
  tiTy <- lookupTypeId ctxt tyID
  llTy <- lookupType ctxt (Just tiTy)
  (alloElem, ret) <- newInstruction (Alloca llTy)
  (storePar, _) <- newInstruction (Store llTy (LocalId paramname) ret)
  let vs = [alloElem] >< [storePar]
  let bvctxt = bindVariable ctxt tiTy fieldID ret
  let vctxt = setNotTopLevel (unbindBreakLabel bvctxt)
  (rs, rlocs, rctxt) <- complArg vctxt tfx alcls
  pure (vs >< rs, [paramname] ++ rlocs, rctxt)


compileFuns :: Context -> (FunId, [TyField], Maybe T.TypeId, Exp) -> CompileM [(Stream, [L.Local])]
compileFuns ctxt (funid, tyfs, returnty, bod) = do
  (vstr, localz, vctxt) <- complArg ctxt tyfs []
  (exprstr, retval) <- compileExp vctxt bod
  case returnty of
    Just tid -> do
     case retval of
          Just (typi, op) -> do
            tigerRty <- lookupTypeId vctxt tid
            checkTypesEqual typi tigerRty
            llvmtype <- lookupType vctxt (Just tigerRty)
            let returnterm = T (Ret llvmtype (Just op))
            pure [((vstr >< exprstr >< [returnterm]), localz)]
          Nothing -> compileError "wrong type"
    Nothing -> do
      case retval of
        Just _ -> compileError "wrong type"
        Nothing -> pure [((vstr >< exprstr >< [T (Ret Void Nothing)]), localz)]



  {- In this clause of compileFunDeclarations, you have to do the hard work.
     Because functions can be mutually recursive, the first step is to arrange
     a call to bindFunctions; doing so will require extracting various information
     from the FunDecs and generating names for the LLVM functions (with newId).

     Then, you'll have to compile the function bodies in the extended context
     returned by bindFunctions. This, in turn, requires four steps, completed
     separately for each function (a helper function might be useful):

       1) Compile the argument list. Here, you have to come up with a name
          for the LLVM equivalent of the Tiger argument (with newId). More
          surprisingly, you will have to 'alloca' space for the argument.
          This is because arguments in Tiger are *editable*, as in this
          example:

            let function silly(x : int) : int = ( x := x + 1; x ) in silly(5) end

          Note that x is updated within the function silly. LLVM, of course,
          doesn't allow this directly. So, we treat x like a local variable,
          allocating space for its value with alloca, and then copying the
          passed-in value into that allocated space (with a 'store' instruction).

          The instructions to store the argument in the allocated space should
          end up at the beginning of the stream.

       2) Update the context to bind the parameter variables, remove the 'break'
          label, and set the context not to be at top-level. Use this updated
          context only when compiling the function at hand, not other functions:
          one function's parameters are definitely not in scope for other functions!

       3) Compile the expression in the function body, resulting in a stream.
          Don't forget to terminate the stream by returning the final value.

       4) Use buildCfg to convert the Stream into a Cfg, and use that to build
          an LLVM Named FunDecl. Put that Named FunDecl into the output stream
          as a "hoisted" element (along with all the hoisted elements returned
          from buildCfg).

     After compiling all the functions, don't forget to call compileDeclarations
     to nab the rest of the declarations in the enclosing 'let', with the context
     extended with the functions. (That is, this context should be the result
     of bindFunctions, *not* any of the contexts built while compiling the function
     bodies.) -}

-- Compile an Lvalue --------------------------------------------------------

{- Lvalues comprise a limited form of expression that denote a place that
   be assigned to. These include plain variables, array locations, and structure
   locations. Because we might want to update a value in an Lvalue, we compile
   an Lvalue into a *pointer* to the memory that might be updated. Thus, if
   our source Lvalue has type t, then compiling it yields an LLVM type
   (Ptr (lookupType t)).
-}

-- Returns a Stream, the type pointed to, and the operand where the resulting
-- pointer lives. Note that the type is the type pointed to, not the type
-- of the Lvalue itself.
compileLvalue :: Context -> T.Lvalue -> CompileM (Stream, Type, L.Operand)
compileLvalue ctxt y = do
  case y of
    VarLV vid -> do
      (typ, popeye) <- lookupVar ctxt vid
      llvmty <- lookupType ctxt (Just typ)
      pure ([], typ, popeye)
    FieldLV _ _ -> unimplemented "compileFieldLV"
    ArrayLV _ _ -> unimplemented "compileArrayLV"

  -- For HW05, you need not handle the FieldLV or ArrayLV cases. Write these
  -- cases in (to avoid pattern-match incompleteness warnings), but just
  -- use 'unimplemented' to report an error.

-- Compile an expression ----------------------------------------------------

{- This is the main workhorse of the compiler. It returns a stream of instructions
   needed to execute the instruction.

   Invariant: The stream returned never ends with a terminator T. (If it did, we
              wouldn't be able to add more instructions.)

   If the Tiger expression results in no value, the second return value from
   this function is Nothing. Otherwise, it is the Type and Operand of the result.
-}
processStringOp :: L.Operand -> L.Operand -> (Stream, L.Operand) -> Condition -> CompileM (Stream, L.Operand)
processStringOp op1 op2 (s, o) cond = do
  (comp, op)       <- newInstruction (Icmp cond I16 o (L.Const 0))
  (alloca, ptr_res) <- newInstruction (Alloca I16)
  (store_then, _)  <- newInstruction (Store I16 (L.Const 1) ptr_res)
  (store_else, _)  <- newInstruction (Store I16 (L.Const 0) ptr_res)
  (load, result)   <- newInstruction (Load (Ptr I16) ptr_res)
  then_lbl <- newId "then"
  else_lbl <- newId "else"
  merge_lbl <- newId "merge"
  pure (s >< [comp, alloca, T (L.Cbr op then_lbl else_lbl), L then_lbl, store_then, T (L.Br merge_lbl), L else_lbl, store_else, T (L.Br merge_lbl), L merge_lbl, load], result)

expandint :: L.Operand -> L.Operand -> Condition -> CompileM (Stream, L.Operand)
expandint xop yop cond = do
  (comp, op)       <- newInstruction (Icmp cond I16 xop yop)
  (alloca, ptr_res) <- newInstruction (Alloca I16)
  (store_then, _)  <- newInstruction (Store I16 (L.Const 1) ptr_res)
  (store_else, _)  <- newInstruction (Store I16 (L.Const 0) ptr_res)
  (load, result)   <- newInstruction (Load (Ptr I16) ptr_res)
  then_lbl <- newId "then"
  else_lbl <- newId "else"
  merge_lbl <- newId "merge"
  pure (comp <| [alloca, T (L.Cbr op then_lbl else_lbl), L then_lbl, store_then, T (L.Br merge_lbl),
                 L else_lbl, store_else, T (L.Br merge_lbl), L merge_lbl, load], result)

transTy :: Type -> Int
transTy (IBuiltIn TigerInt) = 1
transTy (IBuiltIn TigerString) = 0


compileExp :: Context -> T.Exp -> CompileM (Stream, Maybe (Type, L.Operand))
compileExp ctxt tex = case tex of
  (Literal (IntLit x)) -> pure (empty, Just (tigerInt, L.Const (fromIntegral x)))
  (Literal (StringLit x)) -> do
    (s, r) <- compileString x
    pure (s, Just (tigerString, r))
  (Lvalue lval) -> do
    (s, t, o) <- compileLvalue ctxt lval
    pure ((s), Just (t, o))
  --
  (For vid exp1 exp2 exp3) -> do --VarLV

    (str1, ty1, op1)<- compileValueExp ctxt (Assign (VarLV vid) exp1)
    (str2, ty2, op2)<- compileValueExp ctxt exp2
    checkTypesEqual ty2 ty1
    checkIntType ty1
    brkid <- newId "break"
    strtid <- newId "start"
    bodid <- newId "body"
    let brkLbl = L brkid
    let strtlbl = L strtid
    let bodlbl = L bodid
    let brnch = T (Br strtid)
    let brctxt = bindBreakLabel ctxt brkid
    (elemi, opi) <- newInstruction (Icmp Sle I16 op1 op2)
    (str3, op3) <- compileExp brctxt exp3
    case op3 of
      Just (_, _) -> compileError "val cannot be produced by while hallelujah"
      Nothing -> pure ([brnch] >< [strtlbl] >< str1 >< str2 >< [elemi] >< [T (Cbr opi bodid brkid)] >< [bodlbl] >< str3 >< [brnch] >< [brkLbl], Nothing)
  (Assign lval expr) -> do
    (s, t, o) <- compileLvalue ctxt lval
    (str, ty, op)<- compileValueExp ctxt expr
        ---is this really I16
    (str1, _) <- newInstruction (Store I16 op o)
    pure (((s >< str) |> str1), Just (ty, op))
  (Let decs exprs) -> do
    (str, ctx) <- compileDeclarations ctxt decs
    go ctx exprs str
  (Negate expr) -> do
    (str, ty, op1) <- compileValueExp ctxt expr
    checkIntType ty
    (elemi, op) <- newInstruction (Binop Mul I16 (L.Const (-1)) op1)
    pure ((str |> elemi), Just (ty, op))
  (While exp1 exp2) -> do
    (str1, ty1, op1) <- compileValueExp ctxt exp1
    checkIntType ty1
    brkid <- newId "break"
    strtid <- newId "start"
    bodid <- newId "body"
    let brkLbl = L brkid
    let strtlbl = L strtid
    let bodlbl = L bodid
    let brnch = T (Br strtid)
    let brctxt = bindBreakLabel ctxt brkid
    (str2, tyop2) <- compileExp brctxt exp2
    (elemi, opi) <- newInstruction (Icmp Eq I16 op1 (Const 1))
    case tyop2 of
      Just (_, _) -> compileError "val cannot be produced by while hallelujah"
      Nothing -> pure ([brnch] >< [strtlbl] >< str1 >< [elemi] >< [T (Cbr opi bodid brkid)] >< [bodlbl] >< str2 >< [brnch] >< [brkLbl], Nothing)
  (Binary expr1 op expr2) -> do
    (s1, t1, o1) <- compileValueExp ctxt expr1
    let getty = transTy t1
    case getty of
      0 -> case op of
          Greater -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            tcmp <- tstrcmp o1 o2
            (s, r) <- processStringOp o1 o2 tcmp Sgt
            pure ((s1 >< s2 >< s), Just (tigerInt, r))
          GreaterEquals -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            tcmp <- tstrcmp o1 o2
            (s, r) <-  processStringOp o1 o2 tcmp Sge
            pure ((s1 >< s2 >< s), Just (tigerInt, r))
          LessEquals -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            tcmp <- tstrcmp o1 o2
            (s, r) <- processStringOp o1 o2 tcmp Sle
            pure ((s1 >< s2 >< s), Just (tigerInt, r))
          Less -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            tcmp <- tstrcmp o1 o2
            (s, r) <- processStringOp o1 o2 tcmp Slt
            pure ((s1 >< s2 >< s), Just (tigerInt, r))
          NotEquals -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            tcmp <- tstrcmp o1 o2
            (s, r) <- processStringOp o1 o2 tcmp Ne
            pure ((s1 >< s2 >< s), Just (tigerInt, r))
          Equals -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            tcmp <- tstrcmp o1 o2
            (s, r) <- processStringOp o1 o2 tcmp Eq
            pure ((s1 >< s2 >< s), Just (tigerInt, r))
          _ -> compileError "Cannot perform anything other than boolean operations on strings."
      1 -> do
        case op of
          Plus -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- newInstruction (Binop Add I16 o1 o2)
            pure ((s1 >< s2) |> s, Just (tigerInt, r))
          Minus -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- newInstruction (Binop Sub I16 o1 o2)
            pure ((s1 >< s2) |> s, Just (tigerInt, r))
          Times -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- newInstruction (Binop Mul I16 o1 o2)
            pure ((s1 >< s2) |> s, Just (tigerInt, r))
          Divides -> compileError "Division is not supported."
          Greater -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- expandint o1 o2 Sgt
            pure ((s1 >< s2) >< s, Just (tigerInt, r))
          GreaterEquals -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- expandint o1 o2 Sge
            pure ((s1 >< s2) >< s, Just (tigerInt, r))
          LessEquals -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- expandint o1 o2 Sle
            pure ((s1 >< s2) >< s, Just (tigerInt, r))
          Less -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- expandint o1 o2 Slt
            pure ((s1 >< s2) >< s, Just (tigerInt, r))
          NotEquals -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- expandint o1 o2 Ne
            pure ((s1 >< s2) >< s, Just (tigerInt, r))
          Equals -> do
            (s2, t2, o2) <- compileValueExp ctxt expr2
            chk <- checkTypesEqual t1 t2
            (s, r) <- expandint o1 o2 Eq
            pure ((s1 >< s2) >< s, Just (tigerInt, r))
          LogicalAnd -> do
            case o1 of
              (L.Const 0) -> pure (s1, Just (t1, o1))
              _ -> do
                 (s2, t2, o2) <- compileValueExp ctxt expr2
                 checkTypesEqual t1 t2
                 (elemi, opi) <- newInstruction (Icmp Ne I1 o2 (L.Const 0))
                 pure (((s1 >< s2) |> elemi), Just (t1, opi))
          LogicalOr -> do
            case o1 of
              (L.Const 0) -> do
                (s2, t2, o2) <- compileValueExp ctxt expr2
                checkTypesEqual t1 t2
                (elemi, opi) <- newInstruction (Icmp Ne I1 o2 (L.Const 0))
                pure (((s1 >< s2) |> elemi), Just (t1, opi))
              _ -> pure (s1, Just (t1, o1))
  (Seq expr) -> go ctxt expr empty


  (If exp1 exp2 maybeexp) -> case maybeexp of
    (Just exp3) -> do
      (s1, t1, o1) <- compileValueExp ctxt exp1 --compile exp1
      chk1 <- checkIntType t1 --make sure exp1 returns int
      (s2, r2) <- compileExp ctxt exp2
      (s3, r3) <- compileExp ctxt exp3
      checkOpTypesEqual r2 r3
      llty <- lookupOpType r2 --get the llvm type of exp2 and exp3
      case llty of
        L.Void -> do
          (alloca, ptrresult) <- newInstruction (Alloca llty)
          (storethen, _) <- newInstruction (Store llty L.Null ptrresult)
          (storeelse, _) <- newInstruction (Store llty L.Null ptrresult)
          (load, result) <- newInstruction (Load (Ptr llty) ptrresult)
          thenlabel <- newId "then"
          elselabel <- newId "else"
          mergelabel <- newId "merge"
          pure ((s1 >< [alloca, T (L.Cbr o1 thenlabel elselabel), L thenlabel] >< s2 >< [storethen, T (Br mergelabel), L elselabel ] >< s3 >< [storeelse, T (Br mergelabel), L mergelabel, load]), Nothing)

        _ -> do
          (o2,o3) <- getOps r2 r3 --get the operands of exp2 and exp3
          (alloca, ptrresult) <- newInstruction (Alloca llty)
          (storethen, _) <- newInstruction (Store llty o2 ptrresult)
          (storeelse, _) <- newInstruction (Store llty o3 ptrresult)
          (load, result) <- newInstruction (Load (Ptr llty) ptrresult)
          thenlabel <- newId "then"
          elselabel <- newId "else"
          mergelabel <- newId "merge"
          ty <- getType r2
          pure (s1 >< [alloca, T (L.Cbr o1 thenlabel elselabel), L thenlabel] >< s2 >< [storethen, T (Br mergelabel), L elselabel ] >< s3 >< [storeelse, T (Br mergelabel), L mergelabel, load], Just (ty, result))
    (Nothing) -> do
      (s1, Just (t1, o1)) <- compileExp ctxt exp1
      (s2, r2) <- compileExp ctxt exp2
      chk1 <- checkIntType t1
      chk2 <- checkVoidResult r2
      (alloca, ptrresult) <- newInstruction (Alloca L.Void)
      (storethen, _) <- newInstruction (Store L.Void L.Null ptrresult)
      (storeelse, _) <- newInstruction (Store L.Void L.Null ptrresult)
      (load, result) <- newInstruction (Load (Ptr L.Void) ptrresult)
      thenlabel <- newId "then"
      elselabel <- newId "else"
      mergelabel <- newId "merge"
      pure (s1 >< [alloca, T (L.Cbr o1 thenlabel elselabel), L thenlabel] >< s2 >< [storethen, T (L.Br mergelabel), L elselabel ] >< [storeelse, T (Br mergelabel), L mergelabel, load], Nothing)
  _ -> pure (empty, Nothing)


--helper function for compileExp
go :: Context -> [T.Exp] -> Stream -> CompileM (Stream, Maybe (Type, L.Operand))
go ctxt [x] str = do
   (st, y) <- compileExp ctxt x
   let str1 = (str >< st)
   case y of
     Just (ty, op) -> pure (str1, Just (ty, op))
     Nothing       -> pure (str1, Nothing)
go ctxt (x:xs) str = do
    (st, _ ) <- compileExp ctxt x
    go ctxt xs (str >< st)
go ctxt [] str = pure (str, Nothing)





  {- For HW05 you need not handle Nil, NewRecord, or NewArray.
     As in compileLvalue, pattern-match on these, but simply call
     'unimplemented' to issue an error.


     A few tips:
      * Remember to type-check. Every part of an expression has a type.
        These types always have some restriction on them (except for
        expressions that are not the last expression in a sequence).
        Check to make sure the types are correct.

      * See the compileString function, below, for dealing with string
        literals.

      * Our version of Tiger does not support division. Issue an
        error if the user tries to divide.

      * Tiger integers are unbounded (stored as Haskell 'Integer'),
        but LLVM works only with I16. Do not worry about this:
        just use fromIntegral to convert.

      * Remember that & and | are short-circuting operators: they do
        not evaluate their right-hand operands if the final value is
        determined by the left-hand operand.

      * The natural way to implement comparisons will result in an
        LLVM I1. But Tiger will want an int, which is an LLVM I16.
        You will need to write some code that *widens* an I1 into an I16
        of the same value. This can be done with code that behaves
        like 'if b then 1 else 0'.

      * String comparisons require real work, as we need to compare
        individual letters in the strings. You can do this work via
        the function tstrcmp, which will be linked against your compiled
        LLVM code. The tstrcmp function takes in two strings and returns
        an int (I16). The return value is less than 0 iff the first string
        is less than the second, 0 iff the first string equals the second,
        and greater than 0 iff the first string is greater than the second.
        (This is just like C's strcmp function or Java's compareTo functions.)
        The call to tstrcmp can be arranged by calling the Haskell
        function tstrcmp defined above.

      * 'If' is a bit tricky. Use the example from the NB language in class
        for inspiration.

      * Remember to update the context with the 'break' label when compiling
        the loop constructs. -}

-- Compile an expression that is expected to result in a value. If the
-- expression does not result in a value, issue a type error to the user.
compileValueExp :: Context -> T.Exp -> CompileM (Stream, Type, L.Operand)
compileValueExp ctx exp = do
  (s, m_result) <- compileExp ctx exp
  case m_result of
    Just (ty, op) -> pure (s, ty, op)
    Nothing       -> compileError "Expected a value where none was found."

{- Getting string constants into LLVM is a bit tricky. The problem is that we want
   all strings to have the type { i16, [0 x i16] }* in LLVM, but we can't usefully define
   global constants of that type. Let

     %string = type { i16, [0 x i16] }

   That is, a string is its length, along with an array containing the actual data.
   Here might be an attempt to declare an actual string:

     @hello = global %string { i16 5, [5 x i16] [i16 104, i16 101, i16 108, i16 108, i16 111] }

   The problem is that this doesn't type-check, because a %string's second component
   should have 0 elements, not 5. So, we can't declare @hello this way.

   The solution to this is bitcast, which can change the type of a pointer.
   With this in mind, we declare @hello with its correct type, as follows:

     @hello = global { i16, [5 x i16] }
                     { i16 5, [5 x i16] [i16 104, i16 101, i16 108, i16 108, i16 111] }

   Now, when we want to access @hello, we bitcast it into the right type (with
   a supposedly 0-length array):

     %1 = bitcast { i16, [5 x i16] }* @hello to { i16, [0 x i16] }*

   At this point, %1 has the desired type. This is all done by compileString.
-}

-- Compile a string. The returned operand has type 'pstring' and points to
-- the string requested. The actual characters for the string are stored as
-- global data.
compileString :: String -> CompileM (Stream, Operand)
compileString string = do
  let len = length string
  string_name <- newId "string"
  let array_ty = L.Array len I16
      glob_ty  = L.Struct [I16, array_ty]
      string_glob = H $ HGlobal $
        N { name = string_name
          , decl = GD { globalType = glob_ty
                      , globalInit =
                        L.StructGI [ GD { globalType = I16
                                        , globalInit = IntGI (fromIntegral len) }
                                   , GD { globalType = array_ty
                                        , globalInit = ArrayGI (map (GD I16 .
                                                                     IntGI .
                                                                     fromIntegral .
                                                                     ord) string) }]}}

  (bitcast, result) <- newInstruction (Bitcast (L.Ptr glob_ty)
                                               (GlobalId string_name)
                                               pstring)

  pure ([string_glob, bitcast], result)

-- Compile a top-level program ----------------------------------------------

-- We will end up with a list of hoisted elements, but we need to repackage
-- these into an LLVM Program object.
partitionHoisteds :: [Hoisted] -> ([Named L.Ty], [Named GlobalDecl], [Named FunDecl])
partitionHoisteds = go [] [] []
  where
    go tys globs funs (HGlobal glob : hs) = go tys (glob:globs) funs hs
    go tys globs funs (HTy ty       : hs) = go (ty:tys) globs funs hs
    go tys globs funs (HFun fun     : hs) = go tys globs (fun:funs) hs
    go tys globs funs []                  = (tys, globs, funs)

compileProgram :: T.Exp -> CompileM L.Program
compileProgram tex = do
  (s,t,o) <- compileValueExp initialContext tex
  checkIntType t
  let (cfg, hoistedL) = buildCfg (s |> T (Ret L.I16 (Just o)))
  let (typs, globob, funs) = partitionHoisteds hoistedL
  let main = N { name = "main", decl = FD {functionType = FunTy I16 [I16, Ptr (Ptr I8)], functionParams = ["argc", "argv"], functionCfg = cfg }}
  e <- externals
  let program = L.Prog { typeDecls = typs, globalDecls = globob, functionDecls = [main] ++ funs, externalDecls = e}
  pure program


  {- This one is not too bad: call compileValueExp on the given expression, check
     that its type is "int", and then build the resulting Program. Make sure to
     use 'externals' to set the 'externalDecls' field of a Program, so that the
     compiled LLVM code has access to the standard library. -}
