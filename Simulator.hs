{- Author: Lisa Hou and Umme Tanjuma Haque, with structure by Richard Eisenberg
   File: Simulator.hs

   A simulator for the HERA-2.4 machine
-}

{-# LANGUAGE GADTs #-}
  -- We're not really using GADTs here, but sometimes type inference wants this
  -- to be enabled when writing functions over IOVectors.

{-# OPTIONS_GHC -W -Wno-unused-imports #-}
  -- enable standard warnings, but don't care about unused imports

module Simulator where

import HERA.Base
import Data.Bits             ( clearBit, setBit, FiniteBits, (.&.), (.|.), xor, shift, shiftL, shiftR, bit, testBit )
import Data.Char             ( ord )
import Data.Int              ( Int16, Int8 )
import qualified Data.Vector as I         -- "I" for immutable
import Data.Vector           ( Vector )   -- get Vector without qualification
import qualified Data.Vector.Mutable as M
import Data.Vector.Mutable   ( IOVector )
import Data.Word             ( Word16, Word8 )
import Data.IORef            ( IORef, newIORef, readIORef, writeIORef, modifyIORef )
                                -- an IORef is a mutable pointer
import Text.Printf           ( printf )

import Control.Monad         ( when, forM_ )

import HERA.Base             ( Register, Condition(..), fp, memorySize, numRegisters, haltedPC
                             , dataBottom )
import HERA.Machine          ( MInstruction(..), Target(..), MachineProgram(..)
                             , DataSegment(..) )
import CS350.WordN           ( Word5, bitList, listBits )
import CS350.Panic           ( panic, unimplemented )

-- Initialize with something easily recognizable:
defaultWord :: Word16
defaultWord = 0xbaba

-- We have 5 flags
numFlags :: Int
numFlags = 5

-- These are the flag indices:
sFlagIndex, zFlagIndex, vFlagIndex, cFlagIndex, cbFlagIndex :: Int
sFlagIndex = 0
zFlagIndex = 1
vFlagIndex = 2
cFlagIndex = 3
cbFlagIndex = 4

-- These flag-index/value pairs are pinned:
pinnedFlags :: [(Int, Bool)]
pinnedFlags = [(vFlagIndex, False), (cFlagIndex, False), (cbFlagIndex, True)]

------------------------------------------------------------
-- Machine definition

-- The state of our machine is laid out here:
data Machine = M { memory       :: IOVector Word16     -- the machine's memory
                 , registers    :: IOVector Word16     -- the register file
                 , flags        :: IOVector Bool       -- the flags
                 , pcRef        :: IORef Word16        -- the program counter
                 , instructions :: Vector MInstruction -- the program (immutable)
                 }

-- create a Machine to run a given assembled program
load :: MachineProgram -> IO Machine
load (MP { text = prog, dayta = dat }) = do
  mem  <- M.replicate memorySize defaultWord
  regs <- M.replicate numRegisters 0
  flgs <- M.replicate numFlags False
  pc   <- newIORef 0   -- PC starts at 0

  -- write the data to the data segment of memory
  let write_data base offset datum = M.write mem (base + offset) datum
      write_segment (DS { location = data_loc
                        , contents = bytes })
        = I.imapM_ (write_data (fromIntegral data_loc)) bytes
  I.mapM_ write_segment dat

  -- register 0 is always 0:
  M.write regs 0 0
  writePinnedFlags flgs

  -- construct the machine:
  pure (M { memory       = mem
          , registers    = regs
          , flags        = flgs
          , pcRef        = pc
          , instructions = prog })

-- print the machine state to the user
printMachine :: Machine -> IO ()
printMachine (M { memory    = mem
                , registers = regs
                , flags     = flgs
                , pcRef     = pc }) = do
  putStrLn "*** Non-0xbaba memory locations:"
  forM_ [0..memorySize-1] print_memory_loc

  putStrLn ""
  putStrLn "*** Registers:"
  forM_ [0..numRegisters-1] print_register

  putStrLn ""
  putStr "*** Flags: "
  s <- M.read flgs sFlagIndex
  z <- M.read flgs zFlagIndex
  printf "s = %s; z = %s\n" (show s) (show z)

  pc_val <- readIORef pc
  printf "*** Program counter: 0x%04x\n" pc_val

  where
    print_memory_loc addr = do
      val <- M.read mem addr
      when (val /= defaultWord) (printf "    0x%04x: 0x%04x\n" addr val)

    print_register reg = do
      val <- M.read regs reg
      printf "   r%2d = 0x%04x = %d\n" reg val val

-------------------------------------------------------------
-- Utility functions (feel free to add more)

-- Given a Register, get its index in the register vector
registerIndex :: Register -> Int
registerIndex = fromEnum  -- use the magic of the Enum class, to good effect

-- Convert a string into a length-prefixed sequence of words.
toLpString :: String -> [Word16]
toLpString str
  = fromIntegral (length str) : map (fromIntegral . ord) str

-- Given a reference to the flags register, set the pinned flags.
writePinnedFlags :: IOVector Bool -> IO ()
writePinnedFlags flgs = mapM_ write_flag pinnedFlags
  where
    write_flag (index, val) = M.write flgs index val



-------------------------------------------------------------
-- Main simulator

-- This steps the machine by one step forward.
--   1. Fetch the instruction from the location given by the PC
--   2. Process the instruction, updating registers and flags
--   3. Update the PC (unless the instruction is a branch, in which case
--      it's already been updated)
--
-- Returns whether or not the machine has halted (True means halted).
-- In our case, a halted machine has a PC at 0xdead.

step :: Machine -> IO Bool
step (M { memory       = mem
        , registers    = regs
        , flags        = flgs
        , pcRef        = pc
        , instructions = insns }) = do

    pc_val <- readIORef pc

    let insn = insns I.! fromIntegral(pc_val)

    case insn of
      (MSetlo d val)           -> do  M.write regs (registerIndex d) (fromIntegral val)
                                      writeIORef pc (pc_val + 1)

      (MSethi d val)           -> do  n1 <- (M.read regs (registerIndex d))
                                      let n2 = n1 .&. 255
                                      let n3 = (fromIntegral val) :: Word16
                                      let n4 = shiftL n3 8
                                      M.write regs (registerIndex d) (n2 .|. n4)
                                      writeIORef pc (pc_val + 1)

      (MAnd d a b)             -> do  n1 <- M.read regs (registerIndex a)
                                      n2 <- M.read regs (registerIndex b)
                                      let fin = (n1 .&. n2)
                                      M.write regs (registerIndex d) (fin)
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)


      (MOr d a b)              -> do  n1 <- M.read regs (registerIndex a)
                                      n2 <- M.read regs (registerIndex b)
                                      let fin = (n1 .|. n2)
                                      M.write regs (registerIndex d) (fin)
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)


      (MXor d a b)             -> do  n1 <- M.read regs (registerIndex a)
                                      n2 <- M.read regs (registerIndex b)
                                      let fin = (xor n1 n2)
                                      M.write regs (registerIndex d) (fin)
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)


      (MAdd r1 r2 r3)          -> do  n1 <- M.read regs (registerIndex r2)
                                      n2 <- M.read regs (registerIndex r3)
                                      let fin = (n1 + n2)
                                      M.write regs (registerIndex r1) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)


      (MSub r1 r2 r3)          -> do  n1 <- M.read regs (registerIndex r2)
                                      n2 <- M.read regs (registerIndex r3)
                                      let fin = (n1 - n2)
                                      M.write regs (registerIndex r1) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)
      --Mult?
      (MMul r1 r2 r3)          -> do  n1 <- M.read regs (registerIndex r2)
                                      n2 <- M.read regs (registerIndex r3)
                                      let fin = (n1 * n2)
                                      M.write regs (registerIndex r1) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)


      (MInc d inc)             -> do  og <- M.read regs (registerIndex d)
                                      let fin = og + (fromIntegral inc)
                                      M.write regs (registerIndex d) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)

      (MDec d dec)             -> do  og <- M.read regs (registerIndex d)
                                      let fin = og - (fromIntegral dec)
                                      M.write regs (registerIndex d) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)

      (MLsl d b)               -> do  c <- M.read flgs 3
                                      cb <- M.read flgs 4
                                      bval <- M.read regs (registerIndex b)
                                      let fin = (shiftL bval 1) + listBits[c && not cb]
                                      M.write regs (registerIndex d) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)

      (MLsr d b)               -> do  bval <- M.read regs (registerIndex b)
                                      let fin = clearBit (shiftR bval 1) 15
                                      M.write regs (registerIndex d) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)

      (MLsl8 d b)              -> do  bval <- M.read regs (registerIndex b)
                                      let fin = (shiftL bval 8)
                                      M.write regs (registerIndex d) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)

      (MLsr8 d b)              -> do  bval <- M.read regs (registerIndex b)
                                      let fin = (shiftR bval 8)
                                      M.write regs (registerIndex d) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)

      (MAsl d b)               -> do  n1 <- M.read regs (registerIndex b)
                                      let fin = (n1 + n1)
                                      M.write regs (registerIndex d) fin
                                      setFlgs fin
                                      writeIORef pc (pc_val + 1)

      (MAsr d b)               -> do  bval <- M.read regs (registerIndex b)
                                      let fin = shiftR bval 1
                                      if (testBit fin 14)
                                        then do M.write regs (registerIndex d) (setBit fin 15)
                                                setFlgs (setBit fin 15)
                                        else do M.write regs (registerIndex d) fin
                                                setFlgs fin
                                      writeIORef pc (pc_val + 1)

      (MFon n)                 -> do  onorOff MFon n
                                      writeIORef pc (pc_val + 1)

      (MFoff n)                -> do  onorOff MFoff n
                                      writeIORef pc (pc_val + 1)

      (MFset5 n)               -> do  let s = (bitList n) !! 0
                                      let z = (bitList n) !! 1
                                      M.write flgs 0 s
                                      M.write flgs 1 z
                                      writeIORef pc (pc_val + 1)


      (MFset4 n)               -> do  let s = (bitList n) !! 0
                                      let z = (bitList n) !! 1
                                      M.write flgs 0 s
                                      M.write flgs 1 z
                                      writeIORef pc (pc_val + 1)


      (MSavef d)               -> do  s <- (M.read flgs 0)
                                      z <- (M.read flgs 1)
                                      let flags = listBits([s,z,False,False,True] ++ replicate 11 False)
                                      M.write regs (registerIndex d) flags
                                      writeIORef pc (pc_val + 1)

      (MRstrf d)               -> do  dval <- M.read regs (registerIndex d)
                                      let s  = testBit dval 0
                                      let z  = testBit dval 1
                                      M.write flgs 0 s
                                      M.write flgs 1 z
                                      writeIORef pc (pc_val + 1)

      (MLoad d o b)            -> do  bval <- M.read regs (registerIndex b)
                                      let memindex = fromIntegral (bval + (fromIntegral o))
                                      memcell <- M.read mem memindex
                                      M.write regs (registerIndex d) memcell
                                      writeIORef pc (pc_val + 1)

      (MStore d o b)           -> do  dval <- M.read regs (registerIndex d)
                                      bval <- M.read regs (registerIndex b)
                                      M.write mem (fromIntegral (bval + (fromIntegral o))) dval
                                      writeIORef pc (pc_val + 1)

      (MBr None (Relative n))  -> do  writeIORef pc (pc_val + (fromIntegral n))


      (MBr L (Relative n))     -> do  s <- (M.read flgs 0)
                                      v <- (M.read flgs 2)
                                      if (s /= v)
                                        then (writeIORef pc (pc_val + (fromIntegral n)))
                                        else writeIORef pc (pc_val + 1)
      ----
      (MBr Ge (Relative n))    -> do  s <- (M.read flgs 0)
                                      v <- (M.read flgs 2)
                                      if (not (s /= v))
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr Le (Relative n))    -> do  s <- (M.read flgs 0)
                                      z <- (M.read flgs 1)
                                      v <- (M.read flgs 2)
                                      if ((s /= v) || z)
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr G (Relative n))     -> do  s <- (M.read flgs 0)
                                      z <- (M.read flgs 1)
                                      v <- (M.read flgs 2)
                                      if (not ((s /= v) || z))
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr Ule (Relative n))   -> do  z <- (M.read flgs 1)
                                      v <- (M.read flgs 2)
                                      if ((not v) || z)
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr Ug (Relative n))    -> do  z <- (M.read flgs 1)
                                      v <- (M.read flgs 2)
                                      if (not ((not v) || z))
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr Z (Relative n))     -> do  z <- (M.read flgs 1)
                                      if z
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr Nz (Relative n))    -> do  z <- (M.read flgs 1)
                                      if (not z)
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr C (Relative n))     -> do  c <- (M.read flgs 3)
                                      if c
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr Nc (Relative n))    -> do  c <- (M.read flgs 3)
                                      if (not c)
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr S (Relative n))     -> do  s <- (M.read flgs 0)
                                      if s
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr Ns (Relative n))    -> do  s <- (M.read flgs 0)
                                      if (not s)
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr V (Relative n))     -> do  v <- (M.read flgs 2)
                                      if v
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)

      (MBr Nv (Relative n))    -> do  v <- (M.read flgs 2)
                                      if (not v)
                                        then writeIORef pc (pc_val + (fromIntegral n))
                                        else writeIORef pc (pc_val + 1)
      --
      (MBr None (Absolute d))  -> do  i <- M.read regs (registerIndex d)
                                      writeIORef pc i

      (MBr L (Absolute d))     -> do  s <- (M.read flgs 0)
                                      v <- (M.read flgs 2)
                                      i <- M.read regs (registerIndex d)
                                      if (s /= v)
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Ge (Absolute d))    -> do  s <- (M.read flgs 0)
                                      v <- (M.read flgs 2)
                                      i <- M.read regs (registerIndex d)
                                      if (not (s /= v))
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Le (Absolute d))    -> do  s <- (M.read flgs 0)
                                      z <- (M.read flgs 1)
                                      v <- (M.read flgs 2)
                                      i <- M.read regs (registerIndex d)
                                      if ((s /= v) || z)
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr G (Absolute d))     -> do  s <- (M.read flgs 0)
                                      z <- (M.read flgs 1)
                                      v <- (M.read flgs 2)
                                      i <- M.read regs (registerIndex d)
                                      if (not ((s /= v) || z))
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Ule (Absolute d))   -> do  z <- (M.read flgs 1)
                                      v <- (M.read flgs 2)
                                      i <- M.read regs (registerIndex d)
                                      if ((not v) || z)
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Ug (Absolute d))    -> do  z <- (M.read flgs 1)
                                      v <- (M.read flgs 2)
                                      i <- M.read regs (registerIndex d)
                                      if (not ((not v) || z))
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Z (Absolute d))     -> do  z <- (M.read flgs 1)
                                      i <- M.read regs (registerIndex d)
                                      if z
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Nz (Absolute d))    -> do  z <- (M.read flgs 1)
                                      i <- M.read regs (registerIndex d)
                                      if (not z)
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr C (Absolute d))     -> do  c <- (M.read flgs 3)
                                      i <- M.read regs (registerIndex d)
                                      if c
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Nc (Absolute d))    -> do  c <- (M.read flgs 3)
                                      i <- M.read regs (registerIndex d)
                                      if (not c)
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr S (Absolute d))     -> do  s <- (M.read flgs 0)
                                      i <- M.read regs (registerIndex d)
                                      if s
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Ns (Absolute d))    -> do  s <- (M.read flgs 0)
                                      i <- M.read regs (registerIndex d)
                                      if (not s)
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr V (Absolute d))    ->  do  v <- (M.read flgs 2)
                                      i <- M.read regs (registerIndex d)
                                      if (v)
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MBr Nv (Absolute d))    -> do  v <- (M.read flgs 2)
                                      i <- M.read regs (registerIndex d)
                                      if (not v)
                                        then writeIORef pc i
                                        else writeIORef pc (pc_val + 1)

      (MCall a b)              -> do  bval <- M.read regs (registerIndex b)
                                      aval <- M.read regs (registerIndex a)
                                      fpval <- M.read regs 14
                                      writeIORef pc bval
                                      M.write regs (registerIndex b) (pc_val + 1)
                                      M.write regs 14 aval
                                      M.write regs (registerIndex a) fpval

      (MReturn a b)            -> do  bval <- M.read regs (registerIndex b)
                                      aval <- M.read regs (registerIndex a)
                                      fpval <- M.read regs 14
                                      writeIORef pc bval
                                      M.write regs (registerIndex b) (pc_val + 1)
                                      M.write regs 14 aval
                                      M.write regs (registerIndex a) fpval
      (MSwi _)                 -> panic "unimplemented"
      (MRti)                    -> panic "unemplemented"

    M.write regs 0 0
    M.write flgs vFlagIndex False
    M.write flgs cFlagIndex False
    M.write flgs cbFlagIndex True
    updated_pc <- readIORef pc
    pure (updated_pc == 0xdead)


    where
      setFlgs fin = do  if (testBit fin 15) --(fin < 0) doesn't work because Word16 is unsigned.
                         then M.write flgs 0 True
                         else M.write flgs 0 False
                        if (fin == 0)
                         then M.write flgs 1 True
                         else M.write flgs 1 False

      onorOff ins n = do let sflag = testBit n 0
                         let zflag = testBit n 1
                         case (ins n == MFon n) of
                           True -> do
                              M.write flgs 0 sflag
                              M.write flgs 1 zflag
                           False -> do
                             if sflag == True then M.write flgs 0 False else M.write flgs 0 True
                             if zflag == True then M.write flgs 1 False else M.write flgs 1 True
-- Runs a machine until it has halted.
run :: Machine -> IO ()
run m = do
  done <- step m
  when (not done) $
    run m

-- Helpful for debugging: steps and prints the machine.
s :: Machine -> IO ()
s m = do
  step m
  printMachine m
