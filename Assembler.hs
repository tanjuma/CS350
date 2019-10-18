{- Author: Lisa Hou and Umme Tanjuma Haque, with structure by Richard Eisenberg
   File: Assembler.hs

   Defines a HERA assembler.
-}

{-# OPTIONS_GHC -W -Wno-overflowed-literals -Wno-unused-imports #-}
  -- Disable warnings for unused imports as usual, but also for
  -- overflowed literals. This allows us to write, for example, 0xf8 as an Int8
  -- meaning (-8). (Normally, GHC would complain saying that 248 (the decimal
  -- value of 0xf8) is too big for an Int8.)

module Assembler where

import Data.Bits                ( shiftR, toIntegralSized, (.&.) )
  -- toIntegralSized is helpful when calculating whether you can make a relative jump
import Data.Char                ( ord )
import Data.Int                 ( Int8 )
import Data.List                ( genericLength )
import Data.Map                 ( Map )
import qualified Data.Map as M
import Data.Maybe               ( isJust )
import qualified Data.Vector as I
import Data.Word                ( Word16 )

import CS350.Panic       ( panic, unimplemented )
import CS350.Renderable  ( Renderable(..) )
import CS350.WordN       (bitList, listBits )

import HERA.Assembly  ( AssemblyProgram, AInstruction(..), Label )
import HERA.Base      ( Register(..), Condition(..), dataBottom, rt, haltedPC, stackBottom )
import HERA.Machine   ( MachineProgram(..), MInstruction(..), DataSegment(..), Target(..) )


--EXPANDS ASSEMBLYPROGRAM
parse_pseudo :: AssemblyProgram ->AssemblyProgram
parse_pseudo ap = go [] ap
 where
   go :: AssemblyProgram --accumulating AssemblyProgram list
      -> AssemblyProgram --original AssemblyProgram list [AInstruction]???
      -> AssemblyProgram
   go parsedprogram [] = reverse parsedprogram --reverse list
   go parsedprogram (x:xs) = do
     case x of
       (ASet d v)      -> do let a = fromIntegral v
                             let b = fromIntegral (v `shiftR` 8)
                             ASetlo d a : ASethi d b : go parsedprogram xs
       (ASetrf d v)    -> ASetlo d (listBits(take 8 (reverse(bitList(v))))) : ASethi d (listBits(reverse(drop 8(bitList(v))))) : go parsedprogram xs
       (AMove a b)     -> AOr a b R0 : go parsedprogram xs
       (ACmp a b)      -> AFon 0x08 : ASub R0 a b : go parsedprogram xs
       (ANeg d b)      -> AFon 0x08 : ASub d R0 b : go parsedprogram xs
       (ANot d b)      -> ASetlo R11 (0xffff .&. 0xff) : AXor d R11 b : go parsedprogram xs
       (ACon)          -> AFon (0x08) : go parsedprogram xs
       (ACoff)         -> AFoff (0x10) : go parsedprogram xs
       (ACbon)         -> AFon (0x10) : go parsedprogram xs
       (ACcboff)       -> AFoff (0x18) : go parsedprogram xs
       (AFlags a)      -> AFoff (0x10) : AAdd R0 a R0 : go parsedprogram xs
       _               -> x : go parsedprogram xs --just add everything else

--TAKES EXPANDED ASSEMBLY PROGRAM, CREATES A MAP OF DATA LABELS
map_dlabels :: AssemblyProgram -> ([DataSegment], (M.Map String Word16))
map_dlabels ap = go dataBottom ([], M.empty) ap   --0xc000 = stackbottom , ap = remaining assemblyPrgram
  where
    go :: Word16                --data address (accumulated answer)
          -> ([DataSegment], M.Map String Word16) --Tuple with datasegment list and mapped labels/addresses
          -> AssemblyProgram    --remaining assembly
          -> ([DataSegment], M.Map String Word16)  --updated map
    go _ (datas, mappedlabels) [] = (reverse (datas), mappedlabels)
    go n ([], mappedlabels) insn = go n ([DS{location = 0xc000, contents= I.empty}], mappedlabels) insn
    go currentaddress ((seg : segs), mappedlabels) (x:xs) = do
      case x of
        (ADlabel lab)    -> do go currentaddress ((seg:segs), (M.insert lab currentaddress mappedlabels)) xs

        (ADskip skippy)  -> do let nseg = DS {location = (currentaddress + skippy + 1), contents = I.empty }
                               go (currentaddress + skippy) (([nseg] ++ (seg : segs)), mappedlabels) xs

        (ALpString str)  -> do let nseg = DS {location = location seg, contents = (contents seg) I.++ I.fromList([fromIntegral(length str)]) I.++ (strtoWord str)}
                               go (currentaddress + fromIntegral(length str) ) ((nseg:segs), mappedlabels) xs
        --
        (AInteger i)     -> do let nseg = DS {location = location seg, contents = I.snoc (contents seg) (fromIntegral i)}
                               go (currentaddress + 1) ((nseg:segs), mappedlabels) xs

        _                -> do go (currentaddress) ((seg:segs), mappedlabels) xs

strtoWord :: [Char] -> I.Vector Word16
strtoWord x = I.fromList ((map fromIntegral (map ord x)))

--TAKES EXPANDED ASSEMBLY PROGRAM, CREATES A MAP OF LABELS
map_tlabels :: AssemblyProgram -> M.Map String Word16
map_tlabels ap = go stackBottom M.empty ap   --0xc000 = stackbottom , ap = remaining assemblyPrgram
  where
    go :: Word16                --stack address (accumulated answer)
          -> (M.Map String Word16 ) --Mapped labels/addresses
          -> AssemblyProgram    --remaining assembly
          -> (M.Map String Word16 ) --updated map
    go _ mappedlabels [] = mappedlabels
    go currentaddress mappedlabels (x:xs) = do
      case x of
        (ALabel lab)     -> go currentaddress (M.insert lab (currentaddress) mappedlabels) xs
        (ADlabel _)    -> go currentaddress mappedlabels xs
        (ADskip _)  -> go currentaddress mappedlabels xs

        (ALpString _)  -> go currentaddress mappedlabels xs
        (ASetl _ _) -> go (currentaddress + 2) mappedlabels xs
        (ACall _ _) -> go (currentaddress + 3) mappedlabels xs
        (ABr _ _)      -> go (currentaddress+3) mappedlabels xs
        (AHalt)  -> go (currentaddress + 3) mappedlabels xs
        _                -> go (currentaddress +1) mappedlabels xs

from_Maybe :: Maybe a -> a
from_Maybe Nothing = error "No corresponding value found for the searched key!"
from_Maybe (Just x) = x

to_Machine :: AssemblyProgram -> M.Map String Word16 -> M.Map String Word16 -> I.Vector MInstruction
to_Machine [] _ _ = I.empty
to_Machine ap map_d map_t = go I.empty ap
  where
    go :: I.Vector MInstruction
       -> AssemblyProgram
       -> I.Vector MInstruction

    go acc [] = I.reverse acc
    go acc (x : xs) = do
      case x of
        (ASetlo d val)  -> go (I.cons (MSetlo d val) acc) xs
        (ASethi d val)  -> go (I.cons (MSethi d val) acc) xs
        (AAnd d a b)    -> go (I.cons (MAnd d a b) acc) xs
        (AOr d a b)     -> go (I.cons (MOr d a b) acc) xs
        (AXor d a b)    -> go (I.cons (MXor d a b) acc) xs
        (AAdd r1 r2 r3) -> go (I.cons (MAdd r1 r2 r3) acc) xs
        (ASub r1 r2 r3) -> go (I.cons (MSub r1 r2 r3) acc) xs
        (AMul r1 r2 r3) -> go (I.cons (MMul r1 r2 r3) acc) xs
        (AInc d inc)    -> go (I.cons (MInc d inc) acc) xs
        (ADec d dec)    -> go (I.cons (MDec d dec) acc) xs
        (ALsl d b)      -> go (I.cons (MLsl d b) acc) xs
        (ALsr d b)      -> go (I.cons (MLsr d b) acc) xs
        (ALsl8 d b)     -> go (I.cons (MLsl8 d b) acc) xs
        (ALsr8 d b)     -> go (I.cons (MLsr8 d b) acc) xs
        (AAsl d b)      -> go (I.cons (MAsl d b) acc) xs
        (AAsr d b)      -> go (I.cons (MAsr d b) acc) xs
        (AFon n)        -> go (I.cons (MFon n) acc) xs
        (AFoff n)       -> go (I.cons (MFoff n) acc) xs
        (AFset5 n)      -> go (I.cons (MFset5 n) acc) xs
        (AFset4 n)      -> go (I.cons (MFset4 n) acc) xs
        (ASavef d)      -> go (I.cons (MSavef d) acc) xs
        (ARstrf d)      -> go (I.cons (MRstrf d) acc) xs
        (ALoad d o b)   -> go (I.cons (MLoad d o b) acc) xs
        (AStore d o b)  -> go (I.cons (MStore d o b) acc) xs
        (ABr c x)       -> do case (M.lookup x map_t == Nothing) of
                                True -> error "Value not found!"
                                False -> do let a = fromIntegral ((from_Maybe(M.lookup x map_t)) `shiftR` 8)
                                            let b = fromIntegral(from_Maybe(M.lookup x map_t))
                                            go (I.cons (MBr c (Absolute R11)) (I.cons(MSethi R11 a)(I.cons (MSetlo R11 b) acc))) xs

        (ASetl d lab) -> do let a = fromIntegral(from_Maybe(M.lookup lab map_d))
                            let b = fromIntegral ((from_Maybe(M.lookup lab map_d)) `shiftR` 8)
                            go (I.cons (MSethi d b)(I.cons (MSetlo d a) acc)) xs
        (ALabel _)    -> go acc xs
        (ADlabel _)   -> go acc xs
        (AInteger _)  -> go acc xs
        (ALpString _) -> go acc xs
        (ADskip _)    -> go acc xs
        (ANop)        -> go (I.cons(MBr None (Relative 1))acc) xs
        (AHalt)       -> go (I.cons (MBr None(Absolute R11))(I.cons (MSethi R11 0xde)(I.cons (MSetlo R11 0xad) acc))) xs
        _             -> go acc xs


assemble :: AssemblyProgram -> MachineProgram
assemble insns = do let expanded_Program = parse_pseudo insns
                    let (dseg, map_dl) = map_dlabels expanded_Program
                    let map_tl = map_tlabels expanded_Program
                    let m_insns = to_Machine expanded_Program map_dl map_tl
                    MP{text = m_insns, dayta = (I.fromList dseg)}
