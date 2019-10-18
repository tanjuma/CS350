{- Done by: Lisa Hou and Umme Tanjuma Haque
-}
import HERA.Assembly    ( AssemblyProgram, AInstruction(..) )
import HERA.Machine     ( MachineProgram(..), DataSegment(..), Target(..), MInstruction(..) )
import HERA.Base        ( Register(..), Condition(..), fpAlt, pcRet, fp, sp )


  bigTest :: AssemblyProgram
  bigTest = [ ACBon,
              ASet R1 20, -- (x) Setting R1 to have the Word16 20
              ASet R2 10, -- (y) Setting R2 to have the Word16 10
              ASet R3 1, -- Setting R3 to have the Word16 1
              ASet R4 1, -- Setting R4 to have the Word16 1
              ALabel "TOP_OF_LOOP", -- Creating a text label to jump back to
              ASub R0 R1 R2,  -- Subtracting value in R2 from R1 and putting that in R0
              ABz "BOTTOM_OF_LOOP", -- Will branch to the bottom of the loop (the given label) if the R1 value = R2 value
              AAnd R0 R1 R4, -- Doing bitwise And of R1 and R4 and putting that in R6
              ABnz "Y_NOT_EVEN_AND_X_NOT_EVEN", -- Will branch to the label if only the operands are not equal (i.e. - R1 != R4)
              AMove R5 R1, -- Doing bitwise Or of R1 and R0 and putting it in R5
              ALsr R1 R2, -- Logical shift right of R2 stored in R1
              AMove R2 R5, -- Doing Bitwise Or of R5 and R0 and putting it in R2
              ABr "TOP_OF_LOOP", -- Branches back to the label at the top
              ALabel "Y_NOT_EVEN_AND_X_NOT_EVEN", -- Creating a text label
              ASub R0 R1 R2, --  Subtracting R2 from R1 and storing it in R0
              ABule "X_LESS_THAN_Y_AND_NEITHER_EVEN", -- Branches to the label if unsigned result <= 0
              ASub R1 R1 R2, -- Subtracting R2 from R1 and storing it in R1
              ABr "TOP_OF_LOOP", -- Branches unconditionally to the label at the top
              ALabel "X_LESS_THAN_Y_AND_NEITHER_EVEN", -- Creating a text label
              ASub R2 R2 R1, -- Subtracting R1 from R2 and then putting it in R2
              ALabel "BOTTOM_OF_LOOP", -- Creating a label
              AMul R1 R1 R3, -- Multiplying R3 and R1 and putting it in R1
              AMove R3 R1, -- Doing Bitwise OR of R1 and R0 and putting the result in R3 (our final answer)
              AHalt, -- Halts the program
            ]
