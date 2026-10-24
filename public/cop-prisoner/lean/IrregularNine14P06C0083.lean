import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4980 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 261 73 112 36 68 146 274), lower := (rows 11 162 261 73 112 36 68 128 256), losses := [] }

theorem u4980 : Upper (D 6) (R 6) [10,160,257,65,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4981 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 162 261 73 112 36 80 134 262), lower := (rows 11 162 261 73 112 36 80 128 256), losses := [] }

theorem u4981 : Upper (D 6) (R 6) [10,160,257,65,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4981 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4982 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 261 76 22 33 80 224 352), lower := (rows 11 162 261 76 22 33 80 128 256), losses := [] }

theorem u4982 : Upper (D 6) (R 6) [10,160,257,68,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4982 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4983 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 104, targets := 2 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 162 261 76 22 33 96 208 336), lower := (rows 11 162 261 76 22 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 98 144 272), good := (rows 74 226 260 76 478 96 96 128 256) },{ target := 2, region := (rows 1 18 0 8 16 37 127 144 272), good := (rows 107 226 353 104 498 97 96 128 256) }] }

theorem u4983 : Upper (D 6) (R 6) [10,160,257,68,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4984 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 162 261 76 22 48 65 224 352), lower := (rows 11 162 261 76 22 48 65 128 256), losses := [] }

theorem u4984 : Upper (D 6) (R 6) [10,160,257,68,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4984 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4985 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 261 76 22 48 96 193 321), lower := (rows 11 162 261 76 22 48 96 128 256), losses := [] }

theorem u4985 : Upper (D 6) (R 6) [10,160,257,68,6,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4985 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4986 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(1,0),(4,0)], upper := (rows 11 162 261 76 22 96 65 176 304), lower := (rows 11 162 261 76 22 96 65 128 256), losses := [] }

theorem u4986 : Upper (D 6) (R 6) [10,160,257,68,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4987 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 261 76 22 96 80 161 289), lower := (rows 11 162 261 76 22 96 80 128 256), losses := [] }

theorem u4987 : Upper (D 6) (R 6) [10,160,257,68,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4987 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4988 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 261 76 22 96 96 145 273), lower := (rows 11 162 261 76 22 96 96 128 256), losses := [] }

theorem u4988 : Upper (D 6) (R 6) [10,160,257,68,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4989 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 76 52 96 65 146 274), lower := (rows 11 162 261 76 52 96 65 128 256), losses := [] }

theorem u4989 : Upper (D 6) (R 6) [10,160,257,68,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4990 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 162 261 76 52 96 66 145 273), lower := (rows 11 162 261 76 52 96 66 128 256), losses := [] }

theorem u4990 : Upper (D 6) (R 6) [10,160,257,68,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4991 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 261 76 52 96 80 131 259), lower := (rows 11 162 261 76 52 96 80 128 256), losses := [] }

theorem u4991 : Upper (D 6) (R 6) [10,160,257,68,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4991 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4992 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 261 76 81 36 66 176 304), lower := (rows 11 162 261 76 81 36 66 128 256), losses := [] }

theorem u4992 : Upper (D 6) (R 6) [10,160,257,68,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4993 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 261 76 81 36 80 162 290), lower := (rows 11 162 261 76 81 36 80 128 256), losses := [] }

theorem u4993 : Upper (D 6) (R 6) [10,160,257,68,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4993 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4994 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 162 261 76 81 36 96 146 274), lower := (rows 11 162 261 76 81 36 96 128 256), losses := [] }

theorem u4994 : Upper (D 6) (R 6) [10,160,257,68,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4995 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 179, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 261 76 82 33 68 176 304), lower := (rows 11 162 261 76 82 33 68 128 256), losses := [] }

theorem u4995 : Upper (D 6) (R 6) [10,160,257,68,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4996 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 261 76 82 33 80 164 292), lower := (rows 11 162 261 76 82 33 80 128 256), losses := [] }

theorem u4996 : Upper (D 6) (R 6) [10,160,257,68,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4996 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4997 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 261 76 82 33 96 148 276), lower := (rows 11 162 261 76 82 33 96 128 256), losses := [] }

theorem u4997 : Upper (D 6) (R 6) [10,160,257,68,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4998 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 162 261 76 82 36 65 176 304), lower := (rows 11 162 261 76 82 36 65 128 256), losses := [] }

theorem u4998 : Upper (D 6) (R 6) [10,160,257,68,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4999 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 261 76 82 36 80 161 289), lower := (rows 11 162 261 76 82 36 80 128 256), losses := [] }

theorem u4999 : Upper (D 6) (R 6) [10,160,257,68,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4999 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5000 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 261 76 82 36 96 145 273), lower := (rows 11 162 261 76 82 36 96 128 256), losses := [] }

theorem u5000 : Upper (D 6) (R 6) [10,160,257,68,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5001 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 162 261 76 82 48 65 164 292), lower := (rows 11 162 261 76 82 48 65 128 256), losses := [] }

theorem u5001 : Upper (D 6) (R 6) [10,160,257,68,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5001 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5002 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 261 76 82 48 68 161 289), lower := (rows 11 162 261 76 82 48 68 128 256), losses := [] }

theorem u5002 : Upper (D 6) (R 6) [10,160,257,68,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5002 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5003 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 11 162 261 76 82 48 96 133 261), lower := (rows 11 162 261 76 82 48 96 128 256), losses := [] }

theorem u5003 : Upper (D 6) (R 6) [10,160,257,68,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5003 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5004 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 11 162 261 76 112 33 66 148 276), lower := (rows 11 162 261 76 112 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 50 32 67 128 256), good := (rows 90 242 332 76 112 112 82 128 256) }] }

theorem u5004 : Upper (D 6) (R 6) [10,160,257,68,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5005 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 179, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 261 76 112 33 68 146 274), lower := (rows 11 162 261 76 112 33 68 128 256), losses := [] }

theorem u5005 : Upper (D 6) (R 6) [10,160,257,68,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5006 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 261 76 112 33 80 134 262), lower := (rows 11 162 261 76 112 33 80 128 256), losses := [] }

theorem u5006 : Upper (D 6) (R 6) [10,160,257,68,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5006 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5007 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 76 112 36 65 146 274), lower := (rows 11 162 261 76 112 36 65 128 256), losses := [] }

theorem u5007 : Upper (D 6) (R 6) [10,160,257,68,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5008 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 3, region := 48, targets := 2 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 162 261 76 112 36 66 145 273), lower := (rows 11 162 261 76 112 36 66 128 256), losses := [] }

theorem u5008 : Upper (D 6) (R 6) [10,160,257,68,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5009 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 261 76 112 36 80 131 259), lower := (rows 11 162 261 76 112 36 80 128 256), losses := [] }

theorem u5009 : Upper (D 6) (R 6) [10,160,257,68,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5009 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5010 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 162 261 88 22 33 68 224 352), lower := (rows 11 162 261 88 22 33 68 128 256), losses := [] }

theorem u5010 : Upper (D 6) (R 6) [10,160,257,80,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5011 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 11 162 261 88 22 33 96 196 324), lower := (rows 11 162 261 88 22 33 96 128 256), losses := [] }

theorem u5011 : Upper (D 6) (R 6) [10,160,257,80,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5012 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 261 88 22 36 65 224 352), lower := (rows 11 162 261 88 22 36 65 128 256), losses := [] }

theorem u5012 : Upper (D 6) (R 6) [10,160,257,80,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5013 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 162 261 88 22 36 96 193 321), lower := (rows 11 162 261 88 22 36 96 128 256), losses := [] }

theorem u5013 : Upper (D 6) (R 6) [10,160,257,80,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5014 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 73, targets := 4 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 261 88 22 96 65 164 292), lower := (rows 11 162 261 88 22 96 65 128 256), losses := [] }

theorem u5014 : Upper (D 6) (R 6) [10,160,257,80,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5015 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 162 261 88 22 96 68 161 289), lower := (rows 11 162 261 88 22 96 68 128 256), losses := [] }

theorem u5015 : Upper (D 6) (R 6) [10,160,257,80,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5016 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 261 88 22 96 96 133 261), lower := (rows 11 162 261 88 22 96 96 128 256), losses := [] }

theorem u5016 : Upper (D 6) (R 6) [10,160,257,80,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5017 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 162 261 88 52 96 65 134 262), lower := (rows 11 162 261 88 52 96 65 128 256), losses := [] }

theorem u5017 : Upper (D 6) (R 6) [10,160,257,80,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5018 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 261 88 52 96 66 133 261), lower := (rows 11 162 261 88 52 96 66 128 256), losses := [] }

theorem u5018 : Upper (D 6) (R 6) [10,160,257,80,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5019 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 162 261 88 52 96 68 131 259), lower := (rows 11 162 261 88 52 96 68 128 256), losses := [] }

theorem u5019 : Upper (D 6) (R 6) [10,160,257,80,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5020 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 261 104 22 36 65 208 336), lower := (rows 11 162 261 104 22 36 65 128 256), losses := [] }

theorem u5020 : Upper (D 6) (R 6) [10,160,257,96,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5021 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 261 104 22 36 80 193 321), lower := (rows 11 162 261 104 22 36 80 128 256), losses := [] }

theorem u5021 : Upper (D 6) (R 6) [10,160,257,96,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5021 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5022 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 261 104 82 36 65 148 276), lower := (rows 11 162 261 104 82 36 65 128 256), losses := [] }

theorem u5022 : Upper (D 6) (R 6) [10,160,257,96,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5023 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 261 104 82 36 68 145 273), lower := (rows 11 162 261 104 82 36 68 128 256), losses := [] }

theorem u5023 : Upper (D 6) (R 6) [10,160,257,96,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5024 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 162 261 104 82 36 80 133 261), lower := (rows 11 162 261 104 82 36 80 128 256), losses := [] }

theorem u5024 : Upper (D 6) (R 6) [10,160,257,96,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5024 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5025 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 262 25 52 96 65 196 324), lower := (rows 11 162 262 25 52 96 65 128 256), losses := [] }

theorem u5025 : Upper (D 6) (R 6) [10,160,258,17,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5026 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 162 262 25 52 96 68 193 321), lower := (rows 11 162 262 25 52 96 68 128 256), losses := [] }

theorem u5026 : Upper (D 6) (R 6) [10,160,258,17,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5027 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 262 25 84 36 65 224 352), lower := (rows 11 162 262 25 84 36 65 128 256), losses := [] }

theorem u5027 : Upper (D 6) (R 6) [10,160,258,17,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5028 : Route 9 := (fun mask => (mask,id))

def c5028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5028 : Upper (D 6) (R 6) [10,160,258,17,68,4,32] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17,68,4,32] 13 (by decide) (choices 1) [1,64] r5028 c5028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u370
  · exact u371

def b5029 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 262 25 84 96 65 164 292), lower := (rows 11 162 262 25 84 96 65 128 256), losses := [] }

theorem u5029 : Upper (D 6) (R 6) [10,160,258,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5030 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 262 25 84 96 68 161 289), lower := (rows 11 162 262 25 84 96 68 128 256), losses := [] }

theorem u5030 : Upper (D 6) (R 6) [10,160,258,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5031 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 96 },{ cop := 2, region := 112, targets := 1 }], pairs := [(2,5),(2,6),(4,0)], upper := (rows 11 162 262 25 84 96 96 133 261), lower := (rows 11 162 262 25 84 96 96 128 256), losses := [] }

theorem u5031 : Upper (D 6) (R 6) [10,160,258,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5032 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 262 25 112 36 65 196 324), lower := (rows 11 162 262 25 112 36 65 128 256), losses := [] }

theorem u5032 : Upper (D 6) (R 6) [10,160,258,17,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5033 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 262 25 112 36 68 193 321), lower := (rows 11 162 262 25 112 36 68 128 256), losses := [] }

theorem u5033 : Upper (D 6) (R 6) [10,160,258,17,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5034 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 5, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 162 262 28 49 96 65 196 324), lower := (rows 11 162 262 28 49 96 65 128 256), losses := [] }

theorem u5034 : Upper (D 6) (R 6) [10,160,258,20,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5035 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,5),(4,1)], upper := (rows 11 162 262 28 49 96 68 193 321), lower := (rows 11 162 262 28 49 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 109 76 129 257), good := (rows 505 160 356 124 433 96 100 128 256) },{ target := 5, region := (rows 1 2 5 24 16 0 93 145 273), good := (rows 463 130 326 476 477 64 68 128 256) }] }

theorem u5035 : Upper (D 6) (R 6) [10,160,258,20,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5036 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 162 262 28 81 36 65 224 352), lower := (rows 11 162 262 28 81 36 65 128 256), losses := [] }

theorem u5036 : Upper (D 6) (R 6) [10,160,258,20,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5037 : Route 9 := (fun mask => (mask,id))

def c5037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5037 : Upper (D 6) (R 6) [10,160,258,20,65,4,32] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,65,4,32] 13 (by decide) (choices 1) [1,64] r5037 c5037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u372
  · exact u373

def b5038 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 262 28 81 96 65 164 292), lower := (rows 11 162 262 28 81 96 65 128 256), losses := [] }

theorem u5038 : Upper (D 6) (R 6) [10,160,258,20,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5039 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 262 28 81 96 68 161 289), lower := (rows 11 162 262 28 81 96 68 128 256), losses := [] }

theorem u5039 : Upper (D 6) (R 6) [10,160,258,20,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5039
end Delivery.IrregularNine14.P06
