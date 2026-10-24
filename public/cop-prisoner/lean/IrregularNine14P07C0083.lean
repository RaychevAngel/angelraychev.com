import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4980 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 35 67 44 328 145 48 192 134 262), lower := (rows 35 67 44 328 145 48 192 128 256), losses := [] }

theorem u4980 : Upper (D 7) (R 7) [34,65,40,320,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4980 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4981 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 328 145 160 66 148 276), lower := (rows 35 67 44 328 145 160 66 128 256), losses := [] }

theorem u4981 : Upper (D 7) (R 7) [34,65,40,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4982 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 408, targets := 32 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 67 44 328 145 160 68 146 274), lower := (rows 35 67 44 328 145 160 68 128 256), losses := [] }

theorem u4982 : Upper (D 7) (R 7) [34,65,40,320,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4982 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4983 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 428, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 35 67 44 328 145 160 80 134 262), lower := (rows 35 67 44 328 145 160 80 128 256), losses := [] }

theorem u4983 : Upper (D 7) (R 7) [34,65,40,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4983 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4984 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 328 146 160 65 148 276), lower := (rows 35 67 44 328 146 160 65 128 256), losses := [] }

theorem u4984 : Upper (D 7) (R 7) [34,65,40,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4985 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 408, targets := 32 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 67 44 328 146 160 68 145 273), lower := (rows 35 67 44 328 146 160 68 128 256), losses := [] }

theorem u4985 : Upper (D 7) (R 7) [34,65,40,320,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4985 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4986 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 428, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 44 328 146 160 80 133 261), lower := (rows 35 67 44 328 146 160 80 128 256), losses := [] }

theorem u4986 : Upper (D 7) (R 7) [34,65,40,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4986 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4987 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 328 148 48 65 130 386), lower := (rows 35 67 44 328 148 48 65 128 256), losses := [] }

theorem u4987 : Upper (D 7) (R 7) [34,65,40,320,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4987 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4988 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 328 148 48 66 129 385), lower := (rows 35 67 44 328 148 48 66 128 256), losses := [] }

theorem u4988 : Upper (D 7) (R 7) [34,65,40,320,132,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4988 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4989 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,5),(3,5),(3,7)], upper := (rows 35 67 44 328 148 48 192 131 259), lower := (rows 35 67 44 328 148 48 192 128 256), losses := [] }

theorem u4989 : Upper (D 7) (R 7) [34,65,40,320,132,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4989 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4990 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 328 148 160 65 146 274), lower := (rows 35 67 44 328 148 160 65 128 256), losses := [] }

theorem u4990 : Upper (D 7) (R 7) [34,65,40,320,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4991 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 328 148 160 66 145 273), lower := (rows 35 67 44 328 148 160 66 128 256), losses := [] }

theorem u4991 : Upper (D 7) (R 7) [34,65,40,320,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4992 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 264, targets := 32 },{ cop := 1, region := 161, targets := 64 },{ cop := 1, region := 264, targets := 128 }], pairs := [(0,6),(3,5),(3,7)], upper := (rows 35 67 44 328 148 160 80 131 259), lower := (rows 35 67 44 328 148 160 80 128 256), losses := [] }

theorem u4992 : Upper (D 7) (R 7) [34,65,40,320,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4992 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4993 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 100 137 146 36 320 152 280), lower := (rows 35 67 100 137 146 36 320 128 256), losses := [] }

theorem u4993 : Upper (D 7) (R 7) [34,65,96,129,130,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4993 [(5,2),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4994 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 100 137 146 40 320 148 276), lower := (rows 35 67 100 137 146 40 320 128 256), losses := [] }

theorem u4994 : Upper (D 7) (R 7) [34,65,96,129,130,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4994 [(5,3),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4995 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 100 137 146 48 320 140 268), lower := (rows 35 67 100 137 146 48 320 128 256), losses := [] }

theorem u4995 : Upper (D 7) (R 7) [34,65,96,129,130,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4995 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4996 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 148 288 66 152 280), lower := (rows 35 67 100 137 148 288 66 128 256), losses := [] }

theorem u4996 : Upper (D 7) (R 7) [34,65,96,129,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4996 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4997 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 100 137 148 288 72 146 274), lower := (rows 35 67 100 137 148 288 72 128 256), losses := [] }

theorem u4997 : Upper (D 7) (R 7) [34,65,96,129,132,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4997 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4998 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 67 100 137 148 288 80 138 266), lower := (rows 35 67 100 137 148 288 80 128 256), losses := [] }

theorem u4998 : Upper (D 7) (R 7) [34,65,96,129,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4998 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4999 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 67 100 137 274 160 68 152 280), lower := (rows 35 67 100 137 274 160 68 128 256), losses := [] }

theorem u4999 : Upper (D 7) (R 7) [34,65,96,129,258,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4999 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5000 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 275, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 67 100 137 274 160 72 148 276), lower := (rows 35 67 100 137 274 160 72 128 256), losses := [] }

theorem u5000 : Upper (D 7) (R 7) [34,65,96,129,258,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5000 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5001 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 172, targets := 2 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 67 100 137 274 160 80 140 268), lower := (rows 35 67 100 137 274 160 80 128 256), losses := [] }

theorem u5001 : Upper (D 7) (R 7) [34,65,96,129,258,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5001 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5002 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 276 160 66 152 280), lower := (rows 35 67 100 137 276 160 66 128 256), losses := [] }

theorem u5002 : Upper (D 7) (R 7) [34,65,96,129,260,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5003 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 275, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 67 100 137 276 160 72 146 274), lower := (rows 35 67 100 137 276 160 72 128 256), losses := [] }

theorem u5003 : Upper (D 7) (R 7) [34,65,96,129,260,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5003 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5004 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 67 100 137 276 160 80 138 266), lower := (rows 35 67 100 137 276 160 80 128 256), losses := [] }

theorem u5004 : Upper (D 7) (R 7) [34,65,96,129,260,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5004 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5005 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 280 160 66 148 276), lower := (rows 35 67 100 137 280 160 66 128 256), losses := [] }

theorem u5005 : Upper (D 7) (R 7) [34,65,96,129,264,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5006 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 67 100 137 280 160 68 146 274), lower := (rows 35 67 100 137 280 160 68 128 256), losses := [] }

theorem u5006 : Upper (D 7) (R 7) [34,65,96,129,264,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5006 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5007 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 3, targets := 128 },{ cop := 1, region := 164, targets := 1 }], pairs := [(0,7),(1,7),(2,0)], upper := (rows 35 67 100 137 280 160 80 134 262), lower := (rows 35 67 100 137 280 160 80 128 256), losses := [] }

theorem u5007 : Upper (D 7) (R 7) [34,65,96,129,264,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5007 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5008 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 400 48 66 140 268), lower := (rows 35 67 100 137 400 48 66 128 256), losses := [] }

theorem u5008 : Upper (D 7) (R 7) [34,65,96,129,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5008 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5009 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 67 100 137 400 48 68 138 266), lower := (rows 35 67 100 137 400 48 68 128 256), losses := [] }

theorem u5009 : Upper (D 7) (R 7) [34,65,96,129,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5009 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5010 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 100 137 400 48 72 134 262), lower := (rows 35 67 100 137 400 48 72 128 256), losses := [] }

theorem u5010 : Upper (D 7) (R 7) [34,65,96,129,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5010 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5011 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 140 273 160 66 152 280), lower := (rows 35 67 100 140 273 160 66 128 256), losses := [] }

theorem u5011 : Upper (D 7) (R 7) [34,65,96,132,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5012 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 76, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 100 140 273 160 72 146 274), lower := (rows 35 67 100 140 273 160 72 128 256), losses := [] }

theorem u5012 : Upper (D 7) (R 7) [34,65,96,132,257,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5012 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5013 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 172, targets := 1 },{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7),(2,0),(3,0)], upper := (rows 35 67 100 140 273 160 80 138 266), lower := (rows 35 67 100 140 273 160 80 128 256), losses := [] }

theorem u5013 : Upper (D 7) (R 7) [34,65,96,132,257,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5013 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5014 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 100 140 280 33 192 146 274), lower := (rows 35 67 100 140 280 33 192 128 256), losses := [] }

theorem u5014 : Upper (D 7) (R 7) [34,65,96,132,264,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5015 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 140 280 34 192 145 273), lower := (rows 35 67 100 140 280 34 192 128 256), losses := [] }

theorem u5015 : Upper (D 7) (R 7) [34,65,96,132,264,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5016 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 3, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,7),(1,5),(1,7)], upper := (rows 35 67 100 140 280 48 192 131 259), lower := (rows 35 67 100 140 280 48 192 128 256), losses := [] }

theorem u5016 : Upper (D 7) (R 7) [34,65,96,132,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5016 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5017 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 100 140 400 33 80 138 266), lower := (rows 35 67 100 140 400 33 80 128 256), losses := [] }

theorem u5017 : Upper (D 7) (R 7) [34,65,96,132,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5017 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5018 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 140 400 34 80 137 265), lower := (rows 35 67 100 140 400 34 80 128 256), losses := [] }

theorem u5018 : Upper (D 7) (R 7) [34,65,96,132,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5018 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5019 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 100 140 400 40 80 131 259), lower := (rows 35 67 100 140 400 40 80 128 256), losses := [] }

theorem u5019 : Upper (D 7) (R 7) [34,65,96,132,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5019 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5020 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 152 273 160 66 140 268), lower := (rows 35 67 100 152 273 160 66 128 256), losses := [] }

theorem u5020 : Upper (D 7) (R 7) [34,65,96,144,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5021 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 67 100 152 273 160 68 138 266), lower := (rows 35 67 100 152 273 160 68 128 256), losses := [] }

theorem u5021 : Upper (D 7) (R 7) [34,65,96,144,257,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5021 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5022 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 275, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 67 100 152 273 160 72 134 262), lower := (rows 35 67 100 152 273 160 72 128 256), losses := [] }

theorem u5022 : Upper (D 7) (R 7) [34,65,96,144,257,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5022 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5023 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 100 152 276 33 192 138 266), lower := (rows 35 67 100 152 276 33 192 128 256), losses := [] }

theorem u5023 : Upper (D 7) (R 7) [34,65,96,144,260,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5024 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 152 276 34 192 137 265), lower := (rows 35 67 100 152 276 34 192 128 256), losses := [] }

theorem u5024 : Upper (D 7) (R 7) [34,65,96,144,260,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5025 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 275, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 67 100 152 276 40 192 131 259), lower := (rows 35 67 100 152 276 40 192 128 256), losses := [] }

theorem u5025 : Upper (D 7) (R 7) [34,65,96,144,260,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5025 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5026 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 100 152 280 33 192 134 262), lower := (rows 35 67 100 152 280 33 192 128 256), losses := [] }

theorem u5026 : Upper (D 7) (R 7) [34,65,96,144,264,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5027 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 100 152 280 34 192 133 261), lower := (rows 35 67 100 152 280 34 192 128 256), losses := [] }

theorem u5027 : Upper (D 7) (R 7) [34,65,96,144,264,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5028 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 100 152 280 36 192 131 259), lower := (rows 35 67 100 152 280 36 192 128 256), losses := [] }

theorem u5028 : Upper (D 7) (R 7) [34,65,96,144,264,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5028 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5029 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 436, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 138 276 48 72 224 352), lower := (rows 35 67 133 138 276 48 72 128 256), losses := [] }

theorem u5029 : Upper (D 7) (R 7) [34,65,129,130,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5029 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5030 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 138 276 48 96 200 328), lower := (rows 35 67 133 138 276 48 96 128 256), losses := [] }

theorem u5030 : Upper (D 7) (R 7) [34,65,129,130,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5030 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5031 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 152 274 36 72 224 352), lower := (rows 35 67 133 152 274 36 72 128 256), losses := [] }

theorem u5031 : Upper (D 7) (R 7) [34,65,129,144,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5031 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5032 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 152 274 36 96 200 328), lower := (rows 35 67 133 152 274 36 96 128 256), losses := [] }

theorem u5032 : Upper (D 7) (R 7) [34,65,129,144,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5032 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5033 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 152 274 40 68 224 352), lower := (rows 35 67 133 152 274 40 68 128 256), losses := [] }

theorem u5033 : Upper (D 7) (R 7) [34,65,129,144,258,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5033 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5034 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 152 274 40 96 196 324), lower := (rows 35 67 133 152 274 40 96 128 256), losses := [] }

theorem u5034 : Upper (D 7) (R 7) [34,65,129,144,258,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5034 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5035 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 152 304 36 66 200 328), lower := (rows 35 67 133 152 304 36 66 128 256), losses := [] }

theorem u5035 : Upper (D 7) (R 7) [34,65,129,144,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5035 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5036 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 152 304 36 72 194 322), lower := (rows 35 67 133 152 304 36 72 128 256), losses := [] }

theorem u5036 : Upper (D 7) (R 7) [34,65,129,144,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5036 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5037 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 152 336 36 66 168 296), lower := (rows 35 67 133 152 336 36 66 128 256), losses := [] }

theorem u5037 : Upper (D 7) (R 7) [34,65,129,144,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5037 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5038 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 152 336 36 72 162 290), lower := (rows 35 67 133 152 336 36 72 128 256), losses := [] }

theorem u5038 : Upper (D 7) (R 7) [34,65,129,144,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5038 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5039 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 152 336 36 96 138 266), lower := (rows 35 67 133 152 336 36 96 128 256), losses := [] }

theorem u5039 : Upper (D 7) (R 7) [34,65,129,144,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5039 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5039
end Delivery.IrregularNine14.P07
