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

def b5100 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 276 13 81 96 66 164 292), lower := (rows 11 162 276 13 81 96 66 128 256), losses := [] }

theorem u5100 : Upper (D 6) (R 6) [10,160,272,5,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5101 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 13 81 96 68 162 290), lower := (rows 11 162 276 13 81 96 68 128 256), losses := [] }

theorem u5101 : Upper (D 6) (R 6) [10,160,272,5,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5102 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 162 276 13 81 96 96 134 262), lower := (rows 11 162 276 13 81 96 96 128 256), losses := [] }

theorem u5102 : Upper (D 6) (R 6) [10,160,272,5,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5103 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 82 36 65 224 352), lower := (rows 11 162 276 13 82 36 65 128 256), losses := [] }

theorem u5103 : Upper (D 6) (R 6) [10,160,272,5,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5104 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 276 13 82 36 96 193 321), lower := (rows 11 162 276 13 82 36 96 128 256), losses := [] }

theorem u5104 : Upper (D 6) (R 6) [10,160,272,5,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5105 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 82 96 65 164 292), lower := (rows 11 162 276 13 82 96 65 128 256), losses := [] }

theorem u5105 : Upper (D 6) (R 6) [10,160,272,5,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5106 : Route 9 := (fun mask => (mask,id))

def c5106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5106 : Upper (D 6) (R 6) [10,160,272,5,66,64,4] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,66,64,4] 13 (by decide) (choices 1) [1,32] r5106 c5106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u378
  · exact u379

def b5107 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 269, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 11 162 276 13 82 96 96 133 261), lower := (rows 11 162 276 13 82 96 96 128 256), losses := [] }

theorem u5107 : Upper (D 6) (R 6) [10,160,272,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5108 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 84 96 65 162 290), lower := (rows 11 162 276 13 84 96 65 128 256), losses := [] }

theorem u5108 : Upper (D 6) (R 6) [10,160,272,5,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5109 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 7, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 162 276 13 84 96 66 161 289), lower := (rows 11 162 276 13 84 96 66 128 256), losses := [] }

theorem u5109 : Upper (D 6) (R 6) [10,160,272,5,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5110 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 276 13 84 96 96 131 259), lower := (rows 11 162 276 13 84 96 96 128 256), losses := [] }

theorem u5110 : Upper (D 6) (R 6) [10,160,272,5,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5111 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 112 36 65 194 322), lower := (rows 11 162 276 13 112 36 65 128 256), losses := [] }

theorem u5111 : Upper (D 6) (R 6) [10,160,272,5,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5112 : Route 9 := (fun mask => (mask,id))

def c5112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5112 : Upper (D 6) (R 6) [10,160,272,5,96,4,2] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,96,4,2] 13 (by decide) (choices 1) [1,64] r5112 c5112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u380
  · exact u381

def b5113 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 260, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 276 44 82 33 65 196 324), lower := (rows 11 162 276 44 82 33 65 128 256), losses := [] }

theorem u5113 : Upper (D 6) (R 6) [10,160,272,36,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5114 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,0),(4,5)], upper := (rows 11 162 276 44 82 33 68 193 321), lower := (rows 11 162 276 44 82 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 32 76 128 256), good := (rows 90 162 340 108 82 48 68 128 256) }] }

theorem u5114 : Upper (D 6) (R 6) [10,160,272,36,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5115 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 73 21 96 66 164 292), lower := (rows 11 162 276 73 21 96 66 128 256), losses := [] }

theorem u5115 : Upper (D 6) (R 6) [10,160,272,65,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5116 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 73 21 96 68 162 290), lower := (rows 11 162 276 73 21 96 68 128 256), losses := [] }

theorem u5116 : Upper (D 6) (R 6) [10,160,272,65,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5117 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 276 73 21 96 96 134 262), lower := (rows 11 162 276 73 21 96 96 128 256), losses := [] }

theorem u5117 : Upper (D 6) (R 6) [10,160,272,65,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5118 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 276 73 22 96 65 164 292), lower := (rows 11 162 276 73 22 96 65 128 256), losses := [] }

theorem u5118 : Upper (D 6) (R 6) [10,160,272,65,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5119 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 73 22 96 68 161 289), lower := (rows 11 162 276 73 22 96 68 128 256), losses := [] }

theorem u5119 : Upper (D 6) (R 6) [10,160,272,65,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5120 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 276 73 22 96 96 133 261), lower := (rows 11 162 276 73 22 96 96 128 256), losses := [] }

theorem u5120 : Upper (D 6) (R 6) [10,160,272,65,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5121 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 276 73 49 36 66 196 324), lower := (rows 11 162 276 73 49 36 66 128 256), losses := [] }

theorem u5121 : Upper (D 6) (R 6) [10,160,272,65,33,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5122 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 162 276 73 49 36 68 194 322), lower := (rows 11 162 276 73 49 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 24 100 100 128 256), good := (rows 25 224 380 121 121 100 100 128 256) }] }

theorem u5122 : Upper (D 6) (R 6) [10,160,272,65,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5123 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 276 73 52 96 65 134 262), lower := (rows 11 162 276 73 52 96 65 128 256), losses := [] }

theorem u5123 : Upper (D 6) (R 6) [10,160,272,65,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5124 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 73 52 96 66 133 261), lower := (rows 11 162 276 73 52 96 66 128 256), losses := [] }

theorem u5124 : Upper (D 6) (R 6) [10,160,272,65,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5125 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 276 73 52 96 68 131 259), lower := (rows 11 162 276 73 52 96 68 128 256), losses := [] }

theorem u5125 : Upper (D 6) (R 6) [10,160,272,65,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5126 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 276 73 112 36 65 134 262), lower := (rows 11 162 276 73 112 36 65 128 256), losses := [] }

theorem u5126 : Upper (D 6) (R 6) [10,160,272,65,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5127 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 276 73 112 36 66 133 261), lower := (rows 11 162 276 73 112 36 66 128 256), losses := [] }

theorem u5127 : Upper (D 6) (R 6) [10,160,272,65,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5128 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 276 73 112 36 68 131 259), lower := (rows 11 162 276 73 112 36 68 128 256), losses := [] }

theorem u5128 : Upper (D 6) (R 6) [10,160,272,65,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5129 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 76 21 96 65 162 290), lower := (rows 11 162 276 76 21 96 65 128 256), losses := [] }

theorem u5129 : Upper (D 6) (R 6) [10,160,272,68,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5130 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 7, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 162 276 76 21 96 66 161 289), lower := (rows 11 162 276 76 21 96 66 128 256), losses := [] }

theorem u5130 : Upper (D 6) (R 6) [10,160,272,68,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5131 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 276 76 21 96 96 131 259), lower := (rows 11 162 276 76 21 96 96 128 256), losses := [] }

theorem u5131 : Upper (D 6) (R 6) [10,160,272,68,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5132 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 162 276 76 22 33 65 224 352), lower := (rows 11 162 276 76 22 33 65 128 256), losses := [] }

theorem u5132 : Upper (D 6) (R 6) [10,160,272,68,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5133 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 162 276 76 22 33 96 193 321), lower := (rows 11 162 276 76 22 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 98 128 256), good := (rows 74 226 284 76 94 96 96 128 256) }] }

theorem u5133 : Upper (D 6) (R 6) [10,160,272,68,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5134 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 162 276 76 22 96 65 161 289), lower := (rows 11 162 276 76 22 96 65 128 256), losses := [] }

theorem u5134 : Upper (D 6) (R 6) [10,160,272,68,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5135 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 276 76 22 96 96 129 257), lower := (rows 11 162 276 76 22 96 96 128 256), losses := [] }

theorem u5135 : Upper (D 6) (R 6) [10,160,272,68,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5136 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 162 276 76 52 33 65 194 322), lower := (rows 11 162 276 76 52 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 24 97 97 128 256), good := (rows 121 224 284 124 124 97 97 128 256) }] }

theorem u5136 : Upper (D 6) (R 6) [10,160,272,68,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5137 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 162 276 76 52 33 66 193 321), lower := (rows 11 162 276 76 52 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 67 161 289), good := (rows 459 450 276 76 404 449 66 128 256) }] }

theorem u5137 : Upper (D 6) (R 6) [10,160,272,68,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5138 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 162 276 76 82 33 65 164 292), lower := (rows 11 162 276 76 82 33 65 128 256), losses := [] }

theorem u5138 : Upper (D 6) (R 6) [10,160,272,68,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5139 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 276 76 82 33 68 161 289), lower := (rows 11 162 276 76 82 33 68 128 256), losses := [] }

theorem u5139 : Upper (D 6) (R 6) [10,160,272,68,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5140 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 276 76 82 33 96 133 261), lower := (rows 11 162 276 76 82 33 96 128 256), losses := [] }

theorem u5140 : Upper (D 6) (R 6) [10,160,272,68,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5141 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 162 276 76 82 36 65 161 289), lower := (rows 11 162 276 76 82 36 65 128 256), losses := [] }

theorem u5141 : Upper (D 6) (R 6) [10,160,272,68,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5142 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 276 76 82 36 96 129 257), lower := (rows 11 162 276 76 82 36 96 128 256), losses := [] }

theorem u5142 : Upper (D 6) (R 6) [10,160,272,68,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5143 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 276 76 112 33 65 134 262), lower := (rows 11 162 276 76 112 33 65 128 256), losses := [] }

theorem u5143 : Upper (D 6) (R 6) [10,160,272,68,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5144 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 162 276 76 112 33 66 133 261), lower := (rows 11 162 276 76 112 33 66 128 256), losses := [] }

theorem u5144 : Upper (D 6) (R 6) [10,160,272,68,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5145 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 276 76 112 33 68 131 259), lower := (rows 11 162 276 76 112 33 68 128 256), losses := [] }

theorem u5145 : Upper (D 6) (R 6) [10,160,272,68,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5146 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 104 21 33 66 196 324), lower := (rows 11 162 276 104 21 33 66 128 256), losses := [] }

theorem u5146 : Upper (D 6) (R 6) [10,160,272,96,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5147 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 104 21 33 68 194 322), lower := (rows 11 162 276 104 21 33 68 128 256), losses := [] }

theorem u5147 : Upper (D 6) (R 6) [10,160,272,96,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5148 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 104 22 33 65 196 324), lower := (rows 11 162 276 104 22 33 65 128 256), losses := [] }

theorem u5148 : Upper (D 6) (R 6) [10,160,272,96,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5149 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 104 22 33 68 193 321), lower := (rows 11 162 276 104 22 33 68 128 256), losses := [] }

theorem u5149 : Upper (D 6) (R 6) [10,160,272,96,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5150 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 276 104 82 36 65 133 261), lower := (rows 11 162 276 104 82 36 65 128 256), losses := [] }

theorem u5150 : Upper (D 6) (R 6) [10,160,272,96,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5151 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 276 104 82 36 68 129 257), lower := (rows 11 162 276 104 82 36 68 128 256), losses := [] }

theorem u5151 : Upper (D 6) (R 6) [10,160,272,96,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5152 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 104 84 33 65 134 262), lower := (rows 11 162 276 104 84 33 65 128 256), losses := [] }

theorem u5152 : Upper (D 6) (R 6) [10,160,272,96,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5153 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 104 84 33 66 133 261), lower := (rows 11 162 276 104 84 33 66 128 256), losses := [] }

theorem u5153 : Upper (D 6) (R 6) [10,160,272,96,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5154 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 276 104 84 33 68 131 259), lower := (rows 11 162 276 104 84 33 68 128 256), losses := [] }

theorem u5154 : Upper (D 6) (R 6) [10,160,272,96,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5155 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 292 13 81 96 66 148 276), lower := (rows 11 162 292 13 81 96 66 128 256), losses := [] }

theorem u5155 : Upper (D 6) (R 6) [10,160,288,5,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5156 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 3, region := 80, targets := 2 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 162 292 13 81 96 68 146 274), lower := (rows 11 162 292 13 81 96 68 128 256), losses := [] }

theorem u5156 : Upper (D 6) (R 6) [10,160,288,5,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5157 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 292 13 81 96 80 134 262), lower := (rows 11 162 292 13 81 96 80 128 256), losses := [] }

theorem u5157 : Upper (D 6) (R 6) [10,160,288,5,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5157 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5158 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 292 13 82 48 65 196 324), lower := (rows 11 162 292 13 82 48 65 128 256), losses := [] }

theorem u5158 : Upper (D 6) (R 6) [10,160,288,5,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5158 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5159 : PairBound 9 := { available := 65, camps := [], pairs := [(4,0),(4,5)], upper := (rows 11 162 292 13 82 48 68 193 321), lower := (rows 11 162 292 13 82 48 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 57 76 128 256), good := (rows 122 162 356 124 114 48 68 128 256) },{ target := 5, region := (rows 1 2 4 8 17 0 76 137 265), good := (rows 475 130 324 477 82 16 68 128 256) }] }

theorem u5159 : Upper (D 6) (R 6) [10,160,288,5,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5159 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5159
end Delivery.IrregularNine14.P06
