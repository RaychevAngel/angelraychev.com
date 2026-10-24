import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0050
import IrregularNine14P06C0051

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14100 : Route 9 := (fun mask => (mask,id))

def c14100 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14100 : Upper (D 6) (R 6) [10,48,65,160,320,4] 13 := by
  apply FastRouting.sound _ _ [10,48,65,160,320,4] 13 (by decide) (choices 1) [1,2,4] r14100 c14100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3053
  · exact u3054
  · exact u3055

def b14101 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 200 273 34 100 164 292), lower := (rows 11 50 69 200 273 34 64 128 256), losses := [] }

theorem u14101 : Upper (D 6) (R 6) [10,48,65,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14102 : Route 9 := (fun mask => (mask,id))

def c14102 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14102 : Upper (D 6) (R 6) [10,48,65,192,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,65,192,257,4] 13 (by decide) (choices 1) [2,4,32] r14102 c14102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3056
  · exact u3057
  · exact u3058

def b14103 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 306, targets := 64 }], pairs := [(1,2),(1,6),(4,6)], upper := (rows 11 50 69 200 276 33 102 166 294), lower := (rows 11 50 69 200 276 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 64 128 256), good := (rows 43 50 97 200 306 33 64 128 256) }] }

theorem u14103 : Upper (D 6) (R 6) [10,48,65,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14104 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 200 276 34 101 165 293), lower := (rows 11 50 69 200 276 34 64 128 256), losses := [] }

theorem u14104 : Upper (D 6) (R 6) [10,48,65,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14105 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 201, targets := 4 },{ cop := 2, region := 306, targets := 64 }], pairs := [(0,2),(1,6),(3,2)], upper := (rows 11 50 69 200 276 36 99 163 291), lower := (rows 11 50 69 200 276 36 64 128 256), losses := [] }

theorem u14105 : Upper (D 6) (R 6) [10,48,65,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14106 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 50, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 50 69 392 22 33 100 228 356), lower := (rows 11 50 69 392 22 33 64 128 256), losses := [] }

theorem u14106 : Upper (D 6) (R 6) [10,48,65,384,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14107 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 69 392 22 36 97 225 353), lower := (rows 11 50 69 392 22 36 64 128 256), losses := [] }

theorem u14107 : Upper (D 6) (R 6) [10,48,65,384,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14108 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 69 392 22 96 101 165 293), lower := (rows 11 50 69 392 22 96 64 128 256), losses := [] }

theorem u14108 : Upper (D 6) (R 6) [10,48,65,384,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14109 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 324, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 70 44 145 33 324 452 324), lower := (rows 11 50 70 44 145 33 64 128 256), losses := [] }

theorem u14109 : Upper (D 6) (R 6) [10,48,66,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14110 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 70 44 145 36 321 449 321), lower := (rows 11 50 70 44 145 36 64 128 256), losses := [] }

theorem u14110 : Upper (D 6) (R 6) [10,48,66,36,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14111 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 70 44 145 96 325 389 261), lower := (rows 11 50 70 44 145 96 64 128 256), losses := [] }

theorem u14111 : Upper (D 6) (R 6) [10,48,66,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14112 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 70 44 145 288 69 197 325), lower := (rows 11 50 70 44 145 288 64 128 256), losses := [] }

theorem u14112 : Upper (D 6) (R 6) [10,48,66,36,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14112 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14113 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 70 44 148 33 321 449 321), lower := (rows 11 50 70 44 148 33 64 128 256), losses := [] }

theorem u14113 : Upper (D 6) (R 6) [10,48,66,36,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14114 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 70 44 148 96 321 385 257), lower := (rows 11 50 70 44 148 96 64 128 256), losses := [] }

theorem u14114 : Upper (D 6) (R 6) [10,48,66,36,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14115 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 70 44 148 288 65 193 321), lower := (rows 11 50 70 44 148 288 64 128 256), losses := [] }

theorem u14115 : Upper (D 6) (R 6) [10,48,66,36,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14115 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14116 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 50 70 44 400 33 69 197 325), lower := (rows 11 50 70 44 400 33 64 128 256), losses := [] }

theorem u14116 : Upper (D 6) (R 6) [10,48,66,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14117 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 70 44 400 36 65 193 321), lower := (rows 11 50 70 44 400 36 64 128 256), losses := [] }

theorem u14117 : Upper (D 6) (R 6) [10,48,66,36,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14118 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 70 44 400 96 69 133 261), lower := (rows 11 50 70 44 400 96 64 128 256), losses := [] }

theorem u14118 : Upper (D 6) (R 6) [10,48,66,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14119 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 324, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 70 104 145 33 324 388 260), lower := (rows 11 50 70 104 145 33 64 128 256), losses := [] }

theorem u14119 : Upper (D 6) (R 6) [10,48,66,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14120 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 50 70 104 145 36 325 389 261), lower := (rows 11 50 70 104 145 36 64 128 256), losses := [] }

theorem u14120 : Upper (D 6) (R 6) [10,48,66,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14121 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 70 104 145 288 69 133 261), lower := (rows 11 50 70 104 145 288 64 128 256), losses := [] }

theorem u14121 : Upper (D 6) (R 6) [10,48,66,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14121 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14122 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 70 104 148 33 325 389 261), lower := (rows 11 50 70 104 148 33 64 128 256), losses := [] }

theorem u14122 : Upper (D 6) (R 6) [10,48,66,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14123 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 70 104 148 36 321 385 257), lower := (rows 11 50 70 104 148 36 64 128 256), losses := [] }

theorem u14123 : Upper (D 6) (R 6) [10,48,66,96,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14124 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 70 104 148 288 69 133 261), lower := (rows 11 50 70 104 148 288 64 128 256), losses := [] }

theorem u14124 : Upper (D 6) (R 6) [10,48,66,96,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14124 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14125 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 70 104 400 33 69 133 261), lower := (rows 11 50 70 104 400 33 64 128 256), losses := [] }

theorem u14125 : Upper (D 6) (R 6) [10,48,66,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14126 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 50 70 104 400 36 69 133 261), lower := (rows 11 50 70 104 400 36 64 128 256), losses := [] }

theorem u14126 : Upper (D 6) (R 6) [10,48,66,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14127 : Route 9 := (fun mask => (mask,id))

def c14127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14127 : Upper (D 6) (R 6) [10,48,66,129,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,66,129,257,4] 13 (by decide) (choices 1) [4,32] r14127 c14127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3059
  · exact u3060

def r14128 : Route 9 := (fun mask => (mask,id))

def c14128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14128 : Upper (D 6) (R 6) [10,48,66,129,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,66,129,257,64] 13 (by decide) (choices 1) [4,32] r14128 c14128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3061
  · exact u3062

def b14129 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 70 137 276 33 100 228 356), lower := (rows 11 50 70 137 276 33 64 128 256), losses := [] }

theorem u14129 : Upper (D 6) (R 6) [10,48,66,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14130 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 201, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 70 137 276 36 97 225 353), lower := (rows 11 50 70 137 276 36 64 128 256), losses := [] }

theorem u14130 : Upper (D 6) (R 6) [10,48,66,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14131 : Route 9 := (fun mask => (mask,id))

def c14131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14131 : Upper (D 6) (R 6) [10,48,66,129,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,66,129,260,64] 13 (by decide) (choices 1) [1,4,32] r14131 c14131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3063
  · exact u3064
  · exact u3065

def b14132 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 70 137 336 33 100 164 292), lower := (rows 11 50 70 137 336 33 64 128 256), losses := [] }

theorem u14132 : Upper (D 6) (R 6) [10,48,66,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14133 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 50 70 137 336 36 101 165 293), lower := (rows 11 50 70 137 336 36 64 128 256), losses := [] }

theorem u14133 : Upper (D 6) (R 6) [10,48,66,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14134 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 70 140 21 33 352 480 352), lower := (rows 11 50 70 140 21 33 64 128 256), losses := [] }

theorem u14134 : Upper (D 6) (R 6) [10,48,66,132,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14135 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 488, targets := 2 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,0),(1,2),(3,1)], upper := (rows 11 50 70 140 21 96 353 417 289), lower := (rows 11 50 70 140 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 64 128 256), good := (rows 10 50 102 172 54 96 96 128 256) }] }

theorem u14135 : Upper (D 6) (R 6) [10,48,66,132,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14136 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 488, targets := 2 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(3,1)], upper := (rows 11 50 70 140 21 288 97 225 353), lower := (rows 11 50 70 140 21 288 64 128 256), losses := [] }

theorem u14136 : Upper (D 6) (R 6) [10,48,66,132,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14136 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14137 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(2,0),(3,0)], upper := (rows 11 50 70 140 81 33 356 420 292), lower := (rows 11 50 70 140 81 33 64 128 256), losses := [] }

theorem u14137 : Upper (D 6) (R 6) [10,48,66,132,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14138 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 50 70 140 81 36 353 417 289), lower := (rows 11 50 70 140 81 36 64 128 256), losses := [] }

theorem u14138 : Upper (D 6) (R 6) [10,48,66,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14139 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 50 70 140 81 288 101 165 293), lower := (rows 11 50 70 140 81 288 64 128 256), losses := [] }

theorem u14139 : Upper (D 6) (R 6) [10,48,66,132,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14139 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14140 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 70 140 273 33 100 228 356), lower := (rows 11 50 70 140 273 33 64 128 256), losses := [] }

theorem u14140 : Upper (D 6) (R 6) [10,48,66,132,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14141 : Route 9 := (fun mask => (mask,id))

def c14141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14141 : Upper (D 6) (R 6) [10,48,66,132,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,257,4] 13 (by decide) (choices 1) [1,32] r14141 c14141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3066
  · exact u3067

def r14142 : Route 9 := (fun mask => (mask,id))

def c14142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14142 : Upper (D 6) (R 6) [10,48,66,132,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,257,64] 13 (by decide) (choices 1) [1,4,32] r14142 c14142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3068
  · exact u3069
  · exact u3070

def r14143 : Route 9 := (fun mask => (mask,id))

def c14143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14143 : Upper (D 6) (R 6) [10,48,66,132,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,260,1] 13 (by decide) (choices 1) [1,32] r14143 c14143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3071
  · exact u3072

def r14144 : Route 9 := (fun mask => (mask,id))

def c14144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14144 : Upper (D 6) (R 6) [10,48,66,132,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,260,64] 13 (by decide) (choices 1) [1,32] r14144 c14144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3073
  · exact u3074

def r14145 : Route 9 := (fun mask => (mask,id))

def c14145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14145 : Upper (D 6) (R 6) [10,48,66,132,320,1] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,320,1] 13 (by decide) (choices 1) [1,4,32] r14145 c14145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3075
  · exact u3076
  · exact u3077

def b14146 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 50 70 140 336 36 97 161 289), lower := (rows 11 50 70 140 336 36 64 128 256), losses := [] }

theorem u14146 : Upper (D 6) (R 6) [10,48,66,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14147 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 70 168 273 33 68 196 324), lower := (rows 11 50 70 168 273 33 64 128 256), losses := [] }

theorem u14147 : Upper (D 6) (R 6) [10,48,66,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14148 : Route 9 := (fun mask => (mask,id))

def c14148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14148 : Upper (D 6) (R 6) [10,48,66,160,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,66,160,257,4] 13 (by decide) (choices 1) [1,4] r14148 c14148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3078
  · exact u3079

def r14149 : Route 9 := (fun mask => (mask,id))

def c14149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14149 : Upper (D 6) (R 6) [10,48,66,160,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,66,160,257,64] 13 (by decide) (choices 1) [1,4] r14149 c14149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3080
  · exact u3081

def r14150 : Route 9 := (fun mask => (mask,id))

def c14150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14150 : Upper (D 6) (R 6) [10,48,66,160,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,66,160,260,1] 13 (by decide) (choices 1) [1,4] r14150 c14150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3082
  · exact u3083

def b14151 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 70 168 276 36 65 193 321), lower := (rows 11 50 70 168 276 36 64 128 256), losses := [] }

theorem u14151 : Upper (D 6) (R 6) [10,48,66,160,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14152 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 50 70 168 276 96 69 133 261), lower := (rows 11 50 70 168 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 64 128 256), good := (rows 10 50 102 168 310 96 96 128 256) }] }

theorem u14152 : Upper (D 6) (R 6) [10,48,66,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14153 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 50 70 200 21 33 356 420 292), lower := (rows 11 50 70 200 21 33 64 128 256), losses := [] }

theorem u14153 : Upper (D 6) (R 6) [10,48,66,192,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14154 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 457, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 70 200 21 36 353 417 289), lower := (rows 11 50 70 200 21 36 64 128 256), losses := [] }

theorem u14154 : Upper (D 6) (R 6) [10,48,66,192,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14155 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 488, targets := 2 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,6),(3,1)], upper := (rows 11 50 70 200 21 288 101 165 293), lower := (rows 11 50 70 200 21 288 64 128 256), losses := [] }

theorem u14155 : Upper (D 6) (R 6) [10,48,66,192,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14155 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14156 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 70 200 273 33 100 164 292), lower := (rows 11 50 70 200 273 33 64 128 256), losses := [] }

theorem u14156 : Upper (D 6) (R 6) [10,48,66,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14157 : Route 9 := (fun mask => (mask,id))

def c14157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14157 : Upper (D 6) (R 6) [10,48,66,192,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,66,192,257,4] 13 (by decide) (choices 1) [1,4,32] r14157 c14157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3084
  · exact u3085
  · exact u3086

def r14158 : Route 9 := (fun mask => (mask,id))

def c14158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14158 : Upper (D 6) (R 6) [10,48,66,192,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,66,192,260,1] 13 (by decide) (choices 1) [1,4,32] r14158 c14158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3087
  · exact u3088
  · exact u3089

def b14159 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 201, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 70 200 276 36 97 161 289), lower := (rows 11 50 70 200 276 36 64 128 256), losses := [] }

theorem u14159 : Upper (D 6) (R 6) [10,48,66,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14159
end Delivery.IrregularNine14.P06
