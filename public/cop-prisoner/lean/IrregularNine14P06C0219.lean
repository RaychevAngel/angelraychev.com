import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0043

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13140 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 393, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 69 392 82 48 101 165 293), lower := (rows 11 38 69 392 82 48 64 128 256), losses := [] }

theorem u13140 : Upper (D 6) (R 6) [10,36,65,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13140 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13141 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 11 38 69 392 112 33 86 150 278), lower := (rows 11 38 69 392 112 33 64 128 256), losses := [] }

theorem u13141 : Upper (D 6) (R 6) [10,36,65,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13142 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 38 69 392 112 34 85 149 277), lower := (rows 11 38 69 392 112 34 64 128 256), losses := [] }

theorem u13142 : Upper (D 6) (R 6) [10,36,65,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13143 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 392 112 36 83 147 275), lower := (rows 11 38 69 392 112 36 64 128 256), losses := [] }

theorem u13143 : Upper (D 6) (R 6) [10,36,65,384,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13144 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 69 392 112 48 71 135 263), lower := (rows 11 38 69 392 112 48 64 128 256), losses := [] }

theorem u13144 : Upper (D 6) (R 6) [10,36,65,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13144 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13145 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 70 25 148 33 352 480 352), lower := (rows 11 38 70 25 148 33 64 128 256), losses := [] }

theorem u13145 : Upper (D 6) (R 6) [10,36,66,17,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13146 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 25 148 96 353 417 289), lower := (rows 11 38 70 25 148 96 64 128 256), losses := [] }

theorem u13146 : Upper (D 6) (R 6) [10,36,66,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13147 : Route 9 := (fun mask => (mask,id))

def c13147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13147 : Upper (D 6) (R 6) [10,36,66,17,132,256] 13 := by
  apply FastRouting.sound _ _ [10,36,66,17,132,256] 13 (by decide) (choices 1) [1,32] r13147 c13147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2614
  · exact u2615

def b13148 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 70 25 176 33 324 452 324), lower := (rows 11 38 70 25 176 33 64 128 256), losses := [] }

theorem u13148 : Upper (D 6) (R 6) [10,36,66,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13149 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 25 176 36 321 449 321), lower := (rows 11 38 70 25 176 36 64 128 256), losses := [] }

theorem u13149 : Upper (D 6) (R 6) [10,36,66,17,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13150 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 25 176 96 325 389 261), lower := (rows 11 38 70 25 176 96 64 128 256), losses := [] }

theorem u13150 : Upper (D 6) (R 6) [10,36,66,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13151 : Route 9 := (fun mask => (mask,id))

def c13151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13151 : Upper (D 6) (R 6) [10,36,66,17,160,256] 13 := by
  apply FastRouting.sound _ _ [10,36,66,17,160,256] 13 (by decide) (choices 1) [1,4] r13151 c13151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2616
  · exact u2617

def b13152 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 70 25 208 33 356 420 292), lower := (rows 11 38 70 25 208 33 64 128 256), losses := [] }

theorem u13152 : Upper (D 6) (R 6) [10,36,66,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13153 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 25 208 36 353 417 289), lower := (rows 11 38 70 25 208 36 64 128 256), losses := [] }

theorem u13153 : Upper (D 6) (R 6) [10,36,66,17,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13154 : Route 9 := (fun mask => (mask,id))

def c13154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13154 : Upper (D 6) (R 6) [10,36,66,17,192,256] 13 := by
  apply FastRouting.sound _ _ [10,36,66,17,192,256] 13 (by decide) (choices 1) [1,4,32] r13154 c13154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2618
  · exact u2619
  · exact u2620

def b13155 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 70 25 400 33 100 228 356), lower := (rows 11 38 70 25 400 33 64 128 256), losses := [] }

theorem u13155 : Upper (D 6) (R 6) [10,36,66,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13156 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 25 400 36 97 225 353), lower := (rows 11 38 70 25 400 36 64 128 256), losses := [] }

theorem u13156 : Upper (D 6) (R 6) [10,36,66,17,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13157 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 25 400 96 101 165 293), lower := (rows 11 38 70 25 400 96 64 128 256), losses := [] }

theorem u13157 : Upper (D 6) (R 6) [10,36,66,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13158 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 496, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 70 28 145 33 352 480 352), lower := (rows 11 38 70 28 145 33 64 128 256), losses := [] }

theorem u13158 : Upper (D 6) (R 6) [10,36,66,20,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13159 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 28 145 96 353 417 289), lower := (rows 11 38 70 28 145 96 64 128 256), losses := [] }

theorem u13159 : Upper (D 6) (R 6) [10,36,66,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13160 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 496, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 28 145 288 97 225 353), lower := (rows 11 38 70 28 145 288 64 128 256), losses := [] }

theorem u13160 : Upper (D 6) (R 6) [10,36,66,20,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13160 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13161 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 496, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 70 28 400 33 97 225 353), lower := (rows 11 38 70 28 400 33 64 128 256), losses := [] }

theorem u13161 : Upper (D 6) (R 6) [10,36,66,20,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13162 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 28 400 96 97 161 289), lower := (rows 11 38 70 28 400 96 64 128 256), losses := [] }

theorem u13162 : Upper (D 6) (R 6) [10,36,66,20,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13163 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 38 70 56 145 33 324 452 324), lower := (rows 11 38 70 56 145 33 64 128 256), losses := [] }

theorem u13163 : Upper (D 6) (R 6) [10,36,66,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13164 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 56 145 36 321 449 321), lower := (rows 11 38 70 56 145 36 64 128 256), losses := [] }

theorem u13164 : Upper (D 6) (R 6) [10,36,66,48,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13165 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 56 145 96 325 389 261), lower := (rows 11 38 70 56 145 96 64 128 256), losses := [] }

theorem u13165 : Upper (D 6) (R 6) [10,36,66,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13166 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 56 145 288 69 197 325), lower := (rows 11 38 70 56 145 288 64 128 256), losses := [] }

theorem u13166 : Upper (D 6) (R 6) [10,36,66,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13166 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13167 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 70 56 148 33 321 449 321), lower := (rows 11 38 70 56 148 33 64 128 256), losses := [] }

theorem u13167 : Upper (D 6) (R 6) [10,36,66,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13168 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 56 148 96 321 385 257), lower := (rows 11 38 70 56 148 96 64 128 256), losses := [] }

theorem u13168 : Upper (D 6) (R 6) [10,36,66,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13169 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 56 148 288 65 193 321), lower := (rows 11 38 70 56 148 288 64 128 256), losses := [] }

theorem u13169 : Upper (D 6) (R 6) [10,36,66,48,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13169 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13170 : Route 9 := (fun mask => (mask,id))

def c13170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u13170 : Upper (D 6) (R 6) [10,36,66,48,192,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,48,192,1] 13 (by decide) (choices 1) [1,4,256] r13170 c13170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2621
  · exact u2622
  · exact u2623

def b13171 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 56 208 36 321 385 257), lower := (rows 11 38 70 56 208 36 64 128 256), losses := [] }

theorem u13171 : Upper (D 6) (R 6) [10,36,66,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13172 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 56 208 288 69 133 261), lower := (rows 11 38 70 56 208 288 64 128 256), losses := [] }

theorem u13172 : Upper (D 6) (R 6) [10,36,66,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13172 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13173 : Route 9 := (fun mask => (mask,id))

def c13173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13173 : Upper (D 6) (R 6) [10,36,66,48,384,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,48,384,1] 13 (by decide) (choices 1) [1,4] r13173 c13173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2624
  · exact u2625

def b13174 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 56 400 36 65 193 321), lower := (rows 11 38 70 56 400 36 64 128 256), losses := [] }

theorem u13174 : Upper (D 6) (R 6) [10,36,66,48,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13175 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 56 400 96 69 133 261), lower := (rows 11 38 70 56 400 96 64 128 256), losses := [] }

theorem u13175 : Upper (D 6) (R 6) [10,36,66,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13176 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 326, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 70 88 145 33 356 420 292), lower := (rows 11 38 70 88 145 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 49 66 130 258), good := (rows 505 484 452 120 185 57 64 128 256) }] }

theorem u13176 : Upper (D 6) (R 6) [10,36,66,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13177 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 88 145 36 353 417 289), lower := (rows 11 38 70 88 145 36 64 128 256), losses := [] }

theorem u13177 : Upper (D 6) (R 6) [10,36,66,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13178 : Route 9 := (fun mask => (mask,id))

def c13178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13178 : Upper (D 6) (R 6) [10,36,66,80,129,256] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,129,256] 13 (by decide) (choices 1) [1,4,32] r13178 c13178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2626
  · exact u2627
  · exact u2628

def b13179 : PairBound 9 := { available := 289, camps := [], pairs := [(3,1),(4,1),(4,6)], upper := (rows 11 38 70 88 148 33 353 417 289), lower := (rows 11 38 70 88 148 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 15 18 33 97 161 289), good := (rows 505 508 92 88 156 489 64 128 256) },{ target := 6, region := (rows 1 2 4 8 18 33 0 161 289), good := (rows 443 438 22 24 148 417 0 128 256) }] }

theorem u13179 : Upper (D 6) (R 6) [10,36,66,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13180 : Route 9 := (fun mask => (mask,id))

def c13180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13180 : Upper (D 6) (R 6) [10,36,66,80,132,256] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,132,256] 13 (by decide) (choices 1) [1,32] r13180 c13180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2629
  · exact u2630

def r13181 : Route 9 := (fun mask => (mask,id))

def c13181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u13181 : Upper (D 6) (R 6) [10,36,66,80,160,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,160,1] 13 (by decide) (choices 1) [1,4,256] r13181 c13181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2631
  · exact u2632
  · exact u2633

def b13182 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 88 176 36 321 385 257), lower := (rows 11 38 70 88 176 36 64 128 256), losses := [] }

theorem u13182 : Upper (D 6) (R 6) [10,36,66,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13183 : Route 9 := (fun mask => (mask,id))

def c13183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13183 : Upper (D 6) (R 6) [10,36,66,80,160,256] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,160,256] 13 (by decide) (choices 1) [1,4] r13183 c13183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2634
  · exact u2635

def r13184 : Route 9 := (fun mask => (mask,id))

def c13184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13184 : Upper (D 6) (R 6) [10,36,66,80,384,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,384,1] 13 (by decide) (choices 1) [1,4,32] r13184 c13184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2636
  · exact u2637
  · exact u2638

def b13185 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 88 400 36 97 161 289), lower := (rows 11 38 70 88 400 36 64 128 256), losses := [] }

theorem u13185 : Upper (D 6) (R 6) [10,36,66,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13186 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 137 49 36 336 464 336), lower := (rows 11 38 70 137 49 36 64 128 256), losses := [] }

theorem u13186 : Upper (D 6) (R 6) [10,36,66,129,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13187 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 137 49 48 324 452 324), lower := (rows 11 38 70 137 49 48 64 128 256), losses := [] }

theorem u13187 : Upper (D 6) (R 6) [10,36,66,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13187 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13188 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 137 49 96 340 404 276), lower := (rows 11 38 70 137 49 96 64 128 256), losses := [] }

theorem u13188 : Upper (D 6) (R 6) [10,36,66,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13189 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 70, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 70 137 49 288 84 212 340), lower := (rows 11 38 70 137 49 288 64 128 256), losses := [] }

theorem u13189 : Upper (D 6) (R 6) [10,36,66,129,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13189 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13190 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 137 81 36 368 432 304), lower := (rows 11 38 70 137 81 36 64 128 256), losses := [] }

theorem u13190 : Upper (D 6) (R 6) [10,36,66,129,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13191 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 393, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 70 137 81 48 356 420 292), lower := (rows 11 38 70 137 81 48 64 128 256), losses := [] }

theorem u13191 : Upper (D 6) (R 6) [10,36,66,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13191 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13192 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 70 137 81 288 116 180 308), lower := (rows 11 38 70 137 81 288 64 128 256), losses := [] }

theorem u13192 : Upper (D 6) (R 6) [10,36,66,129,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13192 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13193 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 70 137 112 33 340 404 276), lower := (rows 11 38 70 137 112 33 64 128 256), losses := [] }

theorem u13193 : Upper (D 6) (R 6) [10,36,66,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13194 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 137 112 36 337 401 273), lower := (rows 11 38 70 137 112 36 64 128 256), losses := [] }

theorem u13194 : Upper (D 6) (R 6) [10,36,66,129,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13195 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 70 137 112 48 325 389 261), lower := (rows 11 38 70 137 112 48 64 128 256), losses := [] }

theorem u13195 : Upper (D 6) (R 6) [10,36,66,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13195 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13196 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 70 137 112 288 85 149 277), lower := (rows 11 38 70 137 112 288 64 128 256), losses := [] }

theorem u13196 : Upper (D 6) (R 6) [10,36,66,129,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13196 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13197 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 137 273 36 112 240 368), lower := (rows 11 38 70 137 273 36 64 128 256), losses := [] }

theorem u13197 : Upper (D 6) (R 6) [10,36,66,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13198 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 70 137 273 48 100 228 356), lower := (rows 11 38 70 137 273 48 64 128 256), losses := [] }

theorem u13198 : Upper (D 6) (R 6) [10,36,66,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13198 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13199 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 137 273 96 116 180 308), lower := (rows 11 38 70 137 273 96 64 128 256), losses := [] }

theorem u13199 : Upper (D 6) (R 6) [10,36,66,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13199
end Delivery.IrregularNine14.P06
