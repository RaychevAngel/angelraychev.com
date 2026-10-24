import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0016

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7140 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 324 152 145 96 96 224 352), lower := (rows 7 11 324 152 145 32 64 128 256), losses := [] }

theorem u7140 : Upper (D 8) (R 8) [6,9,320,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7141 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 324 152 176 97 97 225 353), lower := (rows 7 11 324 152 176 32 64 128 256), losses := [] }

theorem u7141 : Upper (D 8) (R 8) [6,9,320,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7142 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 324 152 208 33 97 161 289), lower := (rows 7 11 324 152 208 32 64 128 256), losses := [] }

theorem u7142 : Upper (D 8) (R 8) [6,9,320,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7143 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 168 49 240 240 240 496), lower := (rows 7 11 324 168 49 32 64 128 256), losses := [] }

theorem u7143 : Upper (D 8) (R 8) [6,9,320,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7144 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 168 81 176 240 176 432), lower := (rows 7 11 324 168 81 32 64 128 256), losses := [] }

theorem u7144 : Upper (D 8) (R 8) [6,9,320,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7145 : Route 9 := (fun mask => (mask,id))

def c7145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7145 : Upper (D 8) (R 8) [6,9,320,160,96] 13 := by
  apply FastRouting.sound _ _ [6,9,320,160,96] 13 (by decide) (choices 1) [1,16,128] r7145 c7145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u960
  · exact u961
  · exact u962

def b7146 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 168 145 112 112 240 368), lower := (rows 7 11 324 168 145 32 64 128 256), losses := [] }

theorem u7146 : Upper (D 8) (R 8) [6,9,320,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7147 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 324 168 176 113 113 241 369), lower := (rows 7 11 324 168 176 32 64 128 256), losses := [] }

theorem u7147 : Upper (D 8) (R 8) [6,9,320,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7148 : Route 9 := (fun mask => (mask,id))

def c7148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7148 : Upper (D 8) (R 8) [6,9,320,160,192] 13 := by
  apply FastRouting.sound _ _ [6,9,320,160,192] 13 (by decide) (choices 1) [1,16] r7148 c7148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u963
  · exact u964

def b7149 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 41 112 480 448 448 448), lower := (rows 7 26 37 41 112 32 64 128 256), losses := [] }

theorem u7149 : Upper (D 8) (R 8) [6,24,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7150 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 37 41 208 480 480 480 480), lower := (rows 7 26 37 41 208 32 64 128 256), losses := [] }

theorem u7150 : Upper (D 8) (R 8) [6,24,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7151 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 41 304 224 192 192 448), lower := (rows 7 26 37 41 304 32 64 128 256), losses := [] }

theorem u7151 : Upper (D 8) (R 8) [6,24,33,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7152 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 37 41 336 224 224 224 480), lower := (rows 7 26 37 41 336 32 64 128 256), losses := [] }

theorem u7152 : Upper (D 8) (R 8) [6,24,33,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7153 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 37 73 112 416 480 416 416), lower := (rows 7 26 37 73 112 32 64 128 256), losses := [] }

theorem u7153 : Upper (D 8) (R 8) [6,24,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7154 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 73 176 480 480 480 480), lower := (rows 7 26 37 73 176 32 64 128 256), losses := [] }

theorem u7154 : Upper (D 8) (R 8) [6,24,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7155 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 73 208 416 480 416 416), lower := (rows 7 26 37 73 208 32 64 128 256), losses := [] }

theorem u7155 : Upper (D 8) (R 8) [6,24,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7156 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 73 304 224 224 224 480), lower := (rows 7 26 37 73 304 32 64 128 256), losses := [] }

theorem u7156 : Upper (D 8) (R 8) [6,24,33,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7157 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 73 336 160 224 160 416), lower := (rows 7 26 37 73 336 32 64 128 256), losses := [] }

theorem u7157 : Upper (D 8) (R 8) [6,24,33,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7158 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 73 400 224 224 224 480), lower := (rows 7 26 37 73 400 32 64 128 256), losses := [] }

theorem u7158 : Upper (D 8) (R 8) [6,24,33,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7159 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 37 104 112 417 449 385 385), lower := (rows 7 26 37 104 112 32 64 128 256), losses := [] }

theorem u7159 : Upper (D 8) (R 8) [6,24,33,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m7160_128 : Upper (D 8) (R 8) [6,24,33,96,160,128] 13 :=
  permutation_upper _ _ _ [6,24,33,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u966

def r7160 : Route 9 := (fun mask => (mask,id))

def c7160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7160 : Upper (D 8) (R 8) [6,24,33,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,160] 13 (by decide) (choices 1) [1,64,128,256] r7160 c7160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u965
  · exact u966
  · exact m7160_128
  · exact u967

def b7161 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 208 417 481 417 417), lower := (rows 7 26 37 104 208 32 64 128 256), losses := [] }

theorem u7161 : Upper (D 8) (R 8) [6,24,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7162 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 104 273 224 224 224 480), lower := (rows 7 26 37 104 273 32 64 128 256), losses := [] }

theorem u7162 : Upper (D 8) (R 8) [6,24,33,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7163 : Route 9 := (fun mask => (mask,id))

def c7163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7163 : Upper (D 8) (R 8) [6,24,33,96,288] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,288] 13 (by decide) (choices 1) [1,64,128] r7163 c7163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u968
  · exact u969
  · exact u970

def b7164 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 336 161 225 161 417), lower := (rows 7 26 37 104 336 32 64 128 256), losses := [] }

theorem u7164 : Upper (D 8) (R 8) [6,24,33,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7165 : Route 9 := (fun mask => (mask,id))

def c7165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7165 : Upper (D 8) (R 8) [6,24,33,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,384] 13 (by decide) (choices 1) [1,64,128] r7165 c7165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u971
  · exact u972
  · exact u973

def b7166 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 200 208 289 353 417 289), lower := (rows 7 26 37 200 208 32 64 128 256), losses := [] }

theorem u7166 : Upper (D 8) (R 8) [6,24,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7167 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 200 273 224 224 224 480), lower := (rows 7 26 37 200 273 32 64 128 256), losses := [] }

theorem u7167 : Upper (D 8) (R 8) [6,24,33,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7168 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7168 : Upper (D 8) (R 8) [6,24,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,288] 13 (by decide) (choices 1) [1,64] r7168 c7168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u974
  · exact u975

def b7169 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 200 336 161 225 161 417), lower := (rows 7 26 37 200 336 32 64 128 256), losses := [] }

theorem u7169 : Upper (D 8) (R 8) [6,24,33,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7170 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 41 176 480 480 480 480), lower := (rows 7 26 69 41 176 32 64 128 256), losses := [] }

theorem u7170 : Upper (D 8) (R 8) [6,24,65,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7171 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 41 304 224 224 224 480), lower := (rows 7 26 69 41 304 32 64 128 256), losses := [] }

theorem u7171 : Upper (D 8) (R 8) [6,24,65,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7172 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 41 400 224 224 224 480), lower := (rows 7 26 69 41 400 32 64 128 256), losses := [] }

theorem u7172 : Upper (D 8) (R 8) [6,24,65,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7173 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 69 73 176 416 480 416 416), lower := (rows 7 26 69 73 176 32 64 128 256), losses := [] }

theorem u7173 : Upper (D 8) (R 8) [6,24,65,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7174 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 69 73 304 160 224 160 416), lower := (rows 7 26 69 73 304 32 64 128 256), losses := [] }

theorem u7174 : Upper (D 8) (R 8) [6,24,65,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7175 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 69 73 400 160 224 160 416), lower := (rows 7 26 69 73 400 32 64 128 256), losses := [] }

theorem u7175 : Upper (D 8) (R 8) [6,24,65,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7176 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 69 104 176 417 481 417 417), lower := (rows 7 26 69 104 176 32 64 128 256), losses := [] }

theorem u7176 : Upper (D 8) (R 8) [6,24,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7177 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 69 104 304 161 225 161 417), lower := (rows 7 26 69 104 304 32 64 128 256), losses := [] }

theorem u7177 : Upper (D 8) (R 8) [6,24,65,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7178 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 69 104 400 161 225 161 417), lower := (rows 7 26 69 104 400 32 64 128 256), losses := [] }

theorem u7178 : Upper (D 8) (R 8) [6,24,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7179 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 69 137 176 352 352 480 352), lower := (rows 7 26 69 137 176 32 64 128 256), losses := [] }

theorem u7179 : Upper (D 8) (R 8) [6,24,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7180 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 137 304 224 224 224 480), lower := (rows 7 26 69 137 304 32 64 128 256), losses := [] }

theorem u7180 : Upper (D 8) (R 8) [6,24,65,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7181 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 69 137 400 96 96 224 352), lower := (rows 7 26 69 137 400 32 64 128 256), losses := [] }

theorem u7181 : Upper (D 8) (R 8) [6,24,65,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7182 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 168 176 353 353 481 353), lower := (rows 7 26 69 168 176 32 64 128 256), losses := [] }

theorem u7182 : Upper (D 8) (R 8) [6,24,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7183 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 69 168 208 289 353 417 289), lower := (rows 7 26 69 168 208 32 64 128 256), losses := [] }

theorem u7183 : Upper (D 8) (R 8) [6,24,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7184 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 168 273 224 224 224 480), lower := (rows 7 26 69 168 273 32 64 128 256), losses := [] }

theorem u7184 : Upper (D 8) (R 8) [6,24,65,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7185 : Route 9 := (fun mask => (mask,id))

def c7185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7185 : Upper (D 8) (R 8) [6,24,65,160,288] 13 := by
  apply FastRouting.sound _ _ [6,24,65,160,288] 13 (by decide) (choices 1) [1,64,128] r7185 c7185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u976
  · exact u977
  · exact u978

def b7186 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 69 168 336 161 225 161 417), lower := (rows 7 26 69 168 336 32 64 128 256), losses := [] }

theorem u7186 : Upper (D 8) (R 8) [6,24,65,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7187 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 69 168 400 97 97 225 353), lower := (rows 7 26 69 168 400 32 64 128 256), losses := [] }

theorem u7187 : Upper (D 8) (R 8) [6,24,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7188 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 69 200 304 161 225 161 417), lower := (rows 7 26 69 200 304 32 64 128 256), losses := [] }

theorem u7188 : Upper (D 8) (R 8) [6,24,65,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7189 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 69 200 400 33 97 161 289), lower := (rows 7 26 69 200 400 32 64 128 256), losses := [] }

theorem u7189 : Upper (D 8) (R 8) [6,24,65,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7190 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 41 49 480 448 448 448), lower := (rows 7 26 100 41 49 32 64 128 256), losses := [] }

theorem u7190 : Upper (D 8) (R 8) [6,24,96,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7191 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 41 81 416 480 416 416), lower := (rows 7 26 100 41 81 32 64 128 256), losses := [] }

theorem u7191 : Upper (D 8) (R 8) [6,24,96,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7192 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 41 112 417 449 385 385), lower := (rows 7 26 100 41 112 32 64 128 256), losses := [] }

theorem u7192 : Upper (D 8) (R 8) [6,24,96,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7193 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 41 145 480 480 480 480), lower := (rows 7 26 100 41 145 32 64 128 256), losses := [] }

theorem u7193 : Upper (D 8) (R 8) [6,24,96,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7194 : Route 9 := (fun mask => (mask,id))

def c7194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7194 : Upper (D 8) (R 8) [6,24,96,33,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,160] 13 (by decide) (choices 1) [1,64,128,256] r7194 c7194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u979
  · exact u980
  · exact u981
  · exact u982

def b7195 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 100 41 208 417 481 417 417), lower := (rows 7 26 100 41 208 32 64 128 256), losses := [] }

theorem u7195 : Upper (D 8) (R 8) [6,24,96,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7196 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 41 273 224 224 224 480), lower := (rows 7 26 100 41 273 32 64 128 256), losses := [] }

theorem u7196 : Upper (D 8) (R 8) [6,24,96,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7197 : Route 9 := (fun mask => (mask,id))

def c7197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7197 : Upper (D 8) (R 8) [6,24,96,33,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,288] 13 (by decide) (choices 1) [1,64,128] r7197 c7197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u983
  · exact u984
  · exact u985

def b7198 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 100 41 336 161 225 161 417), lower := (rows 7 26 100 41 336 32 64 128 256), losses := [] }

theorem u7198 : Upper (D 8) (R 8) [6,24,96,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7199 : Route 9 := (fun mask => (mask,id))

def c7199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7199 : Upper (D 8) (R 8) [6,24,96,33,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,384] 13 (by decide) (choices 1) [1,64,128] r7199 c7199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u986
  · exact u987
  · exact u988

#print axioms u7199
end Delivery.IrregularNine14.P08
