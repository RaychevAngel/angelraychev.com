import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0058
import IrregularNine14P07C0059

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16140 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 37 73 274 96 194 130 386), lower := (rows 13 50 37 73 274 96 64 128 256), losses := [] }

theorem u16140 : Upper (D 7) (R 7) [12,48,33,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16141 : Route 9 := (fun mask => (mask,id))

def c16141 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16141 : Upper (D 7) (R 7) [12,48,33,65,258,128] 13 := by
  apply FastRouting.sound _ _ [12,48,33,65,258,128] 13 (by decide) (choices 1) [2,128] r16141 c16141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3524
  · exact u3525

def b16142 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 37 73 400 34 194 194 450), lower := (rows 13 50 37 73 400 34 64 128 256), losses := [] }

theorem u16142 : Upper (D 7) (R 7) [12,48,33,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16143 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 37 73 400 96 194 130 386), lower := (rows 13 50 37 73 400 96 64 128 256), losses := [] }

theorem u16143 : Upper (D 7) (R 7) [12,48,33,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16144 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 37 73 400 160 66 194 322), lower := (rows 13 50 37 73 400 160 64 128 256), losses := [] }

theorem u16144 : Upper (D 7) (R 7) [12,48,33,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16145 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 50 37 74 146 33 448 448 448), lower := (rows 13 50 37 74 146 33 64 128 256), losses := [] }

theorem u16145 : Upper (D 7) (R 7) [12,48,33,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16146 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 3, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 13 50 37 74 146 96 449 385 385), lower := (rows 13 50 37 74 146 96 64 128 256), losses := [] }

theorem u16146 : Upper (D 7) (R 7) [12,48,33,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16147 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 37 74 146 160 321 449 321), lower := (rows 13 50 37 74 146 160 64 128 256), losses := [] }

theorem u16147 : Upper (D 7) (R 7) [12,48,33,66,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16148 : Route 9 := (fun mask => (mask,id))

def c16148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16148 : Upper (D 7) (R 7) [12,48,33,66,130,256] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,130,256] 13 (by decide) (choices 1) [1,128] r16148 c16148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3526
  · exact u3527

def b16149 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 50 37 74 208 33 450 386 386), lower := (rows 13 50 37 74 208 33 64 128 256), losses := [] }

theorem u16149 : Upper (D 7) (R 7) [12,48,33,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16150 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 37 74 208 34 449 385 385), lower := (rows 13 50 37 74 208 34 64 128 256), losses := [] }

theorem u16150 : Upper (D 7) (R 7) [12,48,33,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16151 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 13 50 37 74 208 160 323 387 259), lower := (rows 13 50 37 74 208 160 64 128 256), losses := [] }

theorem u16151 : Upper (D 7) (R 7) [12,48,33,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16152 : Route 9 := (fun mask => (mask,id))

def c16152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16152 : Upper (D 7) (R 7) [12,48,33,66,192,256] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,192,256] 13 (by decide) (choices 1) [1,2,128] r16152 c16152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3528
  · exact u3529
  · exact u3530

def b16153 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 50 37 74 274 33 192 192 448), lower := (rows 13 50 37 74 274 33 64 128 256), losses := [] }

theorem u16153 : Upper (D 7) (R 7) [12,48,33,66,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16154 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 3, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 13 50 37 74 274 96 193 129 385), lower := (rows 13 50 37 74 274 96 64 128 256), losses := [] }

theorem u16154 : Upper (D 7) (R 7) [12,48,33,66,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16155 : Route 9 := (fun mask => (mask,id))

def c16155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16155 : Upper (D 7) (R 7) [12,48,33,66,258,128] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,258,128] 13 (by decide) (choices 1) [1,128] r16155 c16155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3531
  · exact u3532

def b16156 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 50 37 74 336 33 194 130 386), lower := (rows 13 50 37 74 336 33 64 128 256), losses := [] }

theorem u16156 : Upper (D 7) (R 7) [12,48,33,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16157 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 37 74 336 34 193 129 385), lower := (rows 13 50 37 74 336 34 64 128 256), losses := [] }

theorem u16157 : Upper (D 7) (R 7) [12,48,33,66,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16158 : Route 9 := (fun mask => (mask,id))

def c16158 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16158 : Upper (D 7) (R 7) [12,48,33,66,320,128] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,320,128] 13 (by decide) (choices 1) [1,2,128] r16158 c16158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3533
  · exact u3534
  · exact u3535

def b16159 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 50 37 74 400 33 194 194 450), lower := (rows 13 50 37 74 400 33 64 128 256), losses := [] }

theorem u16159 : Upper (D 7) (R 7) [12,48,33,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16160 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 50 37 74 400 34 193 193 449), lower := (rows 13 50 37 74 400 34 64 128 256), losses := [] }

theorem u16160 : Upper (D 7) (R 7) [12,48,33,66,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16161 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 37 74 400 96 195 131 387), lower := (rows 13 50 37 74 400 96 64 128 256), losses := [] }

theorem u16161 : Upper (D 7) (R 7) [12,48,33,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16162 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 37 74 400 160 67 195 323), lower := (rows 13 50 37 74 400 160 64 128 256), losses := [] }

theorem u16162 : Upper (D 7) (R 7) [12,48,33,66,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16163 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 50 37 200 82 33 450 386 386), lower := (rows 13 50 37 200 82 33 64 128 256), losses := [] }

theorem u16163 : Upper (D 7) (R 7) [12,48,33,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16164 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 37 200 82 34 449 385 385), lower := (rows 13 50 37 200 82 34 64 128 256), losses := [] }

theorem u16164 : Upper (D 7) (R 7) [12,48,33,192,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16165 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 50 37 200 82 160 323 387 259), lower := (rows 13 50 37 200 82 160 64 128 256), losses := [] }

theorem u16165 : Upper (D 7) (R 7) [12,48,33,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16166 : Route 9 := (fun mask => (mask,id))

def c16166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16166 : Upper (D 7) (R 7) [12,48,33,192,66,256] 13 := by
  apply FastRouting.sound _ _ [12,48,33,192,66,256] 13 (by decide) (choices 1) [1,2,128] r16166 c16166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3536
  · exact u3537
  · exact u3538

def b16167 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 37 200 273 34 194 194 450), lower := (rows 13 50 37 200 273 34 64 128 256), losses := [] }

theorem u16167 : Upper (D 7) (R 7) [12,48,33,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16168 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 37 200 273 96 194 130 386), lower := (rows 13 50 37 200 273 96 64 128 256), losses := [] }

theorem u16168 : Upper (D 7) (R 7) [12,48,33,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16169 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 50 37 200 274 33 194 194 450), lower := (rows 13 50 37 200 274 33 64 128 256), losses := [] }

theorem u16169 : Upper (D 7) (R 7) [12,48,33,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16170 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 50, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 37 200 274 34 193 193 449), lower := (rows 13 50 37 200 274 34 64 128 256), losses := [] }

theorem u16170 : Upper (D 7) (R 7) [12,48,33,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16171 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 37 200 274 96 195 131 387), lower := (rows 13 50 37 200 274 96 64 128 256), losses := [] }

theorem u16171 : Upper (D 7) (R 7) [12,48,33,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16172 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 50 37 200 336 33 194 130 386), lower := (rows 13 50 37 200 336 33 64 128 256), losses := [] }

theorem u16172 : Upper (D 7) (R 7) [12,48,33,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16173 : Route 9 := (fun mask => (mask,id))

def c16173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16173 : Upper (D 7) (R 7) [12,48,33,192,320,2] 13 := by
  apply FastRouting.sound _ _ [12,48,33,192,320,2] 13 (by decide) (choices 1) [1,2,128] r16173 c16173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3539
  · exact u3540
  · exact u3541

def b16174 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 50 37 200 336 160 67 131 259), lower := (rows 13 50 37 200 336 160 64 128 256), losses := [] }

theorem u16174 : Upper (D 7) (R 7) [12,48,33,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16175 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 37 265 82 34 192 192 448), lower := (rows 13 50 37 265 82 34 64 128 256), losses := [] }

theorem u16175 : Upper (D 7) (R 7) [12,48,33,257,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16176 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 50 37 265 82 96 194 130 386), lower := (rows 13 50 37 265 82 96 64 128 256), losses := [] }

theorem u16176 : Upper (D 7) (R 7) [12,48,33,257,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16177 : Route 9 := (fun mask => (mask,id))

def c16177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16177 : Upper (D 7) (R 7) [12,48,33,257,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,33,257,66,128] 13 (by decide) (choices 1) [2,128] r16177 c16177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3542
  · exact u3543

def b16178 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 37 265 208 34 194 194 450), lower := (rows 13 50 37 265 208 34 64 128 256), losses := [] }

theorem u16178 : Upper (D 7) (R 7) [12,48,33,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16179 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 50 37 265 208 96 194 130 386), lower := (rows 13 50 37 265 208 96 64 128 256), losses := [] }

theorem u16179 : Upper (D 7) (R 7) [12,48,33,257,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16180 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 50 37 266 82 33 192 192 448), lower := (rows 13 50 37 266 82 33 64 128 256), losses := [] }

theorem u16180 : Upper (D 7) (R 7) [12,48,33,258,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16181 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 18, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 37 266 82 96 193 129 385), lower := (rows 13 50 37 266 82 96 64 128 256), losses := [] }

theorem u16181 : Upper (D 7) (R 7) [12,48,33,258,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16182 : Route 9 := (fun mask => (mask,id))

def c16182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16182 : Upper (D 7) (R 7) [12,48,33,258,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,33,258,66,128] 13 (by decide) (choices 1) [1,128] r16182 c16182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3544
  · exact u3545

def b16183 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 50 37 266 208 33 194 194 450), lower := (rows 13 50 37 266 208 33 64 128 256), losses := [] }

theorem u16183 : Upper (D 7) (R 7) [12,48,33,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16184 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 50 37 266 208 34 193 193 449), lower := (rows 13 50 37 266 208 34 64 128 256), losses := [] }

theorem u16184 : Upper (D 7) (R 7) [12,48,33,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16185 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 50 37 266 208 96 195 131 387), lower := (rows 13 50 37 266 208 96 64 128 256), losses := [] }

theorem u16185 : Upper (D 7) (R 7) [12,48,33,258,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16186 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 50 37 328 82 33 194 130 386), lower := (rows 13 50 37 328 82 33 64 128 256), losses := [] }

theorem u16186 : Upper (D 7) (R 7) [12,48,33,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16187 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 37 328 82 34 193 129 385), lower := (rows 13 50 37 328 82 34 64 128 256), losses := [] }

theorem u16187 : Upper (D 7) (R 7) [12,48,33,320,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16188 : Route 9 := (fun mask => (mask,id))

def c16188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16188 : Upper (D 7) (R 7) [12,48,33,320,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,33,320,66,128] 13 (by decide) (choices 1) [1,2,128] r16188 c16188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3546
  · exact u3547
  · exact u3548

def b16189 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 37 328 145 34 194 194 450), lower := (rows 13 50 37 328 145 34 64 128 256), losses := [] }

theorem u16189 : Upper (D 7) (R 7) [12,48,33,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16190 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 37 328 145 96 194 130 386), lower := (rows 13 50 37 328 145 96 64 128 256), losses := [] }

theorem u16190 : Upper (D 7) (R 7) [12,48,33,320,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16191 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 37 328 145 160 66 194 322), lower := (rows 13 50 37 328 145 160 64 128 256), losses := [] }

theorem u16191 : Upper (D 7) (R 7) [12,48,33,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16192 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 50 37 328 146 33 194 194 450), lower := (rows 13 50 37 328 146 33 64 128 256), losses := [] }

theorem u16192 : Upper (D 7) (R 7) [12,48,33,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16193 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 37 328 146 34 193 193 449), lower := (rows 13 50 37 328 146 34 64 128 256), losses := [] }

theorem u16193 : Upper (D 7) (R 7) [12,48,33,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16194 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 37 328 146 96 195 131 387), lower := (rows 13 50 37 328 146 96 64 128 256), losses := [] }

theorem u16194 : Upper (D 7) (R 7) [12,48,33,320,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16195 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 37 328 146 160 67 195 323), lower := (rows 13 50 37 328 146 160 64 128 256), losses := [] }

theorem u16195 : Upper (D 7) (R 7) [12,48,33,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16196 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 50 37 328 208 33 194 130 386), lower := (rows 13 50 37 328 208 33 64 128 256), losses := [] }

theorem u16196 : Upper (D 7) (R 7) [12,48,33,320,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16197 : Route 9 := (fun mask => (mask,id))

def c16197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16197 : Upper (D 7) (R 7) [12,48,33,320,192,2] 13 := by
  apply FastRouting.sound _ _ [12,48,33,320,192,2] 13 (by decide) (choices 1) [1,2,128] r16197 c16197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3549
  · exact u3550
  · exact u3551

def b16198 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 37 328 208 160 67 131 259), lower := (rows 13 50 37 328 208 160 64 128 256), losses := [] }

theorem u16198 : Upper (D 7) (R 7) [12,48,33,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16199 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 461, targets := 2 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 69 137 82 34 480 416 416), lower := (rows 13 50 69 137 82 34 64 128 256), losses := [] }

theorem u16199 : Upper (D 7) (R 7) [12,48,65,129,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16199
end Delivery.IrregularNine14.P07
