import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0059

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16200 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 338, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 137 82 160 354 418 290), lower := (rows 13 50 69 137 82 160 64 128 256), losses := [] }

theorem u16200 : Upper (D 7) (R 7) [12,48,65,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16201 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 13 50 69 137 82 288 226 162 418), lower := (rows 13 50 69 137 82 288 64 128 256), losses := [] }

theorem u16201 : Upper (D 7) (R 7) [12,48,65,129,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16201 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16202 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 69 137 274 34 224 224 480), lower := (rows 13 50 69 137 274 34 64 128 256), losses := [] }

theorem u16202 : Upper (D 7) (R 7) [12,48,65,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16203 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 69 137 274 96 226 162 418), lower := (rows 13 50 69 137 274 96 64 128 256), losses := [] }

theorem u16203 : Upper (D 7) (R 7) [12,48,65,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16204 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 34, targets := 64 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 69 137 336 34 226 162 418), lower := (rows 13 50 69 137 336 34 64 128 256), losses := [] }

theorem u16204 : Upper (D 7) (R 7) [12,48,65,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16205 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 338, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 137 336 160 98 162 290), lower := (rows 13 50 69 137 336 160 64 128 256), losses := [] }

theorem u16205 : Upper (D 7) (R 7) [12,48,65,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16206 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 50, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 50 69 138 82 33 480 416 416), lower := (rows 13 50 69 138 82 33 64 128 256), losses := [] }

theorem u16206 : Upper (D 7) (R 7) [12,48,65,130,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16207 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 357, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 13 50 69 138 82 160 353 417 289), lower := (rows 13 50 69 138 82 160 64 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 20 168 64 128 256), good := (rows 62 50 86 170 82 160 64 160 256) }] }

theorem u16207 : Upper (D 7) (R 7) [12,48,65,130,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16208 : Route 9 := (fun mask => (mask,id))

def c16208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16208 : Upper (D 7) (R 7) [12,48,65,130,66,256] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,66,256] 13 (by decide) (choices 1) [1,32,128] r16208 c16208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3552
  · exact u3553
  · exact u3554

def b16209 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 13 50 69 138 208 33 354 418 290), lower := (rows 13 50 69 138 208 33 64 128 256), losses := [] }

theorem u16209 : Upper (D 7) (R 7) [12,48,65,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16210 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 138 208 34 353 417 289), lower := (rows 13 50 69 138 208 34 64 128 256), losses := [] }

theorem u16210 : Upper (D 7) (R 7) [12,48,65,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16211 : Route 9 := (fun mask => (mask,id))

def c16211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16211 : Upper (D 7) (R 7) [12,48,65,130,192,256] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,192,256] 13 (by decide) (choices 1) [1,2,32] r16211 c16211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3555
  · exact u3556
  · exact u3557

def b16212 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 50 69 138 273 34 224 224 480), lower := (rows 13 50 69 138 273 34 64 128 256), losses := [] }

theorem u16212 : Upper (D 7) (R 7) [12,48,65,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16213 : Route 9 := (fun mask => (mask,id))

def c16213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16213 : Upper (D 7) (R 7) [12,48,65,130,257,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,257,64] 13 (by decide) (choices 1) [2,32,128] r16213 c16213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3558
  · exact u3559
  · exact u3560

def b16214 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 13 50 69 138 273 160 98 226 354), lower := (rows 13 50 69 138 273 160 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 24 32 66 0 258), good := (rows 29 370 69 351 273 32 64 0 256) }] }

theorem u16214 : Upper (D 7) (R 7) [12,48,65,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16215 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 69 138 274 33 224 224 480), lower := (rows 13 50 69 138 274 33 64 128 256), losses := [] }

theorem u16215 : Upper (D 7) (R 7) [12,48,65,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16216 : Route 9 := (fun mask => (mask,id))

def c16216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16216 : Upper (D 7) (R 7) [12,48,65,130,258,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,258,64] 13 (by decide) (choices 1) [1,32,128] r16216 c16216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3561
  · exact u3562
  · exact u3563

def r16217 : Route 9 := (fun mask => (mask,id))

def c16217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16217 : Upper (D 7) (R 7) [12,48,65,130,258,128] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,258,128] 13 (by decide) (choices 1) [1,32] r16217 c16217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3564
  · exact u3565

def b16218 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 136, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,0)], upper := (rows 13 50 69 138 336 33 226 162 418), lower := (rows 13 50 69 138 336 33 64 128 256), losses := [] }

theorem u16218 : Upper (D 7) (R 7) [12,48,65,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16219 : Route 9 := (fun mask => (mask,id))

def c16219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16219 : Upper (D 7) (R 7) [12,48,65,130,320,2] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,320,2] 13 (by decide) (choices 1) [1,32,128] r16219 c16219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3566
  · exact u3567
  · exact u3568

def r16220 : Route 9 := (fun mask => (mask,id))

def c16220 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16220 : Upper (D 7) (R 7) [12,48,65,130,320,128] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,320,128] 13 (by decide) (choices 1) [1,2,32] r16220 c16220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3569
  · exact u3570
  · exact u3571

def b16221 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 13 50 69 138 400 33 98 226 354), lower := (rows 13 50 69 138 400 33 64 128 256), losses := [] }

theorem u16221 : Upper (D 7) (R 7) [12,48,65,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16222 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 138 400 34 97 225 353), lower := (rows 13 50 69 138 400 34 64 128 256), losses := [] }

theorem u16222 : Upper (D 7) (R 7) [12,48,65,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16223 : Route 9 := (fun mask => (mask,id))

def c16223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16223 : Upper (D 7) (R 7) [12,48,65,130,384,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,384,64] 13 (by decide) (choices 1) [1,2,32] r16223 c16223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3572
  · exact u3573
  · exact u3574

def b16224 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 69 168 19 34 448 448 448), lower := (rows 13 50 69 168 19 34 64 128 256), losses := [] }

theorem u16224 : Upper (D 7) (R 7) [12,48,65,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16225 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 50, targets := 128 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 50 69 168 19 96 450 386 386), lower := (rows 13 50 69 168 19 96 64 128 256), losses := [] }

theorem u16225 : Upper (D 7) (R 7) [12,48,65,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16226 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 69 168 19 160 322 450 322), lower := (rows 13 50 69 168 19 160 64 128 256), losses := [] }

theorem u16226 : Upper (D 7) (R 7) [12,48,65,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16227 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 13 50 69 168 19 288 194 194 450), lower := (rows 13 50 69 168 19 288 64 128 256), losses := [] }

theorem u16227 : Upper (D 7) (R 7) [12,48,65,160,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16227 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16228 : PairBound 9 := { available := 386, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 50, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 50 69 168 82 33 450 386 386), lower := (rows 13 50 69 168 82 33 64 128 256), losses := [] }

theorem u16228 : Upper (D 7) (R 7) [12,48,65,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16229 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 168 82 34 449 385 385), lower := (rows 13 50 69 168 82 34 64 128 256), losses := [] }

theorem u16229 : Upper (D 7) (R 7) [12,48,65,160,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16230 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 69 168 82 160 323 387 259), lower := (rows 13 50 69 168 82 160 64 128 256), losses := [] }

theorem u16230 : Upper (D 7) (R 7) [12,48,65,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16231 : Route 9 := (fun mask => (mask,id))

def c16231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16231 : Upper (D 7) (R 7) [12,48,65,160,66,256] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,66,256] 13 (by decide) (choices 1) [1,2,128] r16231 c16231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3575
  · exact u3576
  · exact u3577

def b16232 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 69 168 208 33 322 386 258), lower := (rows 13 50 69 168 208 33 64 128 256), losses := [] }

theorem u16232 : Upper (D 7) (R 7) [12,48,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16233 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 168 208 34 323 387 259), lower := (rows 13 50 69 168 208 34 64 128 256), losses := [] }

theorem u16233 : Upper (D 7) (R 7) [12,48,65,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16234 : Route 9 := (fun mask => (mask,id))

def c16234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16234 : Upper (D 7) (R 7) [12,48,65,160,192,256] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,192,256] 13 (by decide) (choices 1) [1,2] r16234 c16234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3578
  · exact u3579

def b16235 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 50 69 168 273 34 194 194 450), lower := (rows 13 50 69 168 273 34 64 128 256), losses := [] }

theorem u16235 : Upper (D 7) (R 7) [12,48,65,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16236 : Route 9 := (fun mask => (mask,id))

def c16236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16236 : Upper (D 7) (R 7) [12,48,65,160,257,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,257,64] 13 (by decide) (choices 1) [2,128] r16236 c16236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3580
  · exact u3581

def b16237 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 69 168 273 160 66 194 322), lower := (rows 13 50 69 168 273 160 64 128 256), losses := [] }

theorem u16237 : Upper (D 7) (R 7) [12,48,65,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16238 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 50 69 168 274 33 194 194 450), lower := (rows 13 50 69 168 274 33 64 128 256), losses := [] }

theorem u16238 : Upper (D 7) (R 7) [12,48,65,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16239 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 50, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 69 168 274 34 193 193 449), lower := (rows 13 50 69 168 274 34 64 128 256), losses := [] }

theorem u16239 : Upper (D 7) (R 7) [12,48,65,160,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16240 : Route 9 := (fun mask => (mask,id))

def c16240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16240 : Upper (D 7) (R 7) [12,48,65,160,258,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,258,64] 13 (by decide) (choices 1) [1,2,128] r16240 c16240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3582
  · exact u3583
  · exact u3584

def b16241 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 69 168 274 160 67 195 323), lower := (rows 13 50 69 168 274 160 64 128 256), losses := [] }

theorem u16241 : Upper (D 7) (R 7) [12,48,65,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16242 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 50 69 168 336 33 194 130 386), lower := (rows 13 50 69 168 336 33 64 128 256), losses := [] }

theorem u16242 : Upper (D 7) (R 7) [12,48,65,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16243 : Route 9 := (fun mask => (mask,id))

def c16243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16243 : Upper (D 7) (R 7) [12,48,65,160,320,2] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,320,2] 13 (by decide) (choices 1) [1,2,128] r16243 c16243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3585
  · exact u3586
  · exact u3587

def b16244 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 69 168 336 160 67 131 259), lower := (rows 13 50 69 168 336 160 64 128 256), losses := [] }

theorem u16244 : Upper (D 7) (R 7) [12,48,65,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16245 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 50 69 168 400 33 66 194 322), lower := (rows 13 50 69 168 400 33 64 128 256), losses := [] }

theorem u16245 : Upper (D 7) (R 7) [12,48,65,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16246 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 168 400 34 67 195 323), lower := (rows 13 50 69 168 400 34 64 128 256), losses := [] }

theorem u16246 : Upper (D 7) (R 7) [12,48,65,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16247 : Route 9 := (fun mask => (mask,id))

def c16247 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16247 : Upper (D 7) (R 7) [12,48,65,160,384,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,384,64] 13 (by decide) (choices 1) [1,2] r16247 c16247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3588
  · exact u3589

def b16248 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 461, targets := 2 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 69 265 82 34 224 160 416), lower := (rows 13 50 69 265 82 34 64 128 256), losses := [] }

theorem u16248 : Upper (D 7) (R 7) [12,48,65,257,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16249 : Route 9 := (fun mask => (mask,id))

def c16249 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16249 : Upper (D 7) (R 7) [12,48,65,257,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,65,257,66,128] 13 (by decide) (choices 1) [2,32,128] r16249 c16249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3590
  · exact u3591
  · exact u3592

def b16250 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 461, targets := 2 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 69 265 146 34 224 224 480), lower := (rows 13 50 69 265 146 34 64 128 256), losses := [] }

theorem u16250 : Upper (D 7) (R 7) [12,48,65,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16251 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 5, region := 146, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 69 265 146 96 226 162 418), lower := (rows 13 50 69 265 146 96 64 128 256), losses := [] }

theorem u16251 : Upper (D 7) (R 7) [12,48,65,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16252 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 69 265 146 160 98 226 354), lower := (rows 13 50 69 265 146 160 64 128 256), losses := [] }

theorem u16252 : Upper (D 7) (R 7) [12,48,65,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16253 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 4, region := 34, targets := 64 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 69 265 208 34 226 162 418), lower := (rows 13 50 69 265 208 34 64 128 256), losses := [] }

theorem u16253 : Upper (D 7) (R 7) [12,48,65,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16254 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 69 265 208 160 98 162 290), lower := (rows 13 50 69 265 208 160 64 128 256), losses := [] }

theorem u16254 : Upper (D 7) (R 7) [12,48,65,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16255 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 50, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 50 69 266 82 33 224 160 416), lower := (rows 13 50 69 266 82 33 64 128 256), losses := [] }

theorem u16255 : Upper (D 7) (R 7) [12,48,65,258,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16256 : Route 9 := (fun mask => (mask,id))

def c16256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16256 : Upper (D 7) (R 7) [12,48,65,258,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258,66,128] 13 (by decide) (choices 1) [1,32,128] r16256 c16256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3593
  · exact u3594
  · exact u3595

def b16257 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 50 69 266 145 34 224 224 480), lower := (rows 13 50 69 266 145 34 64 128 256), losses := [] }

theorem u16257 : Upper (D 7) (R 7) [12,48,65,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16258 : Route 9 := (fun mask => (mask,id))

def c16258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16258 : Upper (D 7) (R 7) [12,48,65,258,129,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258,129,64] 13 (by decide) (choices 1) [2,32,128] r16258 c16258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3596
  · exact u3597
  · exact u3598

def b16259 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 69 266 145 160 98 226 354), lower := (rows 13 50 69 266 145 160 64 128 256), losses := [] }

theorem u16259 : Upper (D 7) (R 7) [12,48,65,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16259
end Delivery.IrregularNine14.P07
