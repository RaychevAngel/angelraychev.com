import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0061
import IrregularNine14P07C0062

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16380 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 34, targets := 65 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(2,7)], upper := (rows 13 50 70 392 145 34 97 225 353), lower := (rows 13 50 70 392 145 34 64 128 256), losses := [] }

theorem u16380 : Upper (D 7) (R 7) [12,48,66,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16381 : Route 9 := (fun mask => (mask,id))

def c16381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16381 : Upper (D 7) (R 7) [12,48,66,384,129,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,129,64] 13 (by decide) (choices 1) [1,2,32] r16381 c16381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3696
  · exact u3697
  · exact u3698

def r16382 : Route 9 := (fun mask => (mask,id))

def c16382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16382 : Upper (D 7) (R 7) [12,48,66,384,130,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,130,1] 13 (by decide) (choices 1) [1,32] r16382 c16382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3699
  · exact u3700

def r16383 : Route 9 := (fun mask => (mask,id))

def c16383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16383 : Upper (D 7) (R 7) [12,48,66,384,130,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,130,64] 13 (by decide) (choices 1) [1,32] r16383 c16383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3701
  · exact u3702

def r16384 : Route 9 := (fun mask => (mask,id))

def c16384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16384 : Upper (D 7) (R 7) [12,48,66,384,192,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,192,1] 13 (by decide) (choices 1) [1,2,32] r16384 c16384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3703
  · exact u3704
  · exact u3705

def b16385 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 392 208 34 97 161 289), lower := (rows 13 50 70 392 208 34 64 128 256), losses := [] }

theorem u16385 : Upper (D 7) (R 7) [12,48,66,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16386 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 100 200 19 33 450 386 386), lower := (rows 13 50 100 200 19 33 64 128 256), losses := [] }

theorem u16386 : Upper (D 7) (R 7) [12,48,96,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16387 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 393, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 100 200 19 34 449 385 385), lower := (rows 13 50 100 200 19 34 64 128 256), losses := [] }

theorem u16387 : Upper (D 7) (R 7) [12,48,96,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16388 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 3, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 13 50 100 200 19 160 323 387 259), lower := (rows 13 50 100 200 19 160 64 128 256), losses := [] }

theorem u16388 : Upper (D 7) (R 7) [12,48,96,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16389 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 200, targets := 32 }], pairs := [(1,6),(3,5),(4,6)], upper := (rows 13 50 100 200 19 288 195 131 387), lower := (rows 13 50 100 200 19 288 64 128 256), losses := [] }

theorem u16389 : Upper (D 7) (R 7) [12,48,96,192,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16389 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16390 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 100 200 146 33 323 387 259), lower := (rows 13 50 100 200 146 33 64 128 256), losses := [] }

theorem u16390 : Upper (D 7) (R 7) [12,48,96,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16391 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 393, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 100 200 146 34 321 385 257), lower := (rows 13 50 100 200 146 34 64 128 256), losses := [] }

theorem u16391 : Upper (D 7) (R 7) [12,48,96,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16392 : Route 9 := (fun mask => (mask,id))

def c16392 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16392 : Upper (D 7) (R 7) [12,48,96,192,130,256] 13 := by
  apply FastRouting.sound _ _ [12,48,96,192,130,256] 13 (by decide) (choices 1) [1,2] r16392 c16392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3706
  · exact u3707

def b16393 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 100 200 273 33 194 130 386), lower := (rows 13 50 100 200 273 33 64 128 256), losses := [] }

theorem u16393 : Upper (D 7) (R 7) [12,48,96,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16394 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 50 100 200 273 34 195 131 387), lower := (rows 13 50 100 200 273 34 64 128 256), losses := [] }

theorem u16394 : Upper (D 7) (R 7) [12,48,96,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16395 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 3, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 13 50 100 200 273 160 67 131 259), lower := (rows 13 50 100 200 273 160 64 128 256), losses := [] }

theorem u16395 : Upper (D 7) (R 7) [12,48,96,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16396 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 100 200 274 33 195 131 387), lower := (rows 13 50 100 200 274 33 64 128 256), losses := [] }

theorem u16396 : Upper (D 7) (R 7) [12,48,96,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16397 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 50, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 100 200 274 34 193 129 385), lower := (rows 13 50 100 200 274 34 64 128 256), losses := [] }

theorem u16397 : Upper (D 7) (R 7) [12,48,96,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16398 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 3, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 13 50 100 200 274 160 67 131 259), lower := (rows 13 50 100 200 274 160 64 128 256), losses := [] }

theorem u16398 : Upper (D 7) (R 7) [12,48,96,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16399 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 100 200 400 33 67 131 259), lower := (rows 13 50 100 200 400 33 64 128 256), losses := [] }

theorem u16399 : Upper (D 7) (R 7) [12,48,96,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16400 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 50 100 200 400 34 67 131 259), lower := (rows 13 50 100 200 400 34 64 128 256), losses := [] }

theorem u16400 : Upper (D 7) (R 7) [12,48,96,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16401 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 100 265 19 34 192 192 448), lower := (rows 13 50 100 265 19 34 64 128 256), losses := [] }

theorem u16401 : Upper (D 7) (R 7) [12,48,96,257,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16402 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 265 19 96 194 130 386), lower := (rows 13 50 100 265 19 96 64 128 256), losses := [] }

theorem u16402 : Upper (D 7) (R 7) [12,48,96,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16403 : Route 9 := (fun mask => (mask,id))

def c16403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16403 : Upper (D 7) (R 7) [12,48,96,257,3,128] 13 := by
  apply FastRouting.sound _ _ [12,48,96,257,3,128] 13 (by decide) (choices 1) [2,128] r16403 c16403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3708
  · exact u3709

def b16404 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 13 50 100 265 145 34 194 194 450), lower := (rows 13 50 100 265 145 34 64 128 256), losses := [] }

theorem u16404 : Upper (D 7) (R 7) [12,48,96,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16405 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 265 145 96 194 130 386), lower := (rows 13 50 100 265 145 96 64 128 256), losses := [] }

theorem u16405 : Upper (D 7) (R 7) [12,48,96,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16406 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 100 265 145 160 66 194 322), lower := (rows 13 50 100 265 145 160 64 128 256), losses := [] }

theorem u16406 : Upper (D 7) (R 7) [12,48,96,257,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16407 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 50 100 265 146 33 194 194 450), lower := (rows 13 50 100 265 146 33 64 128 256), losses := [] }

theorem u16407 : Upper (D 7) (R 7) [12,48,96,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16408 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 393, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 100 265 146 34 193 193 449), lower := (rows 13 50 100 265 146 34 64 128 256), losses := [] }

theorem u16408 : Upper (D 7) (R 7) [12,48,96,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16409 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 265 146 96 195 131 387), lower := (rows 13 50 100 265 146 96 64 128 256), losses := [] }

theorem u16409 : Upper (D 7) (R 7) [12,48,96,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16410 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 100 265 146 160 67 195 323), lower := (rows 13 50 100 265 146 160 64 128 256), losses := [] }

theorem u16410 : Upper (D 7) (R 7) [12,48,96,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16411 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 50 100 265 208 33 194 130 386), lower := (rows 13 50 100 265 208 33 64 128 256), losses := [] }

theorem u16411 : Upper (D 7) (R 7) [12,48,96,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16412 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 100 265 208 34 195 131 387), lower := (rows 13 50 100 265 208 34 64 128 256), losses := [] }

theorem u16412 : Upper (D 7) (R 7) [12,48,96,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16413 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 100 265 208 160 67 131 259), lower := (rows 13 50 100 265 208 160 64 128 256), losses := [] }

theorem u16413 : Upper (D 7) (R 7) [12,48,96,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16414 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 100 266 19 33 192 192 448), lower := (rows 13 50 100 266 19 33 64 128 256), losses := [] }

theorem u16414 : Upper (D 7) (R 7) [12,48,96,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16415 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 266 19 96 193 129 385), lower := (rows 13 50 100 266 19 96 64 128 256), losses := [] }

theorem u16415 : Upper (D 7) (R 7) [12,48,96,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16416 : Route 9 := (fun mask => (mask,id))

def c16416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16416 : Upper (D 7) (R 7) [12,48,96,258,3,128] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258,3,128] 13 (by decide) (choices 1) [1,128] r16416 c16416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3710
  · exact u3711

def b16417 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 100 266 81 33 194 130 386), lower := (rows 13 50 100 266 81 33 64 128 256), losses := [] }

theorem u16417 : Upper (D 7) (R 7) [12,48,96,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16418 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 100 266 81 34 193 129 385), lower := (rows 13 50 100 266 81 34 64 128 256), losses := [] }

theorem u16418 : Upper (D 7) (R 7) [12,48,96,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16419 : Route 9 := (fun mask => (mask,id))

def c16419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16419 : Upper (D 7) (R 7) [12,48,96,258,65,128] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258,65,128] 13 (by decide) (choices 1) [1,2,128] r16419 c16419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3712
  · exact u3713
  · exact u3714

def b16420 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(3,0)], upper := (rows 13 50 100 266 145 33 194 194 450), lower := (rows 13 50 100 266 145 33 64 128 256), losses := [] }

theorem u16420 : Upper (D 7) (R 7) [12,48,96,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16421 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 50 100 266 145 34 193 193 449), lower := (rows 13 50 100 266 145 34 64 128 256), losses := [] }

theorem u16421 : Upper (D 7) (R 7) [12,48,96,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16422 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 266 145 96 195 131 387), lower := (rows 13 50 100 266 145 96 64 128 256), losses := [] }

theorem u16422 : Upper (D 7) (R 7) [12,48,96,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16423 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 100 266 145 160 67 195 323), lower := (rows 13 50 100 266 145 160 64 128 256), losses := [] }

theorem u16423 : Upper (D 7) (R 7) [12,48,96,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16424 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(2,1),(3,5),(4,5)], upper := (rows 13 50 100 266 146 33 193 193 449), lower := (rows 13 50 100 266 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 97 161 289), good := (rows 461 474 452 282 154 449 64 128 256) }] }

theorem u16424 : Upper (D 7) (R 7) [12,48,96,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16425 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 50 100 266 146 96 193 129 385), lower := (rows 13 50 100 266 146 96 64 128 256), losses := [] }

theorem u16425 : Upper (D 7) (R 7) [12,48,96,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16426 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 100 266 146 160 65 193 321), lower := (rows 13 50 100 266 146 160 64 128 256), losses := [] }

theorem u16426 : Upper (D 7) (R 7) [12,48,96,258,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16427 : Route 9 := (fun mask => (mask,id))

def c16427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16427 : Upper (D 7) (R 7) [12,48,96,258,192,1] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258,192,1] 13 (by decide) (choices 1) [1,2,128] r16427 c16427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3715
  · exact u3716
  · exact u3717

def b16428 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 100 266 208 34 193 129 385), lower := (rows 13 50 100 266 208 34 64 128 256), losses := [] }

theorem u16428 : Upper (D 7) (R 7) [12,48,96,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16429 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 100 266 208 160 67 131 259), lower := (rows 13 50 100 266 208 160 64 128 256), losses := [] }

theorem u16429 : Upper (D 7) (R 7) [12,48,96,258,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16430 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 100 328 19 33 194 130 386), lower := (rows 13 50 100 328 19 33 64 128 256), losses := [] }

theorem u16430 : Upper (D 7) (R 7) [12,48,96,320,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16431 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 393, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 100 328 19 34 193 129 385), lower := (rows 13 50 100 328 19 34 64 128 256), losses := [] }

theorem u16431 : Upper (D 7) (R 7) [12,48,96,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16432 : Route 9 := (fun mask => (mask,id))

def c16432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16432 : Upper (D 7) (R 7) [12,48,96,320,3,128] 13 := by
  apply FastRouting.sound _ _ [12,48,96,320,3,128] 13 (by decide) (choices 1) [1,2,128] r16432 c16432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3718
  · exact u3719
  · exact u3720

def b16433 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 100 328 145 33 194 130 386), lower := (rows 13 50 100 328 145 33 64 128 256), losses := [] }

theorem u16433 : Upper (D 7) (R 7) [12,48,96,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16434 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 50 100 328 145 34 195 131 387), lower := (rows 13 50 100 328 145 34 64 128 256), losses := [] }

theorem u16434 : Upper (D 7) (R 7) [12,48,96,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16435 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 13 50 100 328 145 160 67 131 259), lower := (rows 13 50 100 328 145 160 64 128 256), losses := [] }

theorem u16435 : Upper (D 7) (R 7) [12,48,96,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16436 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 100 328 146 33 195 131 387), lower := (rows 13 50 100 328 146 33 64 128 256), losses := [] }

theorem u16436 : Upper (D 7) (R 7) [12,48,96,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16437 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 393, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 100 328 146 34 193 129 385), lower := (rows 13 50 100 328 146 34 64 128 256), losses := [] }

theorem u16437 : Upper (D 7) (R 7) [12,48,96,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16438 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 100 328 146 160 67 131 259), lower := (rows 13 50 100 328 146 160 64 128 256), losses := [] }

theorem u16438 : Upper (D 7) (R 7) [12,48,96,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16439 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 100 392 19 33 194 194 450), lower := (rows 13 50 100 392 19 33 64 128 256), losses := [] }

theorem u16439 : Upper (D 7) (R 7) [12,48,96,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16439
end Delivery.IrregularNine14.P07
