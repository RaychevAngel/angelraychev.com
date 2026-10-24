import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0078
import IrregularNine14P06C0079

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17400 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 44 81 288 85 149 277), lower := (rows 11 162 70 44 81 288 64 128 256), losses := [] }

theorem u17400 : Upper (D 6) (R 6) [10,160,66,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17400 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17401 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 70 44 273 33 84 212 340), lower := (rows 11 162 70 44 273 33 64 128 256), losses := [] }

theorem u17401 : Upper (D 6) (R 6) [10,160,66,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17402 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 70 44 273 36 81 209 337), lower := (rows 11 162 70 44 273 36 64 128 256), losses := [] }

theorem u17402 : Upper (D 6) (R 6) [10,160,66,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17403 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 44 273 48 69 197 325), lower := (rows 11 162 70 44 273 48 64 128 256), losses := [] }

theorem u17403 : Upper (D 6) (R 6) [10,160,66,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17403 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17404 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 70 44 273 96 85 149 277), lower := (rows 11 162 70 44 273 96 64 128 256), losses := [] }

theorem u17404 : Upper (D 6) (R 6) [10,160,66,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17405 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 70 44 276 33 81 209 337), lower := (rows 11 162 70 44 276 33 64 128 256), losses := [] }

theorem u17405 : Upper (D 6) (R 6) [10,160,66,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17406 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 70 44 276 48 65 193 321), lower := (rows 11 162 70 44 276 48 64 128 256), losses := [] }

theorem u17406 : Upper (D 6) (R 6) [10,160,66,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17406 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17407 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 70 44 276 96 81 145 273), lower := (rows 11 162 70 44 276 96 64 128 256), losses := [] }

theorem u17407 : Upper (D 6) (R 6) [10,160,66,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17408 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 70 44 336 33 85 149 277), lower := (rows 11 162 70 44 336 33 64 128 256), losses := [] }

theorem u17408 : Upper (D 6) (R 6) [10,160,66,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17409 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 70 44 336 36 81 145 273), lower := (rows 11 162 70 44 336 36 64 128 256), losses := [] }

theorem u17409 : Upper (D 6) (R 6) [10,160,66,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17410 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 44 336 48 69 133 261), lower := (rows 11 162 70 44 336 48 64 128 256), losses := [] }

theorem u17410 : Upper (D 6) (R 6) [10,160,66,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17410 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17411 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 70 56 81 33 324 388 260), lower := (rows 11 162 70 56 81 33 64 128 256), losses := [] }

theorem u17411 : Upper (D 6) (R 6) [10,160,66,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17412 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 70 56 81 36 325 389 261), lower := (rows 11 162 70 56 81 36 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 40 20 32 64 128 256), good := (rows 11 171 83 56 81 56 64 128 256) }] }

theorem u17412 : Upper (D 6) (R 6) [10,160,66,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17413 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 56 81 288 69 133 261), lower := (rows 11 162 70 56 81 288 64 128 256), losses := [] }

theorem u17413 : Upper (D 6) (R 6) [10,160,66,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17413 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17414 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 162 70 56 273 33 68 196 324), lower := (rows 11 162 70 56 273 33 64 128 256), losses := [] }

theorem u17414 : Upper (D 6) (R 6) [10,160,66,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17415 : Route 9 := (fun mask => (mask,id))

def c17415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17415 : Upper (D 6) (R 6) [10,160,66,48,257,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,257,4] 13 (by decide) (choices 1) [1,4] r17415 c17415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4704
  · exact u4705

def r17416 : Route 9 := (fun mask => (mask,id))

def c17416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17416 : Upper (D 6) (R 6) [10,160,66,48,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,257,64] 13 (by decide) (choices 1) [1,4] r17416 c17416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4706
  · exact u4707

def r17417 : Route 9 := (fun mask => (mask,id))

def c17417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17417 : Upper (D 6) (R 6) [10,160,66,48,260,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,260,1] 13 (by decide) (choices 1) [1,4] r17417 c17417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4708
  · exact u4709

def b17418 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 70 56 276 36 65 193 321), lower := (rows 11 162 70 56 276 36 64 128 256), losses := [] }

theorem u17418 : Upper (D 6) (R 6) [10,160,66,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17419 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 70 56 276 96 69 133 261), lower := (rows 11 162 70 56 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 10 162 102 56 316 96 96 128 256) }] }

theorem u17419 : Upper (D 6) (R 6) [10,160,66,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17420 : Route 9 := (fun mask => (mask,id))

def c17420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17420 : Upper (D 6) (R 6) [10,160,66,48,320,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,320,1] 13 (by decide) (choices 1) [1,4] r17420 c17420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4710
  · exact u4711

def r17421 : Route 9 := (fun mask => (mask,id))

def c17421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17421 : Upper (D 6) (R 6) [10,160,66,48,320,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,320,4] 13 (by decide) (choices 1) [1,4] r17421 c17421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4712
  · exact u4713

def b17422 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 70 88 49 33 324 388 260), lower := (rows 11 162 70 88 49 33 64 128 256), losses := [] }

theorem u17422 : Upper (D 6) (R 6) [10,160,66,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17423 : Route 9 := (fun mask => (mask,id))

def c17423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u17423 : Upper (D 6) (R 6) [10,160,66,80,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,33,4] 13 (by decide) (choices 1) [1,4,256] r17423 c17423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4714
  · exact u4715
  · exact u4716

def b17424 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 162 70 88 49 288 69 133 261), lower := (rows 11 162 70 88 49 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 24 16 0 81 145 273), good := (rows 463 130 70 472 477 256 64 128 256) }] }

theorem u17424 : Upper (D 6) (R 6) [10,160,66,80,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17424 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17425 : Route 9 := (fun mask => (mask,id))

def c17425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u17425 : Upper (D 6) (R 6) [10,160,66,80,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,36,1] 13 (by decide) (choices 1) [1,4,256] r17425 c17425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4717
  · exact u4718
  · exact u4719

def b17426 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 162 70 88 52 36 321 385 257), lower := (rows 11 162 70 88 52 36 64 128 256), losses := [] }

theorem u17426 : Upper (D 6) (R 6) [10,160,66,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17427 : Route 9 := (fun mask => (mask,id))

def c17427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17427 : Upper (D 6) (R 6) [10,160,66,80,36,256] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,36,256] 13 (by decide) (choices 1) [1,4] r17427 c17427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4720
  · exact u4721

def r17428 : Route 9 := (fun mask => (mask,id))

def c17428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17428 : Upper (D 6) (R 6) [10,160,66,80,257,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,257,1] 13 (by decide) (choices 1) [4,32] r17428 c17428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4722
  · exact u4723

def r17429 : Route 9 := (fun mask => (mask,id))

def c17429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17429 : Upper (D 6) (R 6) [10,160,66,80,257,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,257,4] 13 (by decide) (choices 1) [1,4,32] r17429 c17429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4724
  · exact u4725
  · exact u4726

def r17430 : Route 9 := (fun mask => (mask,id))

def c17430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17430 : Upper (D 6) (R 6) [10,160,66,80,260,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,260,1] 13 (by decide) (choices 1) [1,4,32] r17430 c17430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4727
  · exact u4728
  · exact u4729

def r17431 : Route 9 := (fun mask => (mask,id))

def c17431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17431 : Upper (D 6) (R 6) [10,160,66,80,260,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,260,4] 13 (by decide) (choices 1) [1,32] r17431 c17431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4730
  · exact u4731

def r17432 : Route 9 := (fun mask => (mask,id))

def c17432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17432 : Upper (D 6) (R 6) [10,160,66,80,288,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,288,1] 13 (by decide) (choices 1) [1,4] r17432 c17432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4732
  · exact u4733

def r17433 : Route 9 := (fun mask => (mask,id))

def c17433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17433 : Upper (D 6) (R 6) [10,160,66,80,288,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,288,4] 13 (by decide) (choices 1) [1,4] r17433 c17433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4734
  · exact u4735

def b17434 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 70 104 273 33 84 148 276), lower := (rows 11 162 70 104 273 33 64 128 256), losses := [] }

theorem u17434 : Upper (D 6) (R 6) [10,160,66,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17435 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 70 104 273 36 85 149 277), lower := (rows 11 162 70 104 273 36 64 128 256), losses := [] }

theorem u17435 : Upper (D 6) (R 6) [10,160,66,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17436 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 104 273 48 69 133 261), lower := (rows 11 162 70 104 273 48 64 128 256), losses := [] }

theorem u17436 : Upper (D 6) (R 6) [10,160,66,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17436 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17437 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 70 104 276 33 85 149 277), lower := (rows 11 162 70 104 276 33 64 128 256), losses := [] }

theorem u17437 : Upper (D 6) (R 6) [10,160,66,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17438 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 70 104 276 36 81 145 273), lower := (rows 11 162 70 104 276 36 64 128 256), losses := [] }

theorem u17438 : Upper (D 6) (R 6) [10,160,66,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17439 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 104 276 48 69 133 261), lower := (rows 11 162 70 104 276 48 64 128 256), losses := [] }

theorem u17439 : Upper (D 6) (R 6) [10,160,66,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17439 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17440 : Route 9 := (fun mask => (mask,id))

def c17440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17440 : Upper (D 6) (R 6) [10,160,66,257,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257,33,4] 13 (by decide) (choices 1) [4,16] r17440 c17440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4736
  · exact u4737

def b17441 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 70 265 49 48 68 196 324), lower := (rows 11 162 70 265 49 48 64 128 256), losses := [] }

theorem u17441 : Upper (D 6) (R 6) [10,160,66,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17441 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17442 : Route 9 := (fun mask => (mask,id))

def c17442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17442 : Upper (D 6) (R 6) [10,160,66,257,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257,33,64] 13 (by decide) (choices 1) [4,16] r17442 c17442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4738
  · exact u4739

def b17443 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 265 52 33 84 212 340), lower := (rows 11 162 70 265 52 33 64 128 256), losses := [] }

theorem u17443 : Upper (D 6) (R 6) [10,160,66,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17444 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 70 265 52 36 81 209 337), lower := (rows 11 162 70 265 52 36 64 128 256), losses := [] }

theorem u17444 : Upper (D 6) (R 6) [10,160,66,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17445 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 70 265 52 48 69 197 325), lower := (rows 11 162 70 265 52 48 64 128 256), losses := [] }

theorem u17445 : Upper (D 6) (R 6) [10,160,66,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17445 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17446 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 70 265 52 96 85 149 277), lower := (rows 11 162 70 265 52 96 64 128 256), losses := [] }

theorem u17446 : Upper (D 6) (R 6) [10,160,66,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17447 : Route 9 := (fun mask => (mask,id))

def c17447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17447 : Upper (D 6) (R 6) [10,160,66,257,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257,65,4] 13 (by decide) (choices 1) [4,16,32] r17447 c17447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4740
  · exact u4741
  · exact u4742

def b17448 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 70 265 81 48 100 164 292), lower := (rows 11 162 70 265 81 48 64 128 256), losses := [] }

theorem u17448 : Upper (D 6) (R 6) [10,160,66,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17448 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17449 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 265 112 33 84 148 276), lower := (rows 11 162 70 265 112 33 64 128 256), losses := [] }

theorem u17449 : Upper (D 6) (R 6) [10,160,66,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17450 : Route 9 := (fun mask => (mask,id))

def c17450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17450 : Upper (D 6) (R 6) [10,160,66,257,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257,96,4] 13 (by decide) (choices 1) [1,4,16] r17450 c17450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4743
  · exact u4744
  · exact u4745

def b17451 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 70 265 112 48 69 133 261), lower := (rows 11 162 70 265 112 48 64 128 256), losses := [] }

theorem u17451 : Upper (D 6) (R 6) [10,160,66,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17451 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17452 : Route 9 := (fun mask => (mask,id))

def c17452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17452 : Upper (D 6) (R 6) [10,160,66,260,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,5,1] 13 (by decide) (choices 1) [16,32] r17452 c17452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4746
  · exact u4747

def b17453 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,1)], upper := (rows 11 162 70 268 21 48 97 225 353), lower := (rows 11 162 70 268 21 48 64 128 256), losses := [] }

theorem u17453 : Upper (D 6) (R 6) [10,160,66,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17453 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17454 : Route 9 := (fun mask => (mask,id))

def c17454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17454 : Upper (D 6) (R 6) [10,160,66,260,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,5,64] 13 (by decide) (choices 1) [1,16,32] r17454 c17454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4748
  · exact u4749
  · exact u4750

def b17455 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 70 268 49 33 84 212 340), lower := (rows 11 162 70 268 49 33 64 128 256), losses := [] }

theorem u17455 : Upper (D 6) (R 6) [10,160,66,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17456 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 11 162 70 268 49 36 81 209 337), lower := (rows 11 162 70 268 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 81 145 273), good := (rows 505 160 100 300 497 36 64 128 256) },{ target := 6, region := (rows 1 2 4 8 17 44 0 128 256), good := (rows 59 162 38 300 49 36 0 128 256) }] }

theorem u17456 : Upper (D 6) (R 6) [10,160,66,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17457 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 70 268 49 48 69 197 325), lower := (rows 11 162 70 268 49 48 64 128 256), losses := [] }

theorem u17457 : Upper (D 6) (R 6) [10,160,66,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17457 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17458 : Route 9 := (fun mask => (mask,id))

def c17458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17458 : Upper (D 6) (R 6) [10,160,66,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,33,64] 13 (by decide) (choices 1) [1,4,16] r17458 c17458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4751
  · exact u4752
  · exact u4753

def r17459 : Route 9 := (fun mask => (mask,id))

def c17459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17459 : Upper (D 6) (R 6) [10,160,66,260,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,36,1] 13 (by decide) (choices 1) [1,16] r17459 c17459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4754
  · exact u4755

#print axioms u17459
end Delivery.IrregularNine14.P06
