import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0307
import IrregularNine14P06C0308

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34800 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 134 42 81 356 324 452 324), lower := (rows 25 35 134 42 81 32 64 128 256), losses := [] }

theorem u34800 : Upper (D 6) (R 6) [24,33,130,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34801 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 134 42 84 357 325 453 325), lower := (rows 25 35 134 42 84 32 64 128 256), losses := [] }

theorem u34801 : Upper (D 6) (R 6) [24,33,130,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34802 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 134 42 273 100 68 196 324), lower := (rows 25 35 134 42 273 32 64 128 256), losses := [] }

theorem u34802 : Upper (D 6) (R 6) [24,33,130,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34803 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 134 42 276 101 69 197 325), lower := (rows 25 35 134 42 276 32 64 128 256), losses := [] }

theorem u34803 : Upper (D 6) (R 6) [24,33,130,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34804 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 134 42 336 101 69 197 325), lower := (rows 25 35 134 42 336 32 64 128 256), losses := [] }

theorem u34804 : Upper (D 6) (R 6) [24,33,130,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34805 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 134 44 81 358 326 454 326), lower := (rows 25 35 134 44 81 32 64 128 256), losses := [] }

theorem u34805 : Upper (D 6) (R 6) [24,33,130,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34806 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 468, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 134 44 82 357 325 453 325), lower := (rows 25 35 134 44 82 32 64 128 256), losses := [{ target := 5, region := (rows 9 2 22 8 22 0 75 139 267), good := (rows 477 471 470 477 470 0 64 128 256) }] }

theorem u34806 : Upper (D 6) (R 6) [24,33,130,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34807 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 134 44 84 355 323 451 323), lower := (rows 25 35 134 44 84 32 64 128 256), losses := [] }

theorem u34807 : Upper (D 6) (R 6) [24,33,130,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34808 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 134 44 273 102 70 198 326), lower := (rows 25 35 134 44 273 32 64 128 256), losses := [] }

theorem u34808 : Upper (D 6) (R 6) [24,33,130,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34809 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 468, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 134 44 274 101 69 197 325), lower := (rows 25 35 134 44 274 32 64 128 256), losses := [{ target := 5, region := (rows 9 2 22 8 22 0 75 139 267), good := (rows 477 471 470 477 470 0 64 128 256) }] }

theorem u34809 : Upper (D 6) (R 6) [24,33,130,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34810 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 134 44 276 99 67 195 323), lower := (rows 25 35 134 44 276 32 64 128 256), losses := [] }

theorem u34810 : Upper (D 6) (R 6) [24,33,130,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34811 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 468, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 134 44 336 103 71 199 327), lower := (rows 25 35 134 44 336 32 64 128 256), losses := [{ target := 5, region := (rows 9 2 6 8 22 0 66 130 258), good := (rows 25 471 470 29 336 0 64 128 256) }] }

theorem u34811 : Upper (D 6) (R 6) [24,33,130,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34812 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 35 134 73 82 292 356 420 292), lower := (rows 25 35 134 73 82 32 64 128 256), losses := [] }

theorem u34812 : Upper (D 6) (R 6) [24,33,130,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34813 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 35 134 73 84 294 358 422 294), lower := (rows 25 35 134 73 84 32 64 128 256), losses := [] }

theorem u34813 : Upper (D 6) (R 6) [24,33,130,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34814 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 134 73 112 294 326 390 262), lower := (rows 25 35 134 73 112 32 64 128 256), losses := [] }

theorem u34814 : Upper (D 6) (R 6) [24,33,130,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34815 : Route 9 := (fun mask => (mask,id))

def c34815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34815 : Upper (D 6) (R 6) [24,33,130,65,258] 13 := by
  apply FastRouting.sound _ _ [24,33,130,65,258] 13 (by decide) (choices 1) [4,64] r34815 c34815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18446
  · exact u18447

def r34816 : Route 9 := (fun mask => (mask,id))

def c34816 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34816 : Upper (D 6) (R 6) [24,33,130,65,260] 13 := by
  apply FastRouting.sound _ _ [24,33,130,65,260] 13 (by decide) (choices 1) [2,4,64] r34816 c34816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18448
  · exact u18449
  · exact u18450

def b34817 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 134 73 304 102 70 198 326), lower := (rows 25 35 134 73 304 32 64 128 256), losses := [] }

theorem u34817 : Upper (D 6) (R 6) [24,33,130,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34818 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 35 134 73 336 38 102 166 294), lower := (rows 25 35 134 73 336 32 64 128 256), losses := [] }

theorem u34818 : Upper (D 6) (R 6) [24,33,130,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34819 : Route 9 := (fun mask => (mask,id))

def c34819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34819 : Upper (D 6) (R 6) [24,33,130,66,68] 13 := by
  apply FastRouting.sound _ _ [24,33,130,66,68] 13 (by decide) (choices 1) [1,4,256] r34819 c34819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18451
  · exact u18452
  · exact u18453

def b34820 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 134 74 112 293 325 389 261), lower := (rows 25 35 134 74 112 32 64 128 256), losses := [] }

theorem u34820 : Upper (D 6) (R 6) [24,33,130,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34821 : Route 9 := (fun mask => (mask,id))

def c34821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34821 : Upper (D 6) (R 6) [24,33,130,66,257] 13 := by
  apply FastRouting.sound _ _ [24,33,130,66,257] 13 (by decide) (choices 1) [4,64] r34821 c34821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18454
  · exact u18455

def r34822 : Route 9 := (fun mask => (mask,id))

def c34822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34822 : Upper (D 6) (R 6) [24,33,130,66,260] 13 := by
  apply FastRouting.sound _ _ [24,33,130,66,260] 13 (by decide) (choices 1) [1,4,64] r34822 c34822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18456
  · exact u18457
  · exact u18458

def r34823 : Route 9 := (fun mask => (mask,id))

def c34823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34823 : Upper (D 6) (R 6) [24,33,130,66,288] 13 := by
  apply FastRouting.sound _ _ [24,33,130,66,288] 13 (by decide) (choices 1) [1,4,64] r34823 c34823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18459
  · exact u18460
  · exact u18461

def r34824 : Route 9 := (fun mask => (mask,id))

def c34824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34824 : Upper (D 6) (R 6) [24,33,130,66,320] 13 := by
  apply FastRouting.sound _ _ [24,33,130,66,320] 13 (by decide) (choices 1) [1,4] r34824 c34824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18462
  · exact u18463

def b34825 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 17, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 134 76 84 291 355 419 291), lower := (rows 25 35 134 76 84 32 64 128 256), losses := [] }

theorem u34825 : Upper (D 6) (R 6) [24,33,130,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34826 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 1, region := 388, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 25 35 134 76 112 295 327 391 263), lower := (rows 25 35 134 76 112 32 64 128 256), losses := [] }

theorem u34826 : Upper (D 6) (R 6) [24,33,130,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34827 : Route 9 := (fun mask => (mask,id))

def c34827 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34827 : Upper (D 6) (R 6) [24,33,130,68,257] 13 := by
  apply FastRouting.sound _ _ [24,33,130,68,257] 13 (by decide) (choices 1) [2,4,64] r34827 c34827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18464
  · exact u18465
  · exact u18466

def r34828 : Route 9 := (fun mask => (mask,id))

def c34828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34828 : Upper (D 6) (R 6) [24,33,130,68,258] 13 := by
  apply FastRouting.sound _ _ [24,33,130,68,258] 13 (by decide) (choices 1) [1,4,64] r34828 c34828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18467
  · exact u18468
  · exact u18469

def r34829 : Route 9 := (fun mask => (mask,id))

def c34829 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34829 : Upper (D 6) (R 6) [24,33,130,68,260] 13 := by
  apply FastRouting.sound _ _ [24,33,130,68,260] 13 (by decide) (choices 1) [1,2,64] r34829 c34829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18470
  · exact u18471
  · exact u18472

def r34830 : Route 9 := (fun mask => (mask,id))

def c34830 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34830 : Upper (D 6) (R 6) [24,33,130,68,288] 13 := by
  apply FastRouting.sound _ _ [24,33,130,68,288] 13 (by decide) (choices 1) [1,2,4,64] r34830 c34830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18473
  · exact u18474
  · exact u18475
  · exact u18476

def r34831 : Route 9 := (fun mask => (mask,id))

def c34831 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34831 : Upper (D 6) (R 6) [24,33,130,68,320] 13 := by
  apply FastRouting.sound _ _ [24,33,130,68,320] 13 (by decide) (choices 1) [1,2,4] r34831 c34831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18477
  · exact u18478
  · exact u18479

def b34832 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 134 104 273 102 70 198 326), lower := (rows 25 35 134 104 273 32 64 128 256), losses := [] }

theorem u34832 : Upper (D 6) (R 6) [24,33,130,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34833 : Route 9 := (fun mask => (mask,id))

def c34833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34833 : Upper (D 6) (R 6) [24,33,130,96,258] 13 := by
  apply FastRouting.sound _ _ [24,33,130,96,258] 13 (by decide) (choices 1) [1,4,64] r34833 c34833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18480
  · exact u18481
  · exact u18482

def r34834 : Route 9 := (fun mask => (mask,id))

def c34834 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34834 : Upper (D 6) (R 6) [24,33,130,96,260] 13 := by
  apply FastRouting.sound _ _ [24,33,130,96,260] 13 (by decide) (choices 1) [1,2,4,64] r34834 c34834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18483
  · exact u18484
  · exact u18485
  · exact u18486

def b34835 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 1, region := 132, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 25 35 134 104 336 39 71 135 263), lower := (rows 25 35 134 104 336 32 64 128 256), losses := [] }

theorem u34835 : Upper (D 6) (R 6) [24,33,130,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34836 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 164 11 22 356 324 452 324), lower := (rows 25 35 164 11 22 32 64 128 256), losses := [] }

theorem u34836 : Upper (D 6) (R 6) [24,33,160,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34837 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 164 11 82 356 324 452 324), lower := (rows 25 35 164 11 82 32 64 128 256), losses := [] }

theorem u34837 : Upper (D 6) (R 6) [24,33,160,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34838 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 164 11 84 358 326 454 326), lower := (rows 25 35 164 11 84 32 64 128 256), losses := [] }

theorem u34838 : Upper (D 6) (R 6) [24,33,160,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34839 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 164 11 274 100 68 196 324), lower := (rows 25 35 164 11 274 32 64 128 256), losses := [] }

theorem u34839 : Upper (D 6) (R 6) [24,33,160,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34840 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 164 11 276 102 70 198 326), lower := (rows 25 35 164 11 276 32 64 128 256), losses := [] }

theorem u34840 : Upper (D 6) (R 6) [24,33,160,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34841 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 164 11 336 102 70 198 326), lower := (rows 25 35 164 11 336 32 64 128 256), losses := [] }

theorem u34841 : Upper (D 6) (R 6) [24,33,160,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34842 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 164 13 22 354 322 450 322), lower := (rows 25 35 164 13 22 32 64 128 256), losses := [] }

theorem u34842 : Upper (D 6) (R 6) [24,33,160,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34843 : Route 9 := (fun mask => (mask,id))

def c34843 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34843 : Upper (D 6) (R 6) [24,33,160,5,66] 13 := by
  apply FastRouting.sound _ _ [24,33,160,5,66] 13 (by decide) (choices 1) [2,4,64,256] r34843 c34843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18487
  · exact u18488
  · exact u18489
  · exact u18490

def b34844 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 164 13 84 354 322 450 322), lower := (rows 25 35 164 13 84 32 64 128 256), losses := [] }

theorem u34844 : Upper (D 6) (R 6) [24,33,160,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34845 : Route 9 := (fun mask => (mask,id))

def c34845 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34845 : Upper (D 6) (R 6) [24,33,160,5,258] 13 := by
  apply FastRouting.sound _ _ [24,33,160,5,258] 13 (by decide) (choices 1) [2,4,64] r34845 c34845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18491
  · exact u18492
  · exact u18493

def b34846 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 164 13 276 98 66 194 322), lower := (rows 25 35 164 13 276 32 64 128 256), losses := [] }

theorem u34846 : Upper (D 6) (R 6) [24,33,160,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34847 : Route 9 := (fun mask => (mask,id))

def c34847 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34847 : Upper (D 6) (R 6) [24,33,160,5,320] 13 := by
  apply FastRouting.sound _ _ [24,33,160,5,320] 13 (by decide) (choices 1) [2,4,64] r34847 c34847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18494
  · exact u18495
  · exact u18496

def b34848 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 164 14 22 353 321 449 321), lower := (rows 25 35 164 14 22 32 64 128 256), losses := [] }

theorem u34848 : Upper (D 6) (R 6) [24,33,160,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34849 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 3, region := 337, targets := 32 }], pairs := [(0,5),(2,0),(3,0)], upper := (rows 25 35 164 14 81 358 326 454 326), lower := (rows 25 35 164 14 81 32 64 128 256), losses := [] }

theorem u34849 : Upper (D 6) (R 6) [24,33,160,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34850 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 337, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,5),(2,1),(4,5)], upper := (rows 25 35 164 14 82 357 325 453 325), lower := (rows 25 35 164 14 82 32 64 128 256), losses := [] }

theorem u34850 : Upper (D 6) (R 6) [24,33,160,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34851 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 337, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(0,5),(1,2),(4,5)], upper := (rows 25 35 164 14 84 355 323 451 323), lower := (rows 25 35 164 14 84 32 64 128 256), losses := [] }

theorem u34851 : Upper (D 6) (R 6) [24,33,160,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34852 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 3, region := 337, targets := 32 }], pairs := [(0,5),(2,0),(3,0)], upper := (rows 25 35 164 14 273 102 70 198 326), lower := (rows 25 35 164 14 273 32 64 128 256), losses := [] }

theorem u34852 : Upper (D 6) (R 6) [24,33,160,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34853 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 337, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,5),(2,1),(4,5)], upper := (rows 25 35 164 14 274 101 69 197 325), lower := (rows 25 35 164 14 274 32 64 128 256), losses := [] }

theorem u34853 : Upper (D 6) (R 6) [24,33,160,6,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34854 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 337, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(0,5),(1,2),(4,5)], upper := (rows 25 35 164 14 276 99 67 195 323), lower := (rows 25 35 164 14 276 32 64 128 256), losses := [] }

theorem u34854 : Upper (D 6) (R 6) [24,33,160,6,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34855 : Route 9 := (fun mask => (mask,id))

def c34855 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34855 : Upper (D 6) (R 6) [24,33,160,6,320] 13 := by
  apply FastRouting.sound _ _ [24,33,160,6,320] 13 (by decide) (choices 1) [1,2,4,64] r34855 c34855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18497
  · exact u18498
  · exact u18499
  · exact u18500

def b34856 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 35 164 73 82 294 326 390 262), lower := (rows 25 35 164 73 82 32 64 128 256), losses := [] }

theorem u34856 : Upper (D 6) (R 6) [24,33,160,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34857 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 35 164 73 84 294 326 390 262), lower := (rows 25 35 164 73 84 32 64 128 256), losses := [] }

theorem u34857 : Upper (D 6) (R 6) [24,33,160,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34858 : Route 9 := (fun mask => (mask,id))

def c34858 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34858 : Upper (D 6) (R 6) [24,33,160,65,258] 13 := by
  apply FastRouting.sound _ _ [24,33,160,65,258] 13 (by decide) (choices 1) [2,4,64] r34858 c34858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18501
  · exact u18502
  · exact u18503

def r34859 : Route 9 := (fun mask => (mask,id))

def c34859 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34859 : Upper (D 6) (R 6) [24,33,160,65,260] 13 := by
  apply FastRouting.sound _ _ [24,33,160,65,260] 13 (by decide) (choices 1) [2,4,64] r34859 c34859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18504
  · exact u18505
  · exact u18506

#print axioms u34859
end Delivery.IrregularNine14.P06
