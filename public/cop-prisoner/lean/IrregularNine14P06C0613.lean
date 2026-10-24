import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0356
import IrregularNine14P06C0357
import IrregularNine14P06C0358

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36780 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 10, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 164 25 81 294 326 390 262), lower := (rows 35 74 164 25 81 32 64 128 256), losses := [] }

theorem u36780 : Upper (D 6) (R 6) [34,72,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36781 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 164 25 82 293 325 389 261), lower := (rows 35 74 164 25 82 32 64 128 256), losses := [] }

theorem u36781 : Upper (D 6) (R 6) [34,72,160,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36782 : Route 9 := (fun mask => (mask,id))

def c36782 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36782 : Upper (D 6) (R 6) [34,72,160,17,68] 13 := by
  apply FastRouting.sound _ _ [34,72,160,17,68] 13 (by decide) (choices 1) [1,2,4,256] r36782 c36782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21396
  · exact u21397
  · exact u21398
  · exact u21399

def b36783 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 74 164 25 273 102 70 198 326), lower := (rows 35 74 164 25 273 32 64 128 256), losses := [] }

theorem u36783 : Upper (D 6) (R 6) [34,72,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36784 : Route 9 := (fun mask => (mask,id))

def c36784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36784 : Upper (D 6) (R 6) [34,72,160,17,258] 13 := by
  apply FastRouting.sound _ _ [34,72,160,17,258] 13 (by decide) (choices 1) [1,4,64] r36784 c36784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21400
  · exact u21401
  · exact u21402

def r36785 : Route 9 := (fun mask => (mask,id))

def c36785 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36785 : Upper (D 6) (R 6) [34,72,160,17,260] 13 := by
  apply FastRouting.sound _ _ [34,72,160,17,260] 13 (by decide) (choices 1) [1,2,4,64] r36785 c36785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21403
  · exact u21404
  · exact u21405
  · exact u21406

def r36786 : Route 9 := (fun mask => (mask,id))

def c36786 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36786 : Upper (D 6) (R 6) [34,72,160,17,320] 13 := by
  apply FastRouting.sound _ _ [34,72,160,17,320] 13 (by decide) (choices 1) [1,2,4] r36786 c36786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21407
  · exact u21408
  · exact u21409

def b36787 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 74 164 26 21 357 325 453 325), lower := (rows 35 74 164 26 21 32 64 128 256), losses := [] }

theorem u36787 : Upper (D 6) (R 6) [34,72,160,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36788 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 164 26 81 293 325 389 261), lower := (rows 35 74 164 26 81 32 64 128 256), losses := [] }

theorem u36788 : Upper (D 6) (R 6) [34,72,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36789 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 164 26 84 293 325 389 261), lower := (rows 35 74 164 26 84 32 64 128 256), losses := [] }

theorem u36789 : Upper (D 6) (R 6) [34,72,160,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36790 : Route 9 := (fun mask => (mask,id))

def c36790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36790 : Upper (D 6) (R 6) [34,72,160,18,257] 13 := by
  apply FastRouting.sound _ _ [34,72,160,18,257] 13 (by decide) (choices 1) [1,4,64] r36790 c36790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21410
  · exact u21411
  · exact u21412

def r36791 : Route 9 := (fun mask => (mask,id))

def c36791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36791 : Upper (D 6) (R 6) [34,72,160,18,260] 13 := by
  apply FastRouting.sound _ _ [34,72,160,18,260] 13 (by decide) (choices 1) [1,4,64] r36791 c36791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21413
  · exact u21414
  · exact u21415

def b36792 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 164 26 336 37 69 133 261), lower := (rows 35 74 164 26 336 32 64 128 256), losses := [] }

theorem u36792 : Upper (D 6) (R 6) [34,72,160,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36793 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 164 28 19 357 325 453 325), lower := (rows 35 74 164 28 19 32 64 128 256), losses := [] }

theorem u36793 : Upper (D 6) (R 6) [34,72,160,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36794 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 164 28 21 355 323 451 323), lower := (rows 35 74 164 28 21 32 64 128 256), losses := [] }

theorem u36794 : Upper (D 6) (R 6) [34,72,160,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36795 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 164 28 22 353 321 449 321), lower := (rows 35 74 164 28 22 32 64 128 256), losses := [] }

theorem u36795 : Upper (D 6) (R 6) [34,72,160,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36796 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 74 164 28 81 295 327 391 263), lower := (rows 35 74 164 28 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 23 24 16 35 0 131 259), good := (rows 423 431 164 28 445 32 0 128 256) }] }

theorem u36796 : Upper (D 6) (R 6) [34,72,160,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36797 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 164 28 82 293 325 389 261), lower := (rows 35 74 164 28 82 32 64 128 256), losses := [] }

theorem u36797 : Upper (D 6) (R 6) [34,72,160,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36798 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 164 28 84 291 323 387 259), lower := (rows 35 74 164 28 84 32 64 128 256), losses := [] }

theorem u36798 : Upper (D 6) (R 6) [34,72,160,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36799 : Route 9 := (fun mask => (mask,id))

def c36799 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36799 : Upper (D 6) (R 6) [34,72,160,20,257] 13 := by
  apply FastRouting.sound _ _ [34,72,160,20,257] 13 (by decide) (choices 1) [1,2,4,64] r36799 c36799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21416
  · exact u21417
  · exact u21418
  · exact u21419

def r36800 : Route 9 := (fun mask => (mask,id))

def c36800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36800 : Upper (D 6) (R 6) [34,72,160,20,258] 13 := by
  apply FastRouting.sound _ _ [34,72,160,20,258] 13 (by decide) (choices 1) [1,4,64] r36800 c36800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21420
  · exact u21421
  · exact u21422

def b36801 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 164 28 276 99 67 195 323), lower := (rows 35 74 164 28 276 32 64 128 256), losses := [] }

theorem u36801 : Upper (D 6) (R 6) [34,72,160,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36802 : Route 9 := (fun mask => (mask,id))

def c36802 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36802 : Upper (D 6) (R 6) [34,72,160,20,320] 13 := by
  apply FastRouting.sound _ _ [34,72,160,20,320] 13 (by decide) (choices 1) [1,2,4] r36802 c36802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21423
  · exact u21424
  · exact u21425

def b36803 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 164 265 19 116 84 212 340), lower := (rows 35 74 164 265 19 32 64 128 256), losses := [] }

theorem u36803 : Upper (D 6) (R 6) [34,72,160,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36804 : Route 9 := (fun mask => (mask,id))

def c36804 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36804 : Upper (D 6) (R 6) [34,72,160,257,5] 13 := by
  apply FastRouting.sound _ _ [34,72,160,257,5] 13 (by decide) (choices 1) [2,4,16,64] r36804 c36804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21426
  · exact u21427
  · exact u21428
  · exact u21429

def r36805 : Route 9 := (fun mask => (mask,id))

def c36805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36805 : Upper (D 6) (R 6) [34,72,160,257,6] 13 := by
  apply FastRouting.sound _ _ [34,72,160,257,6] 13 (by decide) (choices 1) [1,4,16,64] r36805 c36805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21430
  · exact u21431
  · exact u21432
  · exact u21433

def r36806 : Route 9 := (fun mask => (mask,id))

def c36806 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36806 : Upper (D 6) (R 6) [34,72,160,257,65] 13 := by
  apply FastRouting.sound _ _ [34,72,160,257,65] 13 (by decide) (choices 1) [2,4,16] r36806 c36806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21434
  · exact u21435
  · exact u21436

def b36807 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 164 265 82 53 85 149 277), lower := (rows 35 74 164 265 82 32 64 128 256), losses := [] }

theorem u36807 : Upper (D 6) (R 6) [34,72,160,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36808 : Route 9 := (fun mask => (mask,id))

def c36808 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36808 : Upper (D 6) (R 6) [34,72,160,257,68] 13 := by
  apply FastRouting.sound _ _ [34,72,160,257,68] 13 (by decide) (choices 1) [1,2,4,16] r36808 c36808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21437
  · exact u21438
  · exact u21439
  · exact u21440

def b36809 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 74 164 266 21 117 85 213 341), lower := (rows 35 74 164 266 21 32 64 128 256), losses := [] }

theorem u36809 : Upper (D 6) (R 6) [34,72,160,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36810 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 4, region := 164, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 164 266 81 53 85 149 277), lower := (rows 35 74 164 266 81 32 64 128 256), losses := [] }

theorem u36810 : Upper (D 6) (R 6) [34,72,160,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36811 : Route 9 := (fun mask => (mask,id))

def c36811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36811 : Upper (D 6) (R 6) [34,72,160,258,68] 13 := by
  apply FastRouting.sound _ _ [34,72,160,258,68] 13 (by decide) (choices 1) [1,4,16] r36811 c36811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21441
  · exact u21442
  · exact u21443

def b36812 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 164 268 19 117 85 213 341), lower := (rows 35 74 164 268 19 32 64 128 256), losses := [] }

theorem u36812 : Upper (D 6) (R 6) [34,72,160,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36813 : Route 9 := (fun mask => (mask,id))

def c36813 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36813 : Upper (D 6) (R 6) [34,72,160,260,5] 13 := by
  apply FastRouting.sound _ _ [34,72,160,260,5] 13 (by decide) (choices 1) [1,2,16,64] r36813 c36813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21444
  · exact u21445
  · exact u21446
  · exact u21447

def r36814 : Route 9 := (fun mask => (mask,id))

def c36814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36814 : Upper (D 6) (R 6) [34,72,160,260,6] 13 := by
  apply FastRouting.sound _ _ [34,72,160,260,6] 13 (by decide) (choices 1) [1,16,64] r36814 c36814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21448
  · exact u21449
  · exact u21450

def r36815 : Route 9 := (fun mask => (mask,id))

def c36815 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36815 : Upper (D 6) (R 6) [34,72,160,260,65] 13 := by
  apply FastRouting.sound _ _ [34,72,160,260,65] 13 (by decide) (choices 1) [1,2,4,16] r36815 c36815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21451
  · exact u21452
  · exact u21453
  · exact u21454

def b36816 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 164 268 82 53 85 149 277), lower := (rows 35 74 164 268 82 32 64 128 256), losses := [] }

theorem u36816 : Upper (D 6) (R 6) [34,72,160,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36817 : Route 9 := (fun mask => (mask,id))

def c36817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36817 : Upper (D 6) (R 6) [34,72,160,260,68] 13 := by
  apply FastRouting.sound _ _ [34,72,160,260,68] 13 (by decide) (choices 1) [1,2,16] r36817 c36817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21455
  · exact u21456
  · exact u21457

def b36818 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 164 280 19 101 69 197 325), lower := (rows 35 74 164 280 19 32 64 128 256), losses := [] }

theorem u36818 : Upper (D 6) (R 6) [34,72,160,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36819 : Route 9 := (fun mask => (mask,id))

def c36819 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36819 : Upper (D 6) (R 6) [34,72,160,272,5] 13 := by
  apply FastRouting.sound _ _ [34,72,160,272,5] 13 (by decide) (choices 1) [1,2,4,64] r36819 c36819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21458
  · exact u21459
  · exact u21460
  · exact u21461

def r36820 : Route 9 := (fun mask => (mask,id))

def c36820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36820 : Upper (D 6) (R 6) [34,72,160,272,6] 13 := by
  apply FastRouting.sound _ _ [34,72,160,272,6] 13 (by decide) (choices 1) [1,4,64] r36820 c36820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21462
  · exact u21463
  · exact u21464

def b36821 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 74 164 280 81 39 71 135 263), lower := (rows 35 74 164 280 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 23 24 16 35 0 131 259), good := (rows 423 431 164 284 445 32 0 128 256) }] }

theorem u36821 : Upper (D 6) (R 6) [34,72,160,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36822 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 164 280 82 37 69 133 261), lower := (rows 35 74 164 280 82 32 64 128 256), losses := [] }

theorem u36822 : Upper (D 6) (R 6) [34,72,160,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36823 : Route 9 := (fun mask => (mask,id))

def c36823 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36823 : Upper (D 6) (R 6) [34,72,160,272,68] 13 := by
  apply FastRouting.sound _ _ [34,72,160,272,68] 13 (by decide) (choices 1) [1,2,4] r36823 c36823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21465
  · exact u21466
  · exact u21467

def b36824 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 196 13 19 308 372 436 308), lower := (rows 35 74 196 13 19 32 64 128 256), losses := [] }

theorem u36824 : Upper (D 6) (R 6) [34,72,192,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36825 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 196 13 21 306 370 434 306), lower := (rows 35 74 196 13 21 32 64 128 256), losses := [] }

theorem u36825 : Upper (D 6) (R 6) [34,72,192,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36826 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 297, targets := 64 },{ cop := 4, region := 289, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 74 196 13 22 305 369 433 305), lower := (rows 35 74 196 13 22 32 64 128 256), losses := [] }

theorem u36826 : Upper (D 6) (R 6) [34,72,192,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36827 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 196 13 49 310 342 406 278), lower := (rows 35 74 196 13 49 32 64 128 256), losses := [] }

theorem u36827 : Upper (D 6) (R 6) [34,72,192,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36828 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 196 13 50 309 341 405 277), lower := (rows 35 74 196 13 50 32 64 128 256), losses := [] }

theorem u36828 : Upper (D 6) (R 6) [34,72,192,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36829 : Route 9 := (fun mask => (mask,id))

def c36829 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36829 : Upper (D 6) (R 6) [34,72,192,5,36] 13 := by
  apply FastRouting.sound _ _ [34,72,192,5,36] 13 (by decide) (choices 1) [1,2,16,256] r36829 c36829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21468
  · exact u21469
  · exact u21470
  · exact u21471

def r36830 : Route 9 := (fun mask => (mask,id))

def c36830 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36830 : Upper (D 6) (R 6) [34,72,192,5,257] 13 := by
  apply FastRouting.sound _ _ [34,72,192,5,257] 13 (by decide) (choices 1) [2,4,16] r36830 c36830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21472
  · exact u21473
  · exact u21474

def r36831 : Route 9 := (fun mask => (mask,id))

def c36831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36831 : Upper (D 6) (R 6) [34,72,192,5,258] 13 := by
  apply FastRouting.sound _ _ [34,72,192,5,258] 13 (by decide) (choices 1) [1,4,16] r36831 c36831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21475
  · exact u21476
  · exact u21477

def r36832 : Route 9 := (fun mask => (mask,id))

def c36832 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36832 : Upper (D 6) (R 6) [34,72,192,5,260] 13 := by
  apply FastRouting.sound _ _ [34,72,192,5,260] 13 (by decide) (choices 1) [1,2,16] r36832 c36832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21478
  · exact u21479
  · exact u21480

def r36833 : Route 9 := (fun mask => (mask,id))

def c36833 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36833 : Upper (D 6) (R 6) [34,72,192,5,288] 13 := by
  apply FastRouting.sound _ _ [34,72,192,5,288] 13 (by decide) (choices 1) [1,2,4,16] r36833 c36833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21481
  · exact u21482
  · exact u21483
  · exact u21484

def b36834 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 196 25 19 292 356 420 292), lower := (rows 35 74 196 25 19 32 64 128 256), losses := [] }

theorem u36834 : Upper (D 6) (R 6) [34,72,192,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36835 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 74 196 25 21 294 358 422 294), lower := (rows 35 74 196 25 21 32 64 128 256), losses := [] }

theorem u36835 : Upper (D 6) (R 6) [34,72,192,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36836 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 297, targets := 64 },{ cop := 0, region := 452, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 74 196 25 22 293 357 421 293), lower := (rows 35 74 196 25 22 32 64 128 256), losses := [] }

theorem u36836 : Upper (D 6) (R 6) [34,72,192,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36837 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 196 25 49 294 326 390 262), lower := (rows 35 74 196 25 49 32 64 128 256), losses := [] }

theorem u36837 : Upper (D 6) (R 6) [34,72,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36838 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 196 25 50 293 325 389 261), lower := (rows 35 74 196 25 50 32 64 128 256), losses := [] }

theorem u36838 : Upper (D 6) (R 6) [34,72,192,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36839 : Route 9 := (fun mask => (mask,id))

def c36839 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36839 : Upper (D 6) (R 6) [34,72,192,17,36] 13 := by
  apply FastRouting.sound _ _ [34,72,192,17,36] 13 (by decide) (choices 1) [1,2,4,256] r36839 c36839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21485
  · exact u21486
  · exact u21487
  · exact u21488

#print axioms u36839
end Delivery.IrregularNine14.P06
