import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0440
import IrregularNine14P06C0441

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39780 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 262 76 49 118 86 214 342), lower := (rows 41 131 262 76 49 32 64 128 256), losses := [] }

theorem u39780 : Upper (D 6) (R 6) [40,129,258,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39781 : Route 9 := (fun mask => (mask,id))

def c39781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39781 : Upper (D 6) (R 6) [40,129,258,68,34] 13 := by
  apply FastRouting.sound _ _ [40,129,258,68,34] 13 (by decide) (choices 1) [1,4,16,64] r39781 c39781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26417
  · exact u26418
  · exact u26419
  · exact u26420

def r39782 : Route 9 := (fun mask => (mask,id))

def c39782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39782 : Upper (D 6) (R 6) [40,129,258,68,36] 13 := by
  apply FastRouting.sound _ _ [40,129,258,68,36] 13 (by decide) (choices 1) [1,2,16,64] r39782 c39782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26421
  · exact u26422
  · exact u26423
  · exact u26424

def r39783 : Route 9 := (fun mask => (mask,id))

def c39783 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39783 : Upper (D 6) (R 6) [40,129,258,68,65] 13 := by
  apply FastRouting.sound _ _ [40,129,258,68,65] 13 (by decide) (choices 1) [2,4,16] r39783 c39783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26425
  · exact u26426
  · exact u26427

def r39784 : Route 9 := (fun mask => (mask,id))

def c39784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39784 : Upper (D 6) (R 6) [40,129,258,68,66] 13 := by
  apply FastRouting.sound _ _ [40,129,258,68,66] 13 (by decide) (choices 1) [1,4,16] r39784 c39784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26428
  · exact u26429
  · exact u26430

def b39785 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 131 262 76 84 51 115 179 307), lower := (rows 41 131 262 76 84 32 64 128 256), losses := [] }

theorem u39785 : Upper (D 6) (R 6) [40,129,258,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39786 : Route 9 := (fun mask => (mask,id))

def c39786 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39786 : Upper (D 6) (R 6) [40,129,258,68,96] 13 := by
  apply FastRouting.sound _ _ [40,129,258,68,96] 13 (by decide) (choices 1) [1,2,4,16] r39786 c39786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26431
  · exact u26432
  · exact u26433
  · exact u26434

def b39787 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 262 88 19 100 100 228 356), lower := (rows 41 131 262 88 19 32 64 128 256), losses := [] }

theorem u39787 : Upper (D 6) (R 6) [40,129,258,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39788 : Route 9 := (fun mask => (mask,id))

def c39788 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39788 : Upper (D 6) (R 6) [40,129,258,80,5] 13 := by
  apply FastRouting.sound _ _ [40,129,258,80,5] 13 (by decide) (choices 1) [2,4,64] r39788 c39788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26435
  · exact u26436
  · exact u26437

def b39789 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 131 262 88 22 101 101 229 357), lower := (rows 41 131 262 88 22 32 64 128 256), losses := [] }

theorem u39789 : Upper (D 6) (R 6) [40,129,258,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39790 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 262 88 49 102 70 198 326), lower := (rows 41 131 262 88 49 32 64 128 256), losses := [] }

theorem u39790 : Upper (D 6) (R 6) [40,129,258,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39791 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 262 88 50 101 69 197 325), lower := (rows 41 131 262 88 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 23 24 16 0 67 131 259), good := (rows 463 455 454 92 478 0 64 128 256) }] }

theorem u39791 : Upper (D 6) (R 6) [40,129,258,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39792 : Route 9 := (fun mask => (mask,id))

def c39792 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39792 : Upper (D 6) (R 6) [40,129,258,80,36] 13 := by
  apply FastRouting.sound _ _ [40,129,258,80,36] 13 (by decide) (choices 1) [1,2,4,64] r39792 c39792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26438
  · exact u26439
  · exact u26440
  · exact u26441

def b39793 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 131 262 88 81 38 102 166 294), lower := (rows 41 131 262 88 81 32 64 128 256), losses := [] }

theorem u39793 : Upper (D 6) (R 6) [40,129,258,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39794 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 131 262 88 82 37 101 165 293), lower := (rows 41 131 262 88 82 32 64 128 256), losses := [] }

theorem u39794 : Upper (D 6) (R 6) [40,129,258,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39795 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 131 262 88 84 39 103 167 295), lower := (rows 41 131 262 88 84 32 64 128 256), losses := [] }

theorem u39795 : Upper (D 6) (R 6) [40,129,258,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39796 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 262 88 112 39 71 135 263), lower := (rows 41 131 262 88 112 32 64 128 256), losses := [] }

theorem u39796 : Upper (D 6) (R 6) [40,129,258,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39797 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 41 131 276 13 22 98 98 226 354), lower := (rows 41 131 276 13 22 32 64 128 256), losses := [] }

theorem u39797 : Upper (D 6) (R 6) [40,129,272,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39798 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 41 131 276 13 50 102 70 198 326), lower := (rows 41 131 276 13 50 32 64 128 256), losses := [] }

theorem u39798 : Upper (D 6) (R 6) [40,129,272,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39799 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 276 13 52 98 66 194 322), lower := (rows 41 131 276 13 52 32 64 128 256), losses := [] }

theorem u39799 : Upper (D 6) (R 6) [40,129,272,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39800 : Route 9 := (fun mask => (mask,id))

def c39800 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39800 : Upper (D 6) (R 6) [40,129,272,5,66] 13 := by
  apply FastRouting.sound _ _ [40,129,272,5,66] 13 (by decide) (choices 1) [2,4,64] r39800 c39800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26442
  · exact u26443
  · exact u26444

def b39801 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 41 131 276 13 84 98 98 226 354), lower := (rows 41 131 276 13 84 32 64 128 256), losses := [] }

theorem u39801 : Upper (D 6) (R 6) [40,129,272,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39802 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 41 131 276 13 112 102 70 198 326), lower := (rows 41 131 276 13 112 32 64 128 256), losses := [] }

theorem u39802 : Upper (D 6) (R 6) [40,129,272,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39803 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 276 14 19 100 100 228 356), lower := (rows 41 131 276 14 19 32 64 128 256), losses := [] }

theorem u39803 : Upper (D 6) (R 6) [40,129,272,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39804 : Route 9 := (fun mask => (mask,id))

def c39804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39804 : Upper (D 6) (R 6) [40,129,272,6,5] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,5] 13 (by decide) (choices 1) [2,64] r39804 c39804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26445
  · exact u26446

def b39805 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 131 276 14 22 97 97 225 353), lower := (rows 41 131 276 14 22 32 64 128 256), losses := [] }

theorem u39805 : Upper (D 6) (R 6) [40,129,272,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39806 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 276 14 49 102 70 198 326), lower := (rows 41 131 276 14 49 32 64 128 256), losses := [] }

theorem u39806 : Upper (D 6) (R 6) [40,129,272,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39807 : Route 9 := (fun mask => (mask,id))

def c39807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39807 : Upper (D 6) (R 6) [40,129,272,6,34] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,34] 13 (by decide) (choices 1) [1,4,64] r39807 c39807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26447
  · exact u26448
  · exact u26449

def b39808 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 41 131 276 14 52 99 67 195 323), lower := (rows 41 131 276 14 52 32 64 128 256), losses := [] }

theorem u39808 : Upper (D 6) (R 6) [40,129,272,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39809 : Route 9 := (fun mask => (mask,id))

def c39809 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39809 : Upper (D 6) (R 6) [40,129,272,6,65] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,65] 13 (by decide) (choices 1) [2,4,64] r39809 c39809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26450
  · exact u26451
  · exact u26452

def r39810 : Route 9 := (fun mask => (mask,id))

def c39810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39810 : Upper (D 6) (R 6) [40,129,272,6,66] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,66] 13 (by decide) (choices 1) [1,4,64] r39810 c39810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26453
  · exact u26454
  · exact u26455

def r39811 : Route 9 := (fun mask => (mask,id))

def c39811 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39811 : Upper (D 6) (R 6) [40,129,272,6,68] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,68] 13 (by decide) (choices 1) [1,2,64] r39811 c39811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26456
  · exact u26457
  · exact u26458

def r39812 : Route 9 := (fun mask => (mask,id))

def c39812 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39812 : Upper (D 6) (R 6) [40,129,272,6,96] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,96] 13 (by decide) (choices 1) [1,2,4,64] r39812 c39812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26459
  · exact u26460
  · exact u26461
  · exact u26462

def r39813 : Route 9 := (fun mask => (mask,id))

def c39813 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39813 : Upper (D 6) (R 6) [40,129,272,65,6] 13 := by
  apply FastRouting.sound _ _ [40,129,272,65,6] 13 (by decide) (choices 1) [2,4,64] r39813 c39813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26463
  · exact u26464
  · exact u26465

def b39814 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 131 276 73 50 102 70 198 326), lower := (rows 41 131 276 73 50 32 64 128 256), losses := [] }

theorem u39814 : Upper (D 6) (R 6) [40,129,272,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39815 : Route 9 := (fun mask => (mask,id))

def c39815 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39815 : Upper (D 6) (R 6) [40,129,272,65,36] 13 := by
  apply FastRouting.sound _ _ [40,129,272,65,36] 13 (by decide) (choices 1) [2,4,64] r39815 c39815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26466
  · exact u26467
  · exact u26468

def b39816 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 41 131 276 73 82 38 102 166 294), lower := (rows 41 131 276 73 82 32 64 128 256), losses := [] }

theorem u39816 : Upper (D 6) (R 6) [40,129,272,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39817 : Route 9 := (fun mask => (mask,id))

def c39817 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39817 : Upper (D 6) (R 6) [40,129,272,65,68] 13 := by
  apply FastRouting.sound _ _ [40,129,272,65,68] 13 (by decide) (choices 1) [2,4] r39817 c39817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26469
  · exact u26470

def b39818 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 276 73 112 38 70 134 262), lower := (rows 41 131 276 73 112 32 64 128 256), losses := [] }

theorem u39818 : Upper (D 6) (R 6) [40,129,272,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39819 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 276 74 19 100 100 228 356), lower := (rows 41 131 276 74 19 32 64 128 256), losses := [] }

theorem u39819 : Upper (D 6) (R 6) [40,129,272,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39820 : Route 9 := (fun mask => (mask,id))

def c39820 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39820 : Upper (D 6) (R 6) [40,129,272,66,5] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,5] 13 (by decide) (choices 1) [2,4,64] r39820 c39820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26471
  · exact u26472
  · exact u26473

def r39821 : Route 9 := (fun mask => (mask,id))

def c39821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39821 : Upper (D 6) (R 6) [40,129,272,66,6] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,6] 13 (by decide) (choices 1) [1,4,64] r39821 c39821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26474
  · exact u26475
  · exact u26476

def b39822 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 276 74 49 102 70 198 326), lower := (rows 41 131 276 74 49 32 64 128 256), losses := [] }

theorem u39822 : Upper (D 6) (R 6) [40,129,272,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39823 : Route 9 := (fun mask => (mask,id))

def c39823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39823 : Upper (D 6) (R 6) [40,129,272,66,34] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,34] 13 (by decide) (choices 1) [1,4,64] r39823 c39823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26477
  · exact u26478
  · exact u26479

def r39824 : Route 9 := (fun mask => (mask,id))

def c39824 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39824 : Upper (D 6) (R 6) [40,129,272,66,36] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,36] 13 (by decide) (choices 1) [1,2,4,64] r39824 c39824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26480
  · exact u26481
  · exact u26482
  · exact u26483

def r39825 : Route 9 := (fun mask => (mask,id))

def c39825 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39825 : Upper (D 6) (R 6) [40,129,272,66,65] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,65] 13 (by decide) (choices 1) [2,4] r39825 c39825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26484
  · exact u26485

def b39826 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 131 276 74 82 37 101 165 293), lower := (rows 41 131 276 74 82 32 64 128 256), losses := [] }

theorem u39826 : Upper (D 6) (R 6) [40,129,272,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39827 : Route 9 := (fun mask => (mask,id))

def c39827 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39827 : Upper (D 6) (R 6) [40,129,272,66,68] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,68] 13 (by decide) (choices 1) [1,2,4] r39827 c39827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26486
  · exact u26487
  · exact u26488

def r39828 : Route 9 := (fun mask => (mask,id))

def c39828 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39828 : Upper (D 6) (R 6) [40,129,272,66,96] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,96] 13 (by decide) (choices 1) [1,2,4] r39828 c39828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26489
  · exact u26490
  · exact u26491

def b39829 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 276 76 19 102 102 230 358), lower := (rows 41 131 276 76 19 32 64 128 256), losses := [] }

theorem u39829 : Upper (D 6) (R 6) [40,129,272,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39830 : Route 9 := (fun mask => (mask,id))

def c39830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39830 : Upper (D 6) (R 6) [40,129,272,68,5] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,5] 13 (by decide) (choices 1) [2,64] r39830 c39830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26492
  · exact u26493

def r39831 : Route 9 := (fun mask => (mask,id))

def c39831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39831 : Upper (D 6) (R 6) [40,129,272,68,6] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,6] 13 (by decide) (choices 1) [1,2,64] r39831 c39831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26494
  · exact u26495
  · exact u26496

def b39832 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 276 76 49 102 70 198 326), lower := (rows 41 131 276 76 49 32 64 128 256), losses := [] }

theorem u39832 : Upper (D 6) (R 6) [40,129,272,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39833 : Route 9 := (fun mask => (mask,id))

def c39833 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39833 : Upper (D 6) (R 6) [40,129,272,68,34] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,34] 13 (by decide) (choices 1) [1,2,4,64] r39833 c39833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26497
  · exact u26498
  · exact u26499
  · exact u26500

def b39834 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 41 131 276 76 52 99 67 195 323), lower := (rows 41 131 276 76 52 32 64 128 256), losses := [] }

theorem u39834 : Upper (D 6) (R 6) [40,129,272,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39835 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 131 276 76 81 38 102 166 294), lower := (rows 41 131 276 76 81 32 64 128 256), losses := [] }

theorem u39835 : Upper (D 6) (R 6) [40,129,272,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39836 : Route 9 := (fun mask => (mask,id))

def c39836 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39836 : Upper (D 6) (R 6) [40,129,272,68,66] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,66] 13 (by decide) (choices 1) [1,2,4] r39836 c39836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26501
  · exact u26502
  · exact u26503

def b39837 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 131 276 76 84 35 99 163 291), lower := (rows 41 131 276 76 84 32 64 128 256), losses := [] }

theorem u39837 : Upper (D 6) (R 6) [40,129,272,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39838 : Route 9 := (fun mask => (mask,id))

def c39838 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39838 : Upper (D 6) (R 6) [40,129,272,68,96] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,96] 13 (by decide) (choices 1) [1,2,4] r39838 c39838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26504
  · exact u26505
  · exact u26506

def b39839 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 292 14 19 116 84 212 340), lower := (rows 41 131 292 14 19 32 64 128 256), losses := [] }

theorem u39839 : Upper (D 6) (R 6) [40,129,288,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39839
end Delivery.IrregularNine14.P06
