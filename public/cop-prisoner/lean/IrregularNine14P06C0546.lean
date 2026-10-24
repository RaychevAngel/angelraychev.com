import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0257
import IrregularNine14P06C0258

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32760 : Route 9 := (fun mask => (mask,id))

def c32760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32760 : Upper (D 6) (R 6) [10,129,34,320,65] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320,65] 13 (by decide) (choices 1) [4,16] r32760 c32760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15457
  · exact u15458

def r32761 : Route 9 := (fun mask => (mask,id))

def c32761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32761 : Upper (D 6) (R 6) [10,129,34,320,68] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320,68] 13 (by decide) (choices 1) [1,4,16] r32761 c32761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15459
  · exact u15460
  · exact u15461

def r32762 : Route 9 := (fun mask => (mask,id))

def c32762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32762 : Upper (D 6) (R 6) [10,129,34,320,96] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320,96] 13 (by decide) (choices 1) [1,4,16] r32762 c32762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15462
  · exact u15463
  · exact u15464

def b32763 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 52 13 22 352 352 480 352), lower := (rows 11 131 52 13 22 32 64 128 256), losses := [] }

theorem u32763 : Upper (D 6) (R 6) [10,129,48,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32764 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 13 50 356 324 452 324), lower := (rows 11 131 52 13 50 32 64 128 256), losses := [] }

theorem u32764 : Upper (D 6) (R 6) [10,129,48,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32765 : PairBound 9 := { available := 322, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 13 52 354 322 450 322), lower := (rows 11 131 52 13 52 32 64 128 256), losses := [] }

theorem u32765 : Upper (D 6) (R 6) [10,129,48,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32766 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 13 82 356 356 484 356), lower := (rows 11 131 52 13 82 32 64 128 256), losses := [] }

theorem u32766 : Upper (D 6) (R 6) [10,129,48,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32767 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 3, region := 483, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 131 52 13 84 354 354 482 354), lower := (rows 11 131 52 13 84 32 64 128 256), losses := [] }

theorem u32767 : Upper (D 6) (R 6) [10,129,48,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32768 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 13 112 358 326 454 326), lower := (rows 11 131 52 13 112 32 64 128 256), losses := [] }

theorem u32768 : Upper (D 6) (R 6) [10,129,48,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32769 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 13 274 100 100 228 356), lower := (rows 11 131 52 13 274 32 64 128 256), losses := [] }

theorem u32769 : Upper (D 6) (R 6) [10,129,48,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32770 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 131 52 13 276 98 98 226 354), lower := (rows 11 131 52 13 276 32 64 128 256), losses := [] }

theorem u32770 : Upper (D 6) (R 6) [10,129,48,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32771 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 13 304 102 70 198 326), lower := (rows 11 131 52 13 304 32 64 128 256), losses := [] }

theorem u32771 : Upper (D 6) (R 6) [10,129,48,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32772 : Route 9 := (fun mask => (mask,id))

def c32772 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32772 : Upper (D 6) (R 6) [10,129,48,5,320] 13 := by
  apply FastRouting.sound _ _ [10,129,48,5,320] 13 (by decide) (choices 1) [2,4,64] r32772 c32772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15465
  · exact u15466
  · exact u15467

def b32773 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 41 22 356 324 452 324), lower := (rows 11 131 52 41 22 32 64 128 256), losses := [] }

theorem u32773 : Upper (D 6) (R 6) [10,129,48,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32774 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 41 82 356 324 452 324), lower := (rows 11 131 52 41 82 32 64 128 256), losses := [] }

theorem u32774 : Upper (D 6) (R 6) [10,129,48,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32775 : Route 9 := (fun mask => (mask,id))

def c32775 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32775 : Upper (D 6) (R 6) [10,129,48,33,68] 13 := by
  apply FastRouting.sound _ _ [10,129,48,33,68] 13 (by decide) (choices 1) [2,4,64,256] r32775 c32775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15468
  · exact u15469
  · exact u15470
  · exact u15471

def b32776 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 41 274 100 68 196 324), lower := (rows 11 131 52 41 274 32 64 128 256), losses := [] }

theorem u32776 : Upper (D 6) (R 6) [10,129,48,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32777 : Route 9 := (fun mask => (mask,id))

def c32777 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32777 : Upper (D 6) (R 6) [10,129,48,33,260] 13 := by
  apply FastRouting.sound _ _ [10,129,48,33,260] 13 (by decide) (choices 1) [2,4,64] r32777 c32777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15472
  · exact u15473
  · exact u15474

def r32778 : Route 9 := (fun mask => (mask,id))

def c32778 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32778 : Upper (D 6) (R 6) [10,129,48,33,320] 13 := by
  apply FastRouting.sound _ _ [10,129,48,33,320] 13 (by decide) (choices 1) [2,4,64] r32778 c32778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15475
  · exact u15476
  · exact u15477

def b32779 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 73 22 356 356 484 356), lower := (rows 11 131 52 73 22 32 64 128 256), losses := [] }

theorem u32779 : Upper (D 6) (R 6) [10,129,48,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32780 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 73 50 356 324 452 324), lower := (rows 11 131 52 73 50 32 64 128 256), losses := [] }

theorem u32780 : Upper (D 6) (R 6) [10,129,48,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32781 : PairBound 9 := { available := 326, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 73 52 358 326 454 326), lower := (rows 11 131 52 73 52 32 64 128 256), losses := [] }

theorem u32781 : Upper (D 6) (R 6) [10,129,48,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32782 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 131 52 73 82 292 356 420 292), lower := (rows 11 131 52 73 82 32 64 128 256), losses := [] }

theorem u32782 : Upper (D 6) (R 6) [10,129,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32783 : Route 9 := (fun mask => (mask,id))

def c32783 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32783 : Upper (D 6) (R 6) [10,129,48,65,68] 13 := by
  apply FastRouting.sound _ _ [10,129,48,65,68] 13 (by decide) (choices 1) [2,4,256] r32783 c32783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15478
  · exact u15479
  · exact u15480

def b32784 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 73 112 294 326 390 262), lower := (rows 11 131 52 73 112 32 64 128 256), losses := [] }

theorem u32784 : Upper (D 6) (R 6) [10,129,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32785 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 73 274 100 100 228 356), lower := (rows 11 131 52 73 274 32 64 128 256), losses := [] }

theorem u32785 : Upper (D 6) (R 6) [10,129,48,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32786 : Route 9 := (fun mask => (mask,id))

def c32786 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32786 : Upper (D 6) (R 6) [10,129,48,65,260] 13 := by
  apply FastRouting.sound _ _ [10,129,48,65,260] 13 (by decide) (choices 1) [2,4,64] r32786 c32786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15481
  · exact u15482
  · exact u15483

def b32787 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 73 304 102 70 198 326), lower := (rows 11 131 52 73 304 32 64 128 256), losses := [] }

theorem u32787 : Upper (D 6) (R 6) [10,129,48,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32788 : Route 9 := (fun mask => (mask,id))

def c32788 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32788 : Upper (D 6) (R 6) [10,129,48,65,320] 13 := by
  apply FastRouting.sound _ _ [10,129,48,65,320] 13 (by decide) (choices 1) [2,4] r32788 c32788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15484
  · exact u15485

def b32789 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 76 19 356 356 484 356), lower := (rows 11 131 52 76 19 32 64 128 256), losses := [] }

theorem u32789 : Upper (D 6) (R 6) [10,129,48,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32790 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 419, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 52 76 21 354 354 482 354), lower := (rows 11 131 52 76 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 490 482 60 76 508 32 64 128 256) }] }

theorem u32790 : Upper (D 6) (R 6) [10,129,48,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32791 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 419, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 131 52 76 22 353 353 481 353), lower := (rows 11 131 52 76 22 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 489 481 60 76 508 32 64 128 256) }] }

theorem u32791 : Upper (D 6) (R 6) [10,129,48,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32792 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 76 49 358 326 454 326), lower := (rows 11 131 52 76 49 32 64 128 256), losses := [] }

theorem u32792 : Upper (D 6) (R 6) [10,129,48,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32793 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 76 50 357 325 453 325), lower := (rows 11 131 52 76 50 32 64 128 256), losses := [] }

theorem u32793 : Upper (D 6) (R 6) [10,129,48,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32794 : PairBound 9 := { available := 323, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 76 52 355 323 451 323), lower := (rows 11 131 52 76 52 32 64 128 256), losses := [] }

theorem u32794 : Upper (D 6) (R 6) [10,129,48,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32795 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 52 76 81 294 358 422 294), lower := (rows 11 131 52 76 81 32 64 128 256), losses := [] }

theorem u32795 : Upper (D 6) (R 6) [10,129,48,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32796 : Route 9 := (fun mask => (mask,id))

def c32796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32796 : Upper (D 6) (R 6) [10,129,48,68,66] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,66] 13 (by decide) (choices 1) [1,4,256] r32796 c32796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15486
  · exact u15487
  · exact u15488

def b32797 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 131 52 76 84 291 355 419 291), lower := (rows 11 131 52 76 84 32 64 128 256), losses := [] }

theorem u32797 : Upper (D 6) (R 6) [10,129,48,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32798 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 76 112 295 327 391 263), lower := (rows 11 131 52 76 112 32 64 128 256), losses := [] }

theorem u32798 : Upper (D 6) (R 6) [10,129,48,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32799 : Route 9 := (fun mask => (mask,id))

def c32799 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32799 : Upper (D 6) (R 6) [10,129,48,68,257] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,257] 13 (by decide) (choices 1) [2,4,64] r32799 c32799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15489
  · exact u15490
  · exact u15491

def r32800 : Route 9 := (fun mask => (mask,id))

def c32800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32800 : Upper (D 6) (R 6) [10,129,48,68,258] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,258] 13 (by decide) (choices 1) [1,4,64] r32800 c32800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15492
  · exact u15493
  · exact u15494

def r32801 : Route 9 := (fun mask => (mask,id))

def c32801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32801 : Upper (D 6) (R 6) [10,129,48,68,260] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,260] 13 (by decide) (choices 1) [1,2,64] r32801 c32801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15495
  · exact u15496
  · exact u15497

def b32802 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 76 304 103 71 199 327), lower := (rows 11 131 52 76 304 32 64 128 256), losses := [] }

theorem u32802 : Upper (D 6) (R 6) [10,129,48,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32803 : Route 9 := (fun mask => (mask,id))

def c32803 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32803 : Upper (D 6) (R 6) [10,129,48,68,320] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,320] 13 (by decide) (choices 1) [1,2,4] r32803 c32803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15498
  · exact u15499
  · exact u15500

def b32804 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 104 19 356 324 452 324), lower := (rows 11 131 52 104 19 32 64 128 256), losses := [] }

theorem u32804 : Upper (D 6) (R 6) [10,129,48,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32805 : Route 9 := (fun mask => (mask,id))

def c32805 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32805 : Upper (D 6) (R 6) [10,129,48,96,5] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,5] 13 (by decide) (choices 1) [2,4,64,256] r32805 c32805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15501
  · exact u15502
  · exact u15503
  · exact u15504

def r32806 : Route 9 := (fun mask => (mask,id))

def c32806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32806 : Upper (D 6) (R 6) [10,129,48,96,6] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,6] 13 (by decide) (choices 1) [1,4,64,256] r32806 c32806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15505
  · exact u15506
  · exact u15507
  · exact u15508

def r32807 : Route 9 := (fun mask => (mask,id))

def c32807 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32807 : Upper (D 6) (R 6) [10,129,48,96,65] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,65] 13 (by decide) (choices 1) [2,4,256] r32807 c32807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15509
  · exact u15510
  · exact u15511

def r32808 : Route 9 := (fun mask => (mask,id))

def c32808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32808 : Upper (D 6) (R 6) [10,129,48,96,66] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,66] 13 (by decide) (choices 1) [1,4,256] r32808 c32808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15512
  · exact u15513
  · exact u15514

def b32809 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 104 84 295 327 391 263), lower := (rows 11 131 52 104 84 32 64 128 256), losses := [] }

theorem u32809 : Upper (D 6) (R 6) [10,129,48,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32810 : Route 9 := (fun mask => (mask,id))

def c32810 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32810 : Upper (D 6) (R 6) [10,129,48,96,257] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,257] 13 (by decide) (choices 1) [2,4,64] r32810 c32810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15515
  · exact u15516
  · exact u15517

def r32811 : Route 9 := (fun mask => (mask,id))

def c32811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32811 : Upper (D 6) (R 6) [10,129,48,96,258] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,258] 13 (by decide) (choices 1) [1,4,64] r32811 c32811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15518
  · exact u15519
  · exact u15520

def r32812 : Route 9 := (fun mask => (mask,id))

def c32812 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32812 : Upper (D 6) (R 6) [10,129,48,96,260] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,260] 13 (by decide) (choices 1) [1,2,4,64] r32812 c32812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15521
  · exact u15522
  · exact u15523
  · exact u15524

def r32813 : Route 9 := (fun mask => (mask,id))

def c32813 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32813 : Upper (D 6) (R 6) [10,129,48,96,320] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,320] 13 (by decide) (choices 1) [1,2,4] r32813 c32813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15525
  · exact u15526
  · exact u15527

def b32814 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 265 22 100 100 228 356), lower := (rows 11 131 52 265 22 32 64 128 256), losses := [] }

theorem u32814 : Upper (D 6) (R 6) [10,129,48,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32815 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 265 50 100 68 196 324), lower := (rows 11 131 52 265 50 32 64 128 256), losses := [] }

theorem u32815 : Upper (D 6) (R 6) [10,129,48,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32816 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 265 52 102 70 198 326), lower := (rows 11 131 52 265 52 32 64 128 256), losses := [] }

theorem u32816 : Upper (D 6) (R 6) [10,129,48,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32817 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 265 82 100 100 228 356), lower := (rows 11 131 52 265 82 32 64 128 256), losses := [] }

theorem u32817 : Upper (D 6) (R 6) [10,129,48,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32818 : Route 9 := (fun mask => (mask,id))

def c32818 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32818 : Upper (D 6) (R 6) [10,129,48,257,68] 13 := by
  apply FastRouting.sound _ _ [10,129,48,257,68] 13 (by decide) (choices 1) [2,4,64] r32818 c32818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15528
  · exact u15529
  · exact u15530

def b32819 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 265 112 102 70 198 326), lower := (rows 11 131 52 265 112 32 64 128 256), losses := [] }

theorem u32819 : Upper (D 6) (R 6) [10,129,48,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u32819
end Delivery.IrregularNine14.P06
