import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0146
import IrregularNine14P06C0147

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27660 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 97 162 324 26 28 34 69 133 261), lower := (rows 97 162 324 26 28 34 64 128 256), losses := [] }

theorem u27660 : Upper (D 6) (R 6) [96,160,320,18,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27661 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,2),(1,2),(1,6)], upper := (rows 97 162 324 26 28 36 67 131 259), lower := (rows 97 162 324 26 28 36 64 128 256), losses := [] }

theorem u27661 : Upper (D 6) (R 6) [96,160,320,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27662 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 15, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 14 112 480 480 480 480), lower := (rows 7 11 21 14 112 32 64 128 256), losses := [] }

theorem u27662 : Upper (D 6) (R 6) [6,9,17,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27663 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 15, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 14 176 352 352 480 352), lower := (rows 7 11 21 14 176 32 64 128 256), losses := [] }

theorem u27663 : Upper (D 6) (R 6) [6,9,17,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27664 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 15, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 14 400 96 96 224 352), lower := (rows 7 11 21 14 400 32 64 128 256), losses := [] }

theorem u27664 : Upper (D 6) (R 6) [6,9,17,6,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27665 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 21 42 112 484 452 452 452), lower := (rows 7 11 21 42 112 32 64 128 256), losses := [] }

theorem u27665 : Upper (D 6) (R 6) [6,9,17,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27666 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 21 42 176 356 324 452 324), lower := (rows 7 11 21 42 176 32 64 128 256), losses := [] }

theorem u27666 : Upper (D 6) (R 6) [6,9,17,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27667 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 42 208 356 356 484 356), lower := (rows 7 11 21 42 208 32 64 128 256), losses := [] }

theorem u27667 : Upper (D 6) (R 6) [6,9,17,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27668 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 42 400 100 100 228 356), lower := (rows 7 11 21 42 400 32 64 128 256), losses := [] }

theorem u27668 : Upper (D 6) (R 6) [6,9,17,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27669 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 21 44 112 482 450 450 450), lower := (rows 7 11 21 44 112 32 64 128 256), losses := [] }

theorem u27669 : Upper (D 6) (R 6) [6,9,17,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27670 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 21 44 176 354 322 450 322), lower := (rows 7 11 21 44 176 32 64 128 256), losses := [] }

theorem u27670 : Upper (D 6) (R 6) [6,9,17,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27671 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 44 208 354 354 482 354), lower := (rows 7 11 21 44 208 32 64 128 256), losses := [] }

theorem u27671 : Upper (D 6) (R 6) [6,9,17,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27672 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 44 400 98 98 226 354), lower := (rows 7 11 21 44 400 32 64 128 256), losses := [] }

theorem u27672 : Upper (D 6) (R 6) [6,9,17,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27673 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 21 104 112 422 454 390 390), lower := (rows 7 11 21 104 112 32 64 128 256), losses := [] }

theorem u27673 : Upper (D 6) (R 6) [6,9,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27674 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 11 21 104 146 356 356 484 356), lower := (rows 7 11 21 104 146 32 64 128 256), losses := [] }

theorem u27674 : Upper (D 6) (R 6) [6,9,17,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27675 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 11 21 104 148 354 354 482 354), lower := (rows 7 11 21 104 148 32 64 128 256), losses := [] }

theorem u27675 : Upper (D 6) (R 6) [6,9,17,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27676 : Route 9 := (fun mask => (mask,id))

def c27676 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27676 : Upper (D 6) (R 6) [6,9,17,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,160] 13 (by decide) (choices 1) [2,4,64,256] r27676 c27676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8777
  · exact u8778
  · exact u8779
  · exact u8780

def r27677 : Route 9 := (fun mask => (mask,id))

def c27677 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27677 : Upper (D 6) (R 6) [6,9,17,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384] 13 (by decide) (choices 1) [2,4,64] r27677 c27677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8781
  · exact u8782
  · exact u8783

def b27678 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 372, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 138 304 100 100 228 356), lower := (rows 7 11 21 138 304 32 64 128 256), losses := [] }

theorem u27678 : Upper (D 6) (R 6) [6,9,17,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27679 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 140 304 98 98 226 354), lower := (rows 7 11 21 140 304 32 64 128 256), losses := [] }

theorem u27679 : Upper (D 6) (R 6) [6,9,17,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m27680_4 : Upper (D 6) (R 6) [6,9,17,160,288,4] 13 :=
  permutation_upper _ _ _ [6,9,17,160,288,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8784

def r27680 : Route 9 := (fun mask => (mask,id))

def c27680 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27680 : Upper (D 6) (R 6) [6,9,17,160,288] 13 := by
  apply FastRouting.sound _ _ [6,9,17,160,288] 13 (by decide) (choices 1) [2,4,64] r27680 c27680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8784
  · exact m27680_4
  · exact u8785

def r27681 : Route 9 := (fun mask => (mask,id))

def c27681 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27681 : Upper (D 6) (R 6) [6,9,17,160,320] 13 := by
  apply FastRouting.sound _ _ [6,9,17,160,320] 13 (by decide) (choices 1) [2,4,64] r27681 c27681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8786
  · exact u8787
  · exact u8788

def b27682 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 488, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 88 22 480 480 480 480), lower := (rows 7 11 37 88 22 32 64 128 256), losses := [] }

theorem u27682 : Upper (D 6) (R 6) [6,9,33,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27683 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 5, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 11 37 88 50 484 452 452 452), lower := (rows 7 11 37 88 50 32 64 128 256), losses := [] }

theorem u27683 : Upper (D 6) (R 6) [6,9,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27684 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 37 88 52 482 450 450 450), lower := (rows 7 11 37 88 52 32 64 128 256), losses := [] }

theorem u27684 : Upper (D 6) (R 6) [6,9,33,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27685 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 88 82 420 484 420 420), lower := (rows 7 11 37 88 82 32 64 128 256), losses := [] }

theorem u27685 : Upper (D 6) (R 6) [6,9,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27686 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 88 84 418 482 418 418), lower := (rows 7 11 37 88 84 32 64 128 256), losses := [] }

theorem u27686 : Upper (D 6) (R 6) [6,9,33,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27687 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 88 112 422 454 390 390), lower := (rows 7 11 37 88 112 32 64 128 256), losses := [] }

theorem u27687 : Upper (D 6) (R 6) [6,9,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27688 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 88 146 356 356 484 356), lower := (rows 7 11 37 88 146 32 64 128 256), losses := [] }

theorem u27688 : Upper (D 6) (R 6) [6,9,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27689 : Route 9 := (fun mask => (mask,id))

def c27689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27689 : Upper (D 6) (R 6) [6,9,33,80,132] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,132] 13 (by decide) (choices 1) [2,64,256] r27689 c27689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8789
  · exact u8790
  · exact u8791

def r27690 : Route 9 := (fun mask => (mask,id))

def c27690 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27690 : Upper (D 6) (R 6) [6,9,33,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,160] 13 (by decide) (choices 1) [2,4,64,256] r27690 c27690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8792
  · exact u8793
  · exact u8794
  · exact u8795

def b27691 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 88 208 294 358 422 294), lower := (rows 7 11 37 88 208 32 64 128 256), losses := [] }

theorem u27691 : Upper (D 6) (R 6) [6,9,33,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27692 : Route 9 := (fun mask => (mask,id))

def c27692 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27692 : Upper (D 6) (R 6) [6,9,33,80,384] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,384] 13 (by decide) (choices 1) [2,4,64] r27692 c27692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8796
  · exact u8797
  · exact u8798

def b27693 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 488, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 152 22 352 352 480 352), lower := (rows 7 11 37 152 22 32 64 128 256), losses := [] }

theorem u27693 : Upper (D 6) (R 6) [6,9,33,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27694 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 5, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 11 37 152 50 356 324 452 324), lower := (rows 7 11 37 152 50 32 64 128 256), losses := [] }

theorem u27694 : Upper (D 6) (R 6) [6,9,33,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27695 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 37 152 52 354 322 450 322), lower := (rows 7 11 37 152 52 32 64 128 256), losses := [] }

theorem u27695 : Upper (D 6) (R 6) [6,9,33,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27696 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 152 82 356 356 484 356), lower := (rows 7 11 37 152 82 32 64 128 256), losses := [] }

theorem u27696 : Upper (D 6) (R 6) [6,9,33,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27697 : Route 9 := (fun mask => (mask,id))

def c27697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27697 : Upper (D 6) (R 6) [6,9,33,144,68] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,68] 13 (by decide) (choices 1) [2,64,256] r27697 c27697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8799
  · exact u8800
  · exact u8801

def r27698 : Route 9 := (fun mask => (mask,id))

def c27698 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27698 : Upper (D 6) (R 6) [6,9,33,144,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,96] 13 (by decide) (choices 1) [2,4,64,256] r27698 c27698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8802
  · exact u8803
  · exact u8804
  · exact u8805

def b27699 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 152 274 100 100 228 356), lower := (rows 7 11 37 152 274 32 64 128 256), losses := [] }

theorem u27699 : Upper (D 6) (R 6) [6,9,33,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27700 : Route 9 := (fun mask => (mask,id))

def c27700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27700 : Upper (D 6) (R 6) [6,9,33,144,260] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,260] 13 (by decide) (choices 1) [2,64] r27700 c27700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8806
  · exact u8807

def r27701 : Route 9 := (fun mask => (mask,id))

def c27701 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27701 : Upper (D 6) (R 6) [6,9,33,144,288] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,288] 13 (by decide) (choices 1) [2,4,64] r27701 c27701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8808
  · exact u8809
  · exact u8810

def r27702 : Route 9 := (fun mask => (mask,id))

def c27702 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27702 : Upper (D 6) (R 6) [6,9,33,144,320] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,320] 13 (by decide) (choices 1) [2,4,64] r27702 c27702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8811
  · exact u8812
  · exact u8813

def b27703 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 488, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 200 22 368 368 496 368), lower := (rows 7 11 37 200 22 32 64 128 256), losses := [] }

theorem u27703 : Upper (D 6) (R 6) [6,9,33,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27704 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 5, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 11 37 200 50 372 340 468 340), lower := (rows 7 11 37 200 50 32 64 128 256), losses := [] }

theorem u27704 : Upper (D 6) (R 6) [6,9,33,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27705 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 37 200 52 370 338 466 338), lower := (rows 7 11 37 200 52 32 64 128 256), losses := [] }

theorem u27705 : Upper (D 6) (R 6) [6,9,33,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27706 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 11 37 200 82 308 372 436 308), lower := (rows 7 11 37 200 82 32 64 128 256), losses := [] }

theorem u27706 : Upper (D 6) (R 6) [6,9,33,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27707 : Route 9 := (fun mask => (mask,id))

def c27707 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27707 : Upper (D 6) (R 6) [6,9,33,192,68] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,68] 13 (by decide) (choices 1) [2,16,256] r27707 c27707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8814
  · exact u8815
  · exact u8816

def r27708 : Route 9 := (fun mask => (mask,id))

def c27708 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27708 : Upper (D 6) (R 6) [6,9,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,96] 13 (by decide) (choices 1) [2,4,16,256] r27708 c27708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8817
  · exact u8818
  · exact u8819
  · exact u8820

def r27709 : Route 9 := (fun mask => (mask,id))

def c27709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27709 : Upper (D 6) (R 6) [6,9,33,192,258] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,258] 13 (by decide) (choices 1) [4,16,64] r27709 c27709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8821
  · exact u8822
  · exact u8823

def r27710 : Route 9 := (fun mask => (mask,id))

def c27710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27710 : Upper (D 6) (R 6) [6,9,33,192,260] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,260] 13 (by decide) (choices 1) [2,16,64] r27710 c27710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8824
  · exact u8825
  · exact u8826

def r27711 : Route 9 := (fun mask => (mask,id))

def c27711 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27711 : Upper (D 6) (R 6) [6,9,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,288] 13 (by decide) (choices 1) [2,4,16,64] r27711 c27711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8827
  · exact u8828
  · exact u8829
  · exact u8830

def r27712 : Route 9 := (fun mask => (mask,id))

def c27712 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27712 : Upper (D 6) (R 6) [6,9,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,320] 13 (by decide) (choices 1) [2,4,16] r27712 c27712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8831
  · exact u8832
  · exact u8833

def b27713 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 488, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 392 22 112 112 240 368), lower := (rows 7 11 37 392 22 32 64 128 256), losses := [] }

theorem u27713 : Upper (D 6) (R 6) [6,9,33,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27714 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 5, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 11 37 392 50 116 84 212 340), lower := (rows 7 11 37 392 50 32 64 128 256), losses := [] }

theorem u27714 : Upper (D 6) (R 6) [6,9,33,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27715 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 37 392 52 114 82 210 338), lower := (rows 7 11 37 392 52 32 64 128 256), losses := [] }

theorem u27715 : Upper (D 6) (R 6) [6,9,33,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27716 : Route 9 := (fun mask => (mask,id))

def c27716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27716 : Upper (D 6) (R 6) [6,9,33,384,66] 13 := by
  apply FastRouting.sound _ _ [6,9,33,384,66] 13 (by decide) (choices 1) [4,16,64] r27716 c27716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8834
  · exact u8835
  · exact u8836

def r27717 : Route 9 := (fun mask => (mask,id))

def c27717 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27717 : Upper (D 6) (R 6) [6,9,33,384,68] 13 := by
  apply FastRouting.sound _ _ [6,9,33,384,68] 13 (by decide) (choices 1) [2,16,64] r27717 c27717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8837
  · exact u8838
  · exact u8839

def r27718 : Route 9 := (fun mask => (mask,id))

def c27718 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27718 : Upper (D 6) (R 6) [6,9,33,384,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,384,96] 13 (by decide) (choices 1) [2,4,16,64] r27718 c27718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8840
  · exact u8841
  · exact u8842
  · exact u8843

def b27719 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 52 74 21 480 480 480 480), lower := (rows 7 11 52 74 21 32 64 128 256), losses := [] }

theorem u27719 : Upper (D 6) (R 6) [6,9,48,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27719
end Delivery.IrregularNine14.P06
