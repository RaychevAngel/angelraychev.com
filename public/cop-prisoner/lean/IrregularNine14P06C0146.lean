import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0011

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8760 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 97 138 292 76 22 48 65 131 259), lower := (rows 97 138 292 76 22 48 65 128 256), losses := [] }

theorem u8760 : Upper (D 6) (R 6) [96,136,288,68,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8760 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8761 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 97 138 292 76 22 48 66 129 257), lower := (rows 97 138 292 76 22 48 66 128 256), losses := [] }

theorem u8761 : Upper (D 6) (R 6) [96,136,288,68,6,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8761 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8762 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 138 292 88 21 34 65 134 262), lower := (rows 97 138 292 88 21 34 65 128 256), losses := [] }

theorem u8762 : Upper (D 6) (R 6) [96,136,288,80,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8763 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 138 292 88 21 34 66 133 261), lower := (rows 97 138 292 88 21 34 66 128 256), losses := [] }

theorem u8763 : Upper (D 6) (R 6) [96,136,288,80,5,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8764 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 138 292 88 21 34 68 131 259), lower := (rows 97 138 292 88 21 34 68 128 256), losses := [] }

theorem u8764 : Upper (D 6) (R 6) [96,136,288,80,5,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8765 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 138 292 88 22 33 65 134 262), lower := (rows 97 138 292 88 22 33 65 128 256), losses := [] }

theorem u8765 : Upper (D 6) (R 6) [96,136,288,80,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8766 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 4, region := 72, targets := 1 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 97 138 292 88 22 33 66 133 261), lower := (rows 97 138 292 88 22 33 66 128 256), losses := [] }

theorem u8766 : Upper (D 6) (R 6) [96,136,288,80,6,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8767 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 97 138 292 88 22 33 68 131 259), lower := (rows 97 138 292 88 22 33 68 128 256), losses := [] }

theorem u8767 : Upper (D 6) (R 6) [96,136,288,80,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8768 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 162 324 14 25 33 80 134 262), lower := (rows 97 162 324 14 25 33 80 128 256), losses := [] }

theorem u8768 : Upper (D 6) (R 6) [96,160,320,6,9,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8768 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8769 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 97 162 324 14 25 34 80 133 261), lower := (rows 97 162 324 14 25 34 80 128 256), losses := [] }

theorem u8769 : Upper (D 6) (R 6) [96,160,320,6,9,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8769 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8770 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 97 162 324 14 25 36 80 131 259), lower := (rows 97 162 324 14 25 36 80 128 256), losses := [] }

theorem u8770 : Upper (D 6) (R 6) [96,160,320,6,9,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8770 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8771 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 97 162 324 25 26 36 65 134 262), lower := (rows 97 162 324 25 26 36 65 128 256), losses := [] }

theorem u8771 : Upper (D 6) (R 6) [96,160,320,17,10,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8772 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 97 162 324 25 26 36 66 133 261), lower := (rows 97 162 324 25 26 36 66 128 256), losses := [] }

theorem u8772 : Upper (D 6) (R 6) [96,160,320,17,10,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8773 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 154, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 97 162 324 25 26 36 68 131 259), lower := (rows 97 162 324 25 26 36 68 128 256), losses := [] }

theorem u8773 : Upper (D 6) (R 6) [96,160,320,17,10,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8774 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 162 324 26 28 33 65 134 262), lower := (rows 97 162 324 26 28 33 65 128 256), losses := [] }

theorem u8774 : Upper (D 6) (R 6) [96,160,320,18,12,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8775 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 293, targets := 2 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 162 324 26 28 33 66 133 261), lower := (rows 97 162 324 26 28 33 66 128 256), losses := [] }

theorem u8775 : Upper (D 6) (R 6) [96,160,320,18,12,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8776 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 97 162 324 26 28 33 68 131 259), lower := (rows 97 162 324 26 28 33 68 128 256), losses := [] }

theorem u8776 : Upper (D 6) (R 6) [96,160,320,18,12,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8777 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 104 176 34 324 452 324), lower := (rows 7 11 21 104 176 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 56 56 32 103 167 295), good := (rows 453 477 477 504 504 508 64 128 256) }] }

theorem u8777 : Upper (D 6) (R 6) [6,9,17,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8778 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 11 21 104 176 36 322 450 322), lower := (rows 7 11 21 104 176 36 64 128 256), losses := [{ target := 2, region := (rows 1 6 0 56 56 32 103 167 295), good := (rows 451 475 475 504 504 506 64 128 256) }] }

theorem u8778 : Upper (D 6) (R 6) [6,9,17,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8779 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 21 104 176 96 326 390 262), lower := (rows 7 11 21 104 176 96 64 128 256), losses := [] }

theorem u8779 : Upper (D 6) (R 6) [6,9,17,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8780 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 21 104 176 288 70 198 326), lower := (rows 7 11 21 104 176 288 64 128 256), losses := [] }

theorem u8780 : Upper (D 6) (R 6) [6,9,17,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8780 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8781 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 104 400 34 100 228 356), lower := (rows 7 11 21 104 400 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 40 56 32 96 160 288), good := (rows 5 29 21 504 400 508 64 128 256) }] }

theorem u8781 : Upper (D 6) (R 6) [6,9,17,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m8782_2 : Upper (D 6) (R 6) [6,9,17,96,384,4,2] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u665

def r8782 : Route 9 := (fun mask => (mask,id))

def c8782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8782 : Upper (D 6) (R 6) [6,9,17,96,384,4] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384,4] 13 (by decide) (choices 1) [2,32] r8782 c8782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m8782_2
  · exact u666

def b8783 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 21 104 400 96 102 166 294), lower := (rows 7 11 21 104 400 96 64 128 256), losses := [] }

theorem u8783 : Upper (D 6) (R 6) [6,9,17,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8784 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 168 304 34 68 196 324), lower := (rows 7 11 21 168 304 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 56 56 32 103 167 295), good := (rows 453 477 477 504 504 508 64 128 256) }] }

theorem u8784 : Upper (D 6) (R 6) [6,9,17,160,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m8785_4 : Upper (D 6) (R 6) [6,9,17,160,288,64,4] 13 :=
  permutation_upper _ _ _ [6,9,17,160,288,64,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u667

def r8785 : Route 9 := (fun mask => (mask,id))

def c8785 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8785 : Upper (D 6) (R 6) [6,9,17,160,288,64] 13 := by
  apply FastRouting.sound _ _ [6,9,17,160,288,64] 13 (by decide) (choices 1) [2,4] r8785 c8785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u667
  · exact m8785_4

def b8786 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 168 336 34 100 228 356), lower := (rows 7 11 21 168 336 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 40 56 32 96 160 288), good := (rows 5 29 21 504 336 508 64 128 256) }] }

theorem u8786 : Upper (D 6) (R 6) [6,9,17,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8787 : Route 9 := (fun mask => (mask,id))

def c8787 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8787 : Upper (D 6) (R 6) [6,9,17,160,320,4] 13 := by
  apply FastRouting.sound _ _ [6,9,17,160,320,4] 13 (by decide) (choices 1) [2,32] r8787 c8787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u669
  · exact u670

theorem m8788_2 : Upper (D 6) (R 6) [6,9,17,160,320,64,2] 13 :=
  permutation_upper _ _ _ [6,9,17,160,320,4,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u670

theorem m8788_4 : Upper (D 6) (R 6) [6,9,17,160,320,64,4] 13 :=
  permutation_upper _ _ _ [6,9,17,160,320,2,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u668

def r8788 : Route 9 := (fun mask => (mask,id))

def c8788 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8788 : Upper (D 6) (R 6) [6,9,17,160,320,64] 13 := by
  apply FastRouting.sound _ _ [6,9,17,160,320,64] 13 (by decide) (choices 1) [2,4,32] r8788 c8788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m8788_2
  · exact m8788_4
  · exact u671

def b8789 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 88 148 34 352 480 352), lower := (rows 7 11 37 88 148 34 64 128 256), losses := [] }

theorem u8789 : Upper (D 6) (R 6) [6,9,33,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8790 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 88 148 96 354 418 290), lower := (rows 7 11 37 88 148 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 16 104 64 128 256), good := (rows 5 45 37 120 148 96 96 128 256) }] }

theorem u8790 : Upper (D 6) (R 6) [6,9,33,80,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8791 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 88 148 288 98 226 354), lower := (rows 7 11 37 88 148 288 64 128 256), losses := [] }

theorem u8791 : Upper (D 6) (R 6) [6,9,33,80,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8791 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8792 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 88 176 34 324 452 324), lower := (rows 7 11 37 88 176 34 64 128 256), losses := [] }

theorem u8792 : Upper (D 6) (R 6) [6,9,33,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8793 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 88 176 36 322 450 322), lower := (rows 7 11 37 88 176 36 64 128 256), losses := [] }

theorem u8793 : Upper (D 6) (R 6) [6,9,33,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8794 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 88 176 96 326 390 262), lower := (rows 7 11 37 88 176 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 16 104 64 128 256), good := (rows 5 45 37 120 176 96 96 128 256) }] }

theorem u8794 : Upper (D 6) (R 6) [6,9,33,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8795 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 88 176 288 70 198 326), lower := (rows 7 11 37 88 176 288 64 128 256), losses := [] }

theorem u8795 : Upper (D 6) (R 6) [6,9,33,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8795 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8796 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 88 400 34 100 228 356), lower := (rows 7 11 37 88 400 34 64 128 256), losses := [] }

theorem u8796 : Upper (D 6) (R 6) [6,9,33,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8797 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 88 400 36 98 226 354), lower := (rows 7 11 37 88 400 36 64 128 256), losses := [] }

theorem u8797 : Upper (D 6) (R 6) [6,9,33,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8798 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 88 400 96 102 166 294), lower := (rows 7 11 37 88 400 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 16 104 64 128 256), good := (rows 5 45 37 120 400 96 96 128 256) }] }

theorem u8798 : Upper (D 6) (R 6) [6,9,33,80,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8799 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 152 84 34 352 480 352), lower := (rows 7 11 37 152 84 34 64 128 256), losses := [] }

theorem u8799 : Upper (D 6) (R 6) [6,9,33,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8800 : Route 9 := (fun mask => (mask,id))

def c8800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8800 : Upper (D 6) (R 6) [6,9,33,144,68,64] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,68,64] 13 (by decide) (choices 1) [2,32,256] r8800 c8800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u672
  · exact u673
  · exact u674

def b8801 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 152 84 288 98 226 354), lower := (rows 7 11 37 152 84 288 64 128 256), losses := [] }

theorem u8801 : Upper (D 6) (R 6) [6,9,33,144,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8801 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8802 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 152 112 34 324 452 324), lower := (rows 7 11 37 152 112 34 64 128 256), losses := [] }

theorem u8802 : Upper (D 6) (R 6) [6,9,33,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8803 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 152 112 36 322 450 322), lower := (rows 7 11 37 152 112 36 64 128 256), losses := [] }

theorem u8803 : Upper (D 6) (R 6) [6,9,33,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8804 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 152 112 96 326 390 262), lower := (rows 7 11 37 152 112 96 64 128 256), losses := [] }

theorem u8804 : Upper (D 6) (R 6) [6,9,33,144,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8805 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 152 112 288 70 198 326), lower := (rows 7 11 37 152 112 288 64 128 256), losses := [] }

theorem u8805 : Upper (D 6) (R 6) [6,9,33,144,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8805 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8806 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 152 276 34 96 224 352), lower := (rows 7 11 37 152 276 34 64 128 256), losses := [] }

theorem u8806 : Upper (D 6) (R 6) [6,9,33,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8807 : Route 9 := (fun mask => (mask,id))

def c8807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8807 : Upper (D 6) (R 6) [6,9,33,144,260,64] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,260,64] 13 (by decide) (choices 1) [2,32] r8807 c8807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u675
  · exact u676

def b8808 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 152 304 34 68 196 324), lower := (rows 7 11 37 152 304 34 64 128 256), losses := [] }

theorem u8808 : Upper (D 6) (R 6) [6,9,33,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8809 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 152 304 36 66 194 322), lower := (rows 7 11 37 152 304 36 64 128 256), losses := [] }

theorem u8809 : Upper (D 6) (R 6) [6,9,33,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8810 : Route 9 := (fun mask => (mask,id))

def c8810 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8810 : Upper (D 6) (R 6) [6,9,33,144,288,64] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,288,64] 13 (by decide) (choices 1) [2,4] r8810 c8810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u677
  · exact u678

def b8811 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 152 336 34 100 228 356), lower := (rows 7 11 37 152 336 34 64 128 256), losses := [] }

theorem u8811 : Upper (D 6) (R 6) [6,9,33,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8812 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 152 336 36 98 226 354), lower := (rows 7 11 37 152 336 36 64 128 256), losses := [] }

theorem u8812 : Upper (D 6) (R 6) [6,9,33,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8813 : Route 9 := (fun mask => (mask,id))

def c8813 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8813 : Upper (D 6) (R 6) [6,9,33,144,320,64] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,320,64] 13 (by decide) (choices 1) [2,4,32] r8813 c8813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u679
  · exact u680
  · exact u681

def b8814 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 200 84 34 368 432 304), lower := (rows 7 11 37 200 84 34 64 128 256), losses := [] }

theorem u8814 : Upper (D 6) (R 6) [6,9,33,192,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8815 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 200 84 48 354 418 290), lower := (rows 7 11 37 200 84 48 64 128 256), losses := [] }

theorem u8815 : Upper (D 6) (R 6) [6,9,33,192,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8815 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8816 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 200 84 288 114 178 306), lower := (rows 7 11 37 200 84 288 64 128 256), losses := [] }

theorem u8816 : Upper (D 6) (R 6) [6,9,33,192,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8816 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8817 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 200 112 34 340 404 276), lower := (rows 7 11 37 200 112 34 64 128 256), losses := [] }

theorem u8817 : Upper (D 6) (R 6) [6,9,33,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8818 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 200 112 36 338 402 274), lower := (rows 7 11 37 200 112 36 64 128 256), losses := [] }

theorem u8818 : Upper (D 6) (R 6) [6,9,33,192,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8819 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 37 200 112 48 326 390 262), lower := (rows 7 11 37 200 112 48 64 128 256), losses := [] }

theorem u8819 : Upper (D 6) (R 6) [6,9,33,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8819 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8819
end Delivery.IrregularNine14.P06
