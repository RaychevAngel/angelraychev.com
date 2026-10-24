import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0192

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m29760_4 : Upper (D 7) (R 7) [96,384,3,18,129,8,4] 13 :=
  permutation_upper _ _ _ [96,384,3,18,129,4,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11557

def r29760 : Route 9 := (fun mask => (mask,id))

def c29760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29760 : Upper (D 7) (R 7) [96,384,3,18,129,8] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,129,8] 13 (by decide) (choices 1) [4,32] r29760 c29760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29760_4
  · exact u11559

def b29761 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 26 145 96 108 172 300), lower := (rows 97 386 7 26 145 96 64 128 256), losses := [] }

theorem u29761 : Upper (D 7) (R 7) [96,384,3,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29762 : Route 9 := (fun mask => (mask,id))

def c29762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29762 : Upper (D 7) (R 7) [96,384,3,18,132,1] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,132,1] 13 (by decide) (choices 1) [8,32] r29762 c29762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11560
  · exact u11561

def b29763 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(2,7)], upper := (rows 97 386 7 26 148 40 97 225 353), lower := (rows 97 386 7 26 148 40 64 128 256), losses := [] }

theorem u29763 : Upper (D 7) (R 7) [96,384,3,18,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29763 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29764 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 26 148 96 105 169 297), lower := (rows 97 386 7 26 148 96 64 128 256), losses := [] }

theorem u29764 : Upper (D 7) (R 7) [96,384,3,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29765 : Route 9 := (fun mask => (mask,id))

def c29765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29765 : Upper (D 7) (R 7) [96,384,3,18,160,1] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,160,1] 13 (by decide) (choices 1) [4,8] r29765 c29765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11562
  · exact u11563

def r29766 : Route 9 := (fun mask => (mask,id))

def c29766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29766 : Upper (D 7) (R 7) [96,384,3,18,160,4] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,160,4] 13 (by decide) (choices 1) [1,8] r29766 c29766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11564
  · exact u11565

def b29767 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 386 7 26 176 40 69 197 325), lower := (rows 97 386 7 26 176 40 64 128 256), losses := [] }

theorem u29767 : Upper (D 7) (R 7) [96,384,3,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29767 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29768 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 26 176 96 77 141 269), lower := (rows 97 386 7 26 176 96 64 128 256), losses := [] }

theorem u29768 : Upper (D 7) (R 7) [96,384,3,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29769 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 386 7 28 50 33 200 200 456), lower := (rows 97 386 7 28 50 33 64 128 256), losses := [] }

theorem u29769 : Upper (D 7) (R 7) [96,384,3,20,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29770 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 386 7 28 50 40 193 193 449), lower := (rows 97 386 7 28 50 40 64 128 256), losses := [] }

theorem u29770 : Upper (D 7) (R 7) [96,384,3,20,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29770 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29771 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 28 50 96 201 137 393), lower := (rows 97 386 7 28 50 96 64 128 256), losses := [] }

theorem u29771 : Upper (D 7) (R 7) [96,384,3,20,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29772 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 97 386 7 28 50 160 73 201 329), lower := (rows 97 386 7 28 50 160 64 128 256), losses := [] }

theorem u29772 : Upper (D 7) (R 7) [96,384,3,20,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29773 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 56, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 386 7 28 56 33 194 194 450), lower := (rows 97 386 7 28 56 33 64 128 256), losses := [] }

theorem u29773 : Upper (D 7) (R 7) [96,384,3,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29774 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 97 386 7 28 56 34 193 193 449), lower := (rows 97 386 7 28 56 34 64 128 256), losses := [] }

theorem u29774 : Upper (D 7) (R 7) [96,384,3,20,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29775 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 28 56 96 195 131 387), lower := (rows 97 386 7 28 56 96 64 128 256), losses := [] }

theorem u29775 : Upper (D 7) (R 7) [96,384,3,20,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29776 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 97 386 7 28 56 160 67 195 323), lower := (rows 97 386 7 28 56 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 162 64 128 256), good := (rows 96 418 62 28 56 160 64 160 256) }] }

theorem u29776 : Upper (D 7) (R 7) [96,384,3,20,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29777 : Route 9 := (fun mask => (mask,id))

def c29777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29777 : Upper (D 7) (R 7) [96,384,3,20,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,3,20,129,2] 13 (by decide) (choices 1) [8,32] r29777 c29777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11566
  · exact u11567

theorem m29778_2 : Upper (D 7) (R 7) [96,384,3,20,129,8,2] 13 :=
  permutation_upper _ _ _ [96,384,3,20,129,2,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11566

def r29778 : Route 9 := (fun mask => (mask,id))

def c29778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29778 : Upper (D 7) (R 7) [96,384,3,20,129,8] 13 := by
  apply FastRouting.sound _ _ [96,384,3,20,129,8] 13 (by decide) (choices 1) [2,32] r29778 c29778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29778_2
  · exact u11568

def b29779 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 28 145 96 106 170 298), lower := (rows 97 386 7 28 145 96 64 128 256), losses := [] }

theorem u29779 : Upper (D 7) (R 7) [96,384,3,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29780 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 0, region := 386, targets := 1 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,0),(2,7)], upper := (rows 97 386 7 28 152 33 98 226 354), lower := (rows 97 386 7 28 152 33 64 128 256), losses := [] }

theorem u29780 : Upper (D 7) (R 7) [96,384,3,20,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29781 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 5, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,1)], upper := (rows 97 386 7 28 152 34 97 225 353), lower := (rows 97 386 7 28 152 34 64 128 256), losses := [{ target := 1, region := (rows 33 0 4 12 20 32 97 161 289), good := (rows 481 384 477 28 152 481 64 128 256) }] }

theorem u29781 : Upper (D 7) (R 7) [96,384,3,20,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29782 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 28 152 96 99 163 291), lower := (rows 97 386 7 28 152 96 64 128 256), losses := [] }

theorem u29782 : Upper (D 7) (R 7) [96,384,3,20,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29783 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 450, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 386 7 28 176 33 74 202 330), lower := (rows 97 386 7 28 176 33 64 128 256), losses := [] }

theorem u29783 : Upper (D 7) (R 7) [96,384,3,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29784 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 48, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 97 386 7 28 176 34 73 201 329), lower := (rows 97 386 7 28 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 18 38 64 128 256), good := (rows 96 434 62 60 176 50 64 128 256) },{ target := 6, region := (rows 1 2 4 12 18 38 0 128 256), good := (rows 33 434 63 60 176 50 0 128 256) }] }

theorem u29784 : Upper (D 7) (R 7) [96,384,3,20,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29785 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(0,7),(1,5),(2,5)], upper := (rows 97 386 7 28 176 40 67 195 323), lower := (rows 97 386 7 28 176 40 64 128 256), losses := [{ target := 7, region := (rows 9 2 4 8 16 40 68 0 260), good := (rows 97 258 327 381 48 41 64 0 256) }] }

theorem u29785 : Upper (D 7) (R 7) [96,384,3,20,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29785 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29786 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 28 176 96 75 139 267), lower := (rows 97 386 7 28 176 96 64 128 256), losses := [] }

theorem u29786 : Upper (D 7) (R 7) [96,384,3,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29787 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 40, targets := 192 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,6),(3,7)], upper := (rows 97 386 7 42 84 33 216 152 408), lower := (rows 97 386 7 42 84 33 64 128 256), losses := [] }

theorem u29787 : Upper (D 7) (R 7) [96,384,3,34,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29788 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 386 7 42 84 40 209 145 401), lower := (rows 97 386 7 42 84 40 64 128 256), losses := [] }

theorem u29788 : Upper (D 7) (R 7) [96,384,3,34,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29788 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29789 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 7 42 84 48 201 137 393), lower := (rows 97 386 7 42 84 48 64 128 256), losses := [] }

theorem u29789 : Upper (D 7) (R 7) [96,384,3,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29789 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29790 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 386 7 42 84 160 89 153 281), lower := (rows 97 386 7 42 84 160 64 128 256), losses := [] }

theorem u29790 : Upper (D 7) (R 7) [96,384,3,34,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29791 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 40, targets := 192 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,6),(3,7)], upper := (rows 97 386 7 42 88 33 212 148 404), lower := (rows 97 386 7 42 88 33 64 128 256), losses := [] }

theorem u29791 : Upper (D 7) (R 7) [96,384,3,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29792 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 386 7 42 88 36 209 145 401), lower := (rows 97 386 7 42 88 36 64 128 256), losses := [] }

theorem u29792 : Upper (D 7) (R 7) [96,384,3,34,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29792 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29793 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 7 42 88 48 197 133 389), lower := (rows 97 386 7 42 88 48 64 128 256), losses := [] }

theorem u29793 : Upper (D 7) (R 7) [96,384,3,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29793 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29794 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 386 7 42 88 160 85 149 277), lower := (rows 97 386 7 42 88 160 64 128 256), losses := [] }

theorem u29794 : Upper (D 7) (R 7) [96,384,3,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29795 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 386 7 42 145 36 88 216 344), lower := (rows 97 386 7 42 145 36 64 128 256), losses := [] }

theorem u29795 : Upper (D 7) (R 7) [96,384,3,34,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29795 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29796 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 386 7 42 145 40 84 212 340), lower := (rows 97 386 7 42 145 40 64 128 256), losses := [] }

theorem u29796 : Upper (D 7) (R 7) [96,384,3,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29796 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29797 : Route 9 := (fun mask => (mask,id))

def c29797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29797 : Upper (D 7) (R 7) [96,384,3,34,129,16] 13 := by
  apply FastRouting.sound _ _ [96,384,3,34,129,16] 13 (by decide) (choices 1) [4,8] r29797 c29797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11569
  · exact u11570

def b29798 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 42 145 96 92 156 284), lower := (rows 97 386 7 42 145 96 64 128 256), losses := [] }

theorem u29798 : Upper (D 7) (R 7) [96,384,3,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29799 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 40, targets := 192 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,6),(3,7)], upper := (rows 97 386 7 42 148 33 88 216 344), lower := (rows 97 386 7 42 148 33 64 128 256), losses := [] }

theorem u29799 : Upper (D 7) (R 7) [96,384,3,34,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29800 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 386 7 42 148 40 81 209 337), lower := (rows 97 386 7 42 148 40 64 128 256), losses := [] }

theorem u29800 : Upper (D 7) (R 7) [96,384,3,34,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29800 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29801 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 69, targets := 128 },{ cop := 3, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(2,7)], upper := (rows 97 386 7 42 148 48 73 201 329), lower := (rows 97 386 7 42 148 48 64 128 256), losses := [] }

theorem u29801 : Upper (D 7) (R 7) [96,384,3,34,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29801 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29802 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 42 148 96 89 153 281), lower := (rows 97 386 7 42 148 96 64 128 256), losses := [] }

theorem u29802 : Upper (D 7) (R 7) [96,384,3,34,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29803 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 40, targets := 192 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,6),(3,7)], upper := (rows 97 386 7 42 152 33 84 212 340), lower := (rows 97 386 7 42 152 33 64 128 256), losses := [] }

theorem u29803 : Upper (D 7) (R 7) [96,384,3,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29804 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 386 7 42 152 36 81 209 337), lower := (rows 97 386 7 42 152 36 64 128 256), losses := [] }

theorem u29804 : Upper (D 7) (R 7) [96,384,3,34,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29804 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29805 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 386 7 42 152 48 69 197 325), lower := (rows 97 386 7 42 152 48 64 128 256), losses := [] }

theorem u29805 : Upper (D 7) (R 7) [96,384,3,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29805 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29806 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 42 152 96 85 149 277), lower := (rows 97 386 7 42 152 96 64 128 256), losses := [] }

theorem u29806 : Upper (D 7) (R 7) [96,384,3,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29807 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 40, targets := 192 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,6),(3,7)], upper := (rows 97 386 7 42 208 33 92 156 284), lower := (rows 97 386 7 42 208 33 64 128 256), losses := [] }

theorem u29807 : Upper (D 7) (R 7) [96,384,3,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29808 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 386 7 42 208 36 89 153 281), lower := (rows 97 386 7 42 208 36 64 128 256), losses := [] }

theorem u29808 : Upper (D 7) (R 7) [96,384,3,34,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29808 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29809 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 386 7 42 208 40 85 149 277), lower := (rows 97 386 7 42 208 40 64 128 256), losses := [] }

theorem u29809 : Upper (D 7) (R 7) [96,384,3,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29809 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29810 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 7 42 208 48 77 141 269), lower := (rows 97 386 7 42 208 48 64 128 256), losses := [] }

theorem u29810 : Upper (D 7) (R 7) [96,384,3,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29810 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29811 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 7 44 88 33 210 146 402), lower := (rows 97 386 7 44 88 33 64 128 256), losses := [] }

theorem u29811 : Upper (D 7) (R 7) [96,384,3,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29812 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 7 44 88 34 209 145 401), lower := (rows 97 386 7 44 88 34 64 128 256), losses := [] }

theorem u29812 : Upper (D 7) (R 7) [96,384,3,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29813 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 7 44 88 48 195 131 387), lower := (rows 97 386 7 44 88 48 64 128 256), losses := [] }

theorem u29813 : Upper (D 7) (R 7) [96,384,3,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29813 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29814 : Route 9 := (fun mask => (mask,id))

def c29814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29814 : Upper (D 7) (R 7) [96,384,3,36,72,128] 13 := by
  apply FastRouting.sound _ _ [96,384,3,36,72,128] 13 (by decide) (choices 1) [1,2,16] r29814 c29814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11571
  · exact u11572
  · exact u11573

def b29815 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 7 44 145 34 88 216 344), lower := (rows 97 386 7 44 145 34 64 128 256), losses := [] }

theorem u29815 : Upper (D 7) (R 7) [96,384,3,36,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29816 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 386 7 44 145 40 82 210 338), lower := (rows 97 386 7 44 145 40 64 128 256), losses := [] }

theorem u29816 : Upper (D 7) (R 7) [96,384,3,36,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29816 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29817 : Route 9 := (fun mask => (mask,id))

def c29817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29817 : Upper (D 7) (R 7) [96,384,3,36,129,16] 13 := by
  apply FastRouting.sound _ _ [96,384,3,36,129,16] 13 (by decide) (choices 1) [2,8] r29817 c29817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11574
  · exact u11575

def b29818 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 44 145 96 90 154 282), lower := (rows 97 386 7 44 145 96 64 128 256), losses := [] }

theorem u29818 : Upper (D 7) (R 7) [96,384,3,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29819 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 7 44 152 33 82 210 338), lower := (rows 97 386 7 44 152 33 64 128 256), losses := [] }

theorem u29819 : Upper (D 7) (R 7) [96,384,3,36,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29819
end Delivery.IrregularNine14.P07
