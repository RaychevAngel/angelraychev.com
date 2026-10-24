import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0109
import IrregularNine14P08C0110

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17760 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 152 148 35 99 163 291), lower := (rows 289 67 76 152 148 32 64 128 256), losses := [] }

theorem u17760 : Upper (D 8) (R 8) [288,65,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17761 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 152 176 39 103 167 295), lower := (rows 289 67 76 152 176 32 64 128 256), losses := [] }

theorem u17761 : Upper (D 8) (R 8) [288,65,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17762 : Route 9 := (fun mask => (mask,id))

def c17762 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17762 : Upper (D 8) (R 8) [288,65,72,160,129] 13 := by
  apply FastRouting.sound _ _ [288,65,72,160,129] 13 (by decide) (choices 1) [2,4,16] r17762 c17762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6597
  · exact u6598
  · exact u6599

def r17763 : Route 9 := (fun mask => (mask,id))

def c17763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17763 : Upper (D 8) (R 8) [288,65,72,160,130] 13 := by
  apply FastRouting.sound _ _ [288,65,72,160,130] 13 (by decide) (choices 1) [1,4,16] r17763 c17763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6600
  · exact u6601
  · exact u6602

def b17764 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 168 148 51 115 179 307), lower := (rows 289 67 76 168 148 32 64 128 256), losses := [] }

theorem u17764 : Upper (D 8) (R 8) [288,65,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17765 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 67 76 168 176 55 87 151 279), lower := (rows 289 67 76 168 176 32 64 128 256), losses := [] }

theorem u17765 : Upper (D 8) (R 8) [288,65,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17766_8 : Upper (D 8) (R 8) [288,65,96,129,160,8] 13 :=
  permutation_upper _ _ _ [288,65,96,129,160,2] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6603

theorem m17766_16 : Upper (D 8) (R 8) [288,65,96,129,160,16] 13 :=
  permutation_upper _ _ _ [288,65,96,129,160,4] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6604

def r17766 : Route 9 := (fun mask => (mask,id))

def c17766 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17766 : Upper (D 8) (R 8) [288,65,96,129,160] 13 := by
  apply FastRouting.sound _ _ [288,65,96,129,160] 13 (by decide) (choices 1) [2,4,8,16] r17766 c17766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6603
  · exact u6604
  · exact m17766_8
  · exact m17766_16

def r17767 : Route 9 := (fun mask => (mask,id))

def c17767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17767 : Upper (D 8) (R 8) [288,65,96,130,132] 13 := by
  apply FastRouting.sound _ _ [288,65,96,130,132] 13 (by decide) (choices 1) [1,8,16] r17767 c17767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6605
  · exact u6606
  · exact u6607

def b17768 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 67 100 138 152 53 117 181 309), lower := (rows 289 67 100 138 152 32 64 128 256), losses := [] }

theorem u17768 : Upper (D 8) (R 8) [288,65,96,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17769 : Route 9 := (fun mask => (mask,id))

def c17769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17769 : Upper (D 8) (R 8) [288,65,96,130,160] 13 := by
  apply FastRouting.sound _ _ [288,65,96,130,160] 13 (by decide) (choices 1) [1,4,8,16] r17769 c17769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6608
  · exact u6609
  · exact u6610
  · exact u6611

def b17770 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 67 100 140 152 51 115 179 307), lower := (rows 289 67 100 140 152 32 64 128 256), losses := [] }

theorem u17770 : Upper (D 8) (R 8) [288,65,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17771 : Route 9 := (fun mask => (mask,id))

def c17771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17771 : Upper (D 8) (R 8) [288,65,96,132,160] 13 := by
  apply FastRouting.sound _ _ [288,65,96,132,160] 13 (by decide) (choices 1) [1,2,8,16] r17771 c17771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6612
  · exact u6613
  · exact u6614
  · exact u6615

def b17772 : PairBound 9 := { available := 39, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 67 100 152 152 39 103 167 295), lower := (rows 289 67 100 152 152 32 64 128 256), losses := [] }

theorem u17772 : Upper (D 8) (R 8) [288,65,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17773 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 100 152 176 47 79 143 271), lower := (rows 289 67 100 152 176 32 64 128 256), losses := [] }

theorem u17773 : Upper (D 8) (R 8) [288,65,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17774 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 76 138 176 49 113 177 305), lower := (rows 289 70 76 138 176 32 64 128 256), losses := [] }

theorem u17774 : Upper (D 8) (R 8) [288,68,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17775 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 76 168 146 49 113 177 305), lower := (rows 289 70 76 168 146 32 64 128 256), losses := [] }

theorem u17775 : Upper (D 8) (R 8) [288,68,72,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17776 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 100 138 176 57 89 153 281), lower := (rows 289 70 100 138 176 32 64 128 256), losses := [] }

theorem u17776 : Upper (D 8) (R 8) [288,68,96,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17777 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 134 88 176 41 105 169 297), lower := (rows 289 70 134 88 176 32 64 128 256), losses := [] }

theorem u17777 : Upper (D 8) (R 8) [288,68,130,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17778 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 134 104 176 57 89 153 281), lower := (rows 289 70 134 104 176 32 64 128 256), losses := [] }

theorem u17778 : Upper (D 8) (R 8) [288,68,130,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17779 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 140 88 176 35 99 163 291), lower := (rows 289 70 140 88 176 32 64 128 256), losses := [] }

theorem u17779 : Upper (D 8) (R 8) [288,68,136,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17780 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 140 104 176 51 83 147 275), lower := (rows 289 70 140 104 176 32 64 128 256), losses := [] }

theorem u17780 : Upper (D 8) (R 8) [288,68,136,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17781 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 70 164 88 176 43 75 139 267), lower := (rows 289 70 164 88 176 32 64 128 256), losses := [] }

theorem u17781 : Upper (D 8) (R 8) [288,68,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17782_16 : Upper (D 8) (R 8) [288,68,160,96,136,16] 13 :=
  permutation_upper _ _ _ [288,68,160,96,136,2] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6617

def r17782 : Route 9 := (fun mask => (mask,id))

def c17782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17782 : Upper (D 8) (R 8) [288,68,160,96,136] 13 := by
  apply FastRouting.sound _ _ [288,68,160,96,136] 13 (by decide) (choices 1) [1,2,16] r17782 c17782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6616
  · exact u6617
  · exact m17782_16

def b17783 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 56 152 224 224 224 480), lower := (rows 321 7 7 56 152 32 64 128 256), losses := [] }

theorem u17783 : Upper (D 8) (R 8) [320,5,3,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17784 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 56 208 168 232 168 424), lower := (rows 321 7 7 56 208 32 64 128 256), losses := [] }

theorem u17784 : Upper (D 8) (R 8) [320,5,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17785 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 88 176 168 232 168 424), lower := (rows 321 7 7 88 176 32 64 128 256), losses := [] }

theorem u17785 : Upper (D 8) (R 8) [320,5,3,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17786 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 104 152 176 240 176 432), lower := (rows 321 7 7 104 152 32 64 128 256), losses := [] }

theorem u17786 : Upper (D 8) (R 8) [320,5,3,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17787 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 104 176 184 248 184 440), lower := (rows 321 7 7 104 176 32 64 128 256), losses := [] }

theorem u17787 : Upper (D 8) (R 8) [320,5,3,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17788 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 168 208 56 120 184 312), lower := (rows 321 7 7 168 208 32 64 128 256), losses := [] }

theorem u17788 : Upper (D 8) (R 8) [320,5,3,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17789 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 26 112 160 224 160 416), lower := (rows 321 7 13 26 112 32 64 128 256), losses := [] }

theorem u17789 : Upper (D 8) (R 8) [320,5,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17790 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 26 176 224 224 224 480), lower := (rows 321 7 13 26 176 32 64 128 256), losses := [] }

theorem u17790 : Upper (D 8) (R 8) [320,5,9,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17791 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 26 208 160 224 160 416), lower := (rows 321 7 13 26 208 32 64 128 256), losses := [] }

theorem u17791 : Upper (D 8) (R 8) [320,5,9,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17792 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 42 112 176 240 176 432), lower := (rows 321 7 13 42 112 32 64 128 256), losses := [] }

theorem u17792 : Upper (D 8) (R 8) [320,5,9,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17793 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 42 176 240 240 240 496), lower := (rows 321 7 13 42 176 32 64 128 256), losses := [] }

theorem u17793 : Upper (D 8) (R 8) [320,5,9,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17794 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 42 208 176 240 176 432), lower := (rows 321 7 13 42 208 32 64 128 256), losses := [] }

theorem u17794 : Upper (D 8) (R 8) [320,5,9,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17795 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 56 82 160 224 160 416), lower := (rows 321 7 13 56 82 32 64 128 256), losses := [] }

theorem u17795 : Upper (D 8) (R 8) [320,5,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17796 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 56 146 224 224 224 480), lower := (rows 321 7 13 56 146 32 64 128 256), losses := [] }

theorem u17796 : Upper (D 8) (R 8) [320,5,9,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17797 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 56 208 162 226 162 418), lower := (rows 321 7 13 56 208 32 64 128 256), losses := [] }

theorem u17797 : Upper (D 8) (R 8) [320,5,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17798 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 74 176 176 240 176 432), lower := (rows 321 7 13 74 176 32 64 128 256), losses := [] }

theorem u17798 : Upper (D 8) (R 8) [320,5,9,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17799 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 88 50 160 224 160 416), lower := (rows 321 7 13 88 50 32 64 128 256), losses := [] }

theorem u17799 : Upper (D 8) (R 8) [320,5,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17800 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 88 146 160 224 160 416), lower := (rows 321 7 13 88 146 32 64 128 256), losses := [] }

theorem u17800 : Upper (D 8) (R 8) [320,5,9,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17801 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 88 176 162 226 162 418), lower := (rows 321 7 13 88 176 32 64 128 256), losses := [] }

theorem u17801 : Upper (D 8) (R 8) [320,5,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17802 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 104 50 176 240 176 432), lower := (rows 321 7 13 104 50 32 64 128 256), losses := [] }

theorem u17802 : Upper (D 8) (R 8) [320,5,9,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17803 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 104 146 176 240 176 432), lower := (rows 321 7 13 104 146 32 64 128 256), losses := [] }

theorem u17803 : Upper (D 8) (R 8) [320,5,9,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17804 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 104 176 178 242 178 434), lower := (rows 321 7 13 104 176 32 64 128 256), losses := [] }

theorem u17804 : Upper (D 8) (R 8) [320,5,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17805 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 138 112 176 240 176 432), lower := (rows 321 7 13 138 112 32 64 128 256), losses := [] }

theorem u17805 : Upper (D 8) (R 8) [320,5,9,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17806 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 138 176 112 112 240 368), lower := (rows 321 7 13 138 176 32 64 128 256), losses := [] }

theorem u17806 : Upper (D 8) (R 8) [320,5,9,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17807 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 138 208 48 112 176 304), lower := (rows 321 7 13 138 208 32 64 128 256), losses := [] }

theorem u17807 : Upper (D 8) (R 8) [320,5,9,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17808 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 152 50 224 224 224 480), lower := (rows 321 7 13 152 50 32 64 128 256), losses := [] }

theorem u17808 : Upper (D 8) (R 8) [320,5,9,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17809 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 152 82 160 224 160 416), lower := (rows 321 7 13 152 82 32 64 128 256), losses := [] }

theorem u17809 : Upper (D 8) (R 8) [320,5,9,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17810 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 152 112 162 226 162 418), lower := (rows 321 7 13 152 112 32 64 128 256), losses := [] }

theorem u17810 : Upper (D 8) (R 8) [320,5,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17811 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 168 50 240 240 240 496), lower := (rows 321 7 13 168 50 32 64 128 256), losses := [] }

theorem u17811 : Upper (D 8) (R 8) [320,5,9,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17812 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 168 82 176 240 176 432), lower := (rows 321 7 13 168 82 32 64 128 256), losses := [] }

theorem u17812 : Upper (D 8) (R 8) [320,5,9,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17813 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 168 112 178 242 178 434), lower := (rows 321 7 13 168 112 32 64 128 256), losses := [] }

theorem u17813 : Upper (D 8) (R 8) [320,5,9,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17814 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 168 146 112 112 240 368), lower := (rows 321 7 13 168 146 32 64 128 256), losses := [] }

theorem u17814 : Upper (D 8) (R 8) [320,5,9,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17815 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 168 208 50 114 178 306), lower := (rows 321 7 13 168 208 32 64 128 256), losses := [] }

theorem u17815 : Upper (D 8) (R 8) [320,5,9,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17816 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 200 50 176 240 176 432), lower := (rows 321 7 13 200 50 32 64 128 256), losses := [] }

theorem u17816 : Upper (D 8) (R 8) [320,5,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17817 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 200 146 48 112 176 304), lower := (rows 321 7 13 200 146 32 64 128 256), losses := [] }

theorem u17817 : Upper (D 8) (R 8) [320,5,9,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17818 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 200 176 50 114 178 306), lower := (rows 321 7 13 200 176 32 64 128 256), losses := [] }

theorem u17818 : Upper (D 8) (R 8) [320,5,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17819 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 25 112 160 224 160 416), lower := (rows 321 7 14 25 112 32 64 128 256), losses := [] }

theorem u17819 : Upper (D 8) (R 8) [320,5,10,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17819
end Delivery.IrregularNine14.P08
