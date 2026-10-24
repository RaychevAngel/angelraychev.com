import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0067
import IrregularNine14P03C0069
import IrregularNine14P03C0070
import IrregularNine14P03C0071
import IrregularNine14P03C0073
import IrregularNine14P03C0074
import IrregularNine14P03C0075
import IrregularNine14P03C0076
import IrregularNine14P03C0077
import IrregularNine14P03C0078
import IrregularNine14P03C0079

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6720 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 88 403 419 451 387 387), lower := (rows 97 14 37 88 16 32 64 128 256), losses := [] }

theorem u6720 : Upper (D 3) (R 3) [96,12,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6720
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6721 : PairBound 9 := { available := 467, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 137 467 499 467 467 467), lower := (rows 97 14 37 137 16 32 64 128 256), losses := [] }

theorem u6721 : Upper (D 3) (R 3) [96,12,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6721
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6722 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 138 465 497 465 465 465), lower := (rows 97 14 37 138 16 32 64 128 256), losses := [] }

theorem u6722 : Upper (D 3) (R 3) [96,12,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6722
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6723 : PairBound 9 := { available := 451, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 152 467 483 451 451 451), lower := (rows 97 14 37 152 16 32 64 128 256), losses := [] }

theorem u6723 : Upper (D 3) (R 3) [96,12,33,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6723
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6724 : PairBound 9 := { available := 403, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 200 403 435 467 403 403), lower := (rows 97 14 37 200 16 32 64 128 256), losses := [] }

theorem u6724 : Upper (D 3) (R 3) [96,12,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6724
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6725 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 265 211 243 211 211 467), lower := (rows 97 14 37 265 16 32 64 128 256), losses := [] }

theorem u6725 : Upper (D 3) (R 3) [96,12,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6725
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6726 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 266 209 241 209 209 465), lower := (rows 97 14 37 266 16 32 64 128 256), losses := [] }

theorem u6726 : Upper (D 3) (R 3) [96,12,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6726
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6727 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 280 211 227 195 195 451), lower := (rows 97 14 37 280 16 32 64 128 256), losses := [] }

theorem u6727 : Upper (D 3) (R 3) [96,12,33,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6727
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6728 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 328 147 179 211 147 403), lower := (rows 97 14 37 328 16 32 64 128 256), losses := [] }

theorem u6728 : Upper (D 3) (R 3) [96,12,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6728
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6729 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 392 211 243 211 211 467), lower := (rows 97 14 37 392 16 32 64 128 256), losses := [] }

theorem u6729 : Upper (D 3) (R 3) [96,12,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6729
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6730 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 88 401 417 449 385 385), lower := (rows 97 14 38 88 16 32 64 128 256), losses := [] }

theorem u6730 : Upper (D 3) (R 3) [96,12,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6730
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6731 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 137 465 497 465 465 465), lower := (rows 97 14 38 137 16 32 64 128 256), losses := [] }

theorem u6731 : Upper (D 3) (R 3) [96,12,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6731
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6732 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 152 465 481 449 449 449), lower := (rows 97 14 38 152 16 32 64 128 256), losses := [] }

theorem u6732 : Upper (D 3) (R 3) [96,12,34,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6732
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6733 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 200 401 433 465 401 401), lower := (rows 97 14 38 200 16 32 64 128 256), losses := [] }

theorem u6733 : Upper (D 3) (R 3) [96,12,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6733
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6734 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 265 209 241 209 209 465), lower := (rows 97 14 38 265 16 32 64 128 256), losses := [] }

theorem u6734 : Upper (D 3) (R 3) [96,12,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6734
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6735 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 280 209 225 193 193 449), lower := (rows 97 14 38 280 16 32 64 128 256), losses := [] }

theorem u6735 : Upper (D 3) (R 3) [96,12,34,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6735
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6736 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 328 145 177 209 145 401), lower := (rows 97 14 38 328 16 32 64 128 256), losses := [] }

theorem u6736 : Upper (D 3) (R 3) [96,12,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6736
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6737 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 392 209 241 209 209 465), lower := (rows 97 14 38 392 16 32 64 128 256), losses := [] }

theorem u6737 : Upper (D 3) (R 3) [96,12,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6737
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6738_3 : Upper (D 3) (R 3) [96,12,48,129,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4143

def r6738 : Route 9 := (fun mask => (mask,id))

def c6738 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6738 : Upper (D 3) (R 3) [96,12,48,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r6738 c6738
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6738_3
  · exact u4641
  · exact u4642
  · exact u4643
  · exact u4644
  · exact u4645
  · exact u4646
  · exact u4647
  · exact u4648
  · exact u4649

def b6739 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 52 138 465 481 449 449 449), lower := (rows 97 14 52 138 16 32 64 128 256), losses := [] }

theorem u6739 : Upper (D 3) (R 3) [96,12,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6739
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6740_3 : Upper (D 3) (R 3) [96,12,48,192,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4144

def r6740 : Route 9 := (fun mask => (mask,id))

def c6740 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6740 : Upper (D 3) (R 3) [96,12,48,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r6740 c6740
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6740_3
  · exact u4655
  · exact u4656
  · exact u4657
  · exact u4658
  · exact u4659

theorem m6741_3 : Upper (D 3) (R 3) [96,12,48,257,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4145

def r6741 : Route 9 := (fun mask => (mask,id))

def c6741 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6741 : Upper (D 3) (R 3) [96,12,48,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r6741 c6741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6741_3
  · exact u4660
  · exact u4661
  · exact u4662
  · exact u4663
  · exact u4664

def b6742 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 52 266 209 225 193 193 449), lower := (rows 97 14 52 266 16 32 64 128 256), losses := [] }

theorem u6742 : Upper (D 3) (R 3) [96,12,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6742
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6743_3 : Upper (D 3) (R 3) [96,12,48,320,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4146

def r6743 : Route 9 := (fun mask => (mask,id))

def c6743 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6743 : Upper (D 3) (R 3) [96,12,48,320] 13 := by
  apply FastRouting.sound _ _ [96,12,48,320] 13 (by decide) (choices 2) [3,129,130] r6743 c6743
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6743_3
  · exact u4667
  · exact u4668

theorem m6744_3 : Upper (D 3) (R 3) [96,12,48,384,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4147

def r6744 : Route 9 := (fun mask => (mask,id))

def c6744 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6744 : Upper (D 3) (R 3) [96,12,48,384] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r6744 c6744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6744_3
  · exact u4669
  · exact u4670
  · exact u4671
  · exact u4672
  · exact u4673

def b6745 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 403 435 467 403 403), lower := (rows 97 14 100 137 16 32 64 128 256), losses := [] }

theorem u6745 : Upper (D 3) (R 3) [96,12,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6745
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6746 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 138 401 433 465 401 401), lower := (rows 97 14 100 138 16 32 64 128 256), losses := [] }

theorem u6746 : Upper (D 3) (R 3) [96,12,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6746
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6747 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 152 403 419 451 387 387), lower := (rows 97 14 100 152 16 32 64 128 256), losses := [] }

theorem u6747 : Upper (D 3) (R 3) [96,12,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6747
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6748 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 265 147 179 211 147 403), lower := (rows 97 14 100 265 16 32 64 128 256), losses := [] }

theorem u6748 : Upper (D 3) (R 3) [96,12,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6748
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6749 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 266 145 177 209 145 401), lower := (rows 97 14 100 266 16 32 64 128 256), losses := [] }

theorem u6749 : Upper (D 3) (R 3) [96,12,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6749
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6750 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 280 147 163 195 131 387), lower := (rows 97 14 100 280 16 32 64 128 256), losses := [] }

theorem u6750 : Upper (D 3) (R 3) [96,12,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6750
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6751 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 392 147 179 211 147 403), lower := (rows 97 14 100 392 16 32 64 128 256), losses := [] }

theorem u6751 : Upper (D 3) (R 3) [96,12,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6751
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6752 : PairBound 9 := { available := 371, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 371 371 371 499 371), lower := (rows 97 14 133 137 16 32 64 128 256), losses := [] }

theorem u6752 : Upper (D 3) (R 3) [96,12,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6752
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6753 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 133 138 369 369 369 497 369), lower := (rows 97 14 133 138 16 32 64 128 256), losses := [] }

theorem u6753 : Upper (D 3) (R 3) [96,12,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6753
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6754 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 371 355 355 483 355), lower := (rows 97 14 133 152 16 32 64 128 256), losses := [] }

theorem u6754 : Upper (D 3) (R 3) [96,12,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6754
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6755 : PairBound 9 := { available := 339, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 339 371 339 467 339), lower := (rows 97 14 133 168 16 32 64 128 256), losses := [] }

theorem u6755 : Upper (D 3) (R 3) [96,12,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6755
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6756_3 : Upper (D 3) (R 3) [96,12,129,257,3] 13 :=
  permutation_upper _ _ _ [96,5,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4156

def r6756 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6756 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6756 : Upper (D 3) (R 3) [96,12,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r6756 c6756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6756_3
  · exact u4700
  · exact u4701
  · exact u4702
  · exact u4703
  · exact u4704
  · exact u4705

def r6757 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6757 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6757 : Upper (D 3) (R 3) [96,12,129,258] 13 := by
  apply FastRouting.sound _ _ [96,12,129,258] 13 (by decide) (choices 2) [33,96,129,160] r6757 c6757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4706
  · exact u4707
  · exact u4708
  · exact u4709

theorem m6758_3 : Upper (D 3) (R 3) [96,12,129,272,3] 13 :=
  permutation_upper _ _ _ [96,5,24,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4157

def r6758 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6758 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6758 : Upper (D 3) (R 3) [96,12,129,272] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r6758 c6758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6758_3
  · exact u4710
  · exact u4711
  · exact u4712
  · exact u4713
  · exact u4714
  · exact u4715

theorem m6759_3 : Upper (D 3) (R 3) [96,12,129,288,3] 13 :=
  permutation_upper _ _ _ [96,5,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4158

def r6759 : Route 9 := (fun mask => (mask,id))

def c6759 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6759 : Upper (D 3) (R 3) [96,12,129,288] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r6759 c6759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6759_3
  · exact u4716
  · exact u4717
  · exact u4718
  · exact u4719
  · exact u4720

def b6760 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 392 115 115 115 243 371), lower := (rows 97 14 133 392 16 32 64 128 256), losses := [] }

theorem u6760 : Upper (D 3) (R 3) [96,12,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6760
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6761 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 152 369 353 353 481 353), lower := (rows 97 14 134 152 16 32 64 128 256), losses := [] }

theorem u6761 : Upper (D 3) (R 3) [96,12,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6761
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6762 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 168 337 369 337 465 337), lower := (rows 97 14 134 168 16 32 64 128 256), losses := [] }

theorem u6762 : Upper (D 3) (R 3) [96,12,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6762
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6763 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6763 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6763 : Upper (D 3) (R 3) [96,12,130,257] 13 := by
  apply FastRouting.sound _ _ [96,12,130,257] 13 (by decide) (choices 2) [33,96,129,160] r6763 c6763
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4726
  · exact u4727
  · exact u4728
  · exact u4729

def r6764 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6764 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6764 : Upper (D 3) (R 3) [96,12,130,272] 13 := by
  apply FastRouting.sound _ _ [96,12,130,272] 13 (by decide) (choices 2) [33,96,129,160] r6764 c6764
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4730
  · exact u4731
  · exact u4732
  · exact u4733

def b6765 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 134 296 209 241 209 209 465), lower := (rows 97 14 134 296 16 32 64 128 256), losses := [] }

theorem u6765 : Upper (D 3) (R 3) [96,12,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6765
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6766 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 392 113 113 113 241 369), lower := (rows 97 14 134 392 16 32 64 128 256), losses := [] }

theorem u6766 : Upper (D 3) (R 3) [96,12,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6766
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6767 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 339 355 323 451 323), lower := (rows 97 14 148 168 16 32 64 128 256), losses := [] }

theorem u6767 : Upper (D 3) (R 3) [96,12,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6767
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6768_3 : Upper (D 3) (R 3) [96,12,144,257,3] 13 :=
  permutation_upper _ _ _ [96,5,24,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4161

def r6768 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6768 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6768 : Upper (D 3) (R 3) [96,12,144,257] 13 := by
  apply FastRouting.sound _ _ [96,12,144,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r6768 c6768
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6768_3
  · exact u4740
  · exact u4741
  · exact u4742
  · exact u4743
  · exact u4744
  · exact u4745

def r6769 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6769 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6769 : Upper (D 3) (R 3) [96,12,144,258] 13 := by
  apply FastRouting.sound _ _ [96,12,144,258] 13 (by decide) (choices 2) [33,96,129,160] r6769 c6769
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4746
  · exact u4747
  · exact u4748
  · exact u4749

theorem m6770_3 : Upper (D 3) (R 3) [96,12,144,288,3] 13 :=
  permutation_upper _ _ _ [96,5,24,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4162

def r6770 : Route 9 := (fun mask => (mask,id))

def c6770 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6770 : Upper (D 3) (R 3) [96,12,144,288] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r6770 c6770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6770_3
  · exact u4750
  · exact u4751
  · exact u4752
  · exact u4753
  · exact u4754

def b6771 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 392 115 99 99 227 355), lower := (rows 97 14 148 392 16 32 64 128 256), losses := [] }

theorem u6771 : Upper (D 3) (R 3) [96,12,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6771
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6772 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 200 275 307 339 403 275), lower := (rows 97 14 164 200 16 32 64 128 256), losses := [] }

theorem u6772 : Upper (D 3) (R 3) [96,12,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6772
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6773_3 : Upper (D 3) (R 3) [96,12,160,257,3] 13 :=
  permutation_upper _ _ _ [96,5,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4165

def r6773 : Route 9 := (fun mask => (mask,id))

def c6773 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6773 : Upper (D 3) (R 3) [96,12,160,257] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r6773 c6773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6773_3
  · exact u4758
  · exact u4759
  · exact u4760
  · exact u4761
  · exact u4762

def b6774 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 164 266 209 241 209 209 465), lower := (rows 97 14 164 266 16 32 64 128 256), losses := [] }

theorem u6774 : Upper (D 3) (R 3) [96,12,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6774
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6775_3 : Upper (D 3) (R 3) [96,12,160,272,3] 13 :=
  permutation_upper _ _ _ [96,5,24,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4166

def r6775 : Route 9 := (fun mask => (mask,id))

def c6775 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6775 : Upper (D 3) (R 3) [96,12,160,272] 13 := by
  apply FastRouting.sound _ _ [96,12,160,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r6775 c6775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6775_3
  · exact u4765
  · exact u4766
  · exact u4767
  · exact u4768
  · exact u4769

theorem m6776_3 : Upper (D 3) (R 3) [96,12,160,320,3] 13 :=
  permutation_upper _ _ _ [96,5,24,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4167

def r6776 : Route 9 := (fun mask => (mask,id))

def c6776 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6776 : Upper (D 3) (R 3) [96,12,160,320] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320] 13 (by decide) (choices 2) [3,129,130] r6776 c6776
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6776_3
  · exact u4770
  · exact u4771

def b6777 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 392 83 115 83 211 339), lower := (rows 97 14 164 392 16 32 64 128 256), losses := [] }

theorem u6777 : Upper (D 3) (R 3) [96,12,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6777
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6778_9 : Upper (D 3) (R 3) [96,17,34,68,9] 13 :=
  permutation_upper _ _ _ [96,5,9,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4043

theorem m6778_129 : Upper (D 3) (R 3) [96,17,34,68,129] 13 :=
  permutation_upper _ _ _ [96,5,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4313

theorem m6778_136 : Upper (D 3) (R 3) [96,17,34,68,136] 13 :=
  permutation_upper _ _ _ [96,5,136,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4396

theorem m6778_257 : Upper (D 3) (R 3) [96,17,34,68,257] 13 :=
  permutation_upper _ _ _ [96,5,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4480

theorem m6778_264 : Upper (D 3) (R 3) [96,17,34,68,264] 13 :=
  permutation_upper _ _ _ [96,5,264,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4517

theorem m6778_384 : Upper (D 3) (R 3) [96,17,34,68,384] 13 :=
  permutation_upper _ _ _ [96,5,384,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4564

def r6778 : Route 9 := (fun mask => (mask,id))

def c6778 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6778 : Upper (D 3) (R 3) [96,17,34,68] 13 := by
  apply FastRouting.sound _ _ [96,17,34,68] 13 (by decide) (choices 2) [9,129,136,257,264,384] r6778 c6778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6778_9
  · exact m6778_129
  · exact m6778_136
  · exact m6778_257
  · exact m6778_264
  · exact m6778_384

theorem m6779_5 : Upper (D 3) (R 3) [96,17,34,129,5] 13 :=
  permutation_upper _ _ _ [96,5,9,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4038

theorem m6779_9 : Upper (D 3) (R 3) [96,17,34,129,9] 13 :=
  permutation_upper _ _ _ [96,5,9,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4051

theorem m6779_12 : Upper (D 3) (R 3) [96,17,34,129,12] 13 :=
  permutation_upper _ _ _ [96,5,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4143

theorem m6779_65 : Upper (D 3) (R 3) [96,17,34,129,65] 13 :=
  permutation_upper _ _ _ [96,5,33,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4181

theorem m6779_68 : Upper (D 3) (R 3) [96,17,34,129,68] 13 :=
  permutation_upper _ _ _ [96,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4235

theorem m6779_72 : Upper (D 3) (R 3) [96,17,34,129,72] 13 :=
  permutation_upper _ _ _ [96,5,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4243

theorem m6779_129 : Upper (D 3) (R 3) [96,17,34,129,129] 13 :=
  permutation_upper _ _ _ [96,5,129,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4314

theorem m6779_132 : Upper (D 3) (R 3) [96,17,34,129,132] 13 :=
  permutation_upper _ _ _ [96,5,136,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4391

theorem m6779_136 : Upper (D 3) (R 3) [96,17,34,129,136] 13 :=
  permutation_upper _ _ _ [96,5,136,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4408

theorem m6779_192 : Upper (D 3) (R 3) [96,17,34,129,192] 13 :=
  permutation_upper _ _ _ [96,5,160,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4453

theorem m6779_257 : Upper (D 3) (R 3) [96,17,34,129,257] 13 :=
  permutation_upper _ _ _ [96,5,257,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4481

theorem m6779_260 : Upper (D 3) (R 3) [96,17,34,129,260] 13 :=
  permutation_upper _ _ _ [96,5,264,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4515

theorem m6779_264 : Upper (D 3) (R 3) [96,17,34,129,264] 13 :=
  permutation_upper _ _ _ [96,5,264,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4524

theorem m6779_320 : Upper (D 3) (R 3) [96,17,34,129,320] 13 :=
  permutation_upper _ _ _ [96,5,288,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4546

theorem m6779_384 : Upper (D 3) (R 3) [96,17,34,129,384] 13 :=
  permutation_upper _ _ _ [96,5,384,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4565

def r6779 : Route 9 := (fun mask => (mask,id))

def c6779 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6779 : Upper (D 3) (R 3) [96,17,34,129] 13 := by
  apply FastRouting.sound _ _ [96,17,34,129] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192,257,260,264,320,384] r6779 c6779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6779_5
  · exact m6779_9
  · exact m6779_12
  · exact m6779_65
  · exact m6779_68
  · exact m6779_72
  · exact m6779_129
  · exact m6779_132
  · exact m6779_136
  · exact m6779_192
  · exact m6779_257
  · exact m6779_260
  · exact m6779_264
  · exact m6779_320
  · exact m6779_384

#print axioms u6779
end Delivery.IrregularNine14.P03
