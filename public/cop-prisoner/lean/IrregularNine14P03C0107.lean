import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0063
import IrregularNine14P03C0064
import IrregularNine14P03C0065

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6420 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 262 13 41 209 241 209 209 465), lower := (rows 35 262 13 41 16 32 64 128 256), losses := [] }

theorem u6420 : Upper (D 3) (R 3) [34,260,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6420
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6421 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 13 56 209 225 193 193 449), lower := (rows 35 262 13 56 16 32 64 128 256), losses := [] }

theorem u6421 : Upper (D 3) (R 3) [34,260,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6421
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6422 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 13 73 241 241 241 241 497), lower := (rows 35 262 13 73 16 32 64 128 256), losses := [] }

theorem u6422 : Upper (D 3) (R 3) [34,260,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6422
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6423 : Route 9 := (fun mask => (mask,id))

def c6423 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6423 : Upper (D 3) (R 3) [34,260,9,80] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6423 c6423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3791
  · exact u3792
  · exact u3793
  · exact u3794
  · exact u3795
  · exact u3796

def b6424 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 13 104 209 241 209 209 465), lower := (rows 35 262 13 104 16 32 64 128 256), losses := [] }

theorem u6424 : Upper (D 3) (R 3) [34,260,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6424
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6425 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6425 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6425 : Upper (D 3) (R 3) [34,260,9,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192] 13 (by decide) (choices 2) [33,65,96,192] r6425 c6425
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3797
  · exact u3798
  · exact u3799
  · exact u3800

def b6426 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 28 41 209 225 193 193 449), lower := (rows 35 262 28 41 16 32 64 128 256), losses := [] }

theorem u6426 : Upper (D 3) (R 3) [34,260,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6426
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6427_33 : Upper (D 3) (R 3) [34,260,24,65,33] 13 :=
  permutation_upper _ _ _ [34,260,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3801

def r6427 : Route 9 := (fun mask => (mask,id))

def c6427 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6427 : Upper (D 3) (R 3) [34,260,24,65] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6427 c6427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6427_33
  · exact u3803
  · exact u3804
  · exact u3805
  · exact u3806
  · exact u3807

def b6428 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 28 104 209 225 193 193 449), lower := (rows 35 262 28 104 16 32 64 128 256), losses := [] }

theorem u6428 : Upper (D 3) (R 3) [34,260,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6428
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6429_33 : Upper (D 3) (R 3) [34,260,24,192,33] 13 :=
  permutation_upper _ _ _ [34,260,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3802

theorem m6429_65 : Upper (D 3) (R 3) [34,260,24,192,65] 13 :=
  permutation_upper _ _ _ [34,260,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3807

theorem m6429_96 : Upper (D 3) (R 3) [34,260,24,192,96] 13 :=
  permutation_upper _ _ _ [34,260,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3808

def r6429 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6429 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6429 : Upper (D 3) (R 3) [34,260,24,192] 13 := by
  apply FastRouting.sound _ _ [34,260,24,192] 13 (by decide) (choices 2) [33,65,96,192] r6429 c6429
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m6429_33
  · exact m6429_65
  · exact m6429_96
  · exact u3809

def r6430 : Route 9 := (fun mask => (mask,id))

def c6430 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6430 : Upper (D 3) (R 3) [34,260,65,17] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6430 c6430
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3810
  · exact u3811
  · exact u3812
  · exact u3813
  · exact u3814
  · exact u3815
  · exact u3816
  · exact u3817
  · exact u3818
  · exact u3819

def b6431 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 41 217 249 217 217 473), lower := (rows 35 262 69 41 16 32 64 128 256), losses := [] }

theorem u6431 : Upper (D 3) (R 3) [34,260,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6431
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6432_9 : Upper (D 3) (R 3) [34,260,65,48,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3812

def r6432 : Route 9 := (fun mask => (mask,id))

def c6432 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6432 : Upper (D 3) (R 3) [34,260,65,48] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6432 c6432
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6432_9
  · exact u3824
  · exact u3825
  · exact u3826
  · exact u3827
  · exact u3828

def b6433 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 73 185 185 249 185 441), lower := (rows 35 262 69 73 16 32 64 128 256), losses := [] }

theorem u6433 : Upper (D 3) (R 3) [34,260,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6433
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6434_9 : Upper (D 3) (R 3) [34,260,65,80,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3814

theorem m6434_33 : Upper (D 3) (R 3) [34,260,65,80,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3820

theorem m6434_40 : Upper (D 3) (R 3) [34,260,65,80,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3825

def r6434 : Route 9 := (fun mask => (mask,id))

def c6434 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6434 : Upper (D 3) (R 3) [34,260,65,80] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6434 c6434
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6434_9
  · exact m6434_33
  · exact m6434_40
  · exact u3832
  · exact u3833
  · exact u3834

theorem m6435_9 : Upper (D 3) (R 3) [34,260,65,96,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3815

def r6435 : Route 9 := (fun mask => (mask,id))

def c6435 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6435 : Upper (D 3) (R 3) [34,260,65,96] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96] 13 (by decide) (choices 2) [9,129,136] r6435 c6435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6435_9
  · exact u3835
  · exact u3836

theorem m6436_9 : Upper (D 3) (R 3) [34,260,65,129,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3816

theorem m6436_33 : Upper (D 3) (R 3) [34,260,65,129,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3821

theorem m6436_40 : Upper (D 3) (R 3) [34,260,65,129,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3826

theorem m6436_65 : Upper (D 3) (R 3) [34,260,65,129,65] 13 :=
  permutation_upper _ _ _ [34,260,65,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3829

theorem m6436_72 : Upper (D 3) (R 3) [34,260,65,129,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3832

theorem m6436_96 : Upper (D 3) (R 3) [34,260,65,129,96] 13 :=
  permutation_upper _ _ _ [34,260,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3835

def r6436 : Route 9 := (fun mask => (mask,id))

def c6436 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6436 : Upper (D 3) (R 3) [34,260,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6436 c6436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6436_9
  · exact m6436_33
  · exact m6436_40
  · exact m6436_65
  · exact m6436_72
  · exact m6436_96
  · exact u3837
  · exact u3838
  · exact u3839
  · exact u3840

theorem m6437_9 : Upper (D 3) (R 3) [34,260,65,144,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3817

theorem m6437_33 : Upper (D 3) (R 3) [34,260,65,144,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3822

theorem m6437_40 : Upper (D 3) (R 3) [34,260,65,144,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3827

theorem m6437_65 : Upper (D 3) (R 3) [34,260,65,144,65] 13 :=
  permutation_upper _ _ _ [34,260,65,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3830

theorem m6437_72 : Upper (D 3) (R 3) [34,260,65,144,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3833

theorem m6437_96 : Upper (D 3) (R 3) [34,260,65,144,96] 13 :=
  permutation_upper _ _ _ [34,260,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3836

theorem m6437_129 : Upper (D 3) (R 3) [34,260,65,144,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3838

def r6437 : Route 9 := (fun mask => (mask,id))

def c6437 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6437 : Upper (D 3) (R 3) [34,260,65,144] 13 := by
  apply FastRouting.sound _ _ [34,260,65,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6437 c6437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6437_9
  · exact m6437_33
  · exact m6437_40
  · exact m6437_65
  · exact m6437_72
  · exact m6437_96
  · exact m6437_129
  · exact u3841
  · exact u3842
  · exact u3843

theorem m6438_9 : Upper (D 3) (R 3) [34,260,65,160,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3818

theorem m6438_65 : Upper (D 3) (R 3) [34,260,65,160,65] 13 :=
  permutation_upper _ _ _ [34,260,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3831

theorem m6438_72 : Upper (D 3) (R 3) [34,260,65,160,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3834

theorem m6438_129 : Upper (D 3) (R 3) [34,260,65,160,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3839

theorem m6438_136 : Upper (D 3) (R 3) [34,260,65,160,136] 13 :=
  permutation_upper _ _ _ [34,260,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3842

def r6438 : Route 9 := (fun mask => (mask,id))

def c6438 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6438 : Upper (D 3) (R 3) [34,260,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6438 c6438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6438_9
  · exact m6438_65
  · exact m6438_72
  · exact m6438_129
  · exact m6438_136
  · exact u3844

theorem m6439_9 : Upper (D 3) (R 3) [34,260,65,192,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3819

theorem m6439_33 : Upper (D 3) (R 3) [34,260,65,192,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3823

theorem m6439_40 : Upper (D 3) (R 3) [34,260,65,192,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3828

theorem m6439_129 : Upper (D 3) (R 3) [34,260,65,192,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3840

theorem m6439_136 : Upper (D 3) (R 3) [34,260,65,192,136] 13 :=
  permutation_upper _ _ _ [34,260,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3843

theorem m6439_160 : Upper (D 3) (R 3) [34,260,65,192,160] 13 :=
  permutation_upper _ _ _ [34,260,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3844

def r6439 : Route 9 := (fun mask => (mask,id))

def c6439 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6439 : Upper (D 3) (R 3) [34,260,65,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6439 c6439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6439_9
  · exact m6439_33
  · exact m6439_40
  · exact m6439_129
  · exact m6439_136
  · exact m6439_160

def r6440 : Route 9 := (fun mask => (mask,id))

def c6440 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6440 : Upper (D 3) (R 3) [34,260,72,17] 13 := by
  apply FastRouting.sound _ _ [34,260,72,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6440 c6440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3845
  · exact u3846
  · exact u3847
  · exact u3848
  · exact u3849
  · exact u3850

def b6441 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 76 41 209 241 209 209 465), lower := (rows 35 262 76 41 16 32 64 128 256), losses := [] }

theorem u6441 : Upper (D 3) (R 3) [34,260,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6441
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6442 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 76 56 209 225 193 193 449), lower := (rows 35 262 76 56 16 32 64 128 256), losses := [] }

theorem u6442 : Upper (D 3) (R 3) [34,260,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6442
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6443 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 73 177 177 241 177 433), lower := (rows 35 262 76 73 16 32 64 128 256), losses := [] }

theorem u6443 : Upper (D 3) (R 3) [34,260,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6443
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6444 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 88 177 161 225 161 417), lower := (rows 35 262 76 88 16 32 64 128 256), losses := [] }

theorem u6444 : Upper (D 3) (R 3) [34,260,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6444
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6445 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 104 145 177 209 145 401), lower := (rows 35 262 76 104 16 32 64 128 256), losses := [] }

theorem u6445 : Upper (D 3) (R 3) [34,260,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6445
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6446 : Route 9 := (fun mask => (mask,id))

def c6446 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6446 : Upper (D 3) (R 3) [34,260,72,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6446 c6446
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3851
  · exact u3852
  · exact u3853
  · exact u3854
  · exact u3855
  · exact u3856

def r6447 : Route 9 := (fun mask => (mask,id))

def c6447 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6447 : Upper (D 3) (R 3) [34,260,72,144] 13 := by
  apply FastRouting.sound _ _ [34,260,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6447 c6447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3857
  · exact u3858
  · exact u3859
  · exact u3860
  · exact u3861
  · exact u3862

def b6448 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 76 168 209 241 209 209 465), lower := (rows 35 262 76 168 16 32 64 128 256), losses := [] }

theorem u6448 : Upper (D 3) (R 3) [34,260,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6448
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6449 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 200 177 177 241 177 433), lower := (rows 35 262 76 200 16 32 64 128 256), losses := [] }

theorem u6449 : Upper (D 3) (R 3) [34,260,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6449
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6450 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6450 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6450 : Upper (D 3) (R 3) [34,260,192,17] 13 := by
  apply FastRouting.sound _ _ [34,260,192,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r6450 c6450
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3863
  · exact u3864
  · exact u3865
  · exact u3866
  · exact u3867
  · exact u3868
  · exact u3869

def b6451 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 196 41 217 249 217 217 473), lower := (rows 35 262 196 41 16 32 64 128 256), losses := [] }

theorem u6451 : Upper (D 3) (R 3) [34,260,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6451
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6452_9 : Upper (D 3) (R 3) [34,260,192,48,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3865

def r6452 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6452 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6452 : Upper (D 3) (R 3) [34,260,192,48] 13 := by
  apply FastRouting.sound _ _ [34,260,192,48] 13 (by decide) (choices 2) [9,65,72,192] r6452 c6452
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m6452_9
  · exact u3871
  · exact u3872
  · exact u3873

def b6453 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 196 73 185 185 249 185 441), lower := (rows 35 262 196 73 16 32 64 128 256), losses := [] }

theorem u6453 : Upper (D 3) (R 3) [34,260,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6453
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6454_9 : Upper (D 3) (R 3) [34,260,192,80,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3867

theorem m6454_33 : Upper (D 3) (R 3) [34,260,192,80,33] 13 :=
  permutation_upper _ _ _ [34,260,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3870

theorem m6454_40 : Upper (D 3) (R 3) [34,260,192,80,40] 13 :=
  permutation_upper _ _ _ [34,260,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3872

theorem m6454_129 : Upper (D 3) (R 3) [34,260,192,80,129] 13 :=
  permutation_upper _ _ _ [34,260,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3874

def r6454 : Route 9 := (fun mask => (mask,id))

def c6454 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6454 : Upper (D 3) (R 3) [34,260,192,80] 13 := by
  apply FastRouting.sound _ _ [34,260,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6454 c6454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6454_9
  · exact m6454_33
  · exact m6454_40
  · exact m6454_129
  · exact u3876
  · exact u3877

theorem m6455_9 : Upper (D 3) (R 3) [34,260,192,96,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3868

theorem m6455_129 : Upper (D 3) (R 3) [34,260,192,96,129] 13 :=
  permutation_upper _ _ _ [34,260,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3875

theorem m6455_136 : Upper (D 3) (R 3) [34,260,192,96,136] 13 :=
  permutation_upper _ _ _ [34,260,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3877

def r6455 : Route 9 := (fun mask => (mask,id))

def c6455 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6455 : Upper (D 3) (R 3) [34,260,192,96] 13 := by
  apply FastRouting.sound _ _ [34,260,192,96] 13 (by decide) (choices 2) [9,129,136] r6455 c6455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6455_9
  · exact m6455_129
  · exact m6455_136

def b6456 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 196 200 57 57 121 185 313), lower := (rows 35 262 196 200 16 32 64 128 256), losses := [] }

theorem u6456 : Upper (D 3) (R 3) [34,260,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6456
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6457 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 241 241 241 241 497), lower := (rows 35 322 13 13 16 32 64 128 256), losses := [] }

theorem u6457 : Upper (D 3) (R 3) [34,320,9,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6457
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6458 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 25 245 229 229 229 485), lower := (rows 35 322 13 25 16 32 64 128 256), losses := [] }

theorem u6458 : Upper (D 3) (R 3) [34,320,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6458
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6459 : Route 9 := (fun mask => (mask,id))

def c6459 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6459 : Upper (D 3) (R 3) [34,320,9,20] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6459 c6459
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3889
  · exact u3890
  · exact u3891
  · exact u3892
  · exact u3893
  · exact u3894

def b6460 : PairBound 9 := { available := 213, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 213 245 213 213 469), lower := (rows 35 322 13 41 16 32 64 128 256), losses := [] }

theorem u6460 : Upper (D 3) (R 3) [34,320,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6460
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6461 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 44 209 241 209 209 465), lower := (rows 35 322 13 44 16 32 64 128 256), losses := [] }

theorem u6461 : Upper (D 3) (R 3) [34,320,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6461
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6462 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 56 213 229 197 197 453), lower := (rows 35 322 13 56 16 32 64 128 256), losses := [] }

theorem u6462 : Upper (D 3) (R 3) [34,320,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6462
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6463 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 73 181 181 245 181 437), lower := (rows 35 322 13 73 16 32 64 128 256), losses := [] }

theorem u6463 : Upper (D 3) (R 3) [34,320,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6463
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6464 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 76 177 177 241 177 433), lower := (rows 35 322 13 76 16 32 64 128 256), losses := [] }

theorem u6464 : Upper (D 3) (R 3) [34,320,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6464
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6465 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 88 181 165 229 165 421), lower := (rows 35 322 13 88 16 32 64 128 256), losses := [] }

theorem u6465 : Upper (D 3) (R 3) [34,320,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6465
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6466 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 104 149 181 213 149 405), lower := (rows 35 322 13 104 16 32 64 128 256), losses := [] }

theorem u6466 : Upper (D 3) (R 3) [34,320,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6466
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6467 : PairBound 9 := { available := 245, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 245 245 245 245 501), lower := (rows 35 322 13 137 16 32 64 128 256), losses := [] }

theorem u6467 : Upper (D 3) (R 3) [34,320,9,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6467
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6468 : Route 9 := (fun mask => (mask,id))

def c6468 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6468 : Upper (D 3) (R 3) [34,320,9,132] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6468 c6468
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3924
  · exact u3925
  · exact u3926
  · exact u3927
  · exact u3928
  · exact u3929

theorem m6469_5 : Upper (D 3) (R 3) [34,320,9,144,5] 13 :=
  permutation_upper _ _ _ [34,320,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3886

def r6469 : Route 9 := (fun mask => (mask,id))

def c6469 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6469 : Upper (D 3) (R 3) [34,320,9,144] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r6469 c6469
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6469_5
  · exact u3930
  · exact u3931
  · exact u3932
  · exact u3933
  · exact u3934
  · exact u3935
  · exact u3936
  · exact u3937
  · exact u3938

def b6470 : PairBound 9 := { available := 213, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 168 213 245 213 213 469), lower := (rows 35 322 13 168 16 32 64 128 256), losses := [] }

theorem u6470 : Upper (D 3) (R 3) [34,320,9,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6470
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6471 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 200 181 181 245 181 437), lower := (rows 35 322 13 200 16 32 64 128 256), losses := [] }

theorem u6471 : Upper (D 3) (R 3) [34,320,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6471
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6472_9 : Upper (D 3) (R 3) [34,320,17,36,9] 13 :=
  permutation_upper _ _ _ [34,320,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3882

theorem m6472_65 : Upper (D 3) (R 3) [34,320,17,36,65] 13 :=
  permutation_upper _ _ _ [34,320,9,65,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3905

theorem m6472_72 : Upper (D 3) (R 3) [34,320,17,36,72] 13 :=
  permutation_upper _ _ _ [34,320,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3911

theorem m6472_129 : Upper (D 3) (R 3) [34,320,17,36,129] 13 :=
  permutation_upper _ _ _ [34,320,9,129,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3917

theorem m6472_136 : Upper (D 3) (R 3) [34,320,17,36,136] 13 :=
  permutation_upper _ _ _ [34,320,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3931

theorem m6472_192 : Upper (D 3) (R 3) [34,320,17,36,192] 13 :=
  permutation_upper _ _ _ [34,320,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3943

def r6472 : Route 9 := (fun mask => (mask,id))

def c6472 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6472 : Upper (D 3) (R 3) [34,320,17,36] 13 := by
  apply FastRouting.sound _ _ [34,320,17,36] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6472 c6472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6472_9
  · exact m6472_65
  · exact m6472_72
  · exact m6472_129
  · exact m6472_136
  · exact m6472_192

theorem m6473_9 : Upper (D 3) (R 3) [34,320,17,68,9] 13 :=
  permutation_upper _ _ _ [34,320,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3883

theorem m6473_33 : Upper (D 3) (R 3) [34,320,17,68,33] 13 :=
  permutation_upper _ _ _ [34,320,9,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3895

theorem m6473_40 : Upper (D 3) (R 3) [34,320,17,68,40] 13 :=
  permutation_upper _ _ _ [34,320,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3901

theorem m6473_129 : Upper (D 3) (R 3) [34,320,17,68,129] 13 :=
  permutation_upper _ _ _ [34,320,9,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3918

theorem m6473_136 : Upper (D 3) (R 3) [34,320,17,68,136] 13 :=
  permutation_upper _ _ _ [34,320,9,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3933

theorem m6473_160 : Upper (D 3) (R 3) [34,320,17,68,160] 13 :=
  permutation_upper _ _ _ [34,320,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3939

def r6473 : Route 9 := (fun mask => (mask,id))

def c6473 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6473 : Upper (D 3) (R 3) [34,320,17,68] 13 := by
  apply FastRouting.sound _ _ [34,320,17,68] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6473 c6473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6473_9
  · exact m6473_33
  · exact m6473_40
  · exact m6473_129
  · exact m6473_136
  · exact m6473_160

theorem m6474_5 : Upper (D 3) (R 3) [34,320,17,96,5] 13 :=
  permutation_upper _ _ _ [34,320,9,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3878

theorem m6474_9 : Upper (D 3) (R 3) [34,320,17,96,9] 13 :=
  permutation_upper _ _ _ [34,320,9,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3884

theorem m6474_12 : Upper (D 3) (R 3) [34,320,17,96,12] 13 :=
  permutation_upper _ _ _ [34,320,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3891

theorem m6474_129 : Upper (D 3) (R 3) [34,320,17,96,129] 13 :=
  permutation_upper _ _ _ [34,320,9,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3919

theorem m6474_132 : Upper (D 3) (R 3) [34,320,17,96,132] 13 :=
  permutation_upper _ _ _ [34,320,9,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3926

theorem m6474_136 : Upper (D 3) (R 3) [34,320,17,96,136] 13 :=
  permutation_upper _ _ _ [34,320,9,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3934

def r6474 : Route 9 := (fun mask => (mask,id))

def c6474 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6474 : Upper (D 3) (R 3) [34,320,17,96] 13 := by
  apply FastRouting.sound _ _ [34,320,17,96] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6474 c6474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6474_5
  · exact m6474_9
  · exact m6474_12
  · exact m6474_129
  · exact m6474_132
  · exact m6474_136

theorem m6475_5 : Upper (D 3) (R 3) [34,320,17,129,5] 13 :=
  permutation_upper _ _ _ [34,320,9,5,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3879

theorem m6475_9 : Upper (D 3) (R 3) [34,320,17,129,9] 13 :=
  permutation_upper _ _ _ [34,320,9,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3885

theorem m6475_12 : Upper (D 3) (R 3) [34,320,17,129,12] 13 :=
  permutation_upper _ _ _ [34,320,9,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3892

theorem m6475_33 : Upper (D 3) (R 3) [34,320,17,129,33] 13 :=
  permutation_upper _ _ _ [34,320,9,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3896

theorem m6475_36 : Upper (D 3) (R 3) [34,320,17,129,36] 13 :=
  permutation_upper _ _ _ [34,320,9,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3899

theorem m6475_40 : Upper (D 3) (R 3) [34,320,17,129,40] 13 :=
  permutation_upper _ _ _ [34,320,9,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3902

theorem m6475_65 : Upper (D 3) (R 3) [34,320,17,129,65] 13 :=
  permutation_upper _ _ _ [34,320,9,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3906

theorem m6475_68 : Upper (D 3) (R 3) [34,320,17,129,68] 13 :=
  permutation_upper _ _ _ [34,320,9,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3909

theorem m6475_72 : Upper (D 3) (R 3) [34,320,17,129,72] 13 :=
  permutation_upper _ _ _ [34,320,9,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3912

theorem m6475_96 : Upper (D 3) (R 3) [34,320,17,129,96] 13 :=
  permutation_upper _ _ _ [34,320,9,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3915

theorem m6475_129 : Upper (D 3) (R 3) [34,320,17,129,129] 13 :=
  permutation_upper _ _ _ [34,320,9,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3920

theorem m6475_132 : Upper (D 3) (R 3) [34,320,17,129,132] 13 :=
  permutation_upper _ _ _ [34,320,9,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3927

theorem m6475_136 : Upper (D 3) (R 3) [34,320,17,129,136] 13 :=
  permutation_upper _ _ _ [34,320,9,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3935

theorem m6475_160 : Upper (D 3) (R 3) [34,320,17,129,160] 13 :=
  permutation_upper _ _ _ [34,320,9,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3940

theorem m6475_192 : Upper (D 3) (R 3) [34,320,17,129,192] 13 :=
  permutation_upper _ _ _ [34,320,9,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3944

def r6475 : Route 9 := (fun mask => (mask,id))

def c6475 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6475 : Upper (D 3) (R 3) [34,320,17,129] 13 := by
  apply FastRouting.sound _ _ [34,320,17,129] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r6475 c6475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6475_5
  · exact m6475_9
  · exact m6475_12
  · exact m6475_33
  · exact m6475_36
  · exact m6475_40
  · exact m6475_65
  · exact m6475_68
  · exact m6475_72
  · exact m6475_96
  · exact m6475_129
  · exact m6475_132
  · exact m6475_136
  · exact m6475_160
  · exact m6475_192

theorem m6476_9 : Upper (D 3) (R 3) [34,320,17,132,9] 13 :=
  permutation_upper _ _ _ [34,320,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3886

theorem m6476_33 : Upper (D 3) (R 3) [34,320,17,132,33] 13 :=
  permutation_upper _ _ _ [34,320,9,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3897

theorem m6476_40 : Upper (D 3) (R 3) [34,320,17,132,40] 13 :=
  permutation_upper _ _ _ [34,320,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3903

theorem m6476_65 : Upper (D 3) (R 3) [34,320,17,132,65] 13 :=
  permutation_upper _ _ _ [34,320,9,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3907

theorem m6476_72 : Upper (D 3) (R 3) [34,320,17,132,72] 13 :=
  permutation_upper _ _ _ [34,320,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3913

theorem m6476_96 : Upper (D 3) (R 3) [34,320,17,132,96] 13 :=
  permutation_upper _ _ _ [34,320,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3916

theorem m6476_129 : Upper (D 3) (R 3) [34,320,17,132,129] 13 :=
  permutation_upper _ _ _ [34,320,9,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3921

theorem m6476_136 : Upper (D 3) (R 3) [34,320,17,132,136] 13 :=
  permutation_upper _ _ _ [34,320,9,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3936

theorem m6476_160 : Upper (D 3) (R 3) [34,320,17,132,160] 13 :=
  permutation_upper _ _ _ [34,320,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3941

theorem m6476_192 : Upper (D 3) (R 3) [34,320,17,132,192] 13 :=
  permutation_upper _ _ _ [34,320,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3945

def r6476 : Route 9 := (fun mask => (mask,id))

def c6476 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6476 : Upper (D 3) (R 3) [34,320,17,132] 13 := by
  apply FastRouting.sound _ _ [34,320,17,132] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6476 c6476
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6476_9
  · exact m6476_33
  · exact m6476_40
  · exact m6476_65
  · exact m6476_72
  · exact m6476_96
  · exact m6476_129
  · exact m6476_136
  · exact m6476_160
  · exact m6476_192

theorem m6477_5 : Upper (D 3) (R 3) [34,320,17,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,5,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3880

theorem m6477_9 : Upper (D 3) (R 3) [34,320,17,160,9] 13 :=
  permutation_upper _ _ _ [34,320,9,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3887

theorem m6477_12 : Upper (D 3) (R 3) [34,320,17,160,12] 13 :=
  permutation_upper _ _ _ [34,320,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3893

theorem m6477_65 : Upper (D 3) (R 3) [34,320,17,160,65] 13 :=
  permutation_upper _ _ _ [34,320,9,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3908

theorem m6477_68 : Upper (D 3) (R 3) [34,320,17,160,68] 13 :=
  permutation_upper _ _ _ [34,320,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3910

theorem m6477_72 : Upper (D 3) (R 3) [34,320,17,160,72] 13 :=
  permutation_upper _ _ _ [34,320,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3914

theorem m6477_129 : Upper (D 3) (R 3) [34,320,17,160,129] 13 :=
  permutation_upper _ _ _ [34,320,9,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3922

theorem m6477_132 : Upper (D 3) (R 3) [34,320,17,160,132] 13 :=
  permutation_upper _ _ _ [34,320,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3928

theorem m6477_136 : Upper (D 3) (R 3) [34,320,17,160,136] 13 :=
  permutation_upper _ _ _ [34,320,9,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3937

theorem m6477_192 : Upper (D 3) (R 3) [34,320,17,160,192] 13 :=
  permutation_upper _ _ _ [34,320,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3946

def r6477 : Route 9 := (fun mask => (mask,id))

def c6477 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6477 : Upper (D 3) (R 3) [34,320,17,160] 13 := by
  apply FastRouting.sound _ _ [34,320,17,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6477 c6477
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6477_5
  · exact m6477_9
  · exact m6477_12
  · exact m6477_65
  · exact m6477_68
  · exact m6477_72
  · exact m6477_129
  · exact m6477_132
  · exact m6477_136
  · exact m6477_192

theorem m6478_5 : Upper (D 3) (R 3) [34,320,17,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,5,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3881

theorem m6478_9 : Upper (D 3) (R 3) [34,320,17,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3888

theorem m6478_12 : Upper (D 3) (R 3) [34,320,17,192,12] 13 :=
  permutation_upper _ _ _ [34,320,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3894

theorem m6478_33 : Upper (D 3) (R 3) [34,320,17,192,33] 13 :=
  permutation_upper _ _ _ [34,320,9,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3898

theorem m6478_36 : Upper (D 3) (R 3) [34,320,17,192,36] 13 :=
  permutation_upper _ _ _ [34,320,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3900

theorem m6478_40 : Upper (D 3) (R 3) [34,320,17,192,40] 13 :=
  permutation_upper _ _ _ [34,320,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3904

theorem m6478_129 : Upper (D 3) (R 3) [34,320,17,192,129] 13 :=
  permutation_upper _ _ _ [34,320,9,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3923

theorem m6478_132 : Upper (D 3) (R 3) [34,320,17,192,132] 13 :=
  permutation_upper _ _ _ [34,320,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3929

theorem m6478_136 : Upper (D 3) (R 3) [34,320,17,192,136] 13 :=
  permutation_upper _ _ _ [34,320,9,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3938

theorem m6478_160 : Upper (D 3) (R 3) [34,320,17,192,160] 13 :=
  permutation_upper _ _ _ [34,320,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3942

def r6478 : Route 9 := (fun mask => (mask,id))

def c6478 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6478 : Upper (D 3) (R 3) [34,320,17,192] 13 := by
  apply FastRouting.sound _ _ [34,320,17,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6478 c6478
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6478_5
  · exact m6478_9
  · exact m6478_12
  · exact m6478_33
  · exact m6478_36
  · exact m6478_40
  · exact m6478_129
  · exact m6478_132
  · exact m6478_136
  · exact m6478_160

def b6479 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 28 41 213 229 197 197 453), lower := (rows 35 322 28 41 16 32 64 128 256), losses := [] }

theorem u6479 : Upper (D 3) (R 3) [34,320,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6479
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6479
end Delivery.IrregularNine14.P03
