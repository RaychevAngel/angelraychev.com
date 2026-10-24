import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0043
import IrregularNine14P03C0044
import IrregularNine14P03C0045
import IrregularNine14P03C0046

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5940 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 324 56 209 225 193 193 449), lower := (rows 7 42 324 56 16 32 64 128 256), losses := [] }

theorem u5940 : Upper (D 3) (R 3) [6,40,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5940
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5941 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 73 177 177 241 177 433), lower := (rows 7 42 324 73 16 32 64 128 256), losses := [] }

theorem u5941 : Upper (D 3) (R 3) [6,40,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5941
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5942 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 324 88 177 161 225 161 417), lower := (rows 7 42 324 88 16 32 64 128 256), losses := [] }

theorem u5942 : Upper (D 3) (R 3) [6,40,320,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5942
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5943 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 324 104 145 177 209 145 401), lower := (rows 7 42 324 104 16 32 64 128 256), losses := [] }

theorem u5943 : Upper (D 3) (R 3) [6,40,320,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5943
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5944 : Route 9 := (fun mask => (mask,id))

def c5944 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5944 : Upper (D 3) (R 3) [6,40,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5944 c5944
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2616
  · exact u2617
  · exact u2618
  · exact u2619
  · exact u2620
  · exact u2621

def r5945 : Route 9 := (fun mask => (mask,id))

def c5945 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5945 : Upper (D 3) (R 3) [6,40,320,144] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5945 c5945
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2622
  · exact u2623
  · exact u2624
  · exact u2625
  · exact u2626
  · exact u2627

def b5946 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 324 168 209 241 209 209 465), lower := (rows 7 42 324 168 16 32 64 128 256), losses := [] }

theorem u5946 : Upper (D 3) (R 3) [6,40,320,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5946
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5947 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 324 200 177 177 241 177 433), lower := (rows 7 42 324 200 16 32 64 128 256), losses := [] }

theorem u5947 : Upper (D 3) (R 3) [6,40,320,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5947
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5948 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5948 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5948 : Upper (D 3) (R 3) [6,96,257,17] 13 := by
  apply FastRouting.sound _ _ [6,96,257,17] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r5948 c5948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2628
  · exact u2629
  · exact u2630
  · exact u2631
  · exact u2632
  · exact u2633
  · exact u2634

def b5949 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 261 41 217 249 217 217 473), lower := (rows 7 98 261 41 16 32 64 128 256), losses := [] }

theorem u5949 : Upper (D 3) (R 3) [6,96,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5949
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5950_9 : Upper (D 3) (R 3) [6,96,257,48,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2630

theorem m5950_65 : Upper (D 3) (R 3) [6,96,257,48,65] 13 :=
  permutation_upper _ _ _ [6,96,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2635

def r5950 : Route 9 := (fun mask => (mask,id))

def c5950 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5950 : Upper (D 3) (R 3) [6,96,257,48] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r5950 c5950
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5950_9
  · exact m5950_65
  · exact u2639
  · exact u2640
  · exact u2641
  · exact u2642

def b5951 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 104 153 185 217 153 409), lower := (rows 7 98 261 104 16 32 64 128 256), losses := [] }

theorem u5951 : Upper (D 3) (R 3) [6,96,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5951
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5952_9 : Upper (D 3) (R 3) [6,96,257,129,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2632

theorem m5952_33 : Upper (D 3) (R 3) [6,96,257,129,33] 13 :=
  permutation_upper _ _ _ [6,96,257,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2636

theorem m5952_40 : Upper (D 3) (R 3) [6,96,257,129,40] 13 :=
  permutation_upper _ _ _ [6,96,257,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2640

theorem m5952_96 : Upper (D 3) (R 3) [6,96,257,129,96] 13 :=
  permutation_upper _ _ _ [6,96,257,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2643

def r5952 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5952 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5952 : Upper (D 3) (R 3) [6,96,257,129] 13 := by
  apply FastRouting.sound _ _ [6,96,257,129] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r5952 c5952
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5952_9
  · exact m5952_33
  · exact m5952_40
  · exact m5952_96
  · exact u2645
  · exact u2646
  · exact u2647

theorem m5953_9 : Upper (D 3) (R 3) [6,96,257,144,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2633

theorem m5953_33 : Upper (D 3) (R 3) [6,96,257,144,33] 13 :=
  permutation_upper _ _ _ [6,96,257,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2637

theorem m5953_40 : Upper (D 3) (R 3) [6,96,257,144,40] 13 :=
  permutation_upper _ _ _ [6,96,257,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2641

theorem m5953_96 : Upper (D 3) (R 3) [6,96,257,144,96] 13 :=
  permutation_upper _ _ _ [6,96,257,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2644

theorem m5953_129 : Upper (D 3) (R 3) [6,96,257,144,129] 13 :=
  permutation_upper _ _ _ [6,96,257,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2646

def r5953 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5953 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5953 : Upper (D 3) (R 3) [6,96,257,144] 13 := by
  apply FastRouting.sound _ _ [6,96,257,144] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r5953 c5953
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5953_9
  · exact m5953_33
  · exact m5953_40
  · exact m5953_96
  · exact m5953_129
  · exact u2648
  · exact u2649

theorem m5954_9 : Upper (D 3) (R 3) [6,96,257,160,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2634

theorem m5954_65 : Upper (D 3) (R 3) [6,96,257,160,65] 13 :=
  permutation_upper _ _ _ [6,96,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2638

theorem m5954_72 : Upper (D 3) (R 3) [6,96,257,160,72] 13 :=
  permutation_upper _ _ _ [6,96,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2642

theorem m5954_129 : Upper (D 3) (R 3) [6,96,257,160,129] 13 :=
  permutation_upper _ _ _ [6,96,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2647

theorem m5954_136 : Upper (D 3) (R 3) [6,96,257,160,136] 13 :=
  permutation_upper _ _ _ [6,96,257,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2649

def r5954 : Route 9 := (fun mask => (mask,id))

def c5954 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5954 : Upper (D 3) (R 3) [6,96,257,160] 13 := by
  apply FastRouting.sound _ _ [6,96,257,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r5954 c5954
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5954_9
  · exact m5954_65
  · exact m5954_72
  · exact m5954_129
  · exact m5954_136
  · exact u2650

def r5955 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5955 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5955 : Upper (D 3) (R 3) [6,96,264,17] 13 := by
  apply FastRouting.sound _ _ [6,96,264,17] 13 (by decide) (choices 2) [33,96,129,160] r5955 c5955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2651
  · exact u2652
  · exact u2653
  · exact u2654

def b5956 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 268 41 209 241 209 209 465), lower := (rows 7 98 268 41 16 32 64 128 256), losses := [] }

theorem u5956 : Upper (D 3) (R 3) [6,96,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5956
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5957 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 268 56 209 225 193 193 449), lower := (rows 7 98 268 56 16 32 64 128 256), losses := [] }

theorem u5957 : Upper (D 3) (R 3) [6,96,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5957
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5958 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 268 104 145 177 209 145 401), lower := (rows 7 98 268 104 16 32 64 128 256), losses := [] }

theorem u5958 : Upper (D 3) (R 3) [6,96,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5958
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5959 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5959 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5959 : Upper (D 3) (R 3) [6,96,264,129] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129] 13 (by decide) (choices 2) [33,96,129,160] r5959 c5959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2655
  · exact u2656
  · exact u2657
  · exact u2658

def r5960 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5960 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5960 : Upper (D 3) (R 3) [6,96,264,144] 13 := by
  apply FastRouting.sound _ _ [6,96,264,144] 13 (by decide) (choices 2) [33,96,129,160] r5960 c5960
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2659
  · exact u2660
  · exact u2661
  · exact u2662

def b5961 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 268 168 209 241 209 209 465), lower := (rows 7 98 268 168 16 32 64 128 256), losses := [] }

theorem u5961 : Upper (D 3) (R 3) [6,96,264,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5961
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5962 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5962 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5962 : Upper (D 3) (R 3) [6,96,384,17] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r5962 c5962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2663
  · exact u2664
  · exact u2665
  · exact u2666
  · exact u2667
  · exact u2668
  · exact u2669

def b5963 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 388 41 217 249 217 217 473), lower := (rows 7 98 388 41 16 32 64 128 256), losses := [] }

theorem u5963 : Upper (D 3) (R 3) [6,96,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5963
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5964_9 : Upper (D 3) (R 3) [6,96,384,48,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2665

theorem m5964_65 : Upper (D 3) (R 3) [6,96,384,48,65] 13 :=
  permutation_upper _ _ _ [6,96,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2670

def r5964 : Route 9 := (fun mask => (mask,id))

def c5964 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5964 : Upper (D 3) (R 3) [6,96,384,48] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r5964 c5964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5964_9
  · exact m5964_65
  · exact u2673
  · exact u2674
  · exact u2675
  · exact u2676

def b5965 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 104 153 185 217 153 409), lower := (rows 7 98 388 104 16 32 64 128 256), losses := [] }

theorem u5965 : Upper (D 3) (R 3) [6,96,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5965
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5966 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 137 121 121 121 249 377), lower := (rows 7 98 388 137 16 32 64 128 256), losses := [] }

theorem u5966 : Upper (D 3) (R 3) [6,96,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5966
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5967_9 : Upper (D 3) (R 3) [6,96,384,144,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2668

theorem m5967_33 : Upper (D 3) (R 3) [6,96,384,144,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2671

theorem m5967_40 : Upper (D 3) (R 3) [6,96,384,144,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2675

theorem m5967_96 : Upper (D 3) (R 3) [6,96,384,144,96] 13 :=
  permutation_upper _ _ _ [6,96,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2677

def r5967 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5967 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u5967 : Upper (D 3) (R 3) [6,96,384,144] 13 := by
  apply FastRouting.sound _ _ [6,96,384,144] 13 (by decide) (choices 2) [9,33,40,96] r5967 c5967
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5967_9
  · exact m5967_33
  · exact m5967_40
  · exact m5967_96

theorem m5968_9 : Upper (D 3) (R 3) [6,96,384,160,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2669

theorem m5968_65 : Upper (D 3) (R 3) [6,96,384,160,65] 13 :=
  permutation_upper _ _ _ [6,96,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2672

theorem m5968_72 : Upper (D 3) (R 3) [6,96,384,160,72] 13 :=
  permutation_upper _ _ _ [6,96,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2676

def r5968 : Route 9 := (fun mask => (mask,id))

def c5968 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u5968 : Upper (D 3) (R 3) [6,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,160] 13 (by decide) (choices 2) [9,65,72] r5968 c5968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5968_9
  · exact m5968_65
  · exact m5968_72

def b5969 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 28 41 465 481 449 449 449), lower := (rows 35 7 28 41 16 32 64 128 256), losses := [] }

theorem u5969 : Upper (D 3) (R 3) [34,5,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5969
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5970_33 : Upper (D 3) (R 3) [34,5,24,65,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2678

def r5970 : Route 9 := (fun mask => (mask,id))

def c5970 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5970 : Upper (D 3) (R 3) [34,5,24,65] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5970 c5970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5970_33
  · exact u2682
  · exact u2683
  · exact u2684
  · exact u2685
  · exact u2686
  · exact u2687
  · exact u2688
  · exact u2689
  · exact u2690

def b5971 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 28 104 465 481 449 449 449), lower := (rows 35 7 28 104 16 32 64 128 256), losses := [] }

theorem u5971 : Upper (D 3) (R 3) [34,5,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5971
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5972_33 : Upper (D 3) (R 3) [34,5,24,192,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2679

theorem m5972_65 : Upper (D 3) (R 3) [34,5,24,192,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2686

theorem m5972_96 : Upper (D 3) (R 3) [34,5,24,192,96] 13 :=
  permutation_upper _ _ _ [34,5,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2691

def r5972 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5972 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5972 : Upper (D 3) (R 3) [34,5,24,192] 13 := by
  apply FastRouting.sound _ _ [34,5,24,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r5972 c5972
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5972_33
  · exact m5972_65
  · exact m5972_96
  · exact u2695
  · exact u2696
  · exact u2697
  · exact u2698

theorem m5973_33 : Upper (D 3) (R 3) [34,5,24,257,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2680

theorem m5973_65 : Upper (D 3) (R 3) [34,5,24,257,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2687

theorem m5973_96 : Upper (D 3) (R 3) [34,5,24,257,96] 13 :=
  permutation_upper _ _ _ [34,5,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2692

theorem m5973_192 : Upper (D 3) (R 3) [34,5,24,257,192] 13 :=
  permutation_upper _ _ _ [34,5,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2696

def r5973 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5973 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5973 : Upper (D 3) (R 3) [34,5,24,257] 13 := by
  apply FastRouting.sound _ _ [34,5,24,257] 13 (by decide) (choices 2) [33,65,96,192] r5973 c5973
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5973_33
  · exact m5973_65
  · exact m5973_96
  · exact m5973_192

def b5974 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 28 296 209 225 193 193 449), lower := (rows 35 7 28 296 16 32 64 128 256), losses := [] }

theorem u5974 : Upper (D 3) (R 3) [34,5,24,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5974
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5975_33 : Upper (D 3) (R 3) [34,5,24,320,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2681

theorem m5975_65 : Upper (D 3) (R 3) [34,5,24,320,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2689

theorem m5975_96 : Upper (D 3) (R 3) [34,5,24,320,96] 13 :=
  permutation_upper _ _ _ [34,5,24,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2693

theorem m5975_129 : Upper (D 3) (R 3) [34,5,24,320,129] 13 :=
  permutation_upper _ _ _ [34,5,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2690

theorem m5975_160 : Upper (D 3) (R 3) [34,5,24,320,160] 13 :=
  permutation_upper _ _ _ [34,5,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2694

theorem m5975_192 : Upper (D 3) (R 3) [34,5,24,320,192] 13 :=
  permutation_upper _ _ _ [34,5,24,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2698

def r5975 : Route 9 := (fun mask => (mask,id))

def c5975 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5975 : Upper (D 3) (R 3) [34,5,24,320] 13 := by
  apply FastRouting.sound _ _ [34,5,24,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5975 c5975
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5975_33
  · exact m5975_65
  · exact m5975_96
  · exact m5975_129
  · exact m5975_160
  · exact m5975_192

def r5976 : Route 9 := (fun mask => (mask,id))

def c5976 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5976 : Upper (D 3) (R 3) [34,5,72,17] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5976 c5976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2699
  · exact u2700
  · exact u2701
  · exact u2702
  · exact u2703
  · exact u2704
  · exact u2705
  · exact u2706
  · exact u2707
  · exact u2708

def b5977 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 41 465 497 465 465 465), lower := (rows 35 7 76 41 16 32 64 128 256), losses := [] }

theorem u5977 : Upper (D 3) (R 3) [34,5,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5977
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5978 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 76 56 465 481 449 449 449), lower := (rows 35 7 76 56 16 32 64 128 256), losses := [] }

theorem u5978 : Upper (D 3) (R 3) [34,5,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5978
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5979 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 73 433 433 497 433 433), lower := (rows 35 7 76 73 16 32 64 128 256), losses := [] }

theorem u5979 : Upper (D 3) (R 3) [34,5,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5979
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5980 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 88 433 417 481 417 417), lower := (rows 35 7 76 88 16 32 64 128 256), losses := [] }

theorem u5980 : Upper (D 3) (R 3) [34,5,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5980
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5981 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 104 401 433 465 401 401), lower := (rows 35 7 76 104 16 32 64 128 256), losses := [] }

theorem u5981 : Upper (D 3) (R 3) [34,5,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5981
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5982 : Route 9 := (fun mask => (mask,id))

def c5982 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5982 : Upper (D 3) (R 3) [34,5,72,129] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5982 c5982
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2709
  · exact u2710
  · exact u2711
  · exact u2712
  · exact u2713
  · exact u2714
  · exact u2715
  · exact u2716
  · exact u2717
  · exact u2718

def r5983 : Route 9 := (fun mask => (mask,id))

def c5983 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5983 : Upper (D 3) (R 3) [34,5,72,144] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5983 c5983
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2719
  · exact u2720
  · exact u2721
  · exact u2722
  · exact u2723
  · exact u2724
  · exact u2725
  · exact u2726
  · exact u2727
  · exact u2728

def b5984 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 76 168 465 497 465 465 465), lower := (rows 35 7 76 168 16 32 64 128 256), losses := [] }

theorem u5984 : Upper (D 3) (R 3) [34,5,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5984
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5985 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 200 433 433 497 433 433), lower := (rows 35 7 76 200 16 32 64 128 256), losses := [] }

theorem u5985 : Upper (D 3) (R 3) [34,5,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5985
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5986 : Route 9 := (fun mask => (mask,id))

def c5986 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5986 : Upper (D 3) (R 3) [34,5,72,257] 13 := by
  apply FastRouting.sound _ _ [34,5,72,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5986 c5986
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2729
  · exact u2730
  · exact u2731
  · exact u2732
  · exact u2733
  · exact u2734

def r5987 : Route 9 := (fun mask => (mask,id))

def c5987 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5987 : Upper (D 3) (R 3) [34,5,72,272] 13 := by
  apply FastRouting.sound _ _ [34,5,72,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5987 c5987
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2735
  · exact u2736
  · exact u2737
  · exact u2738
  · exact u2739
  · exact u2740

def b5988 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 76 296 209 241 209 209 465), lower := (rows 35 7 76 296 16 32 64 128 256), losses := [] }

theorem u5988 : Upper (D 3) (R 3) [34,5,72,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5988
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5989 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 328 177 177 241 177 433), lower := (rows 35 7 76 328 16 32 64 128 256), losses := [] }

theorem u5989 : Upper (D 3) (R 3) [34,5,72,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5989
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5990 : Route 9 := (fun mask => (mask,id))

def c5990 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5990 : Upper (D 3) (R 3) [34,5,72,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5990 c5990
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2741
  · exact u2742
  · exact u2743
  · exact u2744
  · exact u2745
  · exact u2746

def r5991 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5991 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u5991 : Upper (D 3) (R 3) [34,5,192,17] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r5991 c5991
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2747
  · exact u2748
  · exact u2749
  · exact u2750
  · exact u2751
  · exact u2752
  · exact u2753
  · exact u2754
  · exact u2755
  · exact u2756
  · exact u2757

def b5992 : PairBound 9 := { available := 473, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 41 473 505 473 473 473), lower := (rows 35 7 196 41 16 32 64 128 256), losses := [] }

theorem u5992 : Upper (D 3) (R 3) [34,5,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5992
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5993_9 : Upper (D 3) (R 3) [34,5,192,48,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2749

def r5993 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5993 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u5993 : Upper (D 3) (R 3) [34,5,192,48] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48] 13 (by decide) (choices 2) [9,65,72,192,257,264,320] r5993 c5993
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5993_9
  · exact u2762
  · exact u2763
  · exact u2764
  · exact u2765
  · exact u2766
  · exact u2767

def b5994 : PairBound 9 := { available := 441, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 196 73 441 441 505 441 441), lower := (rows 35 7 196 73 16 32 64 128 256), losses := [] }

theorem u5994 : Upper (D 3) (R 3) [34,5,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5994
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5995_9 : Upper (D 3) (R 3) [34,5,192,80,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2751

theorem m5995_33 : Upper (D 3) (R 3) [34,5,192,80,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2758

theorem m5995_40 : Upper (D 3) (R 3) [34,5,192,80,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2763

theorem m5995_129 : Upper (D 3) (R 3) [34,5,192,80,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2768

def r5995 : Route 9 := (fun mask => (mask,id))

def c5995 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u5995 : Upper (D 3) (R 3) [34,5,192,80] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r5995 c5995
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5995_9
  · exact m5995_33
  · exact m5995_40
  · exact m5995_129
  · exact u2774
  · exact u2775
  · exact u2776
  · exact u2777
  · exact u2778
  · exact u2779

theorem m5996_9 : Upper (D 3) (R 3) [34,5,192,96,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2752

theorem m5996_129 : Upper (D 3) (R 3) [34,5,192,96,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2769

theorem m5996_136 : Upper (D 3) (R 3) [34,5,192,96,136] 13 :=
  permutation_upper _ _ _ [34,5,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2775

def r5996 : Route 9 := (fun mask => (mask,id))

def c5996 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u5996 : Upper (D 3) (R 3) [34,5,192,96] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r5996 c5996
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5996_9
  · exact m5996_129
  · exact m5996_136
  · exact u2780
  · exact u2781
  · exact u2782

def b5997 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 200 313 313 377 441 313), lower := (rows 35 7 196 200 16 32 64 128 256), losses := [] }

theorem u5997 : Upper (D 3) (R 3) [34,5,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5997
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5998_9 : Upper (D 3) (R 3) [34,5,192,257,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2754

theorem m5998_33 : Upper (D 3) (R 3) [34,5,192,257,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2759

theorem m5998_40 : Upper (D 3) (R 3) [34,5,192,257,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2765

theorem m5998_65 : Upper (D 3) (R 3) [34,5,192,257,65] 13 :=
  permutation_upper _ _ _ [34,5,192,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2770

theorem m5998_72 : Upper (D 3) (R 3) [34,5,192,257,72] 13 :=
  permutation_upper _ _ _ [34,5,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2776

theorem m5998_96 : Upper (D 3) (R 3) [34,5,192,257,96] 13 :=
  permutation_upper _ _ _ [34,5,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2780

theorem m5998_192 : Upper (D 3) (R 3) [34,5,192,257,192] 13 :=
  permutation_upper _ _ _ [34,5,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2783

def r5998 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5998 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5998 : Upper (D 3) (R 3) [34,5,192,257] 13 := by
  apply FastRouting.sound _ _ [34,5,192,257] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r5998 c5998
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5998_9
  · exact m5998_33
  · exact m5998_40
  · exact m5998_65
  · exact m5998_72
  · exact m5998_96
  · exact m5998_192

theorem m5999_9 : Upper (D 3) (R 3) [34,5,192,272,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2755

theorem m5999_33 : Upper (D 3) (R 3) [34,5,192,272,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2760

theorem m5999_40 : Upper (D 3) (R 3) [34,5,192,272,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2766

theorem m5999_65 : Upper (D 3) (R 3) [34,5,192,272,65] 13 :=
  permutation_upper _ _ _ [34,5,192,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2771

theorem m5999_72 : Upper (D 3) (R 3) [34,5,192,272,72] 13 :=
  permutation_upper _ _ _ [34,5,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2777

theorem m5999_96 : Upper (D 3) (R 3) [34,5,192,272,96] 13 :=
  permutation_upper _ _ _ [34,5,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2781

theorem m5999_192 : Upper (D 3) (R 3) [34,5,192,272,192] 13 :=
  permutation_upper _ _ _ [34,5,192,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2784

def r5999 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5999 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5999 : Upper (D 3) (R 3) [34,5,192,272] 13 := by
  apply FastRouting.sound _ _ [34,5,192,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r5999 c5999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5999_9
  · exact m5999_33
  · exact m5999_40
  · exact m5999_65
  · exact m5999_72
  · exact m5999_96
  · exact m5999_192

#print axioms u5999
end Delivery.IrregularNine14.P03
