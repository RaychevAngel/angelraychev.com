import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0045
import IrregularNine14P03C0046
import IrregularNine14P03C0047
import IrregularNine14P03C0048

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m6000_9 : Upper (D 3) (R 3) [34,5,192,288,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2756

theorem m6000_65 : Upper (D 3) (R 3) [34,5,192,288,65] 13 :=
  permutation_upper _ _ _ [34,5,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2772

theorem m6000_72 : Upper (D 3) (R 3) [34,5,192,288,72] 13 :=
  permutation_upper _ _ _ [34,5,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2778

theorem m6000_192 : Upper (D 3) (R 3) [34,5,192,288,192] 13 :=
  permutation_upper _ _ _ [34,5,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2785

def r6000 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6000 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6000 : Upper (D 3) (R 3) [34,5,192,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,288] 13 (by decide) (choices 2) [9,65,72,192] r6000 c6000
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m6000_9
  · exact m6000_65
  · exact m6000_72
  · exact m6000_192

theorem m6001_9 : Upper (D 3) (R 3) [34,5,192,320,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2757

theorem m6001_33 : Upper (D 3) (R 3) [34,5,192,320,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2761

theorem m6001_40 : Upper (D 3) (R 3) [34,5,192,320,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2767

theorem m6001_129 : Upper (D 3) (R 3) [34,5,192,320,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2773

theorem m6001_136 : Upper (D 3) (R 3) [34,5,192,320,136] 13 :=
  permutation_upper _ _ _ [34,5,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2779

theorem m6001_160 : Upper (D 3) (R 3) [34,5,192,320,160] 13 :=
  permutation_upper _ _ _ [34,5,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2782

def r6001 : Route 9 := (fun mask => (mask,id))

def c6001 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6001 : Upper (D 3) (R 3) [34,5,192,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6001 c6001
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6001_9
  · exact m6001_33
  · exact m6001_40
  · exact m6001_129
  · exact m6001_136
  · exact m6001_160

def r6002 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6002 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6002 : Upper (D 3) (R 3) [34,5,264,17] 13 := by
  apply FastRouting.sound _ _ [34,5,264,17] 13 (by decide) (choices 2) [33,65,96,192] r6002 c6002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2786
  · exact u2787
  · exact u2788
  · exact u2789

def b6003 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 268 41 209 241 209 209 465), lower := (rows 35 7 268 41 16 32 64 128 256), losses := [] }

theorem u6003 : Upper (D 3) (R 3) [34,5,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6003
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6004 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 268 56 209 225 193 193 449), lower := (rows 35 7 268 56 16 32 64 128 256), losses := [] }

theorem u6004 : Upper (D 3) (R 3) [34,5,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6004
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6005 : Route 9 := (fun mask => (mask,id))

def c6005 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6005 : Upper (D 3) (R 3) [34,5,264,65] 13 := by
  apply FastRouting.sound _ _ [34,5,264,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6005 c6005
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2790
  · exact u2791
  · exact u2792
  · exact u2793
  · exact u2794
  · exact u2795

def r6006 : Route 9 := (fun mask => (mask,id))

def c6006 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6006 : Upper (D 3) (R 3) [34,5,264,80] 13 := by
  apply FastRouting.sound _ _ [34,5,264,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6006 c6006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2796
  · exact u2797
  · exact u2798
  · exact u2799
  · exact u2800
  · exact u2801

def b6007 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 268 104 209 241 209 209 465), lower := (rows 35 7 268 104 16 32 64 128 256), losses := [] }

theorem u6007 : Upper (D 3) (R 3) [34,5,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6007
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6008 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6008 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6008 : Upper (D 3) (R 3) [34,5,264,192] 13 := by
  apply FastRouting.sound _ _ [34,5,264,192] 13 (by decide) (choices 2) [33,65,96,192] r6008 c6008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2802
  · exact u2803
  · exact u2804
  · exact u2805

def r6009 : Route 9 := (fun mask => (mask,id))

def c6009 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6009 : Upper (D 3) (R 3) [34,5,320,17] 13 := by
  apply FastRouting.sound _ _ [34,5,320,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6009 c6009
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2806
  · exact u2807
  · exact u2808
  · exact u2809
  · exact u2810
  · exact u2811
  · exact u2812
  · exact u2813
  · exact u2814
  · exact u2815

def b6010 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 41 217 249 217 217 473), lower := (rows 35 7 324 41 16 32 64 128 256), losses := [] }

theorem u6010 : Upper (D 3) (R 3) [34,5,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6010
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6011_9 : Upper (D 3) (R 3) [34,5,320,48,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2808

def r6011 : Route 9 := (fun mask => (mask,id))

def c6011 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6011 : Upper (D 3) (R 3) [34,5,320,48] 13 := by
  apply FastRouting.sound _ _ [34,5,320,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6011 c6011
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6011_9
  · exact u2820
  · exact u2821
  · exact u2822
  · exact u2823
  · exact u2824

def b6012 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 324 73 185 185 249 185 441), lower := (rows 35 7 324 73 16 32 64 128 256), losses := [] }

theorem u6012 : Upper (D 3) (R 3) [34,5,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6012
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6013_9 : Upper (D 3) (R 3) [34,5,320,80,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2810

theorem m6013_33 : Upper (D 3) (R 3) [34,5,320,80,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2816

theorem m6013_40 : Upper (D 3) (R 3) [34,5,320,80,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2821

def r6013 : Route 9 := (fun mask => (mask,id))

def c6013 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6013 : Upper (D 3) (R 3) [34,5,320,80] 13 := by
  apply FastRouting.sound _ _ [34,5,320,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6013 c6013
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6013_9
  · exact m6013_33
  · exact m6013_40
  · exact u2828
  · exact u2829
  · exact u2830

theorem m6014_9 : Upper (D 3) (R 3) [34,5,320,96,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2811

def r6014 : Route 9 := (fun mask => (mask,id))

def c6014 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6014 : Upper (D 3) (R 3) [34,5,320,96] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96] 13 (by decide) (choices 2) [9,129,136] r6014 c6014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6014_9
  · exact u2831
  · exact u2832

theorem m6015_9 : Upper (D 3) (R 3) [34,5,320,129,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2812

theorem m6015_33 : Upper (D 3) (R 3) [34,5,320,129,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2817

theorem m6015_40 : Upper (D 3) (R 3) [34,5,320,129,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2822

theorem m6015_65 : Upper (D 3) (R 3) [34,5,320,129,65] 13 :=
  permutation_upper _ _ _ [34,5,320,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2825

theorem m6015_72 : Upper (D 3) (R 3) [34,5,320,129,72] 13 :=
  permutation_upper _ _ _ [34,5,320,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2828

theorem m6015_96 : Upper (D 3) (R 3) [34,5,320,129,96] 13 :=
  permutation_upper _ _ _ [34,5,320,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2831

def r6015 : Route 9 := (fun mask => (mask,id))

def c6015 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6015 : Upper (D 3) (R 3) [34,5,320,129] 13 := by
  apply FastRouting.sound _ _ [34,5,320,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6015 c6015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6015_9
  · exact m6015_33
  · exact m6015_40
  · exact m6015_65
  · exact m6015_72
  · exact m6015_96
  · exact u2833
  · exact u2834
  · exact u2835
  · exact u2836

theorem m6016_9 : Upper (D 3) (R 3) [34,5,320,144,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2813

theorem m6016_33 : Upper (D 3) (R 3) [34,5,320,144,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2818

theorem m6016_40 : Upper (D 3) (R 3) [34,5,320,144,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2823

theorem m6016_65 : Upper (D 3) (R 3) [34,5,320,144,65] 13 :=
  permutation_upper _ _ _ [34,5,320,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2826

theorem m6016_72 : Upper (D 3) (R 3) [34,5,320,144,72] 13 :=
  permutation_upper _ _ _ [34,5,320,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2829

theorem m6016_96 : Upper (D 3) (R 3) [34,5,320,144,96] 13 :=
  permutation_upper _ _ _ [34,5,320,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2832

theorem m6016_129 : Upper (D 3) (R 3) [34,5,320,144,129] 13 :=
  permutation_upper _ _ _ [34,5,320,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2834

def r6016 : Route 9 := (fun mask => (mask,id))

def c6016 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6016 : Upper (D 3) (R 3) [34,5,320,144] 13 := by
  apply FastRouting.sound _ _ [34,5,320,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6016 c6016
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6016_9
  · exact m6016_33
  · exact m6016_40
  · exact m6016_65
  · exact m6016_72
  · exact m6016_96
  · exact m6016_129
  · exact u2837
  · exact u2838
  · exact u2839

theorem m6017_9 : Upper (D 3) (R 3) [34,5,320,160,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2814

theorem m6017_65 : Upper (D 3) (R 3) [34,5,320,160,65] 13 :=
  permutation_upper _ _ _ [34,5,320,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2827

theorem m6017_72 : Upper (D 3) (R 3) [34,5,320,160,72] 13 :=
  permutation_upper _ _ _ [34,5,320,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2830

theorem m6017_129 : Upper (D 3) (R 3) [34,5,320,160,129] 13 :=
  permutation_upper _ _ _ [34,5,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2835

theorem m6017_136 : Upper (D 3) (R 3) [34,5,320,160,136] 13 :=
  permutation_upper _ _ _ [34,5,320,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2838

def r6017 : Route 9 := (fun mask => (mask,id))

def c6017 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6017 : Upper (D 3) (R 3) [34,5,320,160] 13 := by
  apply FastRouting.sound _ _ [34,5,320,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6017 c6017
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6017_9
  · exact m6017_65
  · exact m6017_72
  · exact m6017_129
  · exact m6017_136
  · exact u2840

theorem m6018_9 : Upper (D 3) (R 3) [34,5,320,192,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2815

theorem m6018_33 : Upper (D 3) (R 3) [34,5,320,192,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2819

theorem m6018_40 : Upper (D 3) (R 3) [34,5,320,192,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2824

theorem m6018_129 : Upper (D 3) (R 3) [34,5,320,192,129] 13 :=
  permutation_upper _ _ _ [34,5,320,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2836

theorem m6018_136 : Upper (D 3) (R 3) [34,5,320,192,136] 13 :=
  permutation_upper _ _ _ [34,5,320,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2839

theorem m6018_160 : Upper (D 3) (R 3) [34,5,320,192,160] 13 :=
  permutation_upper _ _ _ [34,5,320,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2840

def r6018 : Route 9 := (fun mask => (mask,id))

def c6018 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6018 : Upper (D 3) (R 3) [34,5,320,192] 13 := by
  apply FastRouting.sound _ _ [34,5,320,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6018 c6018
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6018_9
  · exact m6018_33
  · exact m6018_40
  · exact m6018_129
  · exact m6018_136
  · exact m6018_160

def b6019 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 41 465 481 449 449 449), lower := (rows 35 14 21 41 16 32 64 128 256), losses := [] }

theorem u6019 : Upper (D 3) (R 3) [34,12,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6019
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6020 : Route 9 := (fun mask => (mask,id))

def c6020 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6020 : Upper (D 3) (R 3) [34,12,17,65] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6020 c6020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2841
  · exact u2842
  · exact u2843
  · exact u2844
  · exact u2845
  · exact u2846
  · exact u2847
  · exact u2848
  · exact u2849
  · exact u2850

def b6021 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 104 465 481 449 449 449), lower := (rows 35 14 21 104 16 32 64 128 256), losses := [] }

theorem u6021 : Upper (D 3) (R 3) [34,12,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6021
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6022 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6022 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6022 : Upper (D 3) (R 3) [34,12,17,192] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r6022 c6022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2851
  · exact u2852
  · exact u2853
  · exact u2854
  · exact u2855
  · exact u2856
  · exact u2857

def r6023 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6023 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6023 : Upper (D 3) (R 3) [34,12,17,257] 13 := by
  apply FastRouting.sound _ _ [34,12,17,257] 13 (by decide) (choices 2) [33,65,96,192] r6023 c6023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2858
  · exact u2859
  · exact u2860
  · exact u2861

def b6024 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 296 209 225 193 193 449), lower := (rows 35 14 21 296 16 32 64 128 256), losses := [] }

theorem u6024 : Upper (D 3) (R 3) [34,12,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6024
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6025 : Route 9 := (fun mask => (mask,id))

def c6025 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6025 : Upper (D 3) (R 3) [34,12,17,320] 13 := by
  apply FastRouting.sound _ _ [34,12,17,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6025 c6025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2862
  · exact u2863
  · exact u2864
  · exact u2865
  · exact u2866
  · exact u2867

def b6026 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 37 73 465 497 465 465 465), lower := (rows 35 14 37 73 16 32 64 128 256), losses := [] }

theorem u6026 : Upper (D 3) (R 3) [34,12,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6026
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6027 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 37 88 465 481 449 449 449), lower := (rows 35 14 37 88 16 32 64 128 256), losses := [] }

theorem u6027 : Upper (D 3) (R 3) [34,12,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6027
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6028 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 37 200 465 497 465 465 465), lower := (rows 35 14 37 200 16 32 64 128 256), losses := [] }

theorem u6028 : Upper (D 3) (R 3) [34,12,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6028
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6029 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 37 265 209 241 209 209 465), lower := (rows 35 14 37 265 16 32 64 128 256), losses := [] }

theorem u6029 : Upper (D 3) (R 3) [34,12,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6029
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6030 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 37 280 209 225 193 193 449), lower := (rows 35 14 37 280 16 32 64 128 256), losses := [] }

theorem u6030 : Upper (D 3) (R 3) [34,12,33,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6030
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6031 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 37 328 209 241 209 209 465), lower := (rows 35 14 37 328 16 32 64 128 256), losses := [] }

theorem u6031 : Upper (D 3) (R 3) [34,12,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6031
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6032 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 52 73 465 481 449 449 449), lower := (rows 35 14 52 73 16 32 64 128 256), losses := [] }

theorem u6032 : Upper (D 3) (R 3) [34,12,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6032
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6033 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 52 200 465 481 449 449 449), lower := (rows 35 14 52 200 16 32 64 128 256), losses := [] }

theorem u6033 : Upper (D 3) (R 3) [34,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6033
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6034 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 52 265 209 225 193 193 449), lower := (rows 35 14 52 265 16 32 64 128 256), losses := [] }

theorem u6034 : Upper (D 3) (R 3) [34,12,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6034
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6035 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 52 328 209 225 193 193 449), lower := (rows 35 14 52 328 16 32 64 128 256), losses := [] }

theorem u6035 : Upper (D 3) (R 3) [34,12,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6035
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6036 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 73 433 433 497 433 433), lower := (rows 35 14 69 73 16 32 64 128 256), losses := [] }

theorem u6036 : Upper (D 3) (R 3) [34,12,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6036
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6037 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 88 433 417 481 417 417), lower := (rows 35 14 69 88 16 32 64 128 256), losses := [] }

theorem u6037 : Upper (D 3) (R 3) [34,12,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6037
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6038 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 104 401 433 465 401 401), lower := (rows 35 14 69 104 16 32 64 128 256), losses := [] }

theorem u6038 : Upper (D 3) (R 3) [34,12,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6038
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6039_129 : Upper (D 3) (R 3) [34,12,65,129,129] 13 :=
  permutation_upper _ _ _ [34,12,65,129,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2869

theorem m6039_160 : Upper (D 3) (R 3) [34,12,65,129,160] 13 :=
  permutation_upper _ _ _ [34,12,65,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2870

theorem m6039_384 : Upper (D 3) (R 3) [34,12,65,129,384] 13 :=
  permutation_upper _ _ _ [34,12,65,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2874

def r6039 : Route 9 := (fun mask => (mask,id))

def c6039 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6039 : Upper (D 3) (R 3) [34,12,65,129] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6039 c6039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2868
  · exact u2869
  · exact u2870
  · exact m6039_129
  · exact m6039_160
  · exact u2871
  · exact u2872
  · exact u2873
  · exact u2874
  · exact m6039_384

def r6040 : Route 9 := (fun mask => (mask,id))

def c6040 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6040 : Upper (D 3) (R 3) [34,12,65,144] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6040 c6040
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2875
  · exact u2876
  · exact u2877
  · exact u2878
  · exact u2879
  · exact u2880
  · exact u2881
  · exact u2882
  · exact u2883
  · exact u2884

def b6041 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 69 168 465 497 465 465 465), lower := (rows 35 14 69 168 16 32 64 128 256), losses := [] }

theorem u6041 : Upper (D 3) (R 3) [34,12,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6041
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6042 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 200 433 433 497 433 433), lower := (rows 35 14 69 200 16 32 64 128 256), losses := [] }

theorem u6042 : Upper (D 3) (R 3) [34,12,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6042
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6043 : Route 9 := (fun mask => (mask,id))

def c6043 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6043 : Upper (D 3) (R 3) [34,12,65,257] 13 := by
  apply FastRouting.sound _ _ [34,12,65,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6043 c6043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2885
  · exact u2886
  · exact u2887
  · exact u2888
  · exact u2889
  · exact u2890

def r6044 : Route 9 := (fun mask => (mask,id))

def c6044 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6044 : Upper (D 3) (R 3) [34,12,65,272] 13 := by
  apply FastRouting.sound _ _ [34,12,65,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6044 c6044
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2891
  · exact u2892
  · exact u2893
  · exact u2894
  · exact u2895
  · exact u2896

def b6045 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 69 296 209 241 209 209 465), lower := (rows 35 14 69 296 16 32 64 128 256), losses := [] }

theorem u6045 : Upper (D 3) (R 3) [34,12,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6045
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6046 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 328 177 177 241 177 433), lower := (rows 35 14 69 328 16 32 64 128 256), losses := [] }

theorem u6046 : Upper (D 3) (R 3) [34,12,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6046
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6047 : Route 9 := (fun mask => (mask,id))

def c6047 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6047 : Upper (D 3) (R 3) [34,12,65,384] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6047 c6047
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2897
  · exact u2898
  · exact u2899
  · exact u2900
  · exact u2901
  · exact u2902

def b6048 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 84 104 401 417 449 385 385), lower := (rows 35 14 84 104 16 32 64 128 256), losses := [] }

theorem u6048 : Upper (D 3) (R 3) [34,12,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6048
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6049 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 84 168 465 481 449 449 449), lower := (rows 35 14 84 168 16 32 64 128 256), losses := [] }

theorem u6049 : Upper (D 3) (R 3) [34,12,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6049
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6050 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 200 433 417 481 417 417), lower := (rows 35 14 84 200 16 32 64 128 256), losses := [] }

theorem u6050 : Upper (D 3) (R 3) [34,12,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6050
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6051 : Route 9 := (fun mask => (mask,id))

def c6051 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6051 : Upper (D 3) (R 3) [34,12,80,257] 13 := by
  apply FastRouting.sound _ _ [34,12,80,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6051 c6051
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2903
  · exact u2904
  · exact u2905
  · exact u2906
  · exact u2907
  · exact u2908

def b6052 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 84 296 209 225 193 193 449), lower := (rows 35 14 84 296 16 32 64 128 256), losses := [] }

theorem u6052 : Upper (D 3) (R 3) [34,12,80,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6052
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6053 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 328 177 161 225 161 417), lower := (rows 35 14 84 328 16 32 64 128 256), losses := [] }

theorem u6053 : Upper (D 3) (R 3) [34,12,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6053
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6054 : Route 9 := (fun mask => (mask,id))

def c6054 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6054 : Upper (D 3) (R 3) [34,12,80,384] 13 := by
  apply FastRouting.sound _ _ [34,12,80,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6054 c6054
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2909
  · exact u2910
  · exact u2911
  · exact u2912
  · exact u2913
  · exact u2914

def b6055 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 100 200 401 433 465 401 401), lower := (rows 35 14 100 200 16 32 64 128 256), losses := [] }

theorem u6055 : Upper (D 3) (R 3) [34,12,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6055
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6056 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 100 265 209 241 209 209 465), lower := (rows 35 14 100 265 16 32 64 128 256), losses := [] }

theorem u6056 : Upper (D 3) (R 3) [34,12,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6056
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6057 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 100 280 209 225 193 193 449), lower := (rows 35 14 100 280 16 32 64 128 256), losses := [] }

theorem u6057 : Upper (D 3) (R 3) [34,12,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6057
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6058 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 100 328 145 177 209 145 401), lower := (rows 35 14 100 328 16 32 64 128 256), losses := [] }

theorem u6058 : Upper (D 3) (R 3) [34,12,96,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6058
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6059 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 100 392 209 241 209 209 465), lower := (rows 35 14 100 392 16 32 64 128 256), losses := [] }

theorem u6059 : Upper (D 3) (R 3) [34,12,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6059
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6059
end Delivery.IrregularNine14.P03
