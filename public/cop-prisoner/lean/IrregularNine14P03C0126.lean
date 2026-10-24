import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0099
import IrregularNine14P03C0100
import IrregularNine14P03C0101
import IrregularNine14P03C0102
import IrregularNine14P03C0103
import IrregularNine14P03C0104
import IrregularNine14P03C0105

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7560 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7560 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7560 : Upper (D 3) (R 3) [6,96,384] 13 := by
  apply FastRouting.sound _ _ [6,96,384] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r7560 c7560
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5962
  · exact u5963
  · exact u5964
  · exact u5965
  · exact u5966
  · exact u5967
  · exact u5968

def b7561 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 13 505 497 497 497 497 497), lower := (rows 35 7 13 8 16 32 64 128 256), losses := [] }

theorem u7561 : Upper (D 3) (R 3) [34,5,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7561
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7562 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7562 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7562 : Upper (D 3) (R 3) [34,5,24] 13 := by
  apply FastRouting.sound _ _ [34,5,24] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r7562 c7562
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5969
  · exact u5970
  · exact u5971
  · exact u5972
  · exact u5973
  · exact u5974
  · exact u5975

def b7563 : PairBound 9 := { available := 473, camps := [{ cop := 5, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 37 473 473 505 473 473 473), lower := (rows 35 7 37 8 16 32 64 128 256), losses := [] }

theorem u7563 : Upper (D 3) (R 3) [34,5,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7563
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7564 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 44 473 465 497 465 465 465), lower := (rows 35 7 44 8 16 32 64 128 256), losses := [] }

theorem u7564 : Upper (D 3) (R 3) [34,5,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7564
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7565 : PairBound 9 := { available := 505, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 69 505 505 505 505 505 505), lower := (rows 35 7 69 8 16 32 64 128 256), losses := [] }

theorem u7565 : Upper (D 3) (R 3) [34,5,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7565
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7566 : Route 9 := (fun mask => (mask,id))

def c7566 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7566 : Upper (D 3) (R 3) [34,5,72] 13 := by
  apply FastRouting.sound _ _ [34,5,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r7566 c7566
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5976
  · exact u5977
  · exact u5978
  · exact u5979
  · exact u5980
  · exact u5981
  · exact u5982
  · exact u5983
  · exact u5984
  · exact u5985
  · exact u5986
  · exact u5987
  · exact u5988
  · exact u5989
  · exact u5990

def b7567 : PairBound 9 := { available := 473, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 100 473 473 505 473 473 473), lower := (rows 35 7 100 8 16 32 64 128 256), losses := [] }

theorem u7567 : Upper (D 3) (R 3) [34,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7567
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7568 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7568 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7568 : Upper (D 3) (R 3) [34,5,192] 13 := by
  apply FastRouting.sound _ _ [34,5,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r7568 c7568
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5991
  · exact u5992
  · exact u5993
  · exact u5994
  · exact u5995
  · exact u5996
  · exact u5997
  · exact u5998
  · exact u5999
  · exact u6000
  · exact u6001

def b7569 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 261 249 249 249 249 249 505), lower := (rows 35 7 261 8 16 32 64 128 256), losses := [] }

theorem u7569 : Upper (D 3) (R 3) [34,5,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7569
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7570 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7570 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7570 : Upper (D 3) (R 3) [34,5,264] 13 := by
  apply FastRouting.sound _ _ [34,5,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r7570 c7570
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6002
  · exact u6003
  · exact u6004
  · exact u6005
  · exact u6006
  · exact u6007
  · exact u6008

def b7571 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 292 217 217 249 217 217 473), lower := (rows 35 7 292 8 16 32 64 128 256), losses := [] }

theorem u7571 : Upper (D 3) (R 3) [34,5,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7571
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7572 : Route 9 := (fun mask => (mask,id))

def c7572 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7572 : Upper (D 3) (R 3) [34,5,320] 13 := by
  apply FastRouting.sound _ _ [34,5,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r7572 c7572
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6009
  · exact u6010
  · exact u6011
  · exact u6012
  · exact u6013
  · exact u6014
  · exact u6015
  · exact u6016
  · exact u6017
  · exact u6018

def r7573 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7573 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7573 : Upper (D 3) (R 3) [34,12,17] 13 := by
  apply FastRouting.sound _ _ [34,12,17] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r7573 c7573
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6019
  · exact u6020
  · exact u6021
  · exact u6022
  · exact u6023
  · exact u6024
  · exact u6025

def b7574 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 37 473 465 497 465 465 465), lower := (rows 35 14 37 8 16 32 64 128 256), losses := [] }

theorem u7574 : Upper (D 3) (R 3) [34,12,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7574
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7575 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 52 457 465 481 449 449 449), lower := (rows 35 14 52 8 16 32 64 128 256), losses := [] }

theorem u7575 : Upper (D 3) (R 3) [34,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7575
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7576_17 : Upper (D 3) (R 3) [34,12,65,17] 13 :=
  permutation_upper _ _ _ [34,12,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6020

theorem m7576_33 : Upper (D 3) (R 3) [34,12,65,33] 13 :=
  permutation_upper _ _ _ [34,12,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6026

theorem m7576_48 : Upper (D 3) (R 3) [34,12,65,48] 13 :=
  permutation_upper _ _ _ [34,12,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6032

def r7576 : Route 9 := (fun mask => (mask,id))

def c7576 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7576 : Upper (D 3) (R 3) [34,12,65] 13 := by
  apply FastRouting.sound _ _ [34,12,65] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r7576 c7576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7576_17
  · exact m7576_33
  · exact m7576_48
  · exact u6036
  · exact u6037
  · exact u6038
  · exact u6039
  · exact u6040
  · exact u6041
  · exact u6042
  · exact u6043
  · exact u6044
  · exact u6045
  · exact u6046
  · exact u6047

theorem m7577_33 : Upper (D 3) (R 3) [34,12,80,33] 13 :=
  permutation_upper _ _ _ [34,12,33,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6027

theorem m7577_65 : Upper (D 3) (R 3) [34,12,80,65] 13 :=
  permutation_upper _ _ _ [34,12,65,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6037

theorem m7577_129 : Upper (D 3) (R 3) [34,12,80,129] 13 :=
  permutation_upper _ _ _ [34,12,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6040

def r7577 : Route 9 := (fun mask => (mask,id))

def c7577 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7577 : Upper (D 3) (R 3) [34,12,80] 13 := by
  apply FastRouting.sound _ _ [34,12,80] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r7577 c7577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7577_33
  · exact m7577_65
  · exact u6048
  · exact m7577_129
  · exact u6049
  · exact u6050
  · exact u6051
  · exact u6052
  · exact u6053
  · exact u6054

def b7578 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 100 473 465 497 465 465 465), lower := (rows 35 14 100 8 16 32 64 128 256), losses := [] }

theorem u7578 : Upper (D 3) (R 3) [34,12,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7578
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7579_17 : Upper (D 3) (R 3) [34,12,192,17] 13 :=
  permutation_upper _ _ _ [34,12,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6022

theorem m7579_33 : Upper (D 3) (R 3) [34,12,192,33] 13 :=
  permutation_upper _ _ _ [34,12,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6028

theorem m7579_48 : Upper (D 3) (R 3) [34,12,192,48] 13 :=
  permutation_upper _ _ _ [34,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6033

theorem m7579_65 : Upper (D 3) (R 3) [34,12,192,65] 13 :=
  permutation_upper _ _ _ [34,12,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6042

theorem m7579_80 : Upper (D 3) (R 3) [34,12,192,80] 13 :=
  permutation_upper _ _ _ [34,12,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6050

theorem m7579_96 : Upper (D 3) (R 3) [34,12,192,96] 13 :=
  permutation_upper _ _ _ [34,12,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6055

def r7579 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7579 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7579 : Upper (D 3) (R 3) [34,12,192] 13 := by
  apply FastRouting.sound _ _ [34,12,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r7579 c7579
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7579_17
  · exact m7579_33
  · exact m7579_48
  · exact m7579_65
  · exact m7579_80
  · exact m7579_96
  · exact u6060
  · exact u6061
  · exact u6062
  · exact u6063
  · exact u6064

theorem m7580_17 : Upper (D 3) (R 3) [34,12,257,17] 13 :=
  permutation_upper _ _ _ [34,12,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6023

theorem m7580_33 : Upper (D 3) (R 3) [34,12,257,33] 13 :=
  permutation_upper _ _ _ [34,12,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6029

theorem m7580_48 : Upper (D 3) (R 3) [34,12,257,48] 13 :=
  permutation_upper _ _ _ [34,12,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6034

theorem m7580_65 : Upper (D 3) (R 3) [34,12,257,65] 13 :=
  permutation_upper _ _ _ [34,12,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6043

theorem m7580_80 : Upper (D 3) (R 3) [34,12,257,80] 13 :=
  permutation_upper _ _ _ [34,12,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6051

theorem m7580_96 : Upper (D 3) (R 3) [34,12,257,96] 13 :=
  permutation_upper _ _ _ [34,12,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6056

theorem m7580_192 : Upper (D 3) (R 3) [34,12,257,192] 13 :=
  permutation_upper _ _ _ [34,12,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6061

def r7580 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7580 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7580 : Upper (D 3) (R 3) [34,12,257] 13 := by
  apply FastRouting.sound _ _ [34,12,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r7580 c7580
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7580_17
  · exact m7580_33
  · exact m7580_48
  · exact m7580_65
  · exact m7580_80
  · exact m7580_96
  · exact m7580_192

theorem m7581_33 : Upper (D 3) (R 3) [34,12,272,33] 13 :=
  permutation_upper _ _ _ [34,12,33,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6030

theorem m7581_65 : Upper (D 3) (R 3) [34,12,272,65] 13 :=
  permutation_upper _ _ _ [34,12,65,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6044

theorem m7581_96 : Upper (D 3) (R 3) [34,12,272,96] 13 :=
  permutation_upper _ _ _ [34,12,96,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6057

theorem m7581_192 : Upper (D 3) (R 3) [34,12,272,192] 13 :=
  permutation_upper _ _ _ [34,12,192,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6062

def r7581 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7581 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7581 : Upper (D 3) (R 3) [34,12,272] 13 := by
  apply FastRouting.sound _ _ [34,12,272] 13 (by decide) (choices 2) [33,65,96,192] r7581 c7581
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7581_33
  · exact m7581_65
  · exact m7581_96
  · exact m7581_192

def b7582 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 292 217 209 241 209 209 465), lower := (rows 35 14 292 8 16 32 64 128 256), losses := [] }

theorem u7582 : Upper (D 3) (R 3) [34,12,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7582
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7583_17 : Upper (D 3) (R 3) [34,12,320,17] 13 :=
  permutation_upper _ _ _ [34,12,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6025

theorem m7583_33 : Upper (D 3) (R 3) [34,12,320,33] 13 :=
  permutation_upper _ _ _ [34,12,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6031

theorem m7583_48 : Upper (D 3) (R 3) [34,12,320,48] 13 :=
  permutation_upper _ _ _ [34,12,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6035

theorem m7583_65 : Upper (D 3) (R 3) [34,12,320,65] 13 :=
  permutation_upper _ _ _ [34,12,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6046

theorem m7583_80 : Upper (D 3) (R 3) [34,12,320,80] 13 :=
  permutation_upper _ _ _ [34,12,80,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6053

theorem m7583_96 : Upper (D 3) (R 3) [34,12,320,96] 13 :=
  permutation_upper _ _ _ [34,12,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6058

theorem m7583_129 : Upper (D 3) (R 3) [34,12,320,129] 13 :=
  permutation_upper _ _ _ [34,12,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6047

theorem m7583_144 : Upper (D 3) (R 3) [34,12,320,144] 13 :=
  permutation_upper _ _ _ [34,12,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6054

theorem m7583_160 : Upper (D 3) (R 3) [34,12,320,160] 13 :=
  permutation_upper _ _ _ [34,12,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6059

theorem m7583_192 : Upper (D 3) (R 3) [34,12,320,192] 13 :=
  permutation_upper _ _ _ [34,12,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6064

def r7583 : Route 9 := (fun mask => (mask,id))

def c7583 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7583 : Upper (D 3) (R 3) [34,12,320] 13 := by
  apply FastRouting.sound _ _ [34,12,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r7583 c7583
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7583_17
  · exact m7583_33
  · exact m7583_48
  · exact m7583_65
  · exact m7583_80
  · exact m7583_96
  · exact m7583_129
  · exact m7583_144
  · exact m7583_160
  · exact m7583_192

def r7584 : Route 9 := (fun mask => (mask,id))

def c7584 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u7584 : Upper (D 3) (R 3) [34,65,9] 13 := by
  apply FastRouting.sound _ _ [34,65,9] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r7584 c7584
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6065
  · exact u6066
  · exact u6067
  · exact u6068
  · exact u6069
  · exact u6070
  · exact u6071
  · exact u6072
  · exact u6073
  · exact u6074
  · exact u6075
  · exact u6076
  · exact u6077
  · exact u6078
  · exact u6079
  · exact u6080
  · exact u6081
  · exact u6082
  · exact u6083
  · exact u6084
  · exact u6085

theorem m7585_5 : Upper (D 3) (R 3) [34,65,24,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6067

def r7585 : Route 9 := (fun mask => (mask,id))

def c7585 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7585 : Upper (D 3) (R 3) [34,65,24] 13 := by
  apply FastRouting.sound _ _ [34,65,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r7585 c7585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7585_5
  · exact u6097
  · exact u6098
  · exact u6099
  · exact u6100
  · exact u6101
  · exact u6102
  · exact u6103
  · exact u6104
  · exact u6105
  · exact u6106
  · exact u6107
  · exact u6108
  · exact u6109
  · exact u6110

def b7586 : PairBound 9 := { available := 477, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 477 477 509 477 477 477), lower := (rows 35 67 37 8 16 32 64 128 256), losses := [] }

theorem u7586 : Upper (D 3) (R 3) [34,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7586
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7587_5 : Upper (D 3) (R 3) [34,65,40,5] 13 :=
  permutation_upper _ _ _ [34,65,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6069

theorem m7587_17 : Upper (D 3) (R 3) [34,65,40,17] 13 :=
  permutation_upper _ _ _ [34,65,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6086

theorem m7587_20 : Upper (D 3) (R 3) [34,65,40,20] 13 :=
  permutation_upper _ _ _ [34,65,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6098

def r7587 : Route 9 := (fun mask => (mask,id))

def c7587 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u7587 : Upper (D 3) (R 3) [34,65,40] 13 := by
  apply FastRouting.sound _ _ [34,65,40] 13 (by decide) (choices 2) [5,17,20,65,68,80,129,132,144,192,257,260,272,320,384] r7587 c7587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7587_5
  · exact m7587_17
  · exact m7587_20
  · exact u6119
  · exact u6120
  · exact u6121
  · exact u6122
  · exact u6123
  · exact u6124
  · exact u6125
  · exact u6126
  · exact u6127
  · exact u6128
  · exact u6129
  · exact u6130

def b7588 : PairBound 9 := { available := 445, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 445 445 445 509 445 445), lower := (rows 35 67 69 8 16 32 64 128 256), losses := [] }

theorem u7588 : Upper (D 3) (R 3) [34,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7588
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7589_5 : Upper (D 3) (R 3) [34,65,72,5] 13 :=
  permutation_upper _ _ _ [34,65,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6072

theorem m7589_17 : Upper (D 3) (R 3) [34,65,72,17] 13 :=
  permutation_upper _ _ _ [34,65,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6087

theorem m7589_20 : Upper (D 3) (R 3) [34,65,72,20] 13 :=
  permutation_upper _ _ _ [34,65,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6100

theorem m7589_33 : Upper (D 3) (R 3) [34,65,72,33] 13 :=
  permutation_upper _ _ _ [34,65,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6111

theorem m7589_36 : Upper (D 3) (R 3) [34,65,72,36] 13 :=
  permutation_upper _ _ _ [34,65,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6120

theorem m7589_48 : Upper (D 3) (R 3) [34,65,72,48] 13 :=
  permutation_upper _ _ _ [34,65,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6131

def r7589 : Route 9 := (fun mask => (mask,id))

def c7589 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u7589 : Upper (D 3) (R 3) [34,65,72] 13 := by
  apply FastRouting.sound _ _ [34,65,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r7589 c7589
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7589_5
  · exact m7589_17
  · exact m7589_20
  · exact m7589_33
  · exact m7589_36
  · exact m7589_48
  · exact u6146
  · exact u6147
  · exact u6148
  · exact u6149
  · exact u6150
  · exact u6151
  · exact u6152
  · exact u6153
  · exact u6154

def b7590 : PairBound 9 := { available := 413, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 413 413 445 477 413 413), lower := (rows 35 67 100 8 16 32 64 128 256), losses := [] }

theorem u7590 : Upper (D 3) (R 3) [34,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7590
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7591_5 : Upper (D 3) (R 3) [34,65,129,5] 13 :=
  permutation_upper _ _ _ [34,65,9,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6075

theorem m7591_17 : Upper (D 3) (R 3) [34,65,129,17] 13 :=
  permutation_upper _ _ _ [34,65,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6088

theorem m7591_20 : Upper (D 3) (R 3) [34,65,129,20] 13 :=
  permutation_upper _ _ _ [34,65,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6102

theorem m7591_33 : Upper (D 3) (R 3) [34,65,129,33] 13 :=
  permutation_upper _ _ _ [34,65,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6112

theorem m7591_36 : Upper (D 3) (R 3) [34,65,129,36] 13 :=
  permutation_upper _ _ _ [34,65,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6122

theorem m7591_48 : Upper (D 3) (R 3) [34,65,129,48] 13 :=
  permutation_upper _ _ _ [34,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6132

theorem m7591_65 : Upper (D 3) (R 3) [34,65,129,65] 13 :=
  permutation_upper _ _ _ [34,65,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6139

theorem m7591_68 : Upper (D 3) (R 3) [34,65,129,68] 13 :=
  permutation_upper _ _ _ [34,65,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6146

theorem m7591_80 : Upper (D 3) (R 3) [34,65,129,80] 13 :=
  permutation_upper _ _ _ [34,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6155

theorem m7591_96 : Upper (D 3) (R 3) [34,65,129,96] 13 :=
  permutation_upper _ _ _ [34,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6162

def r7591 : Route 9 := (fun mask => (mask,id))

def c7591 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u7591 : Upper (D 3) (R 3) [34,65,129] 13 := by
  apply FastRouting.sound _ _ [34,65,129] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r7591 c7591
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7591_5
  · exact m7591_17
  · exact m7591_20
  · exact m7591_33
  · exact m7591_36
  · exact m7591_48
  · exact m7591_65
  · exact m7591_68
  · exact m7591_80
  · exact m7591_96
  · exact u6167
  · exact u6168
  · exact u6169
  · exact u6170
  · exact u6171
  · exact u6172
  · exact u6173
  · exact u6174
  · exact u6175
  · exact u6176
  · exact u6177

theorem m7592_5 : Upper (D 3) (R 3) [34,65,136,5] 13 :=
  permutation_upper _ _ _ [34,65,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6076

theorem m7592_17 : Upper (D 3) (R 3) [34,65,136,17] 13 :=
  permutation_upper _ _ _ [34,65,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6089

theorem m7592_20 : Upper (D 3) (R 3) [34,65,136,20] 13 :=
  permutation_upper _ _ _ [34,65,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6103

theorem m7592_33 : Upper (D 3) (R 3) [34,65,136,33] 13 :=
  permutation_upper _ _ _ [34,65,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6113

theorem m7592_36 : Upper (D 3) (R 3) [34,65,136,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6123

theorem m7592_48 : Upper (D 3) (R 3) [34,65,136,48] 13 :=
  permutation_upper _ _ _ [34,65,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6133

theorem m7592_65 : Upper (D 3) (R 3) [34,65,136,65] 13 :=
  permutation_upper _ _ _ [34,65,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6140

theorem m7592_68 : Upper (D 3) (R 3) [34,65,136,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6147

theorem m7592_80 : Upper (D 3) (R 3) [34,65,136,80] 13 :=
  permutation_upper _ _ _ [34,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6156

theorem m7592_96 : Upper (D 3) (R 3) [34,65,136,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6163

theorem m7592_129 : Upper (D 3) (R 3) [34,65,136,129] 13 :=
  permutation_upper _ _ _ [34,65,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6168

def r7592 : Route 9 := (fun mask => (mask,id))

def c7592 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u7592 : Upper (D 3) (R 3) [34,65,136] 13 := by
  apply FastRouting.sound _ _ [34,65,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r7592 c7592
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7592_5
  · exact m7592_17
  · exact m7592_20
  · exact m7592_33
  · exact m7592_36
  · exact m7592_48
  · exact m7592_65
  · exact m7592_68
  · exact m7592_80
  · exact m7592_96
  · exact m7592_129
  · exact u6178
  · exact u6179
  · exact u6180
  · exact u6181
  · exact u6182
  · exact u6183
  · exact u6184
  · exact u6185
  · exact u6186
  · exact u6187

theorem m7593_5 : Upper (D 3) (R 3) [34,65,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6078

theorem m7593_17 : Upper (D 3) (R 3) [34,65,160,17] 13 :=
  permutation_upper _ _ _ [34,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6090

theorem m7593_20 : Upper (D 3) (R 3) [34,65,160,20] 13 :=
  permutation_upper _ _ _ [34,65,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6104

theorem m7593_65 : Upper (D 3) (R 3) [34,65,160,65] 13 :=
  permutation_upper _ _ _ [34,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6141

theorem m7593_68 : Upper (D 3) (R 3) [34,65,160,68] 13 :=
  permutation_upper _ _ _ [34,65,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6149

theorem m7593_80 : Upper (D 3) (R 3) [34,65,160,80] 13 :=
  permutation_upper _ _ _ [34,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6157

theorem m7593_129 : Upper (D 3) (R 3) [34,65,160,129] 13 :=
  permutation_upper _ _ _ [34,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6170

theorem m7593_132 : Upper (D 3) (R 3) [34,65,160,132] 13 :=
  permutation_upper _ _ _ [34,65,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6180

theorem m7593_144 : Upper (D 3) (R 3) [34,65,160,144] 13 :=
  permutation_upper _ _ _ [34,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6188

def r7593 : Route 9 := (fun mask => (mask,id))

def c7593 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u7593 : Upper (D 3) (R 3) [34,65,160] 13 := by
  apply FastRouting.sound _ _ [34,65,160] 13 (by decide) (choices 2) [5,17,20,65,68,80,129,132,144,192,257,260,272,320,384] r7593 c7593
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7593_5
  · exact m7593_17
  · exact m7593_20
  · exact m7593_65
  · exact m7593_68
  · exact m7593_80
  · exact m7593_129
  · exact m7593_132
  · exact m7593_144
  · exact u6195
  · exact u6196
  · exact u6197
  · exact u6198
  · exact u6199
  · exact u6200

theorem m7594_5 : Upper (D 3) (R 3) [34,65,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6079

theorem m7594_17 : Upper (D 3) (R 3) [34,65,192,17] 13 :=
  permutation_upper _ _ _ [34,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6091

theorem m7594_20 : Upper (D 3) (R 3) [34,65,192,20] 13 :=
  permutation_upper _ _ _ [34,65,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6105

theorem m7594_33 : Upper (D 3) (R 3) [34,65,192,33] 13 :=
  permutation_upper _ _ _ [34,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6114

theorem m7594_36 : Upper (D 3) (R 3) [34,65,192,36] 13 :=
  permutation_upper _ _ _ [34,65,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6125

theorem m7594_48 : Upper (D 3) (R 3) [34,65,192,48] 13 :=
  permutation_upper _ _ _ [34,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6134

theorem m7594_129 : Upper (D 3) (R 3) [34,65,192,129] 13 :=
  permutation_upper _ _ _ [34,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6171

theorem m7594_132 : Upper (D 3) (R 3) [34,65,192,132] 13 :=
  permutation_upper _ _ _ [34,65,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6181

theorem m7594_144 : Upper (D 3) (R 3) [34,65,192,144] 13 :=
  permutation_upper _ _ _ [34,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6189

theorem m7594_160 : Upper (D 3) (R 3) [34,65,192,160] 13 :=
  permutation_upper _ _ _ [34,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6195

def r7594 : Route 9 := (fun mask => (mask,id))

def c7594 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u7594 : Upper (D 3) (R 3) [34,65,192] 13 := by
  apply FastRouting.sound _ _ [34,65,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r7594 c7594
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7594_5
  · exact m7594_17
  · exact m7594_20
  · exact m7594_33
  · exact m7594_36
  · exact m7594_48
  · exact m7594_129
  · exact m7594_132
  · exact m7594_144
  · exact m7594_160
  · exact u6201
  · exact u6202
  · exact u6203
  · exact u6204
  · exact u6205

theorem m7595_5 : Upper (D 3) (R 3) [34,65,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6080

theorem m7595_17 : Upper (D 3) (R 3) [34,65,257,17] 13 :=
  permutation_upper _ _ _ [34,65,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6092

theorem m7595_20 : Upper (D 3) (R 3) [34,65,257,20] 13 :=
  permutation_upper _ _ _ [34,65,24,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6106

theorem m7595_33 : Upper (D 3) (R 3) [34,65,257,33] 13 :=
  permutation_upper _ _ _ [34,65,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6115

theorem m7595_36 : Upper (D 3) (R 3) [34,65,257,36] 13 :=
  permutation_upper _ _ _ [34,65,40,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6126

theorem m7595_48 : Upper (D 3) (R 3) [34,65,257,48] 13 :=
  permutation_upper _ _ _ [34,65,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6135

theorem m7595_65 : Upper (D 3) (R 3) [34,65,257,65] 13 :=
  permutation_upper _ _ _ [34,65,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6142

theorem m7595_68 : Upper (D 3) (R 3) [34,65,257,68] 13 :=
  permutation_upper _ _ _ [34,65,72,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6150

theorem m7595_80 : Upper (D 3) (R 3) [34,65,257,80] 13 :=
  permutation_upper _ _ _ [34,65,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6158

theorem m7595_96 : Upper (D 3) (R 3) [34,65,257,96] 13 :=
  permutation_upper _ _ _ [34,65,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6164

theorem m7595_129 : Upper (D 3) (R 3) [34,65,257,129] 13 :=
  permutation_upper _ _ _ [34,65,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6172

theorem m7595_132 : Upper (D 3) (R 3) [34,65,257,132] 13 :=
  permutation_upper _ _ _ [34,65,136,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6182

theorem m7595_144 : Upper (D 3) (R 3) [34,65,257,144] 13 :=
  permutation_upper _ _ _ [34,65,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6190

theorem m7595_160 : Upper (D 3) (R 3) [34,65,257,160] 13 :=
  permutation_upper _ _ _ [34,65,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6196

theorem m7595_192 : Upper (D 3) (R 3) [34,65,257,192] 13 :=
  permutation_upper _ _ _ [34,65,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6201

def r7595 : Route 9 := (fun mask => (mask,id))

def c7595 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7595 : Upper (D 3) (R 3) [34,65,257] 13 := by
  apply FastRouting.sound _ _ [34,65,257] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r7595 c7595
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7595_5
  · exact m7595_17
  · exact m7595_20
  · exact m7595_33
  · exact m7595_36
  · exact m7595_48
  · exact m7595_65
  · exact m7595_68
  · exact m7595_80
  · exact m7595_96
  · exact m7595_129
  · exact m7595_132
  · exact m7595_144
  · exact m7595_160
  · exact m7595_192

theorem m7596_5 : Upper (D 3) (R 3) [34,65,264,5] 13 :=
  permutation_upper _ _ _ [34,65,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6081

theorem m7596_17 : Upper (D 3) (R 3) [34,65,264,17] 13 :=
  permutation_upper _ _ _ [34,65,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6093

theorem m7596_20 : Upper (D 3) (R 3) [34,65,264,20] 13 :=
  permutation_upper _ _ _ [34,65,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6107

theorem m7596_33 : Upper (D 3) (R 3) [34,65,264,33] 13 :=
  permutation_upper _ _ _ [34,65,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6116

theorem m7596_36 : Upper (D 3) (R 3) [34,65,264,36] 13 :=
  permutation_upper _ _ _ [34,65,40,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6127

theorem m7596_48 : Upper (D 3) (R 3) [34,65,264,48] 13 :=
  permutation_upper _ _ _ [34,65,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6136

theorem m7596_65 : Upper (D 3) (R 3) [34,65,264,65] 13 :=
  permutation_upper _ _ _ [34,65,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6143

theorem m7596_68 : Upper (D 3) (R 3) [34,65,264,68] 13 :=
  permutation_upper _ _ _ [34,65,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6151

theorem m7596_80 : Upper (D 3) (R 3) [34,65,264,80] 13 :=
  permutation_upper _ _ _ [34,65,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6159

theorem m7596_96 : Upper (D 3) (R 3) [34,65,264,96] 13 :=
  permutation_upper _ _ _ [34,65,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6165

theorem m7596_129 : Upper (D 3) (R 3) [34,65,264,129] 13 :=
  permutation_upper _ _ _ [34,65,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6173

theorem m7596_132 : Upper (D 3) (R 3) [34,65,264,132] 13 :=
  permutation_upper _ _ _ [34,65,136,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6183

theorem m7596_144 : Upper (D 3) (R 3) [34,65,264,144] 13 :=
  permutation_upper _ _ _ [34,65,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6191

theorem m7596_160 : Upper (D 3) (R 3) [34,65,264,160] 13 :=
  permutation_upper _ _ _ [34,65,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6197

theorem m7596_192 : Upper (D 3) (R 3) [34,65,264,192] 13 :=
  permutation_upper _ _ _ [34,65,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6202

def r7596 : Route 9 := (fun mask => (mask,id))

def c7596 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7596 : Upper (D 3) (R 3) [34,65,264] 13 := by
  apply FastRouting.sound _ _ [34,65,264] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r7596 c7596
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7596_5
  · exact m7596_17
  · exact m7596_20
  · exact m7596_33
  · exact m7596_36
  · exact m7596_48
  · exact m7596_65
  · exact m7596_68
  · exact m7596_80
  · exact m7596_96
  · exact m7596_129
  · exact m7596_132
  · exact m7596_144
  · exact m7596_160
  · exact m7596_192

theorem m7597_5 : Upper (D 3) (R 3) [34,65,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6083

theorem m7597_17 : Upper (D 3) (R 3) [34,65,288,17] 13 :=
  permutation_upper _ _ _ [34,65,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6094

theorem m7597_20 : Upper (D 3) (R 3) [34,65,288,20] 13 :=
  permutation_upper _ _ _ [34,65,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6108

theorem m7597_65 : Upper (D 3) (R 3) [34,65,288,65] 13 :=
  permutation_upper _ _ _ [34,65,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6144

theorem m7597_68 : Upper (D 3) (R 3) [34,65,288,68] 13 :=
  permutation_upper _ _ _ [34,65,72,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6153

theorem m7597_80 : Upper (D 3) (R 3) [34,65,288,80] 13 :=
  permutation_upper _ _ _ [34,65,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6160

theorem m7597_129 : Upper (D 3) (R 3) [34,65,288,129] 13 :=
  permutation_upper _ _ _ [34,65,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6175

theorem m7597_132 : Upper (D 3) (R 3) [34,65,288,132] 13 :=
  permutation_upper _ _ _ [34,65,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6185

theorem m7597_144 : Upper (D 3) (R 3) [34,65,288,144] 13 :=
  permutation_upper _ _ _ [34,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6192

theorem m7597_192 : Upper (D 3) (R 3) [34,65,288,192] 13 :=
  permutation_upper _ _ _ [34,65,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6204

def r7597 : Route 9 := (fun mask => (mask,id))

def c7597 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7597 : Upper (D 3) (R 3) [34,65,288] 13 := by
  apply FastRouting.sound _ _ [34,65,288] 13 (by decide) (choices 2) [5,17,20,65,68,80,129,132,144,192] r7597 c7597
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7597_5
  · exact m7597_17
  · exact m7597_20
  · exact m7597_65
  · exact m7597_68
  · exact m7597_80
  · exact m7597_129
  · exact m7597_132
  · exact m7597_144
  · exact m7597_192

theorem m7598_5 : Upper (D 3) (R 3) [34,65,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6084

theorem m7598_17 : Upper (D 3) (R 3) [34,65,320,17] 13 :=
  permutation_upper _ _ _ [34,65,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6095

theorem m7598_20 : Upper (D 3) (R 3) [34,65,320,20] 13 :=
  permutation_upper _ _ _ [34,65,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6109

theorem m7598_33 : Upper (D 3) (R 3) [34,65,320,33] 13 :=
  permutation_upper _ _ _ [34,65,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6117

theorem m7598_36 : Upper (D 3) (R 3) [34,65,320,36] 13 :=
  permutation_upper _ _ _ [34,65,40,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6129

theorem m7598_48 : Upper (D 3) (R 3) [34,65,320,48] 13 :=
  permutation_upper _ _ _ [34,65,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6137

theorem m7598_129 : Upper (D 3) (R 3) [34,65,320,129] 13 :=
  permutation_upper _ _ _ [34,65,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6176

theorem m7598_132 : Upper (D 3) (R 3) [34,65,320,132] 13 :=
  permutation_upper _ _ _ [34,65,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6186

theorem m7598_144 : Upper (D 3) (R 3) [34,65,320,144] 13 :=
  permutation_upper _ _ _ [34,65,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6193

theorem m7598_160 : Upper (D 3) (R 3) [34,65,320,160] 13 :=
  permutation_upper _ _ _ [34,65,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6199

def r7598 : Route 9 := (fun mask => (mask,id))

def c7598 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7598 : Upper (D 3) (R 3) [34,65,320] 13 := by
  apply FastRouting.sound _ _ [34,65,320] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r7598 c7598
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7598_5
  · exact m7598_17
  · exact m7598_20
  · exact m7598_33
  · exact m7598_36
  · exact m7598_48
  · exact m7598_129
  · exact m7598_132
  · exact m7598_144
  · exact m7598_160

theorem m7599_5 : Upper (D 3) (R 3) [34,65,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6085

theorem m7599_17 : Upper (D 3) (R 3) [34,65,384,17] 13 :=
  permutation_upper _ _ _ [34,65,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6096

theorem m7599_20 : Upper (D 3) (R 3) [34,65,384,20] 13 :=
  permutation_upper _ _ _ [34,65,24,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6110

theorem m7599_33 : Upper (D 3) (R 3) [34,65,384,33] 13 :=
  permutation_upper _ _ _ [34,65,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6118

theorem m7599_36 : Upper (D 3) (R 3) [34,65,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6130

theorem m7599_48 : Upper (D 3) (R 3) [34,65,384,48] 13 :=
  permutation_upper _ _ _ [34,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6138

theorem m7599_65 : Upper (D 3) (R 3) [34,65,384,65] 13 :=
  permutation_upper _ _ _ [34,65,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6145

theorem m7599_68 : Upper (D 3) (R 3) [34,65,384,68] 13 :=
  permutation_upper _ _ _ [34,65,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6154

theorem m7599_80 : Upper (D 3) (R 3) [34,65,384,80] 13 :=
  permutation_upper _ _ _ [34,65,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6161

theorem m7599_96 : Upper (D 3) (R 3) [34,65,384,96] 13 :=
  permutation_upper _ _ _ [34,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6166

theorem m7599_129 : Upper (D 3) (R 3) [34,65,384,129] 13 :=
  permutation_upper _ _ _ [34,65,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6177

theorem m7599_132 : Upper (D 3) (R 3) [34,65,384,132] 13 :=
  permutation_upper _ _ _ [34,65,136,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6187

theorem m7599_144 : Upper (D 3) (R 3) [34,65,384,144] 13 :=
  permutation_upper _ _ _ [34,65,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6194

theorem m7599_160 : Upper (D 3) (R 3) [34,65,384,160] 13 :=
  permutation_upper _ _ _ [34,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6200

theorem m7599_192 : Upper (D 3) (R 3) [34,65,384,192] 13 :=
  permutation_upper _ _ _ [34,65,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6205

def r7599 : Route 9 := (fun mask => (mask,id))

def c7599 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7599 : Upper (D 3) (R 3) [34,65,384] 13 := by
  apply FastRouting.sound _ _ [34,65,384] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r7599 c7599
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7599_5
  · exact m7599_17
  · exact m7599_20
  · exact m7599_33
  · exact m7599_36
  · exact m7599_48
  · exact m7599_65
  · exact m7599_68
  · exact m7599_80
  · exact m7599_96
  · exact m7599_129
  · exact m7599_132
  · exact m7599_144
  · exact m7599_160
  · exact m7599_192

def r7600 : Route 9 := (fun mask => (mask,id))

def c7600 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7600 : Upper (D 3) (R 3) [34,68,9] 13 := by
  apply FastRouting.sound _ _ [34,68,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r7600 c7600
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6206
  · exact u6207
  · exact u6208
  · exact u6209
  · exact u6210
  · exact u6211
  · exact u6212
  · exact u6213
  · exact u6214
  · exact u6215
  · exact u6216
  · exact u6217
  · exact u6218
  · exact u6219
  · exact u6220

def r7601 : Route 9 := (fun mask => (mask,id))

def c7601 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7601 : Upper (D 3) (R 3) [34,68,24] 13 := by
  apply FastRouting.sound _ _ [34,68,24] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r7601 c7601
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6221
  · exact u6222
  · exact u6223
  · exact u6224
  · exact u6225
  · exact u6226
  · exact u6227
  · exact u6228
  · exact u6229
  · exact u6230

def b7602 : PairBound 9 := { available := 473, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 37 473 473 505 473 473 473), lower := (rows 35 70 37 8 16 32 64 128 256), losses := [] }

theorem u7602 : Upper (D 3) (R 3) [34,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7602
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7603 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 44 473 465 497 465 465 465), lower := (rows 35 70 44 8 16 32 64 128 256), losses := [] }

theorem u7603 : Upper (D 3) (R 3) [34,68,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7603
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7604 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 69 441 441 441 505 441 441), lower := (rows 35 70 69 8 16 32 64 128 256), losses := [] }

theorem u7604 : Upper (D 3) (R 3) [34,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7604
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7605 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 76 441 433 433 497 433 433), lower := (rows 35 70 76 8 16 32 64 128 256), losses := [] }

theorem u7605 : Upper (D 3) (R 3) [34,68,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7605
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7606 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 100 409 409 441 473 409 409), lower := (rows 35 70 100 8 16 32 64 128 256), losses := [] }

theorem u7606 : Upper (D 3) (R 3) [34,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7606
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7607 : Route 9 := (fun mask => (mask,id))

def c7607 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7607 : Upper (D 3) (R 3) [34,68,129] 13 := by
  apply FastRouting.sound _ _ [34,68,129] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r7607 c7607
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6231
  · exact u6232
  · exact u6233
  · exact u6234
  · exact u6235
  · exact u6236
  · exact u6237
  · exact u6238
  · exact u6239
  · exact u6240
  · exact u6241
  · exact u6242
  · exact u6243
  · exact u6244
  · exact u6245

def r7608 : Route 9 := (fun mask => (mask,id))

def c7608 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7608 : Upper (D 3) (R 3) [34,68,136] 13 := by
  apply FastRouting.sound _ _ [34,68,136] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r7608 c7608
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6246
  · exact u6247
  · exact u6248
  · exact u6249
  · exact u6250
  · exact u6251
  · exact u6252
  · exact u6253
  · exact u6254
  · exact u6255
  · exact u6256
  · exact u6257
  · exact u6258
  · exact u6259
  · exact u6260

def b7609 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 164 473 473 505 473 473 473), lower := (rows 35 70 164 8 16 32 64 128 256), losses := [] }

theorem u7609 : Upper (D 3) (R 3) [34,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7609
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7610 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 196 441 441 441 505 441 441), lower := (rows 35 70 196 8 16 32 64 128 256), losses := [] }

theorem u7610 : Upper (D 3) (R 3) [34,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7610
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7611 : Route 9 := (fun mask => (mask,id))

def c7611 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7611 : Upper (D 3) (R 3) [34,68,257] 13 := by
  apply FastRouting.sound _ _ [34,68,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r7611 c7611
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6261
  · exact u6262
  · exact u6263
  · exact u6264
  · exact u6265
  · exact u6266
  · exact u6267
  · exact u6268
  · exact u6269
  · exact u6270

def r7612 : Route 9 := (fun mask => (mask,id))

def c7612 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7612 : Upper (D 3) (R 3) [34,68,264] 13 := by
  apply FastRouting.sound _ _ [34,68,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r7612 c7612
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6271
  · exact u6272
  · exact u6273
  · exact u6274
  · exact u6275
  · exact u6276
  · exact u6277
  · exact u6278
  · exact u6279
  · exact u6280

def b7613 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 292 217 217 249 217 217 473), lower := (rows 35 70 292 8 16 32 64 128 256), losses := [] }

theorem u7613 : Upper (D 3) (R 3) [34,68,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7613
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7614 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 185, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 324 185 185 185 249 185 441), lower := (rows 35 70 324 8 16 32 64 128 256), losses := [] }

theorem u7614 : Upper (D 3) (R 3) [34,68,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7614
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7615 : Route 9 := (fun mask => (mask,id))

def c7615 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7615 : Upper (D 3) (R 3) [34,68,384] 13 := by
  apply FastRouting.sound _ _ [34,68,384] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r7615 c7615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6281
  · exact u6282
  · exact u6283
  · exact u6284
  · exact u6285
  · exact u6286
  · exact u6287
  · exact u6288
  · exact u6289
  · exact u6290

def r7616 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7616 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u7616 : Upper (D 3) (R 3) [34,192,9] 13 := by
  apply FastRouting.sound _ _ [34,192,9] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192,257,260,272,288,320] r7616 c7616
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6291
  · exact u6292
  · exact u6293
  · exact u6294
  · exact u6295
  · exact u6296
  · exact u6297
  · exact u6298
  · exact u6299
  · exact u6300
  · exact u6301
  · exact u6302
  · exact u6303
  · exact u6304
  · exact u6305
  · exact u6306

theorem m7617_5 : Upper (D 3) (R 3) [34,192,24,5] 13 :=
  permutation_upper _ _ _ [34,192,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6293

def r7617 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7617 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7617 : Upper (D 3) (R 3) [34,192,24] 13 := by
  apply FastRouting.sound _ _ [34,192,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,192,257,260,288,320] r7617 c7617
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7617_5
  · exact u6314
  · exact u6315
  · exact u6316
  · exact u6317
  · exact u6318
  · exact u6319
  · exact u6320
  · exact u6321
  · exact u6322
  · exact u6323

def b7618 : PairBound 9 := { available := 477, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 37 477 477 509 477 477 477), lower := (rows 35 194 37 8 16 32 64 128 256), losses := [] }

theorem u7618 : Upper (D 3) (R 3) [34,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7618
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7619_5 : Upper (D 3) (R 3) [34,192,40,5] 13 :=
  permutation_upper _ _ _ [34,192,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6295

theorem m7619_17 : Upper (D 3) (R 3) [34,192,40,17] 13 :=
  permutation_upper _ _ _ [34,192,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6307

theorem m7619_20 : Upper (D 3) (R 3) [34,192,40,20] 13 :=
  permutation_upper _ _ _ [34,192,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6315

def r7619 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7619 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u7619 : Upper (D 3) (R 3) [34,192,40] 13 := by
  apply FastRouting.sound _ _ [34,192,40] 13 (by decide) (choices 2) [5,17,20,65,68,80,192,257,260,272,320] r7619 c7619
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7619_5
  · exact m7619_17
  · exact m7619_20
  · exact u6328
  · exact u6329
  · exact u6330
  · exact u6331
  · exact u6332
  · exact u6333
  · exact u6334
  · exact u6335

#print axioms u7619
end Delivery.IrregularNine14.P03
