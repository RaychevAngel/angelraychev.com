import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0141
import IrregularNine14P05C0142
import IrregularNine14P05C0143
import IrregularNine14P05C0144
import IrregularNine14P05C0145
import IrregularNine14P05C0146
import IrregularNine14P05C0147
import IrregularNine14P05C0148
import IrregularNine14P05C0149
import IrregularNine14P05C0150
import IrregularNine14P05C0151
import IrregularNine14P05C0152
import IrregularNine14P05C0153

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9600 : PairBound 9 := { available := 445, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 70 445 445 445 509 445 445), lower := (rows 7 42 70 8 16 32 64 128 256), losses := [] }

theorem u9600 : Upper (D 5) (R 5) [6,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9600
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9601_3 : Upper (D 5) (R 5) [6,40,72,3] 13 :=
  permutation_upper _ _ _ [6,12,33,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8603

theorem m9601_5 : Upper (D 5) (R 5) [6,40,72,5] 13 :=
  permutation_upper _ _ _ [6,12,65,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8623

theorem m9601_6 : Upper (D 5) (R 5) [6,40,72,6] 13 :=
  permutation_upper _ _ _ [6,33,65,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8845

def r9601 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9601 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9601 : Upper (D 5) (R 5) [6,40,72] 13 := by
  apply FastRouting.sound _ _ [6,40,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160,384] r9601 c9601
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9601_3
  · exact m9601_5
  · exact m9601_6
  · exact u8985
  · exact u8986
  · exact u8987
  · exact u8988
  · exact u8989
  · exact u8990
  · exact u8991
  · exact u8992
  · exact u8993
  · exact u8994
  · exact u8995
  · exact u8996
  · exact u8997

theorem m9602_3 : Upper (D 5) (R 5) [6,40,80,3] 13 :=
  permutation_upper _ _ _ [6,12,33,80] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8605

theorem m9602_5 : Upper (D 5) (R 5) [6,40,80,5] 13 :=
  permutation_upper _ _ _ [6,12,80,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8645

theorem m9602_6 : Upper (D 5) (R 5) [6,40,80,6] 13 :=
  permutation_upper _ _ _ [6,33,80,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8878

def r9602 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9602 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9602 : Upper (D 5) (R 5) [6,40,80] 13 := by
  apply FastRouting.sound _ _ [6,40,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9602 c9602
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9602_3
  · exact m9602_5
  · exact m9602_6
  · exact u8998
  · exact u8999
  · exact u9000
  · exact u9001
  · exact u9002
  · exact u9003
  · exact u9004
  · exact u9005

def b9603 : PairBound 9 := { available := 415, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 415 415 447 479 415 415), lower := (rows 7 42 100 8 16 32 64 128 256), losses := [] }

theorem u9603 : Upper (D 5) (R 5) [6,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9603
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9604_3 : Upper (D 5) (R 5) [6,40,192,3] 13 :=
  permutation_upper _ _ _ [6,12,33,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8607

theorem m9604_5 : Upper (D 5) (R 5) [6,40,192,5] 13 :=
  permutation_upper _ _ _ [6,12,192,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8662

theorem m9604_6 : Upper (D 5) (R 5) [6,40,192,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8895

def r9604 : Route 9 := (fun mask => (mask,id))

def c9604 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9604 : Upper (D 5) (R 5) [6,40,192] 13 := by
  apply FastRouting.sound _ _ [6,40,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9604 c9604
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9604_3
  · exact m9604_5
  · exact m9604_6
  · exact u9014
  · exact u9015
  · exact u9016
  · exact u9017
  · exact u9018
  · exact u9019
  · exact u9020
  · exact u9021
  · exact u9022
  · exact u9023
  · exact u9024
  · exact u9025

theorem m9605_3 : Upper (D 5) (R 5) [6,48,65,3] 13 :=
  permutation_upper _ _ _ [6,12,48,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8618

theorem m9605_5 : Upper (D 5) (R 5) [6,48,65,5] 13 :=
  permutation_upper _ _ _ [6,12,66,48] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8633

def r9605 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9605 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9605 : Upper (D 5) (R 5) [6,48,65] 13 := by
  apply FastRouting.sound _ _ [6,48,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9605 c9605
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9605_3
  · exact m9605_5
  · exact u9026
  · exact u9027
  · exact u9028
  · exact u9029
  · exact u9030
  · exact u9031
  · exact u9032
  · exact u9033
  · exact u9034

def b9606 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 70 429 445 429 493 429 429), lower := (rows 7 50 70 8 16 32 64 128 256), losses := [] }

theorem u9606 : Upper (D 5) (R 5) [6,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9606
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9607_3 : Upper (D 5) (R 5) [6,48,72,3] 13 :=
  permutation_upper _ _ _ [6,12,48,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8617

theorem m9607_5 : Upper (D 5) (R 5) [6,48,72,5] 13 :=
  permutation_upper _ _ _ [6,12,65,48] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8625

theorem m9607_6 : Upper (D 5) (R 5) [6,48,72,6] 13 :=
  permutation_upper _ _ _ [6,48,65,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9026

def r9607 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9607 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9607 : Upper (D 5) (R 5) [6,48,72] 13 := by
  apply FastRouting.sound _ _ [6,48,72] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9607 c9607
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9607_3
  · exact m9607_5
  · exact m9607_6
  · exact u9041
  · exact u9042
  · exact u9043
  · exact u9044
  · exact u9045
  · exact u9046
  · exact u9047
  · exact u9048

def b9608 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 50 100 399 415 431 463 399 399), lower := (rows 7 50 100 8 16 32 64 128 256), losses := [] }

theorem u9608 : Upper (D 5) (R 5) [6,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9608
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9609_3 : Upper (D 5) (R 5) [6,48,192,3] 13 :=
  permutation_upper _ _ _ [6,12,48,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8620

theorem m9609_5 : Upper (D 5) (R 5) [6,48,192,5] 13 :=
  permutation_upper _ _ _ [6,12,192,48] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8664

def r9609 : Route 9 := (fun mask => (mask,id))

def c9609 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9609 : Upper (D 5) (R 5) [6,48,192] 13 := by
  apply FastRouting.sound _ _ [6,48,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9609 c9609
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9609_3
  · exact m9609_5
  · exact u9053
  · exact u9054
  · exact u9055
  · exact u9056
  · exact u9057
  · exact u9058
  · exact u9059
  · exact u9060

def b9610 : PairBound 9 := { available := 318, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 133 318 318 318 382 446 318), lower := (rows 7 67 133 8 16 32 64 128 256), losses := [] }

theorem u9610 : Upper (D 5) (R 5) [6,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9611 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 317 317 317 381 445 317), lower := (rows 7 67 134 8 16 32 64 128 256), losses := [] }

theorem u9611 : Upper (D 5) (R 5) [6,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9611
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9612_3 : Upper (D 5) (R 5) [6,65,136,3] 13 :=
  permutation_upper _ _ _ [6,12,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8634

theorem m9612_5 : Upper (D 5) (R 5) [6,65,136,5] 13 :=
  permutation_upper _ _ _ [6,12,65,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8627

def r9612 : Route 9 := (fun mask => (mask,id))

def c9612 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9612 : Upper (D 5) (R 5) [6,65,136] 13 := by
  apply FastRouting.sound _ _ [6,65,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9612 c9612
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9612_3
  · exact m9612_5
  · exact u9077
  · exact u9078
  · exact u9079
  · exact u9080
  · exact u9081
  · exact u9082
  · exact u9083
  · exact u9084
  · exact u9085
  · exact u9086
  · exact u9087
  · exact u9088
  · exact u9089

theorem m9613_3 : Upper (D 5) (R 5) [6,65,144,3] 13 :=
  permutation_upper _ _ _ [6,12,66,144] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8635

theorem m9613_5 : Upper (D 5) (R 5) [6,65,144,5] 13 :=
  permutation_upper _ _ _ [6,12,80,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8648

def r9613 : Route 9 := (fun mask => (mask,id))

def c9613 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9613 : Upper (D 5) (R 5) [6,65,144] 13 := by
  apply FastRouting.sound _ _ [6,65,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9613 c9613
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9613_3
  · exact m9613_5
  · exact u9090
  · exact u9091
  · exact u9092
  · exact u9093
  · exact u9094
  · exact u9095
  · exact u9096
  · exact u9097

theorem m9614_3 : Upper (D 5) (R 5) [6,65,160,3] 13 :=
  permutation_upper _ _ _ [6,12,66,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8636

theorem m9614_5 : Upper (D 5) (R 5) [6,65,160,5] 13 :=
  permutation_upper _ _ _ [6,12,96,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8656

def r9614 : Route 9 := (fun mask => (mask,id))

def c9614 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9614 : Upper (D 5) (R 5) [6,65,160] 13 := by
  apply FastRouting.sound _ _ [6,65,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9614 c9614
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9614_3
  · exact m9614_5
  · exact u9098
  · exact u9099
  · exact u9100
  · exact u9101
  · exact u9102
  · exact u9103
  · exact u9104
  · exact u9105
  · exact u9106
  · exact u9107
  · exact u9108
  · exact u9109
  · exact u9110

theorem m9615_3 : Upper (D 5) (R 5) [6,65,384,3] 13 :=
  permutation_upper _ _ _ [6,12,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8637

theorem m9615_5 : Upper (D 5) (R 5) [6,65,384,5] 13 :=
  permutation_upper _ _ _ [6,12,192,258] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8666

def r9615 : Route 9 := (fun mask => (mask,id))

def c9615 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9615 : Upper (D 5) (R 5) [6,65,384] 13 := by
  apply FastRouting.sound _ _ [6,65,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r9615 c9615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9615_3
  · exact m9615_5
  · exact u9111
  · exact u9112
  · exact u9113
  · exact u9114
  · exact u9115
  · exact u9116
  · exact u9117
  · exact u9118

def b9616 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 312, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 70 134 313 313 313 377 441 313), lower := (rows 7 70 134 8 16 32 64 128 256), losses := [] }

theorem u9616 : Upper (D 5) (R 5) [6,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9617 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 315 315 315 379 443 315), lower := (rows 7 70 140 8 16 32 64 128 256), losses := [] }

theorem u9617 : Upper (D 5) (R 5) [6,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9618 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 148 299 315 299 363 427 299), lower := (rows 7 70 148 8 16 32 64 128 256), losses := [] }

theorem u9618 : Upper (D 5) (R 5) [6,68,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9618
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9619 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 315 315 315 379 443 315), lower := (rows 7 70 164 8 16 32 64 128 256), losses := [] }

theorem u9619 : Upper (D 5) (R 5) [6,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9619
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9620 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 388 59 59 59 123 187 315), lower := (rows 7 70 388 8 16 32 64 128 256), losses := [] }

theorem u9620 : Upper (D 5) (R 5) [6,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9620
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9621_3 : Upper (D 5) (R 5) [6,72,136,3] 13 :=
  permutation_upper _ _ _ [6,12,65,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8626

theorem m9621_5 : Upper (D 5) (R 5) [6,72,136,5] 13 :=
  permutation_upper _ _ _ [6,12,65,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8626

theorem m9621_6 : Upper (D 5) (R 5) [6,72,136,6] 13 :=
  permutation_upper _ _ _ [6,65,129,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9061

theorem m9621_20 : Upper (D 5) (R 5) [6,72,136,20] 13 :=
  permutation_upper _ _ _ [6,72,136,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9154

theorem m9621_36 : Upper (D 5) (R 5) [6,72,136,36] 13 :=
  permutation_upper _ _ _ [6,72,136,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9156

theorem m9621_260 : Upper (D 5) (R 5) [6,72,136,260] 13 :=
  permutation_upper _ _ _ [6,72,136,258] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9159

def r9621 : Route 9 := (fun mask => (mask,id))

def c9621 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9621 : Upper (D 5) (R 5) [6,72,136] 13 := by
  apply FastRouting.sound _ _ [6,72,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9621 c9621
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9621_3
  · exact m9621_5
  · exact m9621_6
  · exact u9153
  · exact u9154
  · exact m9621_20
  · exact u9155
  · exact u9156
  · exact m9621_36
  · exact u9157
  · exact u9158
  · exact u9159
  · exact m9621_260
  · exact u9160
  · exact u9161

theorem m9622_3 : Upper (D 5) (R 5) [6,72,144,3] 13 :=
  permutation_upper _ _ _ [6,12,65,144] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8628

theorem m9622_5 : Upper (D 5) (R 5) [6,72,144,5] 13 :=
  permutation_upper _ _ _ [6,12,80,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8647

theorem m9622_6 : Upper (D 5) (R 5) [6,72,144,6] 13 :=
  permutation_upper _ _ _ [6,65,144,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9090

def r9622 : Route 9 := (fun mask => (mask,id))

def c9622 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9622 : Upper (D 5) (R 5) [6,72,144] 13 := by
  apply FastRouting.sound _ _ [6,72,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9622 c9622
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9622_3
  · exact m9622_5
  · exact m9622_6
  · exact u9162
  · exact u9163
  · exact u9164
  · exact u9165
  · exact u9166
  · exact u9167
  · exact u9168

theorem m9623_3 : Upper (D 5) (R 5) [6,72,160,3] 13 :=
  permutation_upper _ _ _ [6,12,65,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8629

theorem m9623_5 : Upper (D 5) (R 5) [6,72,160,5] 13 :=
  permutation_upper _ _ _ [6,12,96,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8655

theorem m9623_6 : Upper (D 5) (R 5) [6,72,160,6] 13 :=
  permutation_upper _ _ _ [6,65,160,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9098

def r9623 : Route 9 := (fun mask => (mask,id))

def c9623 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9623 : Upper (D 5) (R 5) [6,72,160] 13 := by
  apply FastRouting.sound _ _ [6,72,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9623 c9623
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9623_3
  · exact m9623_5
  · exact m9623_6
  · exact u9169
  · exact u9170
  · exact u9171
  · exact u9172
  · exact u9173
  · exact u9174
  · exact u9175
  · exact u9176
  · exact u9177
  · exact u9178
  · exact u9179
  · exact u9180

theorem m9624_3 : Upper (D 5) (R 5) [6,72,384,3] 13 :=
  permutation_upper _ _ _ [6,12,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8630

theorem m9624_5 : Upper (D 5) (R 5) [6,72,384,5] 13 :=
  permutation_upper _ _ _ [6,12,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8665

theorem m9624_6 : Upper (D 5) (R 5) [6,72,384,6] 13 :=
  permutation_upper _ _ _ [6,65,384,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9111

def r9624 : Route 9 := (fun mask => (mask,id))

def c9624 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9624 : Upper (D 5) (R 5) [6,72,384] 13 := by
  apply FastRouting.sound _ _ [6,72,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r9624 c9624
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9624_3
  · exact m9624_5
  · exact m9624_6
  · exact u9181
  · exact u9182
  · exact u9183
  · exact u9184
  · exact u9185
  · exact u9186
  · exact u9187

theorem m9625_3 : Upper (D 5) (R 5) [6,80,160,3] 13 :=
  permutation_upper _ _ _ [6,12,80,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8649

theorem m9625_5 : Upper (D 5) (R 5) [6,80,160,5] 13 :=
  permutation_upper _ _ _ [6,12,96,144] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8657

def r9625 : Route 9 := (fun mask => (mask,id))

def c9625 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9625 : Upper (D 5) (R 5) [6,80,160] 13 := by
  apply FastRouting.sound _ _ [6,80,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9625 c9625
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9625_3
  · exact m9625_5
  · exact u9188
  · exact u9189
  · exact u9190
  · exact u9191
  · exact u9192
  · exact u9193
  · exact u9194
  · exact u9195

theorem m9626_3 : Upper (D 5) (R 5) [6,80,384,3] 13 :=
  permutation_upper _ _ _ [6,12,80,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8650

theorem m9626_5 : Upper (D 5) (R 5) [6,80,384,5] 13 :=
  permutation_upper _ _ _ [6,12,192,272] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8667

def r9626 : Route 9 := (fun mask => (mask,id))

def c9626 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9626 : Upper (D 5) (R 5) [6,80,384] 13 := by
  apply FastRouting.sound _ _ [6,80,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9626 c9626
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9626_3
  · exact m9626_5
  · exact u9196
  · exact u9197
  · exact u9198
  · exact u9199

def b9627 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 287 287 319 351 415 287), lower := (rows 7 98 164 8 16 32 64 128 256), losses := [] }

theorem u9627 : Upper (D 5) (R 5) [6,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9627
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9628_3 : Upper (D 5) (R 5) [6,96,384,3] 13 :=
  permutation_upper _ _ _ [6,12,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8659

theorem m9628_5 : Upper (D 5) (R 5) [6,96,384,5] 13 :=
  permutation_upper _ _ _ [6,12,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8668

def r9628 : Route 9 := (fun mask => (mask,id))

def c9628 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9628 : Upper (D 5) (R 5) [6,96,384] 13 := by
  apply FastRouting.sound _ _ [6,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r9628 c9628
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9628_3
  · exact m9628_5
  · exact u9205
  · exact u9206
  · exact u9207
  · exact u9208
  · exact u9209
  · exact u9210
  · exact u9211
  · exact u9212

def b9629 : PairBound 9 := { available := 486, camps := [{ cop := 3, region := 3, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 11 21 494 502 486 486 486 486), lower := (rows 11 11 21 8 16 32 64 128 256), losses := [] }

theorem u9629 : Upper (D 5) (R 5) [10,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9630 : PairBound 9 := { available := 502, camps := [{ cop := 3, region := 3, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 11 37 510 502 502 502 502 502), lower := (rows 11 11 37 8 16 32 64 128 256), losses := [] }

theorem u9630 : Upper (D 5) (R 5) [10,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9631 : PairBound 9 := { available := 487, camps := [{ cop := 3, region := 3, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 11 52 495 503 487 487 487 487), lower := (rows 11 11 52 8 16 32 64 128 256), losses := [] }

theorem u9631 : Upper (D 5) (R 5) [10,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9631
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9632 : PairBound 9 := { available := 438, camps := [{ cop := 3, region := 3, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 11 69 446 438 438 502 438 438), lower := (rows 11 11 69 8 16 32 64 128 256), losses := [] }

theorem u9632 : Upper (D 5) (R 5) [10,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9632
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9633 : PairBound 9 := { available := 423, camps := [{ cop := 3, region := 3, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 11 84 431 439 423 487 423 423), lower := (rows 11 11 84 8 16 32 64 128 256), losses := [] }

theorem u9633 : Upper (D 5) (R 5) [10,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9633
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9634 : PairBound 9 := { available := 439, camps := [{ cop := 3, region := 3, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 11 100 447 439 439 503 439 439), lower := (rows 11 11 100 8 16 32 64 128 256), losses := [] }

theorem u9634 : Upper (D 5) (R 5) [10,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9634
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9635 : PairBound 9 := { available := 311, camps := [{ cop := 3, region := 3, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 11 196 319 311 311 375 439 311), lower := (rows 11 11 196 8 16 32 64 128 256), losses := [] }

theorem u9635 : Upper (D 5) (R 5) [10,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9636 : PairBound 9 := { available := 487, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 14 21 495 503 487 487 487 487), lower := (rows 11 14 21 8 16 32 64 128 256), losses := [] }

theorem u9636 : Upper (D 5) (R 5) [10,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9636
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9637 : PairBound 9 := { available := 503, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 14 37 511 503 503 503 503 503), lower := (rows 11 14 37 8 16 32 64 128 256), losses := [] }

theorem u9637 : Upper (D 5) (R 5) [10,12,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9637
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9638 : PairBound 9 := { available := 487, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 14 52 495 503 487 487 487 487), lower := (rows 11 14 52 8 16 32 64 128 256), losses := [] }

theorem u9638 : Upper (D 5) (R 5) [10,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9639 : PairBound 9 := { available := 439, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 14 69 447 439 439 503 439 439), lower := (rows 11 14 69 8 16 32 64 128 256), losses := [] }

theorem u9639 : Upper (D 5) (R 5) [10,12,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9639
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9640 : PairBound 9 := { available := 423, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 14 84 431 439 423 487 423 423), lower := (rows 11 14 84 8 16 32 64 128 256), losses := [] }

theorem u9640 : Upper (D 5) (R 5) [10,12,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9640
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9641 : PairBound 9 := { available := 439, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 14 100 447 439 439 503 439 439), lower := (rows 11 14 100 8 16 32 64 128 256), losses := [] }

theorem u9641 : Upper (D 5) (R 5) [10,12,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9641
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9642 : PairBound 9 := { available := 311, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 14 196 319 311 311 375 439 311), lower := (rows 11 14 196 8 16 32 64 128 256), losses := [] }

theorem u9642 : Upper (D 5) (R 5) [10,12,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9642
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9643_6 : Upper (D 5) (R 5) [10,17,33,6] 13 :=
  permutation_upper _ _ _ [6,12,17,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8586

theorem m9643_34 : Upper (D 5) (R 5) [10,17,33,34] 13 :=
  permutation_upper _ _ _ [6,17,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8675

theorem m9643_36 : Upper (D 5) (R 5) [10,17,33,36] 13 :=
  permutation_upper _ _ _ [6,17,40,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8681

theorem m9643_66 : Upper (D 5) (R 5) [10,17,33,66] 13 :=
  permutation_upper _ _ _ [6,17,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8696

theorem m9643_68 : Upper (D 5) (R 5) [10,17,33,68] 13 :=
  permutation_upper _ _ _ [6,17,72,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8703

theorem m9643_96 : Upper (D 5) (R 5) [10,17,33,96] 13 :=
  permutation_upper _ _ _ [6,17,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8712

theorem m9643_192 : Upper (D 5) (R 5) [10,17,33,192] 13 :=
  permutation_upper _ _ _ [6,17,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8721

def r9643 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9643 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9643 : Upper (D 5) (R 5) [10,17,33] 13 := by
  apply FastRouting.sound _ _ [10,17,33] 13 (by decide) (choices 2) [6,34,36,66,68,96,192] r9643 c9643
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9643_6
  · exact m9643_34
  · exact m9643_36
  · exact m9643_66
  · exact m9643_68
  · exact m9643_96
  · exact m9643_192

theorem m9644_5 : Upper (D 5) (R 5) [10,17,34,5] 13 :=
  permutation_upper _ _ _ [6,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8532

theorem m9644_33 : Upper (D 5) (R 5) [10,17,34,33] 13 :=
  permutation_upper _ _ _ [6,17,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8670

theorem m9644_36 : Upper (D 5) (R 5) [10,17,34,36] 13 :=
  permutation_upper _ _ _ [6,17,40,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8682

theorem m9644_65 : Upper (D 5) (R 5) [10,17,34,65] 13 :=
  permutation_upper _ _ _ [6,17,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8690

theorem m9644_68 : Upper (D 5) (R 5) [10,17,34,68] 13 :=
  permutation_upper _ _ _ [6,17,72,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8704

theorem m9644_96 : Upper (D 5) (R 5) [10,17,34,96] 13 :=
  permutation_upper _ _ _ [6,17,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8713

theorem m9644_192 : Upper (D 5) (R 5) [10,17,34,192] 13 :=
  permutation_upper _ _ _ [6,17,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8722

def r9644 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9644 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9644 : Upper (D 5) (R 5) [10,17,34] 13 := by
  apply FastRouting.sound _ _ [10,17,34] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r9644 c9644
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9644_5
  · exact m9644_33
  · exact m9644_36
  · exact m9644_65
  · exact m9644_68
  · exact m9644_96
  · exact m9644_192

theorem m9645_6 : Upper (D 5) (R 5) [10,17,65,6] 13 :=
  permutation_upper _ _ _ [6,12,17,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8588

theorem m9645_34 : Upper (D 5) (R 5) [10,17,65,34] 13 :=
  permutation_upper _ _ _ [6,17,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8676

theorem m9645_36 : Upper (D 5) (R 5) [10,17,65,36] 13 :=
  permutation_upper _ _ _ [6,17,40,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8684

theorem m9645_130 : Upper (D 5) (R 5) [10,17,65,130] 13 :=
  permutation_upper _ _ _ [6,17,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8698

theorem m9645_132 : Upper (D 5) (R 5) [10,17,65,132] 13 :=
  permutation_upper _ _ _ [6,17,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8706

theorem m9645_160 : Upper (D 5) (R 5) [10,17,65,160] 13 :=
  permutation_upper _ _ _ [6,17,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8715

theorem m9645_384 : Upper (D 5) (R 5) [10,17,65,384] 13 :=
  permutation_upper _ _ _ [6,17,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8724

def r9645 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9645 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9645 : Upper (D 5) (R 5) [10,17,65] 13 := by
  apply FastRouting.sound _ _ [10,17,65] 13 (by decide) (choices 2) [6,34,36,130,132,160,384] r9645 c9645
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9645_6
  · exact m9645_34
  · exact m9645_36
  · exact m9645_130
  · exact m9645_132
  · exact m9645_160
  · exact m9645_384

theorem m9646_5 : Upper (D 5) (R 5) [10,17,66,5] 13 :=
  permutation_upper _ _ _ [6,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8533

theorem m9646_33 : Upper (D 5) (R 5) [10,17,66,33] 13 :=
  permutation_upper _ _ _ [6,17,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8671

theorem m9646_36 : Upper (D 5) (R 5) [10,17,66,36] 13 :=
  permutation_upper _ _ _ [6,17,40,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8685

theorem m9646_129 : Upper (D 5) (R 5) [10,17,66,129] 13 :=
  permutation_upper _ _ _ [6,17,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8692

theorem m9646_132 : Upper (D 5) (R 5) [10,17,66,132] 13 :=
  permutation_upper _ _ _ [6,17,72,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8707

theorem m9646_160 : Upper (D 5) (R 5) [10,17,66,160] 13 :=
  permutation_upper _ _ _ [6,17,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8716

theorem m9646_384 : Upper (D 5) (R 5) [10,17,66,384] 13 :=
  permutation_upper _ _ _ [6,17,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8725

def r9646 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9646 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9646 : Upper (D 5) (R 5) [10,17,66] 13 := by
  apply FastRouting.sound _ _ [10,17,66] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r9646 c9646
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9646_5
  · exact m9646_33
  · exact m9646_36
  · exact m9646_129
  · exact m9646_132
  · exact m9646_160
  · exact m9646_384

theorem m9647_3 : Upper (D 5) (R 5) [10,17,96,3] 13 :=
  permutation_upper _ _ _ [6,5,17,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8478

theorem m9647_5 : Upper (D 5) (R 5) [10,17,96,5] 13 :=
  permutation_upper _ _ _ [6,9,17,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8534

theorem m9647_6 : Upper (D 5) (R 5) [10,17,96,6] 13 :=
  permutation_upper _ _ _ [6,12,17,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8590

theorem m9647_33 : Upper (D 5) (R 5) [10,17,96,33] 13 :=
  permutation_upper _ _ _ [6,17,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8673

theorem m9647_34 : Upper (D 5) (R 5) [10,17,96,34] 13 :=
  permutation_upper _ _ _ [6,17,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8678

theorem m9647_36 : Upper (D 5) (R 5) [10,17,96,36] 13 :=
  permutation_upper _ _ _ [6,17,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8687

theorem m9647_129 : Upper (D 5) (R 5) [10,17,96,129] 13 :=
  permutation_upper _ _ _ [6,17,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8694

theorem m9647_130 : Upper (D 5) (R 5) [10,17,96,130] 13 :=
  permutation_upper _ _ _ [6,17,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8700

theorem m9647_132 : Upper (D 5) (R 5) [10,17,96,132] 13 :=
  permutation_upper _ _ _ [6,17,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8709

theorem m9647_160 : Upper (D 5) (R 5) [10,17,96,160] 13 :=
  permutation_upper _ _ _ [6,17,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8718

theorem m9647_384 : Upper (D 5) (R 5) [10,17,96,384] 13 :=
  permutation_upper _ _ _ [6,17,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8727

def r9647 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9647 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9647 : Upper (D 5) (R 5) [10,17,96] 13 := by
  apply FastRouting.sound _ _ [10,17,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9647 c9647
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9647_3
  · exact m9647_5
  · exact m9647_6
  · exact m9647_33
  · exact m9647_34
  · exact m9647_36
  · exact m9647_129
  · exact m9647_130
  · exact m9647_132
  · exact m9647_160
  · exact m9647_384

theorem m9648_3 : Upper (D 5) (R 5) [10,17,192,3] 13 :=
  permutation_upper _ _ _ [6,5,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8479

theorem m9648_5 : Upper (D 5) (R 5) [10,17,192,5] 13 :=
  permutation_upper _ _ _ [6,9,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8535

theorem m9648_6 : Upper (D 5) (R 5) [10,17,192,6] 13 :=
  permutation_upper _ _ _ [6,12,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8591

theorem m9648_33 : Upper (D 5) (R 5) [10,17,192,33] 13 :=
  permutation_upper _ _ _ [6,17,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8674

theorem m9648_34 : Upper (D 5) (R 5) [10,17,192,34] 13 :=
  permutation_upper _ _ _ [6,17,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8679

theorem m9648_36 : Upper (D 5) (R 5) [10,17,192,36] 13 :=
  permutation_upper _ _ _ [6,17,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8688

theorem m9648_257 : Upper (D 5) (R 5) [10,17,192,257] 13 :=
  permutation_upper _ _ _ [6,17,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8695

theorem m9648_258 : Upper (D 5) (R 5) [10,17,192,258] 13 :=
  permutation_upper _ _ _ [6,17,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8701

theorem m9648_260 : Upper (D 5) (R 5) [10,17,192,260] 13 :=
  permutation_upper _ _ _ [6,17,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8710

theorem m9648_288 : Upper (D 5) (R 5) [10,17,192,288] 13 :=
  permutation_upper _ _ _ [6,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8719

def r9648 : Route 9 := (fun mask => (mask,id))

def c9648 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9648 : Upper (D 5) (R 5) [10,17,192] 13 := by
  apply FastRouting.sound _ _ [10,17,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9648 c9648
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9648_3
  · exact m9648_5
  · exact m9648_6
  · exact m9648_33
  · exact m9648_34
  · exact m9648_36
  · exact m9648_257
  · exact m9648_258
  · exact m9648_260
  · exact m9648_288

theorem m9649_3 : Upper (D 5) (R 5) [10,20,33,3] 13 :=
  permutation_upper _ _ _ [6,5,24,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8480

theorem m9649_5 : Upper (D 5) (R 5) [10,20,33,5] 13 :=
  permutation_upper _ _ _ [6,9,24,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8540

theorem m9649_6 : Upper (D 5) (R 5) [10,20,33,6] 13 :=
  permutation_upper _ _ _ [6,12,24,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8596

theorem m9649_33 : Upper (D 5) (R 5) [10,20,33,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8767

theorem m9649_34 : Upper (D 5) (R 5) [10,20,33,34] 13 :=
  permutation_upper _ _ _ [6,24,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8775

theorem m9649_36 : Upper (D 5) (R 5) [10,20,33,36] 13 :=
  permutation_upper _ _ _ [6,24,40,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8780

theorem m9649_65 : Upper (D 5) (R 5) [10,20,33,65] 13 :=
  permutation_upper _ _ _ [6,24,65,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8788

theorem m9649_66 : Upper (D 5) (R 5) [10,20,33,66] 13 :=
  permutation_upper _ _ _ [6,24,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8796

theorem m9649_68 : Upper (D 5) (R 5) [10,20,33,68] 13 :=
  permutation_upper _ _ _ [6,24,72,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8802

theorem m9649_96 : Upper (D 5) (R 5) [10,20,33,96] 13 :=
  permutation_upper _ _ _ [6,24,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8810

theorem m9649_192 : Upper (D 5) (R 5) [10,20,33,192] 13 :=
  permutation_upper _ _ _ [6,24,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8818

def r9649 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9649 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9649 : Upper (D 5) (R 5) [10,20,33] 13 := by
  apply FastRouting.sound _ _ [10,20,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r9649 c9649
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9649_3
  · exact m9649_5
  · exact m9649_6
  · exact m9649_33
  · exact m9649_34
  · exact m9649_36
  · exact m9649_65
  · exact m9649_66
  · exact m9649_68
  · exact m9649_96
  · exact m9649_192

theorem m9650_5 : Upper (D 5) (R 5) [10,20,34,5] 13 :=
  permutation_upper _ _ _ [6,9,24,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8542

theorem m9650_33 : Upper (D 5) (R 5) [10,20,34,33] 13 :=
  permutation_upper _ _ _ [6,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8768

theorem m9650_36 : Upper (D 5) (R 5) [10,20,34,36] 13 :=
  permutation_upper _ _ _ [6,24,40,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8781

theorem m9650_65 : Upper (D 5) (R 5) [10,20,34,65] 13 :=
  permutation_upper _ _ _ [6,24,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8789

theorem m9650_68 : Upper (D 5) (R 5) [10,20,34,68] 13 :=
  permutation_upper _ _ _ [6,24,72,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8803

theorem m9650_96 : Upper (D 5) (R 5) [10,20,34,96] 13 :=
  permutation_upper _ _ _ [6,24,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8811

theorem m9650_192 : Upper (D 5) (R 5) [10,20,34,192] 13 :=
  permutation_upper _ _ _ [6,24,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8819

def r9650 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9650 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9650 : Upper (D 5) (R 5) [10,20,34] 13 := by
  apply FastRouting.sound _ _ [10,20,34] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r9650 c9650
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9650_5
  · exact m9650_33
  · exact m9650_36
  · exact m9650_65
  · exact m9650_68
  · exact m9650_96
  · exact m9650_192

theorem m9651_3 : Upper (D 5) (R 5) [10,20,65,3] 13 :=
  permutation_upper _ _ _ [6,5,24,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8481

theorem m9651_5 : Upper (D 5) (R 5) [10,20,65,5] 13 :=
  permutation_upper _ _ _ [6,9,24,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8543

theorem m9651_6 : Upper (D 5) (R 5) [10,20,65,6] 13 :=
  permutation_upper _ _ _ [6,12,24,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8597

theorem m9651_33 : Upper (D 5) (R 5) [10,20,65,33] 13 :=
  permutation_upper _ _ _ [6,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8770

theorem m9651_34 : Upper (D 5) (R 5) [10,20,65,34] 13 :=
  permutation_upper _ _ _ [6,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8776

theorem m9651_36 : Upper (D 5) (R 5) [10,20,65,36] 13 :=
  permutation_upper _ _ _ [6,24,40,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8783

theorem m9651_129 : Upper (D 5) (R 5) [10,20,65,129] 13 :=
  permutation_upper _ _ _ [6,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8791

theorem m9651_130 : Upper (D 5) (R 5) [10,20,65,130] 13 :=
  permutation_upper _ _ _ [6,24,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8798

theorem m9651_132 : Upper (D 5) (R 5) [10,20,65,132] 13 :=
  permutation_upper _ _ _ [6,24,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8805

theorem m9651_160 : Upper (D 5) (R 5) [10,20,65,160] 13 :=
  permutation_upper _ _ _ [6,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8813

theorem m9651_384 : Upper (D 5) (R 5) [10,20,65,384] 13 :=
  permutation_upper _ _ _ [6,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8821

def r9651 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9651 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9651 : Upper (D 5) (R 5) [10,20,65] 13 := by
  apply FastRouting.sound _ _ [10,20,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9651 c9651
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9651_3
  · exact m9651_5
  · exact m9651_6
  · exact m9651_33
  · exact m9651_34
  · exact m9651_36
  · exact m9651_129
  · exact m9651_130
  · exact m9651_132
  · exact m9651_160
  · exact m9651_384

theorem m9652_5 : Upper (D 5) (R 5) [10,20,66,5] 13 :=
  permutation_upper _ _ _ [6,9,24,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8545

theorem m9652_33 : Upper (D 5) (R 5) [10,20,66,33] 13 :=
  permutation_upper _ _ _ [6,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8771

theorem m9652_36 : Upper (D 5) (R 5) [10,20,66,36] 13 :=
  permutation_upper _ _ _ [6,24,40,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8784

theorem m9652_129 : Upper (D 5) (R 5) [10,20,66,129] 13 :=
  permutation_upper _ _ _ [6,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8792

theorem m9652_132 : Upper (D 5) (R 5) [10,20,66,132] 13 :=
  permutation_upper _ _ _ [6,24,72,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8806

theorem m9652_160 : Upper (D 5) (R 5) [10,20,66,160] 13 :=
  permutation_upper _ _ _ [6,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8814

theorem m9652_384 : Upper (D 5) (R 5) [10,20,66,384] 13 :=
  permutation_upper _ _ _ [6,24,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8822

def r9652 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9652 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9652 : Upper (D 5) (R 5) [10,20,66] 13 := by
  apply FastRouting.sound _ _ [10,20,66] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r9652 c9652
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9652_5
  · exact m9652_33
  · exact m9652_36
  · exact m9652_129
  · exact m9652_132
  · exact m9652_160
  · exact m9652_384

theorem m9653_3 : Upper (D 5) (R 5) [10,20,96,3] 13 :=
  permutation_upper _ _ _ [6,5,24,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8482

theorem m9653_5 : Upper (D 5) (R 5) [10,20,96,5] 13 :=
  permutation_upper _ _ _ [6,9,24,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8546

theorem m9653_6 : Upper (D 5) (R 5) [10,20,96,6] 13 :=
  permutation_upper _ _ _ [6,12,24,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8598

theorem m9653_33 : Upper (D 5) (R 5) [10,20,96,33] 13 :=
  permutation_upper _ _ _ [6,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8773

theorem m9653_34 : Upper (D 5) (R 5) [10,20,96,34] 13 :=
  permutation_upper _ _ _ [6,24,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8778

theorem m9653_36 : Upper (D 5) (R 5) [10,20,96,36] 13 :=
  permutation_upper _ _ _ [6,24,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8786

theorem m9653_129 : Upper (D 5) (R 5) [10,20,96,129] 13 :=
  permutation_upper _ _ _ [6,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8794

theorem m9653_130 : Upper (D 5) (R 5) [10,20,96,130] 13 :=
  permutation_upper _ _ _ [6,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8800

theorem m9653_132 : Upper (D 5) (R 5) [10,20,96,132] 13 :=
  permutation_upper _ _ _ [6,24,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8808

theorem m9653_160 : Upper (D 5) (R 5) [10,20,96,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8816

theorem m9653_384 : Upper (D 5) (R 5) [10,20,96,384] 13 :=
  permutation_upper _ _ _ [6,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8824

def r9653 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9653 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9653 : Upper (D 5) (R 5) [10,20,96] 13 := by
  apply FastRouting.sound _ _ [10,20,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9653 c9653
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9653_3
  · exact m9653_5
  · exact m9653_6
  · exact m9653_33
  · exact m9653_34
  · exact m9653_36
  · exact m9653_129
  · exact m9653_130
  · exact m9653_132
  · exact m9653_160
  · exact m9653_384

theorem m9654_3 : Upper (D 5) (R 5) [10,20,192,3] 13 :=
  permutation_upper _ _ _ [6,5,24,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8483

theorem m9654_5 : Upper (D 5) (R 5) [10,20,192,5] 13 :=
  permutation_upper _ _ _ [6,9,24,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8547

theorem m9654_6 : Upper (D 5) (R 5) [10,20,192,6] 13 :=
  permutation_upper _ _ _ [6,12,24,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8599

theorem m9654_33 : Upper (D 5) (R 5) [10,20,192,33] 13 :=
  permutation_upper _ _ _ [6,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8774

theorem m9654_34 : Upper (D 5) (R 5) [10,20,192,34] 13 :=
  permutation_upper _ _ _ [6,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8779

theorem m9654_36 : Upper (D 5) (R 5) [10,20,192,36] 13 :=
  permutation_upper _ _ _ [6,24,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8787

theorem m9654_257 : Upper (D 5) (R 5) [10,20,192,257] 13 :=
  permutation_upper _ _ _ [6,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8795

theorem m9654_258 : Upper (D 5) (R 5) [10,20,192,258] 13 :=
  permutation_upper _ _ _ [6,24,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8801

theorem m9654_260 : Upper (D 5) (R 5) [10,20,192,260] 13 :=
  permutation_upper _ _ _ [6,24,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8809

theorem m9654_288 : Upper (D 5) (R 5) [10,20,192,288] 13 :=
  permutation_upper _ _ _ [6,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8817

def r9654 : Route 9 := (fun mask => (mask,id))

def c9654 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9654 : Upper (D 5) (R 5) [10,20,192] 13 := by
  apply FastRouting.sound _ _ [10,20,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9654 c9654
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9654_3
  · exact m9654_5
  · exact m9654_6
  · exact m9654_33
  · exact m9654_34
  · exact m9654_36
  · exact m9654_257
  · exact m9654_258
  · exact m9654_260
  · exact m9654_288

def b9655 : PairBound 9 := { available := 487, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 26 37 495 503 487 487 487 487), lower := (rows 11 26 37 8 16 32 64 128 256), losses := [] }

theorem u9655 : Upper (D 5) (R 5) [10,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9656 : PairBound 9 := { available := 423, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 26 69 431 439 423 487 423 423), lower := (rows 11 26 69 8 16 32 64 128 256), losses := [] }

theorem u9656 : Upper (D 5) (R 5) [10,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9657 : PairBound 9 := { available := 423, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 26 100 431 439 423 487 423 423), lower := (rows 11 26 100 8 16 32 64 128 256), losses := [] }

theorem u9657 : Upper (D 5) (R 5) [10,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9657
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9658 : PairBound 9 := { available := 295, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 11 26 196 303 311 295 359 423 295), lower := (rows 11 26 196 8 16 32 64 128 256), losses := [] }

theorem u9658 : Upper (D 5) (R 5) [10,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9658
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9659_6 : Upper (D 5) (R 5) [10,33,17,6] 13 :=
  permutation_upper _ _ _ [6,12,33,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8600

theorem m9659_34 : Upper (D 5) (R 5) [10,33,17,34] 13 :=
  permutation_upper _ _ _ [6,33,34,17] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8829

theorem m9659_36 : Upper (D 5) (R 5) [10,33,17,36] 13 :=
  permutation_upper _ _ _ [6,33,40,17] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8833

theorem m9659_66 : Upper (D 5) (R 5) [10,33,17,66] 13 :=
  permutation_upper _ _ _ [6,33,66,17] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8855

theorem m9659_68 : Upper (D 5) (R 5) [10,33,17,68] 13 :=
  permutation_upper _ _ _ [6,33,72,17] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8865

theorem m9659_96 : Upper (D 5) (R 5) [10,33,17,96] 13 :=
  permutation_upper _ _ _ [6,33,96,17] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8887

theorem m9659_192 : Upper (D 5) (R 5) [10,33,17,192] 13 :=
  permutation_upper _ _ _ [6,33,192,17] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8896

def r9659 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9659 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9659 : Upper (D 5) (R 5) [10,33,17] 13 := by
  apply FastRouting.sound _ _ [10,33,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,192] r9659 c9659
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9659_6
  · exact m9659_34
  · exact m9659_36
  · exact m9659_66
  · exact m9659_68
  · exact m9659_96
  · exact m9659_192

#print axioms u9659
end Delivery.IrregularNine14.P05
