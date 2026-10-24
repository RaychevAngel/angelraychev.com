import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0100
import IrregularNine14P01C0101
import IrregularNine14P01C0102
import IrregularNine14P01C0103
import IrregularNine14P01C0104

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8820 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 290 7 248 248 248 248 248 504), lower := (rows 23 290 7 8 16 32 64 128 256), losses := [] }

theorem u8820 : Upper (D 1) (R 1) [22,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8820
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8821 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8821 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8821 : Upper (D 1) (R 1) [22,288,9] 13 := by
  apply FastRouting.sound _ _ [22,288,9] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8821 c8821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6034
  · exact u6035
  · exact u6036
  · exact u6037
  · exact u6038
  · exact u6039
  · exact u6040

def b8822 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 290 14 249 241 241 241 241 497), lower := (rows 23 290 14 8 16 32 64 128 256), losses := [] }

theorem u8822 : Upper (D 1) (R 1) [22,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8823 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 21 234 250 234 234 234 490), lower := (rows 23 290 21 8 16 32 64 128 256), losses := [] }

theorem u8823 : Upper (D 1) (R 1) [22,288,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8823
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8824 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 22 233 249 233 233 233 489), lower := (rows 23 290 22 8 16 32 64 128 256), losses := [] }

theorem u8824 : Upper (D 1) (R 1) [22,288,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8825 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 28 235 243 227 227 227 483), lower := (rows 23 290 28 8 16 32 64 128 256), losses := [] }

theorem u8825 : Upper (D 1) (R 1) [22,288,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8825
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8826 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 290 37 218 218 250 218 218 474), lower := (rows 23 290 37 8 16 32 64 128 256), losses := [] }

theorem u8826 : Upper (D 1) (R 1) [22,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8826
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8827 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 290 38 217 217 249 217 217 473), lower := (rows 23 290 38 8 16 32 64 128 256), losses := [] }

theorem u8827 : Upper (D 1) (R 1) [22,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8827
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8828 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 290 44 219 211 243 211 211 467), lower := (rows 23 290 44 8 16 32 64 128 256), losses := [] }

theorem u8828 : Upper (D 1) (R 1) [22,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8828
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8829 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 52 203 219 235 203 203 459), lower := (rows 23 290 52 8 16 32 64 128 256), losses := [] }

theorem u8829 : Upper (D 1) (R 1) [22,288,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8829
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8830 : Route 9 := (fun mask => (mask,id))

def c8830 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8830 : Upper (D 1) (R 1) [22,288,65] 13 := by
  apply FastRouting.sound _ _ [22,288,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r8830 c8830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6041
  · exact u6042
  · exact u6043
  · exact u6044
  · exact u6045
  · exact u6046
  · exact u6047
  · exact u6048
  · exact u6049
  · exact u6050

def b8831 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 290 70 249 249 249 249 249 505), lower := (rows 23 290 70 8 16 32 64 128 256), losses := [] }

theorem u8831 : Upper (D 1) (R 1) [22,288,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8831
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8832 : Route 9 := (fun mask => (mask,id))

def c8832 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8832 : Upper (D 1) (R 1) [22,288,72] 13 := by
  apply FastRouting.sound _ _ [22,288,72] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r8832 c8832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6051
  · exact u6052
  · exact u6053
  · exact u6054
  · exact u6055
  · exact u6056
  · exact u6057
  · exact u6058
  · exact u6059
  · exact u6060
  · exact u6061
  · exact u6062
  · exact u6063
  · exact u6064
  · exact u6065

def b8833 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 84 235 251 235 235 235 491), lower := (rows 23 290 84 8 16 32 64 128 256), losses := [] }

theorem u8833 : Upper (D 1) (R 1) [22,288,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8834 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 290 100 219 219 251 219 219 475), lower := (rows 23 290 100 8 16 32 64 128 256), losses := [] }

theorem u8834 : Upper (D 1) (R 1) [22,288,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8834
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8835 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8835 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8835 : Upper (D 1) (R 1) [22,288,192] 13 := by
  apply FastRouting.sound _ _ [22,288,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r8835 c8835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b8836 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 22 490 498 482 482 482 482), lower := (rows 29 35 22 8 16 32 64 128 256), losses := [] }

theorem u8836 : Upper (D 1) (R 1) [28,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8836
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8837 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 35 38 474 466 498 466 466 466), lower := (rows 29 35 38 8 16 32 64 128 256), losses := [] }

theorem u8837 : Upper (D 1) (R 1) [28,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8837
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8838 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 52 458 466 482 450 450 450), lower := (rows 29 35 52 8 16 32 64 128 256), losses := [] }

theorem u8838 : Upper (D 1) (R 1) [28,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8838
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8839_18 : Upper (D 1) (R 1) [28,33,66,18] 13 :=
  permutation_upper _ _ _ [28,33,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6077

theorem m8839_34 : Upper (D 1) (R 1) [28,33,66,34] 13 :=
  permutation_upper _ _ _ [28,33,34,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6081

theorem m8839_48 : Upper (D 1) (R 1) [28,33,66,48] 13 :=
  permutation_upper _ _ _ [28,33,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6085

def r8839 : Route 9 := (fun mask => (mask,id))

def c8839 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8839 : Upper (D 1) (R 1) [28,33,66] 13 := by
  apply FastRouting.sound _ _ [28,33,66] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192,258,272,288,320,384] r8839 c8839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8839_18
  · exact m8839_34
  · exact m8839_48
  · exact u6089
  · exact u6090
  · exact u6091
  · exact u6092
  · exact u6093
  · exact u6094
  · exact u6095
  · exact u6096
  · exact u6097
  · exact u6098
  · exact u6099
  · exact u6100

def b8840 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 84 490 498 482 482 482 482), lower := (rows 29 35 84 8 16 32 64 128 256), losses := [] }

theorem u8840 : Upper (D 1) (R 1) [28,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8840
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8841 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 29 35 100 474 466 498 466 466 466), lower := (rows 29 35 100 8 16 32 64 128 256), losses := [] }

theorem u8841 : Upper (D 1) (R 1) [28,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8841
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8842_18 : Upper (D 1) (R 1) [28,33,192,18] 13 :=
  permutation_upper _ _ _ [28,33,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6078

theorem m8842_34 : Upper (D 1) (R 1) [28,33,192,34] 13 :=
  permutation_upper _ _ _ [28,33,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6082

theorem m8842_48 : Upper (D 1) (R 1) [28,33,192,48] 13 :=
  permutation_upper _ _ _ [28,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6086

theorem m8842_66 : Upper (D 1) (R 1) [28,33,192,66] 13 :=
  permutation_upper _ _ _ [28,33,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6095

theorem m8842_80 : Upper (D 1) (R 1) [28,33,192,80] 13 :=
  permutation_upper _ _ _ [28,33,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6101

theorem m8842_96 : Upper (D 1) (R 1) [28,33,192,96] 13 :=
  permutation_upper _ _ _ [28,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6105

def r8842 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8842 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8842 : Upper (D 1) (R 1) [28,33,192] 13 := by
  apply FastRouting.sound _ _ [28,33,192] 13 (by decide) (choices 2) [18,34,48,66,80,96,192,258,272,288,320] r8842 c8842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8842_18
  · exact m8842_34
  · exact m8842_48
  · exact m8842_66
  · exact m8842_80
  · exact m8842_96
  · exact u6109
  · exact u6110
  · exact u6111
  · exact u6112
  · exact u6113

theorem m8843_18 : Upper (D 1) (R 1) [28,33,258,18] 13 :=
  permutation_upper _ _ _ [28,33,18,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6079

theorem m8843_34 : Upper (D 1) (R 1) [28,33,258,34] 13 :=
  permutation_upper _ _ _ [28,33,34,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6083

theorem m8843_48 : Upper (D 1) (R 1) [28,33,258,48] 13 :=
  permutation_upper _ _ _ [28,33,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6087

theorem m8843_66 : Upper (D 1) (R 1) [28,33,258,66] 13 :=
  permutation_upper _ _ _ [28,33,66,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6096

theorem m8843_80 : Upper (D 1) (R 1) [28,33,258,80] 13 :=
  permutation_upper _ _ _ [28,33,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6102

theorem m8843_96 : Upper (D 1) (R 1) [28,33,258,96] 13 :=
  permutation_upper _ _ _ [28,33,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6106

theorem m8843_192 : Upper (D 1) (R 1) [28,33,258,192] 13 :=
  permutation_upper _ _ _ [28,33,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6110

def r8843 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8843 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8843 : Upper (D 1) (R 1) [28,33,258] 13 := by
  apply FastRouting.sound _ _ [28,33,258] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8843 c8843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8843_18
  · exact m8843_34
  · exact m8843_48
  · exact m8843_66
  · exact m8843_80
  · exact m8843_96
  · exact m8843_192

def b8844 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 276 234 242 226 226 226 482), lower := (rows 29 35 276 8 16 32 64 128 256), losses := [] }

theorem u8844 : Upper (D 1) (R 1) [28,33,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8844
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8845 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 29 35 292 218 210 242 210 210 466), lower := (rows 29 35 292 8 16 32 64 128 256), losses := [] }

theorem u8845 : Upper (D 1) (R 1) [28,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8845
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8846_18 : Upper (D 1) (R 1) [28,33,320,18] 13 :=
  permutation_upper _ _ _ [28,33,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6080

theorem m8846_34 : Upper (D 1) (R 1) [28,33,320,34] 13 :=
  permutation_upper _ _ _ [28,33,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6084

theorem m8846_48 : Upper (D 1) (R 1) [28,33,320,48] 13 :=
  permutation_upper _ _ _ [28,33,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6088

theorem m8846_66 : Upper (D 1) (R 1) [28,33,320,66] 13 :=
  permutation_upper _ _ _ [28,33,66,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6099

theorem m8846_80 : Upper (D 1) (R 1) [28,33,320,80] 13 :=
  permutation_upper _ _ _ [28,33,80,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6103

theorem m8846_96 : Upper (D 1) (R 1) [28,33,320,96] 13 :=
  permutation_upper _ _ _ [28,33,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6107

theorem m8846_130 : Upper (D 1) (R 1) [28,33,320,130] 13 :=
  permutation_upper _ _ _ [28,33,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6100

theorem m8846_144 : Upper (D 1) (R 1) [28,33,320,144] 13 :=
  permutation_upper _ _ _ [28,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6104

theorem m8846_160 : Upper (D 1) (R 1) [28,33,320,160] 13 :=
  permutation_upper _ _ _ [28,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6108

theorem m8846_192 : Upper (D 1) (R 1) [28,33,320,192] 13 :=
  permutation_upper _ _ _ [28,33,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6113

def r8846 : Route 9 := (fun mask => (mask,id))

def c8846 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8846 : Upper (D 1) (R 1) [28,33,320] 13 := by
  apply FastRouting.sound _ _ [28,33,320] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r8846 c8846
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8846_18
  · exact m8846_34
  · exact m8846_48
  · exact m8846_66
  · exact m8846_80
  · exact m8846_96
  · exact m8846_130
  · exact m8846_144
  · exact m8846_160
  · exact m8846_192

def b8847 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 7 490 498 482 482 482 482), lower := (rows 29 50 7 8 16 32 64 128 256), losses := [] }

theorem u8847 : Upper (D 1) (R 1) [28,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8847
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8848 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 37 458 466 482 450 450 450), lower := (rows 29 50 37 8 16 32 64 128 256), losses := [] }

theorem u8848 : Upper (D 1) (R 1) [28,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8848
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8849 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 50 38 459 467 483 451 451 451), lower := (rows 29 50 38 8 16 32 64 128 256), losses := [] }

theorem u8849 : Upper (D 1) (R 1) [28,48,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8849
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8850 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 69 490 498 482 482 482 482), lower := (rows 29 50 69 8 16 32 64 128 256), losses := [] }

theorem u8850 : Upper (D 1) (R 1) [28,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8850
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8851_3 : Upper (D 1) (R 1) [28,48,66,3] 13 :=
  permutation_upper _ _ _ [28,48,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6114

theorem m8851_33 : Upper (D 1) (R 1) [28,48,66,33] 13 :=
  permutation_upper _ _ _ [28,48,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6120

theorem m8851_34 : Upper (D 1) (R 1) [28,48,66,34] 13 :=
  permutation_upper _ _ _ [28,48,34,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6124

theorem m8851_65 : Upper (D 1) (R 1) [28,48,66,65] 13 :=
  permutation_upper _ _ _ [28,48,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6128

theorem m8851_129 : Upper (D 1) (R 1) [28,48,66,129] 13 :=
  permutation_upper _ _ _ [28,48,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6130

def r8851 : Route 9 := (fun mask => (mask,id))

def c8851 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u8851 : Upper (D 1) (R 1) [28,48,66] 13 := by
  apply FastRouting.sound _ _ [28,48,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r8851 c8851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8851_3
  · exact m8851_33
  · exact m8851_34
  · exact m8851_65
  · exact u6137
  · exact u6138
  · exact m8851_129
  · exact u6139
  · exact u6140
  · exact u6141
  · exact u6142
  · exact u6143
  · exact u6144
  · exact u6145
  · exact u6146

theorem m8852_3 : Upper (D 1) (R 1) [28,48,96,3] 13 :=
  permutation_upper _ _ _ [28,48,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6115

theorem m8852_65 : Upper (D 1) (R 1) [28,48,96,65] 13 :=
  permutation_upper _ _ _ [28,48,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6129

theorem m8852_66 : Upper (D 1) (R 1) [28,48,96,66] 13 :=
  permutation_upper _ _ _ [28,48,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6138

theorem m8852_129 : Upper (D 1) (R 1) [28,48,96,129] 13 :=
  permutation_upper _ _ _ [28,48,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6131

theorem m8852_130 : Upper (D 1) (R 1) [28,48,96,130] 13 :=
  permutation_upper _ _ _ [28,48,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6140

def r8852 : Route 9 := (fun mask => (mask,id))

def c8852 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8852 : Upper (D 1) (R 1) [28,48,96] 13 := by
  apply FastRouting.sound _ _ [28,48,96] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r8852 c8852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8852_3
  · exact m8852_65
  · exact m8852_66
  · exact m8852_129
  · exact m8852_130
  · exact u6147
  · exact u6148
  · exact u6149
  · exact u6150
  · exact u6151

theorem m8853_3 : Upper (D 1) (R 1) [28,48,192,3] 13 :=
  permutation_upper _ _ _ [28,48,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6116

theorem m8853_33 : Upper (D 1) (R 1) [28,48,192,33] 13 :=
  permutation_upper _ _ _ [28,48,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6121

theorem m8853_34 : Upper (D 1) (R 1) [28,48,192,34] 13 :=
  permutation_upper _ _ _ [28,48,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6125

theorem m8853_65 : Upper (D 1) (R 1) [28,48,192,65] 13 :=
  permutation_upper _ _ _ [28,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6132

theorem m8853_66 : Upper (D 1) (R 1) [28,48,192,66] 13 :=
  permutation_upper _ _ _ [28,48,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6141

theorem m8853_96 : Upper (D 1) (R 1) [28,48,192,96] 13 :=
  permutation_upper _ _ _ [28,48,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6147

def r8853 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8853 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u8853 : Upper (D 1) (R 1) [28,48,192] 13 := by
  apply FastRouting.sound _ _ [28,48,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r8853 c8853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8853_3
  · exact m8853_33
  · exact m8853_34
  · exact m8853_65
  · exact m8853_66
  · exact m8853_96
  · exact u6152
  · exact u6153
  · exact u6154
  · exact u6155
  · exact u6156

def b8854 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 261 234 242 226 226 226 482), lower := (rows 29 50 261 8 16 32 64 128 256), losses := [] }

theorem u8854 : Upper (D 1) (R 1) [28,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8854
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8855_3 : Upper (D 1) (R 1) [28,48,258,3] 13 :=
  permutation_upper _ _ _ [28,48,3,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6117

theorem m8855_33 : Upper (D 1) (R 1) [28,48,258,33] 13 :=
  permutation_upper _ _ _ [28,48,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6122

theorem m8855_34 : Upper (D 1) (R 1) [28,48,258,34] 13 :=
  permutation_upper _ _ _ [28,48,34,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6126

theorem m8855_65 : Upper (D 1) (R 1) [28,48,258,65] 13 :=
  permutation_upper _ _ _ [28,48,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6133

theorem m8855_66 : Upper (D 1) (R 1) [28,48,258,66] 13 :=
  permutation_upper _ _ _ [28,48,66,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6143

theorem m8855_96 : Upper (D 1) (R 1) [28,48,258,96] 13 :=
  permutation_upper _ _ _ [28,48,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6149

theorem m8855_192 : Upper (D 1) (R 1) [28,48,258,192] 13 :=
  permutation_upper _ _ _ [28,48,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6154

def r8855 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8855 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8855 : Upper (D 1) (R 1) [28,48,258] 13 := by
  apply FastRouting.sound _ _ [28,48,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r8855 c8855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8855_3
  · exact m8855_33
  · exact m8855_34
  · exact m8855_65
  · exact m8855_66
  · exact m8855_96
  · exact m8855_192

theorem m8856_3 : Upper (D 1) (R 1) [28,48,288,3] 13 :=
  permutation_upper _ _ _ [28,48,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6118

theorem m8856_65 : Upper (D 1) (R 1) [28,48,288,65] 13 :=
  permutation_upper _ _ _ [28,48,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6134

theorem m8856_66 : Upper (D 1) (R 1) [28,48,288,66] 13 :=
  permutation_upper _ _ _ [28,48,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6144

theorem m8856_192 : Upper (D 1) (R 1) [28,48,288,192] 13 :=
  permutation_upper _ _ _ [28,48,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6155

def r8856 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8856 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 2 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8856 : Upper (D 1) (R 1) [28,48,288] 13 := by
  apply FastRouting.sound _ _ [28,48,288] 13 (by decide) (choices 2) [3,65,66,192] r8856 c8856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m8856_3
  · exact m8856_65
  · exact m8856_66
  · exact m8856_192

theorem m8857_3 : Upper (D 1) (R 1) [28,48,320,3] 13 :=
  permutation_upper _ _ _ [28,48,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6119

theorem m8857_33 : Upper (D 1) (R 1) [28,48,320,33] 13 :=
  permutation_upper _ _ _ [28,48,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6123

theorem m8857_34 : Upper (D 1) (R 1) [28,48,320,34] 13 :=
  permutation_upper _ _ _ [28,48,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6127

theorem m8857_65 : Upper (D 1) (R 1) [28,48,320,65] 13 :=
  permutation_upper _ _ _ [28,48,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6135

theorem m8857_66 : Upper (D 1) (R 1) [28,48,320,66] 13 :=
  permutation_upper _ _ _ [28,48,66,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6145

theorem m8857_96 : Upper (D 1) (R 1) [28,48,320,96] 13 :=
  permutation_upper _ _ _ [28,48,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6150

theorem m8857_129 : Upper (D 1) (R 1) [28,48,320,129] 13 :=
  permutation_upper _ _ _ [28,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6136

theorem m8857_130 : Upper (D 1) (R 1) [28,48,320,130] 13 :=
  permutation_upper _ _ _ [28,48,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6146

theorem m8857_160 : Upper (D 1) (R 1) [28,48,320,160] 13 :=
  permutation_upper _ _ _ [28,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6151

theorem m8857_192 : Upper (D 1) (R 1) [28,48,320,192] 13 :=
  permutation_upper _ _ _ [28,48,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6156

def r8857 : Route 9 := (fun mask => (mask,id))

def c8857 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8857 : Upper (D 1) (R 1) [28,48,320] 13 := by
  apply FastRouting.sound _ _ [28,48,320] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r8857 c8857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8857_3
  · exact m8857_33
  · exact m8857_34
  · exact m8857_65
  · exact m8857_66
  · exact m8857_96
  · exact m8857_129
  · exact m8857_130
  · exact m8857_160
  · exact m8857_192

def r8858 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8858 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8858 : Upper (D 1) (R 1) [28,96,3] 13 := by
  apply FastRouting.sound _ _ [28,96,3] 13 (by decide) (choices 2) [18,34,48,96,130,144,160,258,272,288,384] r8858 c8858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6157
  · exact u6158
  · exact u6159
  · exact u6160
  · exact u6161
  · exact u6162
  · exact u6163
  · exact u6164
  · exact u6165
  · exact u6166
  · exact u6167

def b8859 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 21 490 498 482 482 482 482), lower := (rows 29 98 21 8 16 32 64 128 256), losses := [] }

theorem u8859 : Upper (D 1) (R 1) [28,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8859
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8860 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 22 491 499 483 483 483 483), lower := (rows 29 98 22 8 16 32 64 128 256), losses := [] }

theorem u8860 : Upper (D 1) (R 1) [28,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8860
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8861 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 29 98 37 474 466 498 466 466 466), lower := (rows 29 98 37 8 16 32 64 128 256), losses := [] }

theorem u8861 : Upper (D 1) (R 1) [28,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8861
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8862 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 38 475 467 499 467 467 467), lower := (rows 29 98 38 8 16 32 64 128 256), losses := [] }

theorem u8862 : Upper (D 1) (R 1) [28,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8862
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8863 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 52 459 467 483 451 451 451), lower := (rows 29 98 52 8 16 32 64 128 256), losses := [] }

theorem u8863 : Upper (D 1) (R 1) [28,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8863
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8864 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 100 411 403 435 467 403 403), lower := (rows 29 98 100 8 16 32 64 128 256), losses := [] }

theorem u8864 : Upper (D 1) (R 1) [28,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8864
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8865_18 : Upper (D 1) (R 1) [28,96,129,18] 13 :=
  permutation_upper _ _ _ [28,96,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6173

theorem m8865_34 : Upper (D 1) (R 1) [28,96,129,34] 13 :=
  permutation_upper _ _ _ [28,96,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6185

theorem m8865_48 : Upper (D 1) (R 1) [28,96,129,48] 13 :=
  permutation_upper _ _ _ [28,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6192

theorem m8865_96 : Upper (D 1) (R 1) [28,96,129,96] 13 :=
  permutation_upper _ _ _ [28,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6199

def r8865 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8865 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8865 : Upper (D 1) (R 1) [28,96,129] 13 := by
  apply FastRouting.sound _ _ [28,96,129] 13 (by decide) (choices 2) [18,34,48,96,130,144,160,258,272,288,384] r8865 c8865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8865_18
  · exact m8865_34
  · exact m8865_48
  · exact m8865_96
  · exact u6204
  · exact u6205
  · exact u6206
  · exact u6207
  · exact u6208
  · exact u6209
  · exact u6210

theorem m8866_3 : Upper (D 1) (R 1) [28,96,130,3] 13 :=
  permutation_upper _ _ _ [28,96,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6161

theorem m8866_17 : Upper (D 1) (R 1) [28,96,130,17] 13 :=
  permutation_upper _ _ _ [28,96,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6168

theorem m8866_18 : Upper (D 1) (R 1) [28,96,130,18] 13 :=
  permutation_upper _ _ _ [28,96,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6174

theorem m8866_33 : Upper (D 1) (R 1) [28,96,130,33] 13 :=
  permutation_upper _ _ _ [28,96,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6180

theorem m8866_34 : Upper (D 1) (R 1) [28,96,130,34] 13 :=
  permutation_upper _ _ _ [28,96,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6186

theorem m8866_48 : Upper (D 1) (R 1) [28,96,130,48] 13 :=
  permutation_upper _ _ _ [28,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6193

theorem m8866_96 : Upper (D 1) (R 1) [28,96,130,96] 13 :=
  permutation_upper _ _ _ [28,96,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6200

theorem m8866_129 : Upper (D 1) (R 1) [28,96,130,129] 13 :=
  permutation_upper _ _ _ [28,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6204

def r8866 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8866 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8866 : Upper (D 1) (R 1) [28,96,130] 13 := by
  apply FastRouting.sound _ _ [28,96,130] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160,257,258,272,288,384] r8866 c8866
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8866_3
  · exact m8866_17
  · exact m8866_18
  · exact m8866_33
  · exact m8866_34
  · exact m8866_48
  · exact m8866_96
  · exact m8866_129
  · exact u6211
  · exact u6212
  · exact u6213
  · exact u6214
  · exact u6215
  · exact u6216
  · exact u6217
  · exact u6218

def b8867 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 148 491 499 483 483 483 483), lower := (rows 29 98 148 8 16 32 64 128 256), losses := [] }

theorem u8867 : Upper (D 1) (R 1) [28,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8867
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8868_3 : Upper (D 1) (R 1) [28,96,160,3] 13 :=
  permutation_upper _ _ _ [28,96,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6163

theorem m8868_17 : Upper (D 1) (R 1) [28,96,160,17] 13 :=
  permutation_upper _ _ _ [28,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6169

theorem m8868_18 : Upper (D 1) (R 1) [28,96,160,18] 13 :=
  permutation_upper _ _ _ [28,96,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6175

theorem m8868_65 : Upper (D 1) (R 1) [28,96,160,65] 13 :=
  permutation_upper _ _ _ [28,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6181

theorem m8868_66 : Upper (D 1) (R 1) [28,96,160,66] 13 :=
  permutation_upper _ _ _ [28,96,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6187

theorem m8868_80 : Upper (D 1) (R 1) [28,96,160,80] 13 :=
  permutation_upper _ _ _ [28,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6194

theorem m8868_129 : Upper (D 1) (R 1) [28,96,160,129] 13 :=
  permutation_upper _ _ _ [28,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6206

theorem m8868_130 : Upper (D 1) (R 1) [28,96,160,130] 13 :=
  permutation_upper _ _ _ [28,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6213

theorem m8868_144 : Upper (D 1) (R 1) [28,96,160,144] 13 :=
  permutation_upper _ _ _ [28,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6219

def r8868 : Route 9 := (fun mask => (mask,id))

def c8868 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8868 : Upper (D 1) (R 1) [28,96,160] 13 := by
  apply FastRouting.sound _ _ [28,96,160] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192,257,258,272,320,384] r8868 c8868
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8868_3
  · exact m8868_17
  · exact m8868_18
  · exact m8868_65
  · exact m8868_66
  · exact m8868_80
  · exact m8868_129
  · exact m8868_130
  · exact m8868_144
  · exact u6224
  · exact u6225
  · exact u6226
  · exact u6227
  · exact u6228
  · exact u6229

theorem m8869_18 : Upper (D 1) (R 1) [28,96,257,18] 13 :=
  permutation_upper _ _ _ [28,96,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6176

theorem m8869_34 : Upper (D 1) (R 1) [28,96,257,34] 13 :=
  permutation_upper _ _ _ [28,96,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6188

theorem m8869_48 : Upper (D 1) (R 1) [28,96,257,48] 13 :=
  permutation_upper _ _ _ [28,96,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6195

theorem m8869_96 : Upper (D 1) (R 1) [28,96,257,96] 13 :=
  permutation_upper _ _ _ [28,96,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6201

theorem m8869_130 : Upper (D 1) (R 1) [28,96,257,130] 13 :=
  permutation_upper _ _ _ [28,96,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6214

theorem m8869_144 : Upper (D 1) (R 1) [28,96,257,144] 13 :=
  permutation_upper _ _ _ [28,96,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6220

theorem m8869_160 : Upper (D 1) (R 1) [28,96,257,160] 13 :=
  permutation_upper _ _ _ [28,96,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6225

def r8869 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8869 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8869 : Upper (D 1) (R 1) [28,96,257] 13 := by
  apply FastRouting.sound _ _ [28,96,257] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r8869 c8869
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8869_18
  · exact m8869_34
  · exact m8869_48
  · exact m8869_96
  · exact m8869_130
  · exact m8869_144
  · exact m8869_160

theorem m8870_3 : Upper (D 1) (R 1) [28,96,258,3] 13 :=
  permutation_upper _ _ _ [28,96,3,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6164

theorem m8870_17 : Upper (D 1) (R 1) [28,96,258,17] 13 :=
  permutation_upper _ _ _ [28,96,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6170

theorem m8870_18 : Upper (D 1) (R 1) [28,96,258,18] 13 :=
  permutation_upper _ _ _ [28,96,18,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6177

theorem m8870_33 : Upper (D 1) (R 1) [28,96,258,33] 13 :=
  permutation_upper _ _ _ [28,96,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6182

theorem m8870_34 : Upper (D 1) (R 1) [28,96,258,34] 13 :=
  permutation_upper _ _ _ [28,96,34,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6189

theorem m8870_48 : Upper (D 1) (R 1) [28,96,258,48] 13 :=
  permutation_upper _ _ _ [28,96,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6196

theorem m8870_96 : Upper (D 1) (R 1) [28,96,258,96] 13 :=
  permutation_upper _ _ _ [28,96,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6202

theorem m8870_129 : Upper (D 1) (R 1) [28,96,258,129] 13 :=
  permutation_upper _ _ _ [28,96,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6207

theorem m8870_130 : Upper (D 1) (R 1) [28,96,258,130] 13 :=
  permutation_upper _ _ _ [28,96,130,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6215

theorem m8870_144 : Upper (D 1) (R 1) [28,96,258,144] 13 :=
  permutation_upper _ _ _ [28,96,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6221

theorem m8870_160 : Upper (D 1) (R 1) [28,96,258,160] 13 :=
  permutation_upper _ _ _ [28,96,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6226

def r8870 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8870 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8870 : Upper (D 1) (R 1) [28,96,258] 13 := by
  apply FastRouting.sound _ _ [28,96,258] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r8870 c8870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8870_3
  · exact m8870_17
  · exact m8870_18
  · exact m8870_33
  · exact m8870_34
  · exact m8870_48
  · exact m8870_96
  · exact m8870_129
  · exact m8870_130
  · exact m8870_144
  · exact m8870_160

def b8871 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 276 235 243 227 227 227 483), lower := (rows 29 98 276 8 16 32 64 128 256), losses := [] }

theorem u8871 : Upper (D 1) (R 1) [28,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8871
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8872_3 : Upper (D 1) (R 1) [28,96,288,3] 13 :=
  permutation_upper _ _ _ [28,96,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6166

theorem m8872_17 : Upper (D 1) (R 1) [28,96,288,17] 13 :=
  permutation_upper _ _ _ [28,96,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6171

theorem m8872_18 : Upper (D 1) (R 1) [28,96,288,18] 13 :=
  permutation_upper _ _ _ [28,96,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6178

theorem m8872_65 : Upper (D 1) (R 1) [28,96,288,65] 13 :=
  permutation_upper _ _ _ [28,96,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6183

theorem m8872_66 : Upper (D 1) (R 1) [28,96,288,66] 13 :=
  permutation_upper _ _ _ [28,96,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6190

theorem m8872_80 : Upper (D 1) (R 1) [28,96,288,80] 13 :=
  permutation_upper _ _ _ [28,96,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6197

theorem m8872_129 : Upper (D 1) (R 1) [28,96,288,129] 13 :=
  permutation_upper _ _ _ [28,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6209

theorem m8872_130 : Upper (D 1) (R 1) [28,96,288,130] 13 :=
  permutation_upper _ _ _ [28,96,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6217

theorem m8872_144 : Upper (D 1) (R 1) [28,96,288,144] 13 :=
  permutation_upper _ _ _ [28,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6222

theorem m8872_192 : Upper (D 1) (R 1) [28,96,288,192] 13 :=
  permutation_upper _ _ _ [28,96,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6228

def r8872 : Route 9 := (fun mask => (mask,id))

def c8872 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8872 : Upper (D 1) (R 1) [28,96,288] 13 := by
  apply FastRouting.sound _ _ [28,96,288] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r8872 c8872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8872_3
  · exact m8872_17
  · exact m8872_18
  · exact m8872_65
  · exact m8872_66
  · exact m8872_80
  · exact m8872_129
  · exact m8872_130
  · exact m8872_144
  · exact m8872_192

theorem m8873_3 : Upper (D 1) (R 1) [28,96,384,3] 13 :=
  permutation_upper _ _ _ [28,96,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6167

theorem m8873_17 : Upper (D 1) (R 1) [28,96,384,17] 13 :=
  permutation_upper _ _ _ [28,96,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6172

theorem m8873_18 : Upper (D 1) (R 1) [28,96,384,18] 13 :=
  permutation_upper _ _ _ [28,96,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6179

theorem m8873_33 : Upper (D 1) (R 1) [28,96,384,33] 13 :=
  permutation_upper _ _ _ [28,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6184

theorem m8873_34 : Upper (D 1) (R 1) [28,96,384,34] 13 :=
  permutation_upper _ _ _ [28,96,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6191

theorem m8873_48 : Upper (D 1) (R 1) [28,96,384,48] 13 :=
  permutation_upper _ _ _ [28,96,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6198

theorem m8873_96 : Upper (D 1) (R 1) [28,96,384,96] 13 :=
  permutation_upper _ _ _ [28,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6203

theorem m8873_129 : Upper (D 1) (R 1) [28,96,384,129] 13 :=
  permutation_upper _ _ _ [28,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6210

theorem m8873_130 : Upper (D 1) (R 1) [28,96,384,130] 13 :=
  permutation_upper _ _ _ [28,96,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6218

theorem m8873_144 : Upper (D 1) (R 1) [28,96,384,144] 13 :=
  permutation_upper _ _ _ [28,96,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6223

theorem m8873_160 : Upper (D 1) (R 1) [28,96,384,160] 13 :=
  permutation_upper _ _ _ [28,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6229

def r8873 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8873 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8873 : Upper (D 1) (R 1) [28,96,384] 13 := by
  apply FastRouting.sound _ _ [28,96,384] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r8873 c8873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8873_3
  · exact m8873_17
  · exact m8873_18
  · exact m8873_33
  · exact m8873_34
  · exact m8873_48
  · exact m8873_96
  · exact m8873_129
  · exact m8873_130
  · exact m8873_144
  · exact m8873_160

def b8874 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 259 22 234 242 226 226 226 482), lower := (rows 29 259 22 8 16 32 64 128 256), losses := [] }

theorem u8874 : Upper (D 1) (R 1) [28,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8874
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8875_18 : Upper (D 1) (R 1) [28,257,34,18] 13 :=
  permutation_upper _ _ _ [28,257,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6230

def r8875 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8875 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8875 : Upper (D 1) (R 1) [28,257,34] 13 := by
  apply FastRouting.sound _ _ [28,257,34] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8875 c8875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8875_18
  · exact u6232
  · exact u6233
  · exact u6234
  · exact u6235
  · exact u6236
  · exact u6237

def b8876 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 259 52 234 242 226 226 226 482), lower := (rows 29 259 52 8 16 32 64 128 256), losses := [] }

theorem u8876 : Upper (D 1) (R 1) [28,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8876
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8877_18 : Upper (D 1) (R 1) [28,257,96,18] 13 :=
  permutation_upper _ _ _ [28,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6231

theorem m8877_34 : Upper (D 1) (R 1) [28,257,96,34] 13 :=
  permutation_upper _ _ _ [28,257,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6236

theorem m8877_48 : Upper (D 1) (R 1) [28,257,96,48] 13 :=
  permutation_upper _ _ _ [28,257,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6238

theorem m8877_130 : Upper (D 1) (R 1) [28,257,96,130] 13 :=
  permutation_upper _ _ _ [28,257,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6237

theorem m8877_144 : Upper (D 1) (R 1) [28,257,96,144] 13 :=
  permutation_upper _ _ _ [28,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6239

def r8877 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8877 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8877 : Upper (D 1) (R 1) [28,257,96] 13 := by
  apply FastRouting.sound _ _ [28,257,96] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r8877 c8877
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8877_18
  · exact m8877_34
  · exact m8877_48
  · exact u6240
  · exact m8877_130
  · exact m8877_144
  · exact u6241

def b8878 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 29 274 7 234 242 226 226 226 482), lower := (rows 29 274 7 8 16 32 64 128 256), losses := [] }

theorem u8878 : Upper (D 1) (R 1) [28,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8878
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8879 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 29 274 37 234 242 226 226 226 482), lower := (rows 29 274 37 8 16 32 64 128 256), losses := [] }

theorem u8879 : Upper (D 1) (R 1) [28,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8879
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8879
end Delivery.IrregularNine14.P01
