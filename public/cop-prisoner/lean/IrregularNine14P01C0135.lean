import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0080
import IrregularNine14P01C0081
import IrregularNine14P01C0082

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8100 : Route 9 := (fun mask => (mask,id))

def c8100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8100 : Upper (D 1) (R 1) [274,96,40,130] 13 := by
  apply FastRouting.sound _ _ [274,96,40,130] 13 (by decide) (choices 1) [1,4,64,128] r8100 c8100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4837
  · exact u4838
  · exact u4839
  · exact u4840

def b8101 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 275 98 44 140 211 243 211 211 467), lower := (rows 275 98 44 140 16 32 64 128 256), losses := [] }

theorem u8101 : Upper (D 1) (R 1) [274,96,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8102 : Route 9 := (fun mask => (mask,id))

def c8102 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8102 : Upper (D 1) (R 1) [274,96,40,144] 13 := by
  apply FastRouting.sound _ _ [274,96,40,144] 13 (by decide) (choices 1) [1,2,4,64,128] r8102 c8102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4841
  · exact u4842
  · exact u4843
  · exact u4844
  · exact u4845

def r8103 : Route 9 := (fun mask => (mask,id))

def c8103 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8103 : Upper (D 1) (R 1) [274,96,40,192] 13 := by
  apply FastRouting.sound _ _ [274,96,40,192] 13 (by decide) (choices 1) [1,2,4,128] r8103 c8103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4846
  · exact u4847
  · exact u4848
  · exact u4849

def r8104 : Route 9 := (fun mask => (mask,id))

def c8104 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u8104 : Upper (D 1) (R 1) [274,96,48,129] 13 := by
  apply FastRouting.sound _ _ [274,96,48,129] 13 (by decide) (choices 1) [2,4,8,64,128] r8104 c8104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4850
  · exact u4851
  · exact u4852
  · exact u4853
  · exact u4854

def r8105 : Route 9 := (fun mask => (mask,id))

def c8105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8105 : Upper (D 1) (R 1) [274,96,48,130] 13 := by
  apply FastRouting.sound _ _ [274,96,48,130] 13 (by decide) (choices 1) [1,4,8,64,128] r8105 c8105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4855
  · exact u4856
  · exact u4857
  · exact u4858
  · exact u4859

def r8106 : Route 9 := (fun mask => (mask,id))

def c8106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8106 : Upper (D 1) (R 1) [274,96,48,132] 13 := by
  apply FastRouting.sound _ _ [274,96,48,132] 13 (by decide) (choices 1) [1,2,8,64,128] r8106 c8106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4860
  · exact u4861
  · exact u4862
  · exact u4863
  · exact u4864

def r8107 : Route 9 := (fun mask => (mask,id))

def c8107 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8107 : Upper (D 1) (R 1) [274,96,48,192] 13 := by
  apply FastRouting.sound _ _ [274,96,48,192] 13 (by decide) (choices 1) [1,2,4,8,128] r8107 c8107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4865
  · exact u4866
  · exact u4867
  · exact u4868
  · exact u4869

def b8108 : PairBound 9 := { available := 158, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 100 137 158 190 222 158 414), lower := (rows 275 98 100 137 16 32 64 128 256), losses := [] }

theorem u8108 : Upper (D 1) (R 1) [274,96,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8109 : PairBound 9 := { available := 157, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 100 138 157 189 221 157 413), lower := (rows 275 98 100 138 16 32 64 128 256), losses := [] }

theorem u8109 : Upper (D 1) (R 1) [274,96,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8109
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8110 : PairBound 9 := { available := 155, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 100 140 155 187 219 155 411), lower := (rows 275 98 100 140 16 32 64 128 256), losses := [] }

theorem u8110 : Upper (D 1) (R 1) [274,96,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8110
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8111 : PairBound 9 := { available := 143, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 100 152 159 175 207 143 399), lower := (rows 275 98 100 152 16 32 64 128 256), losses := [] }

theorem u8111 : Upper (D 1) (R 1) [274,96,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8112 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8112 : Upper (D 1) (R 1) [274,96,129,130] 13 := by
  apply FastRouting.sound _ _ [274,96,129,130] 13 (by decide) (choices 1) [4,8,32] r8112 c8112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4870
  · exact u4871
  · exact u4872

def b8113 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 275 98 133 140 122 122 122 250 378), lower := (rows 275 98 133 140 16 32 64 128 256), losses := [] }

theorem u8113 : Upper (D 1) (R 1) [274,96,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8114 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8114 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u8114 : Upper (D 1) (R 1) [274,96,129,144] 13 := by
  apply FastRouting.sound _ _ [274,96,129,144] 13 (by decide) (choices 1) [2,4,8,32] r8114 c8114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4873
  · exact u4874
  · exact u4875
  · exact u4876

def r8115 : Route 9 := (fun mask => (mask,id))

def c8115 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8115 : Upper (D 1) (R 1) [274,96,129,160] 13 := by
  apply FastRouting.sound _ _ [274,96,129,160] 13 (by decide) (choices 1) [2,4,8,64] r8115 c8115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4877
  · exact u4878
  · exact u4879
  · exact u4880

def b8116 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 275 98 134 140 121 121 121 249 377), lower := (rows 275 98 134 140 16 32 64 128 256), losses := [] }

theorem u8116 : Upper (D 1) (R 1) [274,96,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8117 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8117 : Upper (D 1) (R 1) [274,96,130,144] 13 := by
  apply FastRouting.sound _ _ [274,96,130,144] 13 (by decide) (choices 1) [1,4,8,32] r8117 c8117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4881
  · exact u4882
  · exact u4883
  · exact u4884

def r8118 : Route 9 := (fun mask => (mask,id))

def c8118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8118 : Upper (D 1) (R 1) [274,96,130,160] 13 := by
  apply FastRouting.sound _ _ [274,96,130,160] 13 (by decide) (choices 1) [1,4,8,64] r8118 c8118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4885
  · exact u4886
  · exact u4887
  · exact u4888

def b8119 : PairBound 9 := { available := 115, camps := [{ cop := 7, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 140 140 115 115 115 243 371), lower := (rows 275 98 140 140 16 32 64 128 256), losses := [] }

theorem u8119 : Upper (D 1) (R 1) [274,96,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8119
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8120 : PairBound 9 := { available := 103, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 140 152 119 103 103 231 359), lower := (rows 275 98 140 152 16 32 64 128 256), losses := [] }

theorem u8120 : Upper (D 1) (R 1) [274,96,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8120
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8121 : PairBound 9 := { available := 87, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 140 168 87 119 87 215 343), lower := (rows 275 98 140 168 16 32 64 128 256), losses := [] }

theorem u8121 : Upper (D 1) (R 1) [274,96,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8121
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8122 : Route 9 := (fun mask => (mask,id))

def c8122 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8122 : Upper (D 1) (R 1) [274,96,144,160] 13 := by
  apply FastRouting.sound _ _ [274,96,144,160] 13 (by decide) (choices 1) [1,2,4,8,64] r8122 c8122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4889
  · exact u4890
  · exact u4891
  · exact u4892
  · exact u4893

theorem m8123_8 : Upper (D 1) (R 1) [274,96,160,192,8] 13 :=
  permutation_upper _ _ _ [274,96,160,192,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4896

def r8123 : Route 9 := (fun mask => (mask,id))

def c8123 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8123 : Upper (D 1) (R 1) [274,96,160,192] 13 := by
  apply FastRouting.sound _ _ [274,96,160,192] 13 (by decide) (choices 1) [1,2,4,8] r8123 c8123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4894
  · exact u4895
  · exact u4896
  · exact m8123_8

def b8124 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 277 11 38 26 240 224 224 224 480), lower := (rows 277 11 38 26 16 32 64 128 256), losses := [] }

theorem u8124 : Upper (D 1) (R 1) [276,9,34,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8124
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8125 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 11 38 42 208 240 208 208 464), lower := (rows 277 11 38 42 16 32 64 128 256), losses := [] }

theorem u8125 : Upper (D 1) (R 1) [276,9,34,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8125
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8126 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 11 38 56 210 226 194 194 450), lower := (rows 277 11 38 56 16 32 64 128 256), losses := [] }

theorem u8126 : Upper (D 1) (R 1) [276,9,34,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8126
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8127 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 277 11 38 74 240 240 240 240 496), lower := (rows 277 11 38 74 16 32 64 128 256), losses := [] }

theorem u8127 : Upper (D 1) (R 1) [276,9,34,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8128 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 11 38 88 242 226 226 226 482), lower := (rows 277 11 38 88 16 32 64 128 256), losses := [] }

theorem u8128 : Upper (D 1) (R 1) [276,9,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8129 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 277 11 38 104 210 242 210 210 466), lower := (rows 277 11 38 104 16 32 64 128 256), losses := [] }

theorem u8129 : Upper (D 1) (R 1) [276,9,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8130 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8130 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8130 : Upper (D 1) (R 1) [276,9,34,192] 13 := by
  apply FastRouting.sound _ _ [276,9,34,192] 13 (by decide) (choices 1) [2,32,64] r8130 c8130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4897
  · exact u4898
  · exact u4899

def b8131 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 277 11 100 26 242 226 226 226 482), lower := (rows 277 11 100 26 16 32 64 128 256), losses := [] }

theorem u8131 : Upper (D 1) (R 1) [276,9,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8132 : Route 9 := (fun mask => (mask,id))

def c8132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8132 : Upper (D 1) (R 1) [276,9,96,34] 13 := by
  apply FastRouting.sound _ _ [276,9,96,34] 13 (by decide) (choices 1) [2,64,128] r8132 c8132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4900
  · exact u4901
  · exact u4902

def b8133 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 11 100 56 210 226 194 194 450), lower := (rows 277 11 100 56 16 32 64 128 256), losses := [] }

theorem u8133 : Upper (D 1) (R 1) [276,9,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8133
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8134 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 11 100 104 146 178 210 146 402), lower := (rows 277 11 100 104 16 32 64 128 256), losses := [] }

theorem u8134 : Upper (D 1) (R 1) [276,9,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8135 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8135 : Upper (D 1) (R 1) [276,9,96,130] 13 := by
  apply FastRouting.sound _ _ [276,9,96,130] 13 (by decide) (choices 1) [2,32,128] r8135 c8135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4903
  · exact u4904
  · exact u4905

def b8136 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 11 100 152 242 226 226 226 482), lower := (rows 277 11 100 152 16 32 64 128 256), losses := [] }

theorem u8136 : Upper (D 1) (R 1) [276,9,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8136
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8137 : Route 9 := (fun mask => (mask,id))

def c8137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8137 : Upper (D 1) (R 1) [276,9,96,160] 13 := by
  apply FastRouting.sound _ _ [276,9,96,160] 13 (by decide) (choices 1) [2,64,128] r8137 c8137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4906
  · exact u4907
  · exact u4908

def b8138 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 277 26 38 11 240 224 224 224 480), lower := (rows 277 26 38 11 16 32 64 128 256), losses := [] }

theorem u8138 : Upper (D 1) (R 1) [276,24,34,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8138
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8139 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 26 38 41 210 226 194 194 450), lower := (rows 277 26 38 41 16 32 64 128 256), losses := [] }

theorem u8139 : Upper (D 1) (R 1) [276,24,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8139
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8140 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 26 38 42 209 225 193 193 449), lower := (rows 277 26 38 42 16 32 64 128 256), losses := [] }

theorem u8140 : Upper (D 1) (R 1) [276,24,34,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8140
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8141 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 26 38 73 242 226 226 226 482), lower := (rows 277 26 38 73 16 32 64 128 256), losses := [] }

theorem u8141 : Upper (D 1) (R 1) [276,24,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8142 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 277 26 38 74 241 225 225 225 481), lower := (rows 277 26 38 74 16 32 64 128 256), losses := [] }

theorem u8142 : Upper (D 1) (R 1) [276,24,34,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8142
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8143 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 277 26 38 104 211 227 195 195 451), lower := (rows 277 26 38 104 16 32 64 128 256), losses := [] }

theorem u8143 : Upper (D 1) (R 1) [276,24,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8143
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8144 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8144 : Upper (D 1) (R 1) [276,24,34,192] 13 := by
  apply FastRouting.sound _ _ [276,24,34,192] 13 (by decide) (choices 1) [1,2,32,64] r8144 c8144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4909
  · exact u4910
  · exact u4911
  · exact u4912

def b8145 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 277 26 100 11 242 226 226 226 482), lower := (rows 277 26 100 11 16 32 64 128 256), losses := [] }

theorem u8145 : Upper (D 1) (R 1) [276,24,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8145
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8146 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 26 100 41 210 226 194 194 450), lower := (rows 277 26 100 41 16 32 64 128 256), losses := [] }

theorem u8146 : Upper (D 1) (R 1) [276,24,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8147 : Route 9 := (fun mask => (mask,id))

def c8147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8147 : Upper (D 1) (R 1) [276,24,96,34] 13 := by
  apply FastRouting.sound _ _ [276,24,96,34] 13 (by decide) (choices 1) [1,2,64,128] r8147 c8147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4913
  · exact u4914
  · exact u4915
  · exact u4916

def b8148 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 26 100 104 147 163 195 131 387), lower := (rows 277 26 100 104 16 32 64 128 256), losses := [] }

theorem u8148 : Upper (D 1) (R 1) [276,24,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8148
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8149 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 26 100 137 242 226 226 226 482), lower := (rows 277 26 100 137 16 32 64 128 256), losses := [] }

theorem u8149 : Upper (D 1) (R 1) [276,24,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8149
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8150 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8150 : Upper (D 1) (R 1) [276,24,96,130] 13 := by
  apply FastRouting.sound _ _ [276,24,96,130] 13 (by decide) (choices 1) [1,2,32,128] r8150 c8150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4917
  · exact u4918
  · exact u4919
  · exact u4920

def r8151 : Route 9 := (fun mask => (mask,id))

def c8151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8151 : Upper (D 1) (R 1) [276,24,96,160] 13 := by
  apply FastRouting.sound _ _ [276,24,96,160] 13 (by decide) (choices 1) [1,2,64,128] r8151 c8151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4921
  · exact u4922
  · exact u4923
  · exact u4924

def b8152 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 277 35 14 26 240 224 224 224 480), lower := (rows 277 35 14 26 16 32 64 128 256), losses := [] }

theorem u8152 : Upper (D 1) (R 1) [276,33,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8153 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 14 42 208 240 208 208 464), lower := (rows 277 35 14 42 16 32 64 128 256), losses := [] }

theorem u8153 : Upper (D 1) (R 1) [276,33,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8153
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8154 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 14 56 210 226 194 194 450), lower := (rows 277 35 14 56 16 32 64 128 256), losses := [] }

theorem u8154 : Upper (D 1) (R 1) [276,33,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8154
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8155 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 14 74 240 240 240 240 496), lower := (rows 277 35 14 74 16 32 64 128 256), losses := [] }

theorem u8155 : Upper (D 1) (R 1) [276,33,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8155
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8156 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 14 88 242 226 226 226 482), lower := (rows 277 35 14 88 16 32 64 128 256), losses := [] }

theorem u8156 : Upper (D 1) (R 1) [276,33,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8156
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8157 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 277 35 14 104 210 242 210 210 466), lower := (rows 277 35 14 104 16 32 64 128 256), losses := [] }

theorem u8157 : Upper (D 1) (R 1) [276,33,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8158 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8158 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8158 : Upper (D 1) (R 1) [276,33,10,192] 13 := by
  apply FastRouting.sound _ _ [276,33,10,192] 13 (by decide) (choices 1) [2,32,64] r8158 c8158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4925
  · exact u4926
  · exact u4927

def b8159 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 70 26 248 232 232 232 488), lower := (rows 277 35 70 26 16 32 64 128 256), losses := [] }

theorem u8159 : Upper (D 1) (R 1) [276,33,66,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8159
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8159
end Delivery.IrregularNine14.P01
