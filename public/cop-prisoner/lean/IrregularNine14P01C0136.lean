import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0082
import IrregularNine14P01C0083

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8160 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 35 70 42 216 248 216 216 472), lower := (rows 277 35 70 42 16 32 64 128 256), losses := [] }

theorem u8160 : Upper (D 1) (R 1) [276,33,66,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8160
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8161 : Route 9 := (fun mask => (mask,id))

def c8161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8161 : Upper (D 1) (R 1) [276,33,66,48] 13 := by
  apply FastRouting.sound _ _ [276,33,66,48] 13 (by decide) (choices 1) [2,8,64,128] r8161 c8161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4928
  · exact u4929
  · exact u4930
  · exact u4931

def b8162 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 35 70 74 184 184 248 184 440), lower := (rows 277 35 70 74 16 32 64 128 256), losses := [] }

theorem u8162 : Upper (D 1) (R 1) [276,33,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8163 : Route 9 := (fun mask => (mask,id))

def c8163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8163 : Upper (D 1) (R 1) [276,33,66,80] 13 := by
  apply FastRouting.sound _ _ [276,33,66,80] 13 (by decide) (choices 1) [2,8,32,128] r8163 c8163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4932
  · exact u4933
  · exact u4934
  · exact u4935

def r8164 : Route 9 := (fun mask => (mask,id))

def c8164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8164 : Upper (D 1) (R 1) [276,33,66,96] 13 := by
  apply FastRouting.sound _ _ [276,33,66,96] 13 (by decide) (choices 1) [2,8,128] r8164 c8164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4936
  · exact u4937
  · exact u4938

def r8165 : Route 9 := (fun mask => (mask,id))

def c8165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8165 : Upper (D 1) (R 1) [276,33,66,130] 13 := by
  apply FastRouting.sound _ _ [276,33,66,130] 13 (by decide) (choices 1) [8,32,64,128] r8165 c8165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4939
  · exact u4940
  · exact u4941
  · exact u4942

def r8166 : Route 9 := (fun mask => (mask,id))

def c8166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8166 : Upper (D 1) (R 1) [276,33,66,144] 13 := by
  apply FastRouting.sound _ _ [276,33,66,144] 13 (by decide) (choices 1) [2,8,32,64,128] r8166 c8166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4943
  · exact u4944
  · exact u4945
  · exact u4946
  · exact u4947

def r8167 : Route 9 := (fun mask => (mask,id))

def c8167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8167 : Upper (D 1) (R 1) [276,33,66,160] 13 := by
  apply FastRouting.sound _ _ [276,33,66,160] 13 (by decide) (choices 1) [2,8,64,128] r8167 c8167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4948
  · exact u4949
  · exact u4950
  · exact u4951

def r8168 : Route 9 := (fun mask => (mask,id))

def c8168 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8168 : Upper (D 1) (R 1) [276,33,66,192] 13 := by
  apply FastRouting.sound _ _ [276,33,66,192] 13 (by decide) (choices 1) [2,8,32,128] r8168 c8168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4952
  · exact u4953
  · exact u4954
  · exact u4955

def b8169 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 76 26 242 226 226 226 482), lower := (rows 277 35 76 26 16 32 64 128 256), losses := [] }

theorem u8169 : Upper (D 1) (R 1) [276,33,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8170 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 35 76 42 210 242 210 210 466), lower := (rows 277 35 76 42 16 32 64 128 256), losses := [] }

theorem u8170 : Upper (D 1) (R 1) [276,33,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8170
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8171 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 76 56 210 226 194 194 450), lower := (rows 277 35 76 56 16 32 64 128 256), losses := [] }

theorem u8171 : Upper (D 1) (R 1) [276,33,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8172 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 35 76 74 178 178 242 178 434), lower := (rows 277 35 76 74 16 32 64 128 256), losses := [] }

theorem u8172 : Upper (D 1) (R 1) [276,33,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8172
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8173 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 35 76 88 178 162 226 162 418), lower := (rows 277 35 76 88 16 32 64 128 256), losses := [] }

theorem u8173 : Upper (D 1) (R 1) [276,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8174 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 35 76 104 146 178 210 146 402), lower := (rows 277 35 76 104 16 32 64 128 256), losses := [] }

theorem u8174 : Upper (D 1) (R 1) [276,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8174
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8175 : Route 9 := (fun mask => (mask,id))

def c8175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8175 : Upper (D 1) (R 1) [276,33,72,130] 13 := by
  apply FastRouting.sound _ _ [276,33,72,130] 13 (by decide) (choices 1) [2,32,64,128] r8175 c8175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4956
  · exact u4957
  · exact u4958
  · exact u4959

def b8176 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 76 152 242 226 226 226 482), lower := (rows 277 35 76 152 16 32 64 128 256), losses := [] }

theorem u8176 : Upper (D 1) (R 1) [276,33,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8176
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8177 : Route 9 := (fun mask => (mask,id))

def c8177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8177 : Upper (D 1) (R 1) [276,33,72,160] 13 := by
  apply FastRouting.sound _ _ [276,33,72,160] 13 (by decide) (choices 1) [2,64,128] r8177 c8177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4960
  · exact u4961
  · exact u4962

def b8178 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 35 76 200 178 178 242 178 434), lower := (rows 277 35 76 200 16 32 64 128 256), losses := [] }

theorem u8178 : Upper (D 1) (R 1) [276,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8179 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 196 26 250 234 234 234 490), lower := (rows 277 35 196 26 16 32 64 128 256), losses := [] }

theorem u8179 : Upper (D 1) (R 1) [276,33,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8179
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8180 : PairBound 9 := { available := 218, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 35 196 42 218 250 218 218 474), lower := (rows 277 35 196 42 16 32 64 128 256), losses := [] }

theorem u8180 : Upper (D 1) (R 1) [276,33,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8180
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8181 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8181 : Upper (D 1) (R 1) [276,33,192,48] 13 := by
  apply FastRouting.sound _ _ [276,33,192,48] 13 (by decide) (choices 1) [2,8,64] r8181 c8181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4963
  · exact u4964
  · exact u4965

def r8182 : Route 9 := (fun mask => (mask,id))

def c8182 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8182 : Upper (D 1) (R 1) [276,33,192,66] 13 := by
  apply FastRouting.sound _ _ [276,33,192,66] 13 (by decide) (choices 1) [2,8,32,128] r8182 c8182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4966
  · exact u4967
  · exact u4968
  · exact u4969

def r8183 : Route 9 := (fun mask => (mask,id))

def c8183 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8183 : Upper (D 1) (R 1) [276,33,192,80] 13 := by
  apply FastRouting.sound _ _ [276,33,192,80] 13 (by decide) (choices 1) [2,8,32,128] r8183 c8183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4970
  · exact u4971
  · exact u4972
  · exact u4973

def r8184 : Route 9 := (fun mask => (mask,id))

def c8184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8184 : Upper (D 1) (R 1) [276,33,192,96] 13 := by
  apply FastRouting.sound _ _ [276,33,192,96] 13 (by decide) (choices 1) [2,8,128] r8184 c8184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4974
  · exact u4975
  · exact u4976

def b8185 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 196 200 58 58 122 186 314), lower := (rows 277 35 196 200 16 32 64 128 256), losses := [] }

theorem u8185 : Upper (D 1) (R 1) [276,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8185
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8186 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 7 26 240 224 224 224 480), lower := (rows 277 42 7 26 16 32 64 128 256), losses := [] }

theorem u8186 : Upper (D 1) (R 1) [276,40,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8186
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8187 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 7 42 208 240 208 208 464), lower := (rows 277 42 7 42 16 32 64 128 256), losses := [] }

theorem u8187 : Upper (D 1) (R 1) [276,40,3,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8187
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8188 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 277 42 7 56 210 226 194 194 450), lower := (rows 277 42 7 56 16 32 64 128 256), losses := [] }

theorem u8188 : Upper (D 1) (R 1) [276,40,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8188
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8189 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 7 74 240 240 240 240 496), lower := (rows 277 42 7 74 16 32 64 128 256), losses := [] }

theorem u8189 : Upper (D 1) (R 1) [276,40,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8189
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8190 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 162, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 7 88 242 226 226 226 482), lower := (rows 277 42 7 88 16 32 64 128 256), losses := [] }

theorem u8190 : Upper (D 1) (R 1) [276,40,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8191 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 7 104 210 242 210 210 466), lower := (rows 277 42 7 104 16 32 64 128 256), losses := [] }

theorem u8191 : Upper (D 1) (R 1) [276,40,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8191
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8192 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8192 : Upper (D 1) (R 1) [276,40,3,192] 13 := by
  apply FastRouting.sound _ _ [276,40,3,192] 13 (by decide) (choices 1) [2,32,64] r8192 c8192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4977
  · exact u4978
  · exact u4979

def b8193 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 69 26 242 226 226 226 482), lower := (rows 277 42 69 26 16 32 64 128 256), losses := [] }

theorem u8193 : Upper (D 1) (R 1) [276,40,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8193
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8194 : PairBound 9 := { available := 210, camps := [{ cop := 5, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 69 42 210 242 210 210 466), lower := (rows 277 42 69 42 16 32 64 128 256), losses := [] }

theorem u8194 : Upper (D 1) (R 1) [276,40,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8194
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8195 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 277 42 69 56 210 226 194 194 450), lower := (rows 277 42 69 56 16 32 64 128 256), losses := [] }

theorem u8195 : Upper (D 1) (R 1) [276,40,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8195
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8196 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 69 74 178 178 242 178 434), lower := (rows 277 42 69 74 16 32 64 128 256), losses := [] }

theorem u8196 : Upper (D 1) (R 1) [276,40,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8196
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8197 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 162, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 69 88 178 162 226 162 418), lower := (rows 277 42 69 88 16 32 64 128 256), losses := [] }

theorem u8197 : Upper (D 1) (R 1) [276,40,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8197
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8198 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 277 42 69 104 146 178 210 146 402), lower := (rows 277 42 69 104 16 32 64 128 256), losses := [] }

theorem u8198 : Upper (D 1) (R 1) [276,40,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8198
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8199 : Route 9 := (fun mask => (mask,id))

def c8199 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8199 : Upper (D 1) (R 1) [276,40,65,130] 13 := by
  apply FastRouting.sound _ _ [276,40,65,130] 13 (by decide) (choices 1) [2,32,64,128] r8199 c8199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4980
  · exact u4981
  · exact u4982
  · exact u4983

def b8200 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 69 152 242 226 226 226 482), lower := (rows 277 42 69 152 16 32 64 128 256), losses := [] }

theorem u8200 : Upper (D 1) (R 1) [276,40,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8200
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8201 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 69 168 210 242 210 210 466), lower := (rows 277 42 69 168 16 32 64 128 256), losses := [] }

theorem u8201 : Upper (D 1) (R 1) [276,40,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8201
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8202 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 69 200 178 178 242 178 434), lower := (rows 277 42 69 200 16 32 64 128 256), losses := [] }

theorem u8202 : Upper (D 1) (R 1) [276,40,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8202
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8203 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 433, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 70 11 240 240 240 240 496), lower := (rows 277 42 70 11 16 32 64 128 256), losses := [] }

theorem u8203 : Upper (D 1) (R 1) [276,40,66,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8203
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8204 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 70 25 242 226 226 226 482), lower := (rows 277 42 70 25 16 32 64 128 256), losses := [] }

theorem u8204 : Upper (D 1) (R 1) [276,40,66,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8205 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 433, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 70 26 241 225 225 225 481), lower := (rows 277 42 70 26 16 32 64 128 256), losses := [] }

theorem u8205 : Upper (D 1) (R 1) [276,40,66,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8205
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8206 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 70 41 210 242 210 210 466), lower := (rows 277 42 70 41 16 32 64 128 256), losses := [] }

theorem u8206 : Upper (D 1) (R 1) [276,40,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8206
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8207 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 70 42 209 241 209 209 465), lower := (rows 277 42 70 42 16 32 64 128 256), losses := [] }

theorem u8207 : Upper (D 1) (R 1) [276,40,66,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8207
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8208 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 70 56 211 227 195 195 451), lower := (rows 277 42 70 56 16 32 64 128 256), losses := [] }

theorem u8208 : Upper (D 1) (R 1) [276,40,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8209 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 70 73 178 178 242 178 434), lower := (rows 277 42 70 73 16 32 64 128 256), losses := [] }

theorem u8209 : Upper (D 1) (R 1) [276,40,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8209
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8210 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 42 70 74 177 177 241 177 433), lower := (rows 277 42 70 74 16 32 64 128 256), losses := [] }

theorem u8210 : Upper (D 1) (R 1) [276,40,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8210
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8211 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 70 88 179 163 227 163 419), lower := (rows 277 42 70 88 16 32 64 128 256), losses := [] }

theorem u8211 : Upper (D 1) (R 1) [276,40,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8211
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8212 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 70 104 147 179 211 147 403), lower := (rows 277 42 70 104 16 32 64 128 256), losses := [] }

theorem u8212 : Upper (D 1) (R 1) [276,40,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8212
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8213 : Route 9 := (fun mask => (mask,id))

def c8213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8213 : Upper (D 1) (R 1) [276,40,66,129] 13 := by
  apply FastRouting.sound _ _ [276,40,66,129] 13 (by decide) (choices 1) [2,32,64,128] r8213 c8213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4984
  · exact u4985
  · exact u4986
  · exact u4987

def b8214 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 433, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 70 138 241 241 241 241 497), lower := (rows 277 42 70 138 16 32 64 128 256), losses := [] }

theorem u8214 : Upper (D 1) (R 1) [276,40,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8214
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8215 : Route 9 := (fun mask => (mask,id))

def c8215 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8215 : Upper (D 1) (R 1) [276,40,66,144] 13 := by
  apply FastRouting.sound _ _ [276,40,66,144] 13 (by decide) (choices 1) [1,2,32,64,128] r8215 c8215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4988
  · exact u4989
  · exact u4990
  · exact u4991
  · exact u4992

def b8216 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 70 168 211 243 211 211 467), lower := (rows 277 42 70 168 16 32 64 128 256), losses := [] }

theorem u8216 : Upper (D 1) (R 1) [276,40,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8216
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8217 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 70 200 179 179 243 179 435), lower := (rows 277 42 70 200 16 32 64 128 256), losses := [] }

theorem u8217 : Upper (D 1) (R 1) [276,40,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8217
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8218 : Route 9 := (fun mask => (mask,id))

def c8218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8218 : Upper (D 1) (R 1) [276,40,96,3] 13 := by
  apply FastRouting.sound _ _ [276,40,96,3] 13 (by decide) (choices 1) [2,64,128] r8218 c8218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4993
  · exact u4994
  · exact u4995

def b8219 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 100 25 210 226 194 194 450), lower := (rows 277 42 100 25 16 32 64 128 256), losses := [] }

theorem u8219 : Upper (D 1) (R 1) [276,40,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8219
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8219
end Delivery.IrregularNine14.P01
