import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0079
import IrregularNine14P01C0080

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8040 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 7 28 248 232 232 232 488), lower := (rows 275 98 7 28 16 32 64 128 256), losses := [] }

theorem u8040 : Upper (D 1) (R 1) [274,96,3,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8040
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8041 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 7 44 216 248 216 216 472), lower := (rows 275 98 7 44 16 32 64 128 256), losses := [] }

theorem u8041 : Upper (D 1) (R 1) [274,96,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8041
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8042 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 7 56 220 236 204 204 460), lower := (rows 275 98 7 56 16 32 64 128 256), losses := [] }

theorem u8042 : Upper (D 1) (R 1) [274,96,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8042
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8043 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 7 140 248 248 248 248 504), lower := (rows 275 98 7 140 16 32 64 128 256), losses := [] }

theorem u8043 : Upper (D 1) (R 1) [274,96,3,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8043
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8044 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 7 152 252 236 236 236 492), lower := (rows 275 98 7 152 16 32 64 128 256), losses := [] }

theorem u8044 : Upper (D 1) (R 1) [274,96,3,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8044
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8045 : PairBound 9 := { available := 220, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 7 168 220 252 220 220 476), lower := (rows 275 98 7 168 16 32 64 128 256), losses := [] }

theorem u8045 : Upper (D 1) (R 1) [274,96,3,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8045
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8046 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 13 14 240 240 240 240 496), lower := (rows 275 98 13 14 16 32 64 128 256), losses := [] }

theorem u8046 : Upper (D 1) (R 1) [274,96,9,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8046
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8047 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 13 26 244 228 228 228 484), lower := (rows 275 98 13 26 16 32 64 128 256), losses := [] }

theorem u8047 : Upper (D 1) (R 1) [274,96,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8047
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8048 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 13 28 242 226 226 226 482), lower := (rows 275 98 13 28 16 32 64 128 256), losses := [] }

theorem u8048 : Upper (D 1) (R 1) [274,96,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8048
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8049 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 98 13 42 212 244 212 212 468), lower := (rows 275 98 13 42 16 32 64 128 256), losses := [] }

theorem u8049 : Upper (D 1) (R 1) [274,96,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8049
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8050 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 275 98 13 44 210 242 210 210 466), lower := (rows 275 98 13 44 16 32 64 128 256), losses := [] }

theorem u8050 : Upper (D 1) (R 1) [274,96,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8050
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8051 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 13 56 214 230 198 198 454), lower := (rows 275 98 13 56 16 32 64 128 256), losses := [] }

theorem u8051 : Upper (D 1) (R 1) [274,96,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8051
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8052 : PairBound 9 := { available := 150, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 98 13 104 150 182 214 150 406), lower := (rows 275 98 13 104 16 32 64 128 256), losses := [] }

theorem u8052 : Upper (D 1) (R 1) [274,96,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8052
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8053 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8053 : Upper (D 1) (R 1) [274,96,9,130] 13 := by
  apply FastRouting.sound _ _ [274,96,9,130] 13 (by decide) (choices 1) [4,32,128] r8053 c8053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4776
  · exact u4777
  · exact u4778

def r8054 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8054 : Upper (D 1) (R 1) [274,96,9,132] 13 := by
  apply FastRouting.sound _ _ [274,96,9,132] 13 (by decide) (choices 1) [2,32,128] r8054 c8054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4779
  · exact u4780
  · exact u4781

def b8055 : PairBound 9 := { available := 230, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 13 152 246 230 230 230 486), lower := (rows 275 98 13 152 16 32 64 128 256), losses := [] }

theorem u8055 : Upper (D 1) (R 1) [274,96,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8055
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8056 : Route 9 := (fun mask => (mask,id))

def c8056 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8056 : Upper (D 1) (R 1) [274,96,9,160] 13 := by
  apply FastRouting.sound _ _ [274,96,9,160] 13 (by decide) (choices 1) [2,4,64,128] r8056 c8056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4782
  · exact u4783
  · exact u4784
  · exact u4785

def b8057 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 14 25 244 228 228 228 484), lower := (rows 275 98 14 25 16 32 64 128 256), losses := [] }

theorem u8057 : Upper (D 1) (R 1) [274,96,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8057
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8058 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 14 28 241 225 225 225 481), lower := (rows 275 98 14 28 16 32 64 128 256), losses := [] }

theorem u8058 : Upper (D 1) (R 1) [274,96,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8058
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8059 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 98 14 41 212 244 212 212 468), lower := (rows 275 98 14 41 16 32 64 128 256), losses := [] }

theorem u8059 : Upper (D 1) (R 1) [274,96,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8059
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8060 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 14 44 209 241 209 209 465), lower := (rows 275 98 14 44 16 32 64 128 256), losses := [] }

theorem u8060 : Upper (D 1) (R 1) [274,96,10,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8060
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8061 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 98 14 56 213 229 197 197 453), lower := (rows 275 98 14 56 16 32 64 128 256), losses := [] }

theorem u8061 : Upper (D 1) (R 1) [274,96,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8061
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8062 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 14 104 149 181 213 149 405), lower := (rows 275 98 14 104 16 32 64 128 256), losses := [] }

theorem u8062 : Upper (D 1) (R 1) [274,96,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8062
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8063 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8063 : Upper (D 1) (R 1) [274,96,10,129] 13 := by
  apply FastRouting.sound _ _ [274,96,10,129] 13 (by decide) (choices 1) [4,32,128] r8063 c8063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4786
  · exact u4787
  · exact u4788

def r8064 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8064 : Upper (D 1) (R 1) [274,96,10,132] 13 := by
  apply FastRouting.sound _ _ [274,96,10,132] 13 (by decide) (choices 1) [1,32,128] r8064 c8064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4789
  · exact u4790
  · exact u4791

def r8065 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8065 : Upper (D 1) (R 1) [274,96,10,144] 13 := by
  apply FastRouting.sound _ _ [274,96,10,144] 13 (by decide) (choices 1) [1,4,32,128] r8065 c8065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4792
  · exact u4793
  · exact u4794
  · exact u4795

def b8066 : PairBound 9 := { available := 213, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 98 14 168 213 245 213 213 469), lower := (rows 275 98 14 168 16 32 64 128 256), losses := [] }

theorem u8066 : Upper (D 1) (R 1) [274,96,10,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8066
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8067 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 21 44 218 234 202 202 458), lower := (rows 275 98 21 44 16 32 64 128 256), losses := [] }

theorem u8067 : Upper (D 1) (R 1) [274,96,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8067
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8068 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 21 138 252 236 236 236 492), lower := (rows 275 98 21 138 16 32 64 128 256), losses := [] }

theorem u8068 : Upper (D 1) (R 1) [274,96,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8068
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8069 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 21 140 250 234 234 234 490), lower := (rows 275 98 21 140 16 32 64 128 256), losses := [] }

theorem u8069 : Upper (D 1) (R 1) [274,96,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8069
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8070 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 21 168 222 238 206 206 462), lower := (rows 275 98 21 168 16 32 64 128 256), losses := [] }

theorem u8070 : Upper (D 1) (R 1) [274,96,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8070
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8071 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 22 41 220 236 204 204 460), lower := (rows 275 98 22 41 16 32 64 128 256), losses := [] }

theorem u8071 : Upper (D 1) (R 1) [274,96,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8071
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8072 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 22 44 217 233 201 201 457), lower := (rows 275 98 22 44 16 32 64 128 256), losses := [] }

theorem u8072 : Upper (D 1) (R 1) [274,96,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8072
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8073 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 22 137 252 236 236 236 492), lower := (rows 275 98 22 137 16 32 64 128 256), losses := [] }

theorem u8073 : Upper (D 1) (R 1) [274,96,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8073
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8074 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 22 140 249 233 233 233 489), lower := (rows 275 98 22 140 16 32 64 128 256), losses := [] }

theorem u8074 : Upper (D 1) (R 1) [274,96,18,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8074
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8075 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 22 168 221 237 205 205 461), lower := (rows 275 98 22 168 16 32 64 128 256), losses := [] }

theorem u8075 : Upper (D 1) (R 1) [274,96,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8075
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8076 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 28 41 214 230 198 198 454), lower := (rows 275 98 28 41 16 32 64 128 256), losses := [] }

theorem u8076 : Upper (D 1) (R 1) [274,96,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8076
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8077 : PairBound 9 := { available := 197, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 98 28 42 213 229 197 197 453), lower := (rows 275 98 28 42 16 32 64 128 256), losses := [] }

theorem u8077 : Upper (D 1) (R 1) [274,96,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8077
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8078 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 28 44 211 227 195 195 451), lower := (rows 275 98 28 44 16 32 64 128 256), losses := [] }

theorem u8078 : Upper (D 1) (R 1) [274,96,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8078
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8079 : PairBound 9 := { available := 135, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 98 28 104 151 167 199 135 391), lower := (rows 275 98 28 104 16 32 64 128 256), losses := [] }

theorem u8079 : Upper (D 1) (R 1) [274,96,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8079
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8080 : PairBound 9 := { available := 230, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 28 137 246 230 230 230 486), lower := (rows 275 98 28 137 16 32 64 128 256), losses := [] }

theorem u8080 : Upper (D 1) (R 1) [274,96,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8080
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8081 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8081 : Upper (D 1) (R 1) [274,96,24,130] 13 := by
  apply FastRouting.sound _ _ [274,96,24,130] 13 (by decide) (choices 1) [1,4,32,128] r8081 c8081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4796
  · exact u4797
  · exact u4798
  · exact u4799

def b8082 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 28 140 243 227 227 227 483), lower := (rows 275 98 28 140 16 32 64 128 256), losses := [] }

theorem u8082 : Upper (D 1) (R 1) [274,96,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8082
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8083 : Route 9 := (fun mask => (mask,id))

def c8083 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8083 : Upper (D 1) (R 1) [274,96,24,160] 13 := by
  apply FastRouting.sound _ _ [274,96,24,160] 13 (by decide) (choices 1) [1,2,4,64,128] r8083 c8083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4800
  · exact u4801
  · exact u4802
  · exact u4803
  · exact u4804

def b8084 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 98 37 74 156 188 220 156 412), lower := (rows 275 98 37 74 16 32 64 128 256), losses := [] }

theorem u8084 : Upper (D 1) (R 1) [274,96,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8084
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8085 : Route 9 := (fun mask => (mask,id))

def c8085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8085 : Upper (D 1) (R 1) [274,96,33,68] 13 := by
  apply FastRouting.sound _ _ [274,96,33,68] 13 (by decide) (choices 1) [2,8,128] r8085 c8085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4805
  · exact u4806
  · exact u4807

def r8086 : Route 9 := (fun mask => (mask,id))

def c8086 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8086 : Upper (D 1) (R 1) [274,96,33,80] 13 := by
  apply FastRouting.sound _ _ [274,96,33,80] 13 (by decide) (choices 1) [2,4,8,128] r8086 c8086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4808
  · exact u4809
  · exact u4810
  · exact u4811

def r8087 : Route 9 := (fun mask => (mask,id))

def c8087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8087 : Upper (D 1) (R 1) [274,96,33,130] 13 := by
  apply FastRouting.sound _ _ [274,96,33,130] 13 (by decide) (choices 1) [4,8,64,128] r8087 c8087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4812
  · exact u4813
  · exact u4814
  · exact u4815

def r8088 : Route 9 := (fun mask => (mask,id))

def c8088 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8088 : Upper (D 1) (R 1) [274,96,33,132] 13 := by
  apply FastRouting.sound _ _ [274,96,33,132] 13 (by decide) (choices 1) [2,8,64,128] r8088 c8088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4816
  · exact u4817
  · exact u4818
  · exact u4819

def r8089 : Route 9 := (fun mask => (mask,id))

def c8089 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u8089 : Upper (D 1) (R 1) [274,96,33,144] 13 := by
  apply FastRouting.sound _ _ [274,96,33,144] 13 (by decide) (choices 1) [2,4,8,64,128] r8089 c8089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4820
  · exact u4821
  · exact u4822
  · exact u4823
  · exact u4824

def r8090 : Route 9 := (fun mask => (mask,id))

def c8090 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8090 : Upper (D 1) (R 1) [274,96,33,192] 13 := by
  apply FastRouting.sound _ _ [274,96,33,192] 13 (by decide) (choices 1) [2,4,8,128] r8090 c8090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4825
  · exact u4826
  · exact u4827
  · exact u4828

def b8091 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 38 76 153 185 217 153 409), lower := (rows 275 98 38 76 16 32 64 128 256), losses := [] }

theorem u8091 : Upper (D 1) (R 1) [274,96,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8091
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8092 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 38 88 157 173 205 141 397), lower := (rows 275 98 38 88 16 32 64 128 256), losses := [] }

theorem u8092 : Upper (D 1) (R 1) [274,96,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8092
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8093 : PairBound 9 := { available := 220, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 38 137 220 252 220 220 476), lower := (rows 275 98 38 137 16 32 64 128 256), losses := [] }

theorem u8093 : Upper (D 1) (R 1) [274,96,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8093
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8094 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 38 140 217 249 217 217 473), lower := (rows 275 98 38 140 16 32 64 128 256), losses := [] }

theorem u8094 : Upper (D 1) (R 1) [274,96,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8094
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8095 : PairBound 9 := { available := 205, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 38 152 221 237 205 205 461), lower := (rows 275 98 38 152 16 32 64 128 256), losses := [] }

theorem u8095 : Upper (D 1) (R 1) [274,96,34,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8095
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8096 : PairBound 9 := { available := 157, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 38 200 157 189 221 157 413), lower := (rows 275 98 38 200 16 32 64 128 256), losses := [] }

theorem u8096 : Upper (D 1) (R 1) [274,96,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8096
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8097 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 44 76 147 179 211 147 403), lower := (rows 275 98 44 76 16 32 64 128 256), losses := [] }

theorem u8097 : Upper (D 1) (R 1) [274,96,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8097
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8098 : Route 9 := (fun mask => (mask,id))

def c8098 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8098 : Upper (D 1) (R 1) [274,96,40,80] 13 := by
  apply FastRouting.sound _ _ [274,96,40,80] 13 (by decide) (choices 1) [1,2,4,128] r8098 c8098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4829
  · exact u4830
  · exact u4831
  · exact u4832

def r8099 : Route 9 := (fun mask => (mask,id))

def c8099 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8099 : Upper (D 1) (R 1) [274,96,40,129] 13 := by
  apply FastRouting.sound _ _ [274,96,40,129] 13 (by decide) (choices 1) [2,4,64,128] r8099 c8099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4833
  · exact u4834
  · exact u4835
  · exact u4836

#print axioms u8099
end Delivery.IrregularNine14.P01
