import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0083
import IrregularNine14P01C0084
import IrregularNine14P01C0085

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8220 : Route 9 := (fun mask => (mask,id))

def c8220 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8220 : Upper (D 1) (R 1) [276,40,96,18] 13 := by
  apply FastRouting.sound _ _ [276,40,96,18] 13 (by decide) (choices 1) [1,2,64,128] r8220 c8220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4996
  · exact u4997
  · exact u4998
  · exact u4999

def b8221 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 73 146 178 210 146 402), lower := (rows 277 42 100 73 16 32 64 128 256), losses := [] }

theorem u8221 : Upper (D 1) (R 1) [276,40,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8222 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 100 74 147 179 211 147 403), lower := (rows 277 42 100 74 16 32 64 128 256), losses := [] }

theorem u8222 : Upper (D 1) (R 1) [276,40,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8222
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8223 : Route 9 := (fun mask => (mask,id))

def c8223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8223 : Upper (D 1) (R 1) [276,40,96,80] 13 := by
  apply FastRouting.sound _ _ [276,40,96,80] 13 (by decide) (choices 1) [1,2,128] r8223 c8223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5000
  · exact u5001
  · exact u5002

def r8224 : Route 9 := (fun mask => (mask,id))

def c8224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8224 : Upper (D 1) (R 1) [276,40,96,129] 13 := by
  apply FastRouting.sound _ _ [276,40,96,129] 13 (by decide) (choices 1) [2,64,128] r8224 c8224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5003
  · exact u5004
  · exact u5005

def r8225 : Route 9 := (fun mask => (mask,id))

def c8225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8225 : Upper (D 1) (R 1) [276,40,96,130] 13 := by
  apply FastRouting.sound _ _ [276,40,96,130] 13 (by decide) (choices 1) [1,2,64,128] r8225 c8225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5006
  · exact u5007
  · exact u5008
  · exact u5009

def r8226 : Route 9 := (fun mask => (mask,id))

def c8226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8226 : Upper (D 1) (R 1) [276,40,96,144] 13 := by
  apply FastRouting.sound _ _ [276,40,96,144] 13 (by decide) (choices 1) [1,2,64,128] r8226 c8226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5010
  · exact u5011
  · exact u5012
  · exact u5013

def r8227 : Route 9 := (fun mask => (mask,id))

def c8227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8227 : Upper (D 1) (R 1) [276,40,96,192] 13 := by
  apply FastRouting.sound _ _ [276,40,96,192] 13 (by decide) (choices 1) [1,2,128] r8227 c8227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5014
  · exact u5015
  · exact u5016

def r8228 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8228 : Upper (D 1) (R 1) [276,40,192,3] 13 := by
  apply FastRouting.sound _ _ [276,40,192,3] 13 (by decide) (choices 1) [2,32,64] r8228 c8228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5017
  · exact u5018
  · exact u5019

def b8229 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 196 25 242 226 226 226 482), lower := (rows 277 42 196 25 16 32 64 128 256), losses := [] }

theorem u8229 : Upper (D 1) (R 1) [276,40,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8229
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8230 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8230 : Upper (D 1) (R 1) [276,40,192,18] 13 := by
  apply FastRouting.sound _ _ [276,40,192,18] 13 (by decide) (choices 1) [1,2,32,64] r8230 c8230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5020
  · exact u5021
  · exact u5022
  · exact u5023

def b8231 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 196 41 210 242 210 210 466), lower := (rows 277 42 196 41 16 32 64 128 256), losses := [] }

theorem u8231 : Upper (D 1) (R 1) [276,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8231
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8232 : PairBound 9 := { available := 211, camps := [{ cop := 5, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 196 42 211 243 211 211 467), lower := (rows 277 42 196 42 16 32 64 128 256), losses := [] }

theorem u8232 : Upper (D 1) (R 1) [276,40,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8232
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8233 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 196 56 211 227 195 195 451), lower := (rows 277 42 196 56 16 32 64 128 256), losses := [] }

theorem u8233 : Upper (D 1) (R 1) [276,40,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8233
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8234 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 196 73 178 178 242 178 434), lower := (rows 277 42 196 73 16 32 64 128 256), losses := [] }

theorem u8234 : Upper (D 1) (R 1) [276,40,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8234
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8235 : Route 9 := (fun mask => (mask,id))

def c8235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8235 : Upper (D 1) (R 1) [276,40,192,66] 13 := by
  apply FastRouting.sound _ _ [276,40,192,66] 13 (by decide) (choices 1) [1,2,32,128] r8235 c8235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5024
  · exact u5025
  · exact u5026
  · exact u5027

def r8236 : Route 9 := (fun mask => (mask,id))

def c8236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8236 : Upper (D 1) (R 1) [276,40,192,80] 13 := by
  apply FastRouting.sound _ _ [276,40,192,80] 13 (by decide) (choices 1) [1,2,32,128] r8236 c8236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5028
  · exact u5029
  · exact u5030
  · exact u5031

def b8237 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 196 104 147 179 211 147 403), lower := (rows 277 42 196 104 16 32 64 128 256), losses := [] }

theorem u8237 : Upper (D 1) (R 1) [276,40,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8237
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8238 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 196 200 51 51 115 179 307), lower := (rows 277 42 196 200 16 32 64 128 256), losses := [] }

theorem u8238 : Upper (D 1) (R 1) [276,40,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8239 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 277 50 14 11 240 224 224 224 480), lower := (rows 277 50 14 11 16 32 64 128 256), losses := [] }

theorem u8239 : Upper (D 1) (R 1) [276,48,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8239
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8240 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 14 41 210 226 194 194 450), lower := (rows 277 50 14 41 16 32 64 128 256), losses := [] }

theorem u8240 : Upper (D 1) (R 1) [276,48,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8241 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 14 42 209 225 193 193 449), lower := (rows 277 50 14 42 16 32 64 128 256), losses := [] }

theorem u8241 : Upper (D 1) (R 1) [276,48,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8241
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8242 : PairBound 9 := { available := 226, camps := [], pairs := [(3,4)], upper := (rows 277 50 14 73 242 226 226 226 482), lower := (rows 277 50 14 73 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 9 0 38 70 134 262), good := (rows 493 482 494 73 0 32 64 128 256) }] }

theorem u8242 : Upper (D 1) (R 1) [276,48,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8242
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8243 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 14 74 241 225 225 225 481), lower := (rows 277 50 14 74 16 32 64 128 256), losses := [] }

theorem u8243 : Upper (D 1) (R 1) [276,48,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8244 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 14 104 211 227 195 195 451), lower := (rows 277 50 14 104 16 32 64 128 256), losses := [] }

theorem u8244 : Upper (D 1) (R 1) [276,48,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8245 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8245 : Upper (D 1) (R 1) [276,48,10,192] 13 := by
  apply FastRouting.sound _ _ [276,48,10,192] 13 (by decide) (choices 1) [1,2,32,64] r8245 c8245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5032
  · exact u5033
  · exact u5034
  · exact u5035

def b8246 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 44 11 210 226 194 194 450), lower := (rows 277 50 44 11 16 32 64 128 256), losses := [] }

theorem u8246 : Upper (D 1) (R 1) [276,48,40,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8246
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8247 : Route 9 := (fun mask => (mask,id))

def c8247 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8247 : Upper (D 1) (R 1) [276,48,40,65] 13 := by
  apply FastRouting.sound _ _ [276,48,40,65] 13 (by decide) (choices 1) [2,64,128] r8247 c8247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5036
  · exact u5037
  · exact u5038

def r8248 : Route 9 := (fun mask => (mask,id))

def c8248 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8248 : Upper (D 1) (R 1) [276,48,40,66] 13 := by
  apply FastRouting.sound _ _ [276,48,40,66] 13 (by decide) (choices 1) [1,2,64,128] r8248 c8248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5039
  · exact u5040
  · exact u5041
  · exact u5042

def r8249 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8249 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8249 : Upper (D 1) (R 1) [276,48,40,192] 13 := by
  apply FastRouting.sound _ _ [276,48,40,192] 13 (by decide) (choices 1) [1,2,64] r8249 c8249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5043
  · exact u5044
  · exact u5045

def b8250 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 70 11 248 232 232 232 488), lower := (rows 277 50 70 11 16 32 64 128 256), losses := [] }

theorem u8250 : Upper (D 1) (R 1) [276,48,66,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8250
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8251 : Route 9 := (fun mask => (mask,id))

def c8251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8251 : Upper (D 1) (R 1) [276,48,66,33] 13 := by
  apply FastRouting.sound _ _ [276,48,66,33] 13 (by decide) (choices 1) [2,8,64,128] r8251 c8251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5046
  · exact u5047
  · exact u5048
  · exact u5049

def b8252 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 50 70 42 217 233 201 201 457), lower := (rows 277 50 70 42 16 32 64 128 256), losses := [] }

theorem u8252 : Upper (D 1) (R 1) [276,48,66,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8253 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 73 186 170 234 170 426), lower := (rows 277 50 70 73 16 32 64 128 256), losses := [] }

theorem u8253 : Upper (D 1) (R 1) [276,48,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8254 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 50 70 74 185 169 233 169 425), lower := (rows 277 50 70 74 16 32 64 128 256), losses := [] }

theorem u8254 : Upper (D 1) (R 1) [276,48,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8255 : Route 9 := (fun mask => (mask,id))

def c8255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8255 : Upper (D 1) (R 1) [276,48,66,96] 13 := by
  apply FastRouting.sound _ _ [276,48,66,96] 13 (by decide) (choices 1) [1,2,8,128] r8255 c8255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5050
  · exact u5051
  · exact u5052
  · exact u5053

def r8256 : Route 9 := (fun mask => (mask,id))

def c8256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8256 : Upper (D 1) (R 1) [276,48,66,129] 13 := by
  apply FastRouting.sound _ _ [276,48,66,129] 13 (by decide) (choices 1) [2,8,32,64,128] r8256 c8256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5054
  · exact u5055
  · exact u5056
  · exact u5057
  · exact u5058

def r8257 : Route 9 := (fun mask => (mask,id))

def c8257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8257 : Upper (D 1) (R 1) [276,48,66,130] 13 := by
  apply FastRouting.sound _ _ [276,48,66,130] 13 (by decide) (choices 1) [1,8,32,64,128] r8257 c8257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5059
  · exact u5060
  · exact u5061
  · exact u5062
  · exact u5063

def r8258 : Route 9 := (fun mask => (mask,id))

def c8258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8258 : Upper (D 1) (R 1) [276,48,66,160] 13 := by
  apply FastRouting.sound _ _ [276,48,66,160] 13 (by decide) (choices 1) [1,2,8,64,128] r8258 c8258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5064
  · exact u5065
  · exact u5066
  · exact u5067
  · exact u5068

def r8259 : Route 9 := (fun mask => (mask,id))

def c8259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8259 : Upper (D 1) (R 1) [276,48,66,192] 13 := by
  apply FastRouting.sound _ _ [276,48,66,192] 13 (by decide) (choices 1) [1,2,8,32,128] r8259 c8259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5069
  · exact u5070
  · exact u5071
  · exact u5072
  · exact u5073

def b8260 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 76 11 242 226 226 226 482), lower := (rows 277 50 76 11 16 32 64 128 256), losses := [] }

theorem u8260 : Upper (D 1) (R 1) [276,48,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8260
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8261 : Route 9 := (fun mask => (mask,id))

def c8261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8261 : Upper (D 1) (R 1) [276,48,72,33] 13 := by
  apply FastRouting.sound _ _ [276,48,72,33] 13 (by decide) (choices 1) [2,64,128] r8261 c8261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5074
  · exact u5075
  · exact u5076

def b8262 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 50 76 42 211 227 195 195 451), lower := (rows 277 50 76 42 16 32 64 128 256), losses := [] }

theorem u8262 : Upper (D 1) (R 1) [276,48,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8262
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8263 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 50 76 73 178 162 226 162 418), lower := (rows 277 50 76 73 16 32 64 128 256), losses := [] }

theorem u8263 : Upper (D 1) (R 1) [276,48,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8264 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 50 76 74 179 163 227 163 419), lower := (rows 277 50 76 74 16 32 64 128 256), losses := [] }

theorem u8264 : Upper (D 1) (R 1) [276,48,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8265 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 50 76 104 147 163 195 131 387), lower := (rows 277 50 76 104 16 32 64 128 256), losses := [] }

theorem u8265 : Upper (D 1) (R 1) [276,48,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8265
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8266 : Route 9 := (fun mask => (mask,id))

def c8266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8266 : Upper (D 1) (R 1) [276,48,72,129] 13 := by
  apply FastRouting.sound _ _ [276,48,72,129] 13 (by decide) (choices 1) [2,32,64,128] r8266 c8266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5077
  · exact u5078
  · exact u5079
  · exact u5080

def r8267 : Route 9 := (fun mask => (mask,id))

def c8267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8267 : Upper (D 1) (R 1) [276,48,72,130] 13 := by
  apply FastRouting.sound _ _ [276,48,72,130] 13 (by decide) (choices 1) [1,2,32,64,128] r8267 c8267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5081
  · exact u5082
  · exact u5083
  · exact u5084
  · exact u5085

def r8268 : Route 9 := (fun mask => (mask,id))

def c8268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8268 : Upper (D 1) (R 1) [276,48,72,160] 13 := by
  apply FastRouting.sound _ _ [276,48,72,160] 13 (by decide) (choices 1) [1,2,64,128] r8268 c8268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5086
  · exact u5087
  · exact u5088
  · exact u5089

def b8269 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 50 76 200 179 163 227 163 419), lower := (rows 277 50 76 200 16 32 64 128 256), losses := [] }

theorem u8269 : Upper (D 1) (R 1) [276,48,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8269
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8270 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 100 11 218 234 202 202 458), lower := (rows 277 50 100 11 16 32 64 128 256), losses := [] }

theorem u8270 : Upper (D 1) (R 1) [276,48,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8270
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8271 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 73 154 170 202 138 394), lower := (rows 277 50 100 73 16 32 64 128 256), losses := [] }

theorem u8271 : Upper (D 1) (R 1) [276,48,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8271
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8272 : Route 9 := (fun mask => (mask,id))

def c8272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8272 : Upper (D 1) (R 1) [276,48,96,66] 13 := by
  apply FastRouting.sound _ _ [276,48,96,66] 13 (by decide) (choices 1) [1,2,8,128] r8272 c8272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5090
  · exact u5091
  · exact u5092
  · exact u5093

def r8273 : Route 9 := (fun mask => (mask,id))

def c8273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8273 : Upper (D 1) (R 1) [276,48,96,129] 13 := by
  apply FastRouting.sound _ _ [276,48,96,129] 13 (by decide) (choices 1) [2,8,64,128] r8273 c8273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5094
  · exact u5095
  · exact u5096
  · exact u5097

def r8274 : Route 9 := (fun mask => (mask,id))

def c8274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8274 : Upper (D 1) (R 1) [276,48,96,130] 13 := by
  apply FastRouting.sound _ _ [276,48,96,130] 13 (by decide) (choices 1) [1,2,8,64,128] r8274 c8274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5098
  · exact u5099
  · exact u5100
  · exact u5101
  · exact u5102

def r8275 : Route 9 := (fun mask => (mask,id))

def c8275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8275 : Upper (D 1) (R 1) [276,48,96,192] 13 := by
  apply FastRouting.sound _ _ [276,48,96,192] 13 (by decide) (choices 1) [1,2,8,128] r8275 c8275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5103
  · exact u5104
  · exact u5105
  · exact u5106

def b8276 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 196 11 250 234 234 234 490), lower := (rows 277 50 196 11 16 32 64 128 256), losses := [] }

theorem u8276 : Upper (D 1) (R 1) [276,48,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8276
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8277 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8277 : Upper (D 1) (R 1) [276,48,192,33] 13 := by
  apply FastRouting.sound _ _ [276,48,192,33] 13 (by decide) (choices 1) [2,8,64] r8277 c8277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5107
  · exact u5108
  · exact u5109

def b8278 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 50 196 42 219 235 203 203 459), lower := (rows 277 50 196 42 16 32 64 128 256), losses := [] }

theorem u8278 : Upper (D 1) (R 1) [276,48,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8278
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8279 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 196 73 186 170 234 170 426), lower := (rows 277 50 196 73 16 32 64 128 256), losses := [] }

theorem u8279 : Upper (D 1) (R 1) [276,48,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8279
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8279
end Delivery.IrregularNine14.P01
