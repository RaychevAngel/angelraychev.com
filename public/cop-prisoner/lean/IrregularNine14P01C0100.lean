import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0037
import IrregularNine14P01C0038

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6000 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6000 : Upper (D 1) (R 1) [22,96,384,144] 13 := by
  apply FastRouting.sound _ _ [22,96,384,144] 13 (by decide) (choices 1) [1,2,8,32] r6000 c6000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2251
  · exact u2252
  · exact u2253
  · exact u2254

def r6001 : Route 9 := (fun mask => (mask,id))

def c6001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6001 : Upper (D 1) (R 1) [22,96,384,160] 13 := by
  apply FastRouting.sound _ _ [22,96,384,160] 13 (by decide) (choices 1) [1,2,8,64] r6001 c6001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2255
  · exact u2256
  · exact u2257
  · exact u2258

def b6002 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 259 44 26 240 224 224 224 480), lower := (rows 23 259 44 26 16 32 64 128 256), losses := [] }

theorem u6002 : Upper (D 1) (R 1) [22,257,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6002
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6003 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 259 44 42 208 240 208 208 464), lower := (rows 23 259 44 42 16 32 64 128 256), losses := [] }

theorem u6003 : Upper (D 1) (R 1) [22,257,40,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6003
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6004 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 44 56 210 226 194 194 450), lower := (rows 23 259 44 56 16 32 64 128 256), losses := [] }

theorem u6004 : Upper (D 1) (R 1) [22,257,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6004
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6005 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 44 74 240 240 240 240 496), lower := (rows 23 259 44 74 16 32 64 128 256), losses := [] }

theorem u6005 : Upper (D 1) (R 1) [22,257,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6005
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6006 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 259 44 88 242 226 226 226 482), lower := (rows 23 259 44 88 16 32 64 128 256), losses := [] }

theorem u6006 : Upper (D 1) (R 1) [22,257,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6006
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6007 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 44 104 210 242 210 210 466), lower := (rows 23 259 44 104 16 32 64 128 256), losses := [] }

theorem u6007 : Upper (D 1) (R 1) [22,257,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6007
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6008 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6008 : Upper (D 1) (R 1) [22,257,40,192] 13 := by
  apply FastRouting.sound _ _ [22,257,40,192] 13 (by decide) (choices 1) [2,32,64] r6008 c6008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2259
  · exact u2260
  · exact u2261

def b6009 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 259 100 26 248 232 232 232 488), lower := (rows 23 259 100 26 16 32 64 128 256), losses := [] }

theorem u6009 : Upper (D 1) (R 1) [22,257,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6009
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6010 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 100 42 216 248 216 216 472), lower := (rows 23 259 100 42 16 32 64 128 256), losses := [] }

theorem u6010 : Upper (D 1) (R 1) [22,257,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6010
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6011 : Route 9 := (fun mask => (mask,id))

def c6011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6011 : Upper (D 1) (R 1) [22,257,96,48] 13 := by
  apply FastRouting.sound _ _ [22,257,96,48] 13 (by decide) (choices 1) [2,8,64,128] r6011 c6011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2262
  · exact u2263
  · exact u2264
  · exact u2265

def b6012 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 259 100 104 154 186 218 154 410), lower := (rows 23 259 100 104 16 32 64 128 256), losses := [] }

theorem u6012 : Upper (D 1) (R 1) [22,257,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6012
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6013 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 116, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 100 138 248 248 248 248 504), lower := (rows 23 259 100 138 16 32 64 128 256), losses := [] }

theorem u6013 : Upper (D 1) (R 1) [22,257,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6013
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6014 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6014 : Upper (D 1) (R 1) [22,257,96,144] 13 := by
  apply FastRouting.sound _ _ [22,257,96,144] 13 (by decide) (choices 1) [2,8,32,128] r6014 c6014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2266
  · exact u2267
  · exact u2268
  · exact u2269

def r6015 : Route 9 := (fun mask => (mask,id))

def c6015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6015 : Upper (D 1) (R 1) [22,257,96,160] 13 := by
  apply FastRouting.sound _ _ [22,257,96,160] 13 (by decide) (choices 1) [2,8,64,128] r6015 c6015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2270
  · exact u2271
  · exact u2272
  · exact u2273

def b6016 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 266 37 26 240 224 224 224 480), lower := (rows 23 266 37 26 16 32 64 128 256), losses := [] }

theorem u6016 : Upper (D 1) (R 1) [22,264,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6016
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6017 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 266 37 42 208 240 208 208 464), lower := (rows 23 266 37 42 16 32 64 128 256), losses := [] }

theorem u6017 : Upper (D 1) (R 1) [22,264,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6017
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6018 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 266 37 56 210 226 194 194 450), lower := (rows 23 266 37 56 16 32 64 128 256), losses := [] }

theorem u6018 : Upper (D 1) (R 1) [22,264,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6018
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6019 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 266 37 74 240 240 240 240 496), lower := (rows 23 266 37 74 16 32 64 128 256), losses := [] }

theorem u6019 : Upper (D 1) (R 1) [22,264,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6019
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6020 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 266 37 88 242 226 226 226 482), lower := (rows 23 266 37 88 16 32 64 128 256), losses := [] }

theorem u6020 : Upper (D 1) (R 1) [22,264,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6020
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6021 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 402, targets := 32 }], pairs := [(1,5)], upper := (rows 23 266 37 104 210 242 210 210 466), lower := (rows 23 266 37 104 16 32 64 128 256), losses := [] }

theorem u6021 : Upper (D 1) (R 1) [22,264,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6021
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6022 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6022 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6022 : Upper (D 1) (R 1) [22,264,33,192] 13 := by
  apply FastRouting.sound _ _ [22,264,33,192] 13 (by decide) (choices 1) [2,32,64] r6022 c6022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2274
  · exact u2275
  · exact u2276

def b6023 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 266 100 11 240 240 240 240 496), lower := (rows 23 266 100 11 16 32 64 128 256), losses := [] }

theorem u6023 : Upper (D 1) (R 1) [22,264,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6023
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6024 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 266 100 25 242 226 226 226 482), lower := (rows 23 266 100 25 16 32 64 128 256), losses := [] }

theorem u6024 : Upper (D 1) (R 1) [22,264,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6024
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6025 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 266 100 26 241 225 225 225 481), lower := (rows 23 266 100 26 16 32 64 128 256), losses := [] }

theorem u6025 : Upper (D 1) (R 1) [22,264,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6025
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6026 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 23 266 100 41 210 242 210 210 466), lower := (rows 23 266 100 41 16 32 64 128 256), losses := [] }

theorem u6026 : Upper (D 1) (R 1) [22,264,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6026
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6027 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 266 100 42 209 241 209 209 465), lower := (rows 23 266 100 42 16 32 64 128 256), losses := [] }

theorem u6027 : Upper (D 1) (R 1) [22,264,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6027
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6028 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 266 100 56 211 227 195 195 451), lower := (rows 23 266 100 56 16 32 64 128 256), losses := [] }

theorem u6028 : Upper (D 1) (R 1) [22,264,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6029 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 266 100 104 147 179 211 147 403), lower := (rows 23 266 100 104 16 32 64 128 256), losses := [] }

theorem u6029 : Upper (D 1) (R 1) [22,264,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6029
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6030 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6030 : Upper (D 1) (R 1) [22,264,96,129] 13 := by
  apply FastRouting.sound _ _ [22,264,96,129] 13 (by decide) (choices 1) [2,32,128] r6030 c6030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2277
  · exact u2278
  · exact u2279

def b6031 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 266 100 138 241 241 241 241 497), lower := (rows 23 266 100 138 16 32 64 128 256), losses := [] }

theorem u6031 : Upper (D 1) (R 1) [22,264,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6031
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6032 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 266 100 152 243 227 227 227 483), lower := (rows 23 266 100 152 16 32 64 128 256), losses := [] }

theorem u6032 : Upper (D 1) (R 1) [22,264,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6032
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6033 : Route 9 := (fun mask => (mask,id))

def c6033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6033 : Upper (D 1) (R 1) [22,264,96,160] 13 := by
  apply FastRouting.sound _ _ [22,264,96,160] 13 (by decide) (choices 1) [1,2,64,128] r6033 c6033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2280
  · exact u2281
  · exact u2282
  · exact u2283

def b6034 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 13 26 240 224 224 224 480), lower := (rows 23 290 13 26 16 32 64 128 256), losses := [] }

theorem u6034 : Upper (D 1) (R 1) [22,288,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6034
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6035 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 290 13 42 208 240 208 208 464), lower := (rows 23 290 13 42 16 32 64 128 256), losses := [] }

theorem u6035 : Upper (D 1) (R 1) [22,288,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6035
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6036 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 13 56 210 226 194 194 450), lower := (rows 23 290 13 56 16 32 64 128 256), losses := [] }

theorem u6036 : Upper (D 1) (R 1) [22,288,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6037 : Route 9 := (fun mask => (mask,id))

def c6037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6037 : Upper (D 1) (R 1) [22,288,9,66] 13 := by
  apply FastRouting.sound _ _ [22,288,9,66] 13 (by decide) (choices 1) [32,64,128] r6037 c6037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2284
  · exact u2285
  · exact u2286

def b6038 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 13 88 242 226 226 226 482), lower := (rows 23 290 13 88 16 32 64 128 256), losses := [] }

theorem u6038 : Upper (D 1) (R 1) [22,288,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6038
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6039 : Route 9 := (fun mask => (mask,id))

def c6039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6039 : Upper (D 1) (R 1) [22,288,9,96] 13 := by
  apply FastRouting.sound _ _ [22,288,9,96] 13 (by decide) (choices 1) [2,64,128] r6039 c6039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2287
  · exact u2288
  · exact u2289

def r6040 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6040 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6040 : Upper (D 1) (R 1) [22,288,9,192] 13 := by
  apply FastRouting.sound _ _ [22,288,9,192] 13 (by decide) (choices 1) [2,32,64] r6040 c6040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2290
  · exact u2291
  · exact u2292

def b6041 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 290 69 26 248 232 232 232 488), lower := (rows 23 290 69 26 16 32 64 128 256), losses := [] }

theorem u6041 : Upper (D 1) (R 1) [22,288,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6041
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6042 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 290 69 42 216 248 216 216 472), lower := (rows 23 290 69 42 16 32 64 128 256), losses := [] }

theorem u6042 : Upper (D 1) (R 1) [22,288,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6042
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6043 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 69 56 218 234 202 202 458), lower := (rows 23 290 69 56 16 32 64 128 256), losses := [] }

theorem u6043 : Upper (D 1) (R 1) [22,288,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6043
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6044 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 69 74 184 184 248 184 440), lower := (rows 23 290 69 74 16 32 64 128 256), losses := [] }

theorem u6044 : Upper (D 1) (R 1) [22,288,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6044
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6045 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 69 88 186 170 234 170 426), lower := (rows 23 290 69 88 16 32 64 128 256), losses := [] }

theorem u6045 : Upper (D 1) (R 1) [22,288,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6045
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6046 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 402, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 69 104 154 186 218 154 410), lower := (rows 23 290 69 104 16 32 64 128 256), losses := [] }

theorem u6046 : Upper (D 1) (R 1) [22,288,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6046
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6047 : Route 9 := (fun mask => (mask,id))

def c6047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u6047 : Upper (D 1) (R 1) [22,288,65,130] 13 := by
  apply FastRouting.sound _ _ [22,288,65,130] 13 (by decide) (choices 1) [8,32,64,128] r6047 c6047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2293
  · exact u2294
  · exact u2295
  · exact u2296

def b6048 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 69 152 250 234 234 234 490), lower := (rows 23 290 69 152 16 32 64 128 256), losses := [] }

theorem u6048 : Upper (D 1) (R 1) [22,288,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6048
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6049 : Route 9 := (fun mask => (mask,id))

def c6049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6049 : Upper (D 1) (R 1) [22,288,65,160] 13 := by
  apply FastRouting.sound _ _ [22,288,65,160] 13 (by decide) (choices 1) [2,8,64,128] r6049 c6049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2297
  · exact u2298
  · exact u2299
  · exact u2300

def b6050 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 69 200 186 186 250 186 442), lower := (rows 23 290 69 200 16 32 64 128 256), losses := [] }

theorem u6050 : Upper (D 1) (R 1) [22,288,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6050
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6051 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 290 76 11 240 240 240 240 496), lower := (rows 23 290 76 11 16 32 64 128 256), losses := [] }

theorem u6051 : Upper (D 1) (R 1) [22,288,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6051
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6052 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 290 76 25 242 226 226 226 482), lower := (rows 23 290 76 25 16 32 64 128 256), losses := [] }

theorem u6052 : Upper (D 1) (R 1) [22,288,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6052
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6053 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 290 76 26 241 225 225 225 481), lower := (rows 23 290 76 26 16 32 64 128 256), losses := [] }

theorem u6053 : Upper (D 1) (R 1) [22,288,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6053
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6054 : PairBound 9 := { available := 210, camps := [], pairs := [(2,5)], upper := (rows 23 290 76 41 210 242 210 210 466), lower := (rows 23 290 76 41 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 67 131 259), good := (rows 471 466 76 477 16 0 64 128 256) }] }

theorem u6054 : Upper (D 1) (R 1) [22,288,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6054
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6055 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 290 76 42 209 241 209 209 465), lower := (rows 23 290 76 42 16 32 64 128 256), losses := [] }

theorem u6055 : Upper (D 1) (R 1) [22,288,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6055
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6056 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 76 56 211 227 195 195 451), lower := (rows 23 290 76 56 16 32 64 128 256), losses := [] }

theorem u6056 : Upper (D 1) (R 1) [22,288,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6056
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6057 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 76 73 178 178 242 178 434), lower := (rows 23 290 76 73 16 32 64 128 256), losses := [] }

theorem u6057 : Upper (D 1) (R 1) [22,288,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6057
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6058 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 76 74 177 177 241 177 433), lower := (rows 23 290 76 74 16 32 64 128 256), losses := [] }

theorem u6058 : Upper (D 1) (R 1) [22,288,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6058
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6059 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 76 88 179 163 227 163 419), lower := (rows 23 290 76 88 16 32 64 128 256), losses := [] }

theorem u6059 : Upper (D 1) (R 1) [22,288,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6059
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6059
end Delivery.IrregularNine14.P01
