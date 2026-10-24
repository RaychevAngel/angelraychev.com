import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0038
import IrregularNine14P01C0039

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6060 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 76 104 147 179 211 147 403), lower := (rows 23 290 76 104 16 32 64 128 256), losses := [] }

theorem u6060 : Upper (D 1) (R 1) [22,288,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6060
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6061 : Route 9 := (fun mask => (mask,id))

def c6061 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6061 : Upper (D 1) (R 1) [22,288,72,129] 13 := by
  apply FastRouting.sound _ _ [22,288,72,129] 13 (by decide) (choices 1) [2,32,64,128] r6061 c6061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2301
  · exact u2302
  · exact u2303
  · exact u2304

def r6062 : Route 9 := (fun mask => (mask,id))

def c6062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6062 : Upper (D 1) (R 1) [22,288,72,130] 13 := by
  apply FastRouting.sound _ _ [22,288,72,130] 13 (by decide) (choices 1) [1,32,64,128] r6062 c6062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2305
  · exact u2306
  · exact u2307
  · exact u2308

def b6063 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 76 152 243 227 227 227 483), lower := (rows 23 290 76 152 16 32 64 128 256), losses := [] }

theorem u6063 : Upper (D 1) (R 1) [22,288,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6063
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6064 : Route 9 := (fun mask => (mask,id))

def c6064 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6064 : Upper (D 1) (R 1) [22,288,72,160] 13 := by
  apply FastRouting.sound _ _ [22,288,72,160] 13 (by decide) (choices 1) [1,2,64,128] r6064 c6064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2309
  · exact u2310
  · exact u2311
  · exact u2312

def b6065 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 76 200 179 179 243 179 435), lower := (rows 23 290 76 200 16 32 64 128 256), losses := [] }

theorem u6065 : Upper (D 1) (R 1) [22,288,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6065
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6066 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 290 196 11 248 248 248 248 504), lower := (rows 23 290 196 11 16 32 64 128 256), losses := [] }

theorem u6066 : Upper (D 1) (R 1) [22,288,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6066
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6067 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 290 196 25 250 234 234 234 490), lower := (rows 23 290 196 25 16 32 64 128 256), losses := [] }

theorem u6067 : Upper (D 1) (R 1) [22,288,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6067
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6068 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 290 196 26 249 233 233 233 489), lower := (rows 23 290 196 26 16 32 64 128 256), losses := [] }

theorem u6068 : Upper (D 1) (R 1) [22,288,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6068
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6069 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6069 : Upper (D 1) (R 1) [22,288,192,33] 13 := by
  apply FastRouting.sound _ _ [22,288,192,33] 13 (by decide) (choices 1) [2,8,64] r6069 c6069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2313
  · exact u2314
  · exact u2315

def b6070 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 290 196 42 217 249 217 217 473), lower := (rows 23 290 196 42 16 32 64 128 256), losses := [] }

theorem u6070 : Upper (D 1) (R 1) [22,288,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6070
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6071 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6071 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6071 : Upper (D 1) (R 1) [22,288,192,48] 13 := by
  apply FastRouting.sound _ _ [22,288,192,48] 13 (by decide) (choices 1) [1,2,8,64] r6071 c6071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2316
  · exact u2317
  · exact u2318
  · exact u2319

def b6072 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 196 73 186 186 250 186 442), lower := (rows 23 290 196 73 16 32 64 128 256), losses := [] }

theorem u6072 : Upper (D 1) (R 1) [22,288,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6072
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6073 : Route 9 := (fun mask => (mask,id))

def c6073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6073 : Upper (D 1) (R 1) [22,288,192,66] 13 := by
  apply FastRouting.sound _ _ [22,288,192,66] 13 (by decide) (choices 1) [1,8,32,128] r6073 c6073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2320
  · exact u2321
  · exact u2322
  · exact u2323

def r6074 : Route 9 := (fun mask => (mask,id))

def c6074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6074 : Upper (D 1) (R 1) [22,288,192,80] 13 := by
  apply FastRouting.sound _ _ [22,288,192,80] 13 (by decide) (choices 1) [1,2,8,32,128] r6074 c6074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2324
  · exact u2325
  · exact u2326
  · exact u2327
  · exact u2328

def r6075 : Route 9 := (fun mask => (mask,id))

def c6075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6075 : Upper (D 1) (R 1) [22,288,192,96] 13 := by
  apply FastRouting.sound _ _ [22,288,192,96] 13 (by decide) (choices 1) [1,2,8,128] r6075 c6075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2329
  · exact u2330
  · exact u2331
  · exact u2332

def b6076 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 290 196 200 59 59 123 187 315), lower := (rows 23 290 196 200 16 32 64 128 256), losses := [] }

theorem u6076 : Upper (D 1) (R 1) [22,288,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6076
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6077 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 22 74 496 480 480 480 480), lower := (rows 29 35 22 74 16 32 64 128 256), losses := [] }

theorem u6077 : Upper (D 1) (R 1) [28,33,18,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6077
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6078 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 22 200 498 482 482 482 482), lower := (rows 29 35 22 200 16 32 64 128 256), losses := [] }

theorem u6078 : Upper (D 1) (R 1) [28,33,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6078
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6079 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 22 266 240 224 224 224 480), lower := (rows 29 35 22 266 16 32 64 128 256), losses := [] }

theorem u6079 : Upper (D 1) (R 1) [28,33,18,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6079
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6080 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 22 328 242 226 226 226 482), lower := (rows 29 35 22 328 16 32 64 128 256), losses := [] }

theorem u6080 : Upper (D 1) (R 1) [28,33,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6080
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6081 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 35 38 74 464 496 464 464 464), lower := (rows 29 35 38 74 16 32 64 128 256), losses := [] }

theorem u6081 : Upper (D 1) (R 1) [28,33,34,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6081
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6082 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 35 38 200 466 498 466 466 466), lower := (rows 29 35 38 200 16 32 64 128 256), losses := [] }

theorem u6082 : Upper (D 1) (R 1) [28,33,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6082
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6083 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 35 38 266 208 240 208 208 464), lower := (rows 29 35 38 266 16 32 64 128 256), losses := [] }

theorem u6083 : Upper (D 1) (R 1) [28,33,34,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6083
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6084 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 35 38 328 210 242 210 210 466), lower := (rows 29 35 38 328 16 32 64 128 256), losses := [] }

theorem u6084 : Upper (D 1) (R 1) [28,33,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6084
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6085 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 52 74 466 482 450 450 450), lower := (rows 29 35 52 74 16 32 64 128 256), losses := [] }

theorem u6085 : Upper (D 1) (R 1) [28,33,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6085
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6086 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 52 200 466 482 450 450 450), lower := (rows 29 35 52 200 16 32 64 128 256), losses := [] }

theorem u6086 : Upper (D 1) (R 1) [28,33,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6086
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6087 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 52 266 210 226 194 194 450), lower := (rows 29 35 52 266 16 32 64 128 256), losses := [] }

theorem u6087 : Upper (D 1) (R 1) [28,33,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6087
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6088 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 52 328 210 226 194 194 450), lower := (rows 29 35 52 328 16 32 64 128 256), losses := [] }

theorem u6088 : Upper (D 1) (R 1) [28,33,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6088
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6089 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 35 70 74 432 432 496 432 432), lower := (rows 29 35 70 74 16 32 64 128 256), losses := [] }

theorem u6089 : Upper (D 1) (R 1) [28,33,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6089
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6090 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 70 88 434 418 482 418 418), lower := (rows 29 35 70 88 16 32 64 128 256), losses := [] }

theorem u6090 : Upper (D 1) (R 1) [28,33,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6090
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6091 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 70 104 402 434 466 402 402), lower := (rows 29 35 70 104 16 32 64 128 256), losses := [] }

theorem u6091 : Upper (D 1) (R 1) [28,33,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6091
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m6092_128 : Upper (D 1) (R 1) [28,33,66,130,128] 13 :=
  permutation_upper _ _ _ [28,33,66,130,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2334

def r6092 : Route 9 := (fun mask => (mask,id))

def c6092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6092 : Upper (D 1) (R 1) [28,33,66,130] 13 := by
  apply FastRouting.sound _ _ [28,33,66,130] 13 (by decide) (choices 1) [32,64,128,256] r6092 c6092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2333
  · exact u2334
  · exact m6092_128
  · exact u2335

def b6093 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 70 152 498 482 482 482 482), lower := (rows 29 35 70 152 16 32 64 128 256), losses := [] }

theorem u6093 : Upper (D 1) (R 1) [28,33,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6093
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6094 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 29 35 70 168 466 498 466 466 466), lower := (rows 29 35 70 168 16 32 64 128 256), losses := [] }

theorem u6094 : Upper (D 1) (R 1) [28,33,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6094
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6095 : PairBound 9 := { available := 434, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 70 200 434 434 498 434 434), lower := (rows 29 35 70 200 16 32 64 128 256), losses := [] }

theorem u6095 : Upper (D 1) (R 1) [28,33,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6095
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6096 : Route 9 := (fun mask => (mask,id))

def c6096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6096 : Upper (D 1) (R 1) [28,33,66,258] 13 := by
  apply FastRouting.sound _ _ [28,33,66,258] 13 (by decide) (choices 1) [32,64,128] r6096 c6096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2336
  · exact u2337
  · exact u2338

def b6097 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 70 280 242 226 226 226 482), lower := (rows 29 35 70 280 16 32 64 128 256), losses := [] }

theorem u6097 : Upper (D 1) (R 1) [28,33,66,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6097
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6098 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 29 35 70 296 210 242 210 210 466), lower := (rows 29 35 70 296 16 32 64 128 256), losses := [] }

theorem u6098 : Upper (D 1) (R 1) [28,33,66,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6098
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6099 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 70 328 178 178 242 178 434), lower := (rows 29 35 70 328 16 32 64 128 256), losses := [] }

theorem u6099 : Upper (D 1) (R 1) [28,33,66,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6099
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6100 : Route 9 := (fun mask => (mask,id))

def c6100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6100 : Upper (D 1) (R 1) [28,33,66,384] 13 := by
  apply FastRouting.sound _ _ [28,33,66,384] 13 (by decide) (choices 1) [2,32,64,128] r6100 c6100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2339
  · exact u2340
  · exact u2341
  · exact u2342

def b6101 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 84 200 434 418 482 418 418), lower := (rows 29 35 84 200 16 32 64 128 256), losses := [] }

theorem u6101 : Upper (D 1) (R 1) [28,33,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6102 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 84 266 242 226 226 226 482), lower := (rows 29 35 84 266 16 32 64 128 256), losses := [] }

theorem u6102 : Upper (D 1) (R 1) [28,33,80,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6102
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6103 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 162, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 84 328 178 162 226 162 418), lower := (rows 29 35 84 328 16 32 64 128 256), losses := [] }

theorem u6103 : Upper (D 1) (R 1) [28,33,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6104 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 84 392 242 226 226 226 482), lower := (rows 29 35 84 392 16 32 64 128 256), losses := [] }

theorem u6104 : Upper (D 1) (R 1) [28,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6104
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6105 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 100 200 402 434 466 402 402), lower := (rows 29 35 100 200 16 32 64 128 256), losses := [] }

theorem u6105 : Upper (D 1) (R 1) [28,33,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6105
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6106 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 29 35 100 266 210 242 210 210 466), lower := (rows 29 35 100 266 16 32 64 128 256), losses := [] }

theorem u6106 : Upper (D 1) (R 1) [28,33,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6106
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6107 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 100 328 146 178 210 146 402), lower := (rows 29 35 100 328 16 32 64 128 256), losses := [] }

theorem u6107 : Upper (D 1) (R 1) [28,33,96,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6108 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 29 35 100 392 210 242 210 210 466), lower := (rows 29 35 100 392 16 32 64 128 256), losses := [] }

theorem u6108 : Upper (D 1) (R 1) [28,33,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6109 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 29 35 196 200 306 306 370 434 306), lower := (rows 29 35 196 200 16 32 64 128 256), losses := [] }

theorem u6109 : Upper (D 1) (R 1) [28,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6109
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6110 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6110 : Upper (D 1) (R 1) [28,33,192,258] 13 := by
  apply FastRouting.sound _ _ [28,33,192,258] 13 (by decide) (choices 1) [2,32,64] r6110 c6110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2343
  · exact u2344
  · exact u2345

def b6111 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 35 196 280 242 226 226 226 482), lower := (rows 29 35 196 280 16 32 64 128 256), losses := [] }

theorem u6111 : Upper (D 1) (R 1) [28,33,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6112 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 29 35 196 296 210 242 210 210 466), lower := (rows 29 35 196 296 16 32 64 128 256), losses := [] }

theorem u6112 : Upper (D 1) (R 1) [28,33,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6112
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6113 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 196 328 178 178 242 178 434), lower := (rows 29 35 196 328 16 32 64 128 256), losses := [] }

theorem u6113 : Upper (D 1) (R 1) [28,33,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6114 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 7 74 496 480 480 480 480), lower := (rows 29 50 7 74 16 32 64 128 256), losses := [] }

theorem u6114 : Upper (D 1) (R 1) [28,48,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6115 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 7 104 466 482 450 450 450), lower := (rows 29 50 7 104 16 32 64 128 256), losses := [] }

theorem u6115 : Upper (D 1) (R 1) [28,48,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6115
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6116 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 7 200 498 482 482 482 482), lower := (rows 29 50 7 200 16 32 64 128 256), losses := [] }

theorem u6116 : Upper (D 1) (R 1) [28,48,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6117 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 7 266 240 224 224 224 480), lower := (rows 29 50 7 266 16 32 64 128 256), losses := [] }

theorem u6117 : Upper (D 1) (R 1) [28,48,3,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6118 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 7 296 210 226 194 194 450), lower := (rows 29 50 7 296 16 32 64 128 256), losses := [] }

theorem u6118 : Upper (D 1) (R 1) [28,48,3,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6119 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 7 328 242 226 226 226 482), lower := (rows 29 50 7 328 16 32 64 128 256), losses := [] }

theorem u6119 : Upper (D 1) (R 1) [28,48,3,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6119
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6119
end Delivery.IrregularNine14.P01
