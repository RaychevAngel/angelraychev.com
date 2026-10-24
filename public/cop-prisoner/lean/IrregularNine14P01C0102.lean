import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0039

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6120 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 37 74 466 482 450 450 450), lower := (rows 29 50 37 74 16 32 64 128 256), losses := [] }

theorem u6120 : Upper (D 1) (R 1) [28,48,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6120
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6121 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 37 200 466 482 450 450 450), lower := (rows 29 50 37 200 16 32 64 128 256), losses := [] }

theorem u6121 : Upper (D 1) (R 1) [28,48,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6121
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6122 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 37 266 210 226 194 194 450), lower := (rows 29 50 37 266 16 32 64 128 256), losses := [] }

theorem u6122 : Upper (D 1) (R 1) [28,48,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6122
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6123 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 37 328 210 226 194 194 450), lower := (rows 29 50 37 328 16 32 64 128 256), losses := [] }

theorem u6123 : Upper (D 1) (R 1) [28,48,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6123
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6124 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 50 38 74 465 481 449 449 449), lower := (rows 29 50 38 74 16 32 64 128 256), losses := [] }

theorem u6124 : Upper (D 1) (R 1) [28,48,34,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6124
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6125 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 50 38 200 467 483 451 451 451), lower := (rows 29 50 38 200 16 32 64 128 256), losses := [] }

theorem u6125 : Upper (D 1) (R 1) [28,48,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6125
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6126 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 50 38 266 209 225 193 193 449), lower := (rows 29 50 38 266 16 32 64 128 256), losses := [] }

theorem u6126 : Upper (D 1) (R 1) [28,48,34,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6126
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6127 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 50 38 328 211 227 195 195 451), lower := (rows 29 50 38 328 16 32 64 128 256), losses := [] }

theorem u6127 : Upper (D 1) (R 1) [28,48,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6128 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 69 74 434 418 482 418 418), lower := (rows 29 50 69 74 16 32 64 128 256), losses := [] }

theorem u6128 : Upper (D 1) (R 1) [28,48,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6129 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 69 104 402 418 450 386 386), lower := (rows 29 50 69 104 16 32 64 128 256), losses := [] }

theorem u6129 : Upper (D 1) (R 1) [28,48,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6130 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 69 138 498 482 482 482 482), lower := (rows 29 50 69 138 16 32 64 128 256), losses := [] }

theorem u6130 : Upper (D 1) (R 1) [28,48,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6130
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6131 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 69 168 466 482 450 450 450), lower := (rows 29 50 69 168 16 32 64 128 256), losses := [] }

theorem u6131 : Upper (D 1) (R 1) [28,48,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6132 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 69 200 434 418 482 418 418), lower := (rows 29 50 69 200 16 32 64 128 256), losses := [] }

theorem u6132 : Upper (D 1) (R 1) [28,48,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6133 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 69 266 242 226 226 226 482), lower := (rows 29 50 69 266 16 32 64 128 256), losses := [] }

theorem u6133 : Upper (D 1) (R 1) [28,48,65,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6133
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6134 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 69 296 210 226 194 194 450), lower := (rows 29 50 69 296 16 32 64 128 256), losses := [] }

theorem u6134 : Upper (D 1) (R 1) [28,48,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6135 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 69 328 178 162 226 162 418), lower := (rows 29 50 69 328 16 32 64 128 256), losses := [] }

theorem u6135 : Upper (D 1) (R 1) [28,48,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6135
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6136 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 69 392 242 226 226 226 482), lower := (rows 29 50 69 392 16 32 64 128 256), losses := [] }

theorem u6136 : Upper (D 1) (R 1) [28,48,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6136
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6137 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 50 70 74 433 417 481 417 417), lower := (rows 29 50 70 74 16 32 64 128 256), losses := [] }

theorem u6137 : Upper (D 1) (R 1) [28,48,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6137
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6138 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 104 403 419 451 387 387), lower := (rows 29 50 70 104 16 32 64 128 256), losses := [] }

theorem u6138 : Upper (D 1) (R 1) [28,48,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6138
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m6139_128 : Upper (D 1) (R 1) [28,48,66,130,128] 13 :=
  permutation_upper _ _ _ [28,48,66,130,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2348

def r6139 : Route 9 := (fun mask => (mask,id))

def c6139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6139 : Upper (D 1) (R 1) [28,48,66,130] 13 := by
  apply FastRouting.sound _ _ [28,48,66,130] 13 (by decide) (choices 1) [1,32,64,128,256] r6139 c6139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2346
  · exact u2347
  · exact u2348
  · exact m6139_128
  · exact u2349

def r6140 : Route 9 := (fun mask => (mask,id))

def c6140 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u6140 : Upper (D 1) (R 1) [28,48,66,160] 13 := by
  apply FastRouting.sound _ _ [28,48,66,160] 13 (by decide) (choices 1) [1,2,64,128,256] r6140 c6140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2350
  · exact u2351
  · exact u2352
  · exact u2353
  · exact u2354

def b6141 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 200 435 419 483 419 419), lower := (rows 29 50 70 200 16 32 64 128 256), losses := [] }

theorem u6141 : Upper (D 1) (R 1) [28,48,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6142 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 29 50 70 265 242 226 226 226 482), lower := (rows 29 50 70 265 16 32 64 128 256), losses := [] }

theorem u6142 : Upper (D 1) (R 1) [28,48,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6142
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6143 : Route 9 := (fun mask => (mask,id))

def c6143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6143 : Upper (D 1) (R 1) [28,48,66,258] 13 := by
  apply FastRouting.sound _ _ [28,48,66,258] 13 (by decide) (choices 1) [1,32,64,128] r6143 c6143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2355
  · exact u2356
  · exact u2357
  · exact u2358

def r6144 : Route 9 := (fun mask => (mask,id))

def c6144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6144 : Upper (D 1) (R 1) [28,48,66,288] 13 := by
  apply FastRouting.sound _ _ [28,48,66,288] 13 (by decide) (choices 1) [1,2,64,128] r6144 c6144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2359
  · exact u2360
  · exact u2361
  · exact u2362

def b6145 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 328 179 163 227 163 419), lower := (rows 29 50 70 328 16 32 64 128 256), losses := [] }

theorem u6145 : Upper (D 1) (R 1) [28,48,66,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6145
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6146 : Route 9 := (fun mask => (mask,id))

def c6146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6146 : Upper (D 1) (R 1) [28,48,66,384] 13 := by
  apply FastRouting.sound _ _ [28,48,66,384] 13 (by decide) (choices 1) [1,2,32,64,128] r6146 c6146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2363
  · exact u2364
  · exact u2365
  · exact u2366
  · exact u2367

def b6147 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 100 200 403 419 451 387 387), lower := (rows 29 50 100 200 16 32 64 128 256), losses := [] }

theorem u6147 : Upper (D 1) (R 1) [28,48,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6147
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6148 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 29 50 100 265 210 226 194 194 450), lower := (rows 29 50 100 265 16 32 64 128 256), losses := [] }

theorem u6148 : Upper (D 1) (R 1) [28,48,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6148
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6149 : Route 9 := (fun mask => (mask,id))

def c6149 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6149 : Upper (D 1) (R 1) [28,48,96,258] 13 := by
  apply FastRouting.sound _ _ [28,48,96,258] 13 (by decide) (choices 1) [1,2,64,128] r6149 c6149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2368
  · exact u2369
  · exact u2370
  · exact u2371

def b6150 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 100 328 147 163 195 131 387), lower := (rows 29 50 100 328 16 32 64 128 256), losses := [] }

theorem u6150 : Upper (D 1) (R 1) [28,48,96,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6150
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6151 : Route 9 := (fun mask => (mask,id))

def c6151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6151 : Upper (D 1) (R 1) [28,48,96,384] 13 := by
  apply FastRouting.sound _ _ [28,48,96,384] 13 (by decide) (choices 1) [1,2,64,128] r6151 c6151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2372
  · exact u2373
  · exact u2374
  · exact u2375

def b6152 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 29 50 196 200 307 291 355 419 291), lower := (rows 29 50 196 200 16 32 64 128 256), losses := [] }

theorem u6152 : Upper (D 1) (R 1) [28,48,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6153 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 29 50 196 265 242 226 226 226 482), lower := (rows 29 50 196 265 16 32 64 128 256), losses := [] }

theorem u6153 : Upper (D 1) (R 1) [28,48,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6153
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6154 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6154 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6154 : Upper (D 1) (R 1) [28,48,192,258] 13 := by
  apply FastRouting.sound _ _ [28,48,192,258] 13 (by decide) (choices 1) [1,2,32,64] r6154 c6154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2376
  · exact u2377
  · exact u2378
  · exact u2379

def r6155 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6155 : Upper (D 1) (R 1) [28,48,192,288] 13 := by
  apply FastRouting.sound _ _ [28,48,192,288] 13 (by decide) (choices 1) [1,2,64] r6155 c6155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2380
  · exact u2381
  · exact u2382

def b6156 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 196 328 179 163 227 163 419), lower := (rows 29 50 196 328 16 32 64 128 256), losses := [] }

theorem u6156 : Upper (D 1) (R 1) [28,48,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6156
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6157 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 5, targets := 32 }], pairs := [(0,5)], upper := (rows 29 98 7 26 496 480 480 480 480), lower := (rows 29 98 7 26 16 32 64 128 256), losses := [] }

theorem u6157 : Upper (D 1) (R 1) [28,96,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6158 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 98 7 42 464 496 464 464 464), lower := (rows 29 98 7 42 16 32 64 128 256), losses := [] }

theorem u6158 : Upper (D 1) (R 1) [28,96,3,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6158
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6159 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 56 466 482 450 450 450), lower := (rows 29 98 7 56 16 32 64 128 256), losses := [] }

theorem u6159 : Upper (D 1) (R 1) [28,96,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6159
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6160 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 98 7 104 402 434 466 402 402), lower := (rows 29 98 7 104 16 32 64 128 256), losses := [] }

theorem u6160 : Upper (D 1) (R 1) [28,96,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6160
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6161 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6161 : Upper (D 1) (R 1) [28,96,3,130] 13 := by
  apply FastRouting.sound _ _ [28,96,3,130] 13 (by decide) (choices 1) [32,128,256] r6161 c6161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2383
  · exact u2384
  · exact u2385

def b6162 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 152 498 482 482 482 482), lower := (rows 29 98 7 152 16 32 64 128 256), losses := [] }

theorem u6162 : Upper (D 1) (R 1) [28,96,3,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6163 : Route 9 := (fun mask => (mask,id))

def c6163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u6163 : Upper (D 1) (R 1) [28,96,3,160] 13 := by
  apply FastRouting.sound _ _ [28,96,3,160] 13 (by decide) (choices 1) [2,64,128,256] r6163 c6163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2386
  · exact u2387
  · exact u2388
  · exact u2389

def r6164 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6164 : Upper (D 1) (R 1) [28,96,3,258] 13 := by
  apply FastRouting.sound _ _ [28,96,3,258] 13 (by decide) (choices 1) [32,128] r6164 c6164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2390
  · exact u2391

def b6165 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 280 242 226 226 226 482), lower := (rows 29 98 7 280 16 32 64 128 256), losses := [] }

theorem u6165 : Upper (D 1) (R 1) [28,96,3,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6165
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6166 : Route 9 := (fun mask => (mask,id))

def c6166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6166 : Upper (D 1) (R 1) [28,96,3,288] 13 := by
  apply FastRouting.sound _ _ [28,96,3,288] 13 (by decide) (choices 1) [2,64,128] r6166 c6166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2392
  · exact u2393
  · exact u2394

def r6167 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6167 : Upper (D 1) (R 1) [28,96,3,384] 13 := by
  apply FastRouting.sound _ _ [28,96,3,384] 13 (by decide) (choices 1) [2,32,128] r6167 c6167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2395
  · exact u2396
  · exact u2397

def b6168 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 21 138 498 482 482 482 482), lower := (rows 29 98 21 138 16 32 64 128 256), losses := [] }

theorem u6168 : Upper (D 1) (R 1) [28,96,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6168
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6169 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 21 168 466 482 450 450 450), lower := (rows 29 98 21 168 16 32 64 128 256), losses := [] }

theorem u6169 : Upper (D 1) (R 1) [28,96,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6170 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 21 266 242 226 226 226 482), lower := (rows 29 98 21 266 16 32 64 128 256), losses := [] }

theorem u6170 : Upper (D 1) (R 1) [28,96,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6170
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6171 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 21 296 210 226 194 194 450), lower := (rows 29 98 21 296 16 32 64 128 256), losses := [] }

theorem u6171 : Upper (D 1) (R 1) [28,96,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6172 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 21 392 242 226 226 226 482), lower := (rows 29 98 21 392 16 32 64 128 256), losses := [] }

theorem u6172 : Upper (D 1) (R 1) [28,96,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6172
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6173 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 22 137 498 482 482 482 482), lower := (rows 29 98 22 137 16 32 64 128 256), losses := [] }

theorem u6173 : Upper (D 1) (R 1) [28,96,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6174 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 22 138 497 481 481 481 481), lower := (rows 29 98 22 138 16 32 64 128 256), losses := [] }

theorem u6174 : Upper (D 1) (R 1) [28,96,18,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6174
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6175 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 22 168 467 483 451 451 451), lower := (rows 29 98 22 168 16 32 64 128 256), losses := [] }

theorem u6175 : Upper (D 1) (R 1) [28,96,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6175
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6176 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 22 265 242 226 226 226 482), lower := (rows 29 98 22 265 16 32 64 128 256), losses := [] }

theorem u6176 : Upper (D 1) (R 1) [28,96,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6176
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6177 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 22 266 241 225 225 225 481), lower := (rows 29 98 22 266 16 32 64 128 256), losses := [] }

theorem u6177 : Upper (D 1) (R 1) [28,96,18,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6177
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6178 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 22 296 211 227 195 195 451), lower := (rows 29 98 22 296 16 32 64 128 256), losses := [] }

theorem u6178 : Upper (D 1) (R 1) [28,96,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6179 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 22 392 243 227 227 227 483), lower := (rows 29 98 22 392 16 32 64 128 256), losses := [] }

theorem u6179 : Upper (D 1) (R 1) [28,96,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6179
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6179
end Delivery.IrregularNine14.P01
