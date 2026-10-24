import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0018
import IrregularNine14P00C0019

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2400 : Route 9 := (fun mask => (mask,id))

def c2400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2400 : Upper (D 0) (R 0) [22,96,257,48] 13 := by
  apply FastRouting.sound _ _ [22,96,257,48] 13 (by decide) (choices 1) [1,8,64,128] r2400 c2400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1126
  · exact u1127
  · exact u1128
  · exact u1129

def b2401 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 23 98 261 104 153 185 217 153 409), lower := (rows 23 98 261 104 16 32 64 128 256), losses := [] }

theorem u2401 : Upper (D 0) (R 0) [22,96,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2401
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2402 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0)], upper := (rows 23 98 261 137 248 248 248 248 504), lower := (rows 23 98 261 137 16 32 64 128 256), losses := [] }

theorem u2402 : Upper (D 0) (R 0) [22,96,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2402
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2403 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2403 : Upper (D 0) (R 0) [22,96,257,144] 13 := by
  apply FastRouting.sound _ _ [22,96,257,144] 13 (by decide) (choices 1) [1,8,32,128] r2403 c2403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1130
  · exact u1131
  · exact u1132
  · exact u1133

def r2404 : Route 9 := (fun mask => (mask,id))

def c2404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2404 : Upper (D 0) (R 0) [22,96,257,160] 13 := by
  apply FastRouting.sound _ _ [22,96,257,160] 13 (by decide) (choices 1) [1,8,64,128] r2404 c2404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1134
  · exact u1135
  · exact u1136
  · exact u1137

def b2405 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 268 25 241 225 225 225 481), lower := (rows 23 98 268 25 16 32 64 128 256), losses := [] }

theorem u2405 : Upper (D 0) (R 0) [22,96,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2405
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2406 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 268 41 209 241 209 209 465), lower := (rows 23 98 268 41 16 32 64 128 256), losses := [] }

theorem u2406 : Upper (D 0) (R 0) [22,96,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2406
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2407 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 268 56 209 225 193 193 449), lower := (rows 23 98 268 56 16 32 64 128 256), losses := [] }

theorem u2407 : Upper (D 0) (R 0) [22,96,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2407
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2408 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 23 98 268 104 145 177 209 145 401), lower := (rows 23 98 268 104 16 32 64 128 256), losses := [] }

theorem u2408 : Upper (D 0) (R 0) [22,96,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2408
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2409 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2409 : Upper (D 0) (R 0) [22,96,264,129] 13 := by
  apply FastRouting.sound _ _ [22,96,264,129] 13 (by decide) (choices 1) [1,32,128] r2409 c2409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1138
  · exact u1139
  · exact u1140

def b2410 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 268 152 241 225 225 225 481), lower := (rows 23 98 268 152 16 32 64 128 256), losses := [] }

theorem u2410 : Upper (D 0) (R 0) [22,96,264,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2410
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2411 : Route 9 := (fun mask => (mask,id))

def c2411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2411 : Upper (D 0) (R 0) [22,96,264,160] 13 := by
  apply FastRouting.sound _ _ [22,96,264,160] 13 (by decide) (choices 1) [1,64,128] r2411 c2411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1141
  · exact u1142
  · exact u1143

def b2412 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 388 25 249 233 233 233 489), lower := (rows 23 98 388 25 16 32 64 128 256), losses := [] }

theorem u2412 : Upper (D 0) (R 0) [22,96,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2412
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2413 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 388 41 217 249 217 217 473), lower := (rows 23 98 388 41 16 32 64 128 256), losses := [] }

theorem u2413 : Upper (D 0) (R 0) [22,96,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2413
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2414 : Route 9 := (fun mask => (mask,id))

def c2414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2414 : Upper (D 0) (R 0) [22,96,384,48] 13 := by
  apply FastRouting.sound _ _ [22,96,384,48] 13 (by decide) (choices 1) [1,8,64,128] r2414 c2414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1144
  · exact u1145
  · exact u1146
  · exact u1147

def b2415 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 23 98 388 104 153 185 217 153 409), lower := (rows 23 98 388 104 16 32 64 128 256), losses := [] }

theorem u2415 : Upper (D 0) (R 0) [22,96,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2415
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2416 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 388 137 121 121 121 249 377), lower := (rows 23 98 388 137 16 32 64 128 256), losses := [] }

theorem u2416 : Upper (D 0) (R 0) [22,96,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2416
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2417 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2417 : Upper (D 0) (R 0) [22,96,384,144] 13 := by
  apply FastRouting.sound _ _ [22,96,384,144] 13 (by decide) (choices 1) [1,8,32] r2417 c2417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1148
  · exact u1149
  · exact u1150

def r2418 : Route 9 := (fun mask => (mask,id))

def c2418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2418 : Upper (D 0) (R 0) [22,96,384,160] 13 := by
  apply FastRouting.sound _ _ [22,96,384,160] 13 (by decide) (choices 1) [1,8,64] r2418 c2418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1151
  · exact u1152
  · exact u1153

def b2419 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 76 25 496 480 480 480 480), lower := (rows 51 7 76 25 16 32 64 128 256), losses := [] }

theorem u2419 : Upper (D 0) (R 0) [50,5,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2419
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2420 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 56 465 481 449 449 449), lower := (rows 51 7 76 56 16 32 64 128 256), losses := [] }

theorem u2420 : Upper (D 0) (R 0) [50,5,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2420
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2421 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 51 7 76 73 432 432 496 432 432), lower := (rows 51 7 76 73 16 32 64 128 256), losses := [] }

theorem u2421 : Upper (D 0) (R 0) [50,5,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2421
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2422 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 88 433 417 481 417 417), lower := (rows 51 7 76 88 16 32 64 128 256), losses := [] }

theorem u2422 : Upper (D 0) (R 0) [50,5,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2422
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2423 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 137 496 496 496 496 496), lower := (rows 51 7 76 137 16 32 64 128 256), losses := [] }

theorem u2423 : Upper (D 0) (R 0) [50,5,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2423
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2424 : Route 9 := (fun mask => (mask,id))

def c2424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u2424 : Upper (D 0) (R 0) [50,5,72,144] 13 := by
  apply FastRouting.sound _ _ [50,5,72,144] 13 (by decide) (choices 1) [1,32,64,128,256] r2424 c2424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1154
  · exact u1155
  · exact u1156
  · exact u1157
  · exact u1158

def b2425 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 200 433 433 497 433 433), lower := (rows 51 7 76 200 16 32 64 128 256), losses := [] }

theorem u2425 : Upper (D 0) (R 0) [50,5,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2425
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2426 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 265 240 240 240 240 496), lower := (rows 51 7 76 265 16 32 64 128 256), losses := [] }

theorem u2426 : Upper (D 0) (R 0) [50,5,72,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2426
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2427 : Route 9 := (fun mask => (mask,id))

def c2427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2427 : Upper (D 0) (R 0) [50,5,72,272] 13 := by
  apply FastRouting.sound _ _ [50,5,72,272] 13 (by decide) (choices 1) [1,32,64,128] r2427 c2427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1159
  · exact u1160
  · exact u1161
  · exact u1162

def b2428 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 328 177 177 241 177 433), lower := (rows 51 7 76 328 16 32 64 128 256), losses := [] }

theorem u2428 : Upper (D 0) (R 0) [50,5,72,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2428
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2429 : Route 9 := (fun mask => (mask,id))

def c2429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2429 : Upper (D 0) (R 0) [50,5,72,384] 13 := by
  apply FastRouting.sound _ _ [50,5,72,384] 13 (by decide) (choices 1) [1,32,64,128] r2429 c2429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1163
  · exact u1164
  · exact u1165
  · exact u1166

def b2430 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 196 25 504 488 488 488 488), lower := (rows 51 7 196 25 16 32 64 128 256), losses := [] }

theorem u2430 : Upper (D 0) (R 0) [50,5,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2430
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2431 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 196 56 473 489 457 457 457), lower := (rows 51 7 196 56 16 32 64 128 256), losses := [] }

theorem u2431 : Upper (D 0) (R 0) [50,5,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2431
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2432 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 196 73 440 440 504 440 440), lower := (rows 51 7 196 73 16 32 64 128 256), losses := [] }

theorem u2432 : Upper (D 0) (R 0) [50,5,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2432
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2433 : Route 9 := (fun mask => (mask,id))

def c2433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u2433 : Upper (D 0) (R 0) [50,5,192,80] 13 := by
  apply FastRouting.sound _ _ [50,5,192,80] 13 (by decide) (choices 1) [1,8,32,128,256] r2433 c2433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1167
  · exact u1168
  · exact u1169
  · exact u1170
  · exact u1171

def b2434 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 51 7 196 200 313 313 377 441 313), lower := (rows 51 7 196 200 16 32 64 128 256), losses := [] }

theorem u2434 : Upper (D 0) (R 0) [50,5,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2434
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 196 265 248 248 248 248 504), lower := (rows 51 7 196 265 16 32 64 128 256), losses := [] }

theorem u2435 : Upper (D 0) (R 0) [50,5,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2435
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2436 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2436 : Upper (D 0) (R 0) [50,5,192,272] 13 := by
  apply FastRouting.sound _ _ [50,5,192,272] 13 (by decide) (choices 1) [1,8,32,64] r2436 c2436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1172
  · exact u1173
  · exact u1174
  · exact u1175

def r2437 : Route 9 := (fun mask => (mask,id))

def c2437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2437 : Upper (D 0) (R 0) [50,5,192,320] 13 := by
  apply FastRouting.sound _ _ [50,5,192,320] 13 (by decide) (choices 1) [1,8,32,128] r2437 c2437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1176
  · exact u1177
  · exact u1178
  · exact u1179

def b2438 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 268 25 240 224 224 224 480), lower := (rows 51 7 268 25 16 32 64 128 256), losses := [] }

theorem u2438 : Upper (D 0) (R 0) [50,5,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2438
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2439 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 268 56 209 225 193 193 449), lower := (rows 51 7 268 56 16 32 64 128 256), losses := [] }

theorem u2439 : Upper (D 0) (R 0) [50,5,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2439
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 268 73 240 240 240 240 496), lower := (rows 51 7 268 73 16 32 64 128 256), losses := [] }

theorem u2440 : Upper (D 0) (R 0) [50,5,264,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2440
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2441 : Route 9 := (fun mask => (mask,id))

def c2441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2441 : Upper (D 0) (R 0) [50,5,264,80] 13 := by
  apply FastRouting.sound _ _ [50,5,264,80] 13 (by decide) (choices 1) [1,32,64,128] r2441 c2441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1180
  · exact u1181
  · exact u1182
  · exact u1183

def r2442 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2442 : Upper (D 0) (R 0) [50,5,264,192] 13 := by
  apply FastRouting.sound _ _ [50,5,264,192] 13 (by decide) (choices 1) [1,32,64] r2442 c2442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1184
  · exact u1185
  · exact u1186

def b2443 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 324 25 248 232 232 232 488), lower := (rows 51 7 324 25 16 32 64 128 256), losses := [] }

theorem u2443 : Upper (D 0) (R 0) [50,5,320,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2443
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2444 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 324 56 217 233 201 201 457), lower := (rows 51 7 324 56 16 32 64 128 256), losses := [] }

theorem u2444 : Upper (D 0) (R 0) [50,5,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2444
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2445 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 324 73 184 184 248 184 440), lower := (rows 51 7 324 73 16 32 64 128 256), losses := [] }

theorem u2445 : Upper (D 0) (R 0) [50,5,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2445
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2446 : Route 9 := (fun mask => (mask,id))

def c2446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2446 : Upper (D 0) (R 0) [50,5,320,80] 13 := by
  apply FastRouting.sound _ _ [50,5,320,80] 13 (by decide) (choices 1) [1,8,32,128] r2446 c2446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1187
  · exact u1188
  · exact u1189
  · exact u1190

def b2447 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 324 137 248 248 248 248 504), lower := (rows 51 7 324 137 16 32 64 128 256), losses := [] }

theorem u2447 : Upper (D 0) (R 0) [50,5,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2447
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2448 : Route 9 := (fun mask => (mask,id))

def c2448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2448 : Upper (D 0) (R 0) [50,5,320,144] 13 := by
  apply FastRouting.sound _ _ [50,5,320,144] 13 (by decide) (choices 1) [1,8,32,64,128] r2448 c2448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1191
  · exact u1192
  · exact u1193
  · exact u1194
  · exact u1195

def r2449 : Route 9 := (fun mask => (mask,id))

def c2449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2449 : Upper (D 0) (R 0) [50,5,320,192] 13 := by
  apply FastRouting.sound _ _ [50,5,320,192] 13 (by decide) (choices 1) [1,8,32,128] r2449 c2449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1196
  · exact u1197
  · exact u1198
  · exact u1199

def b2450 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 21 73 496 480 480 480 480), lower := (rows 51 14 21 73 16 32 64 128 256), losses := [] }

theorem u2450 : Upper (D 0) (R 0) [50,12,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2450
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2451 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 21 200 497 481 481 481 481), lower := (rows 51 14 21 200 16 32 64 128 256), losses := [] }

theorem u2451 : Upper (D 0) (R 0) [50,12,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2451
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2452 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 21 265 240 224 224 224 480), lower := (rows 51 14 21 265 16 32 64 128 256), losses := [] }

theorem u2452 : Upper (D 0) (R 0) [50,12,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2452
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2453 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 21 328 241 225 225 225 481), lower := (rows 51 14 21 328 16 32 64 128 256), losses := [] }

theorem u2453 : Upper (D 0) (R 0) [50,12,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2453
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2454 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 14 52 73 465 481 449 449 449), lower := (rows 51 14 52 73 16 32 64 128 256), losses := [] }

theorem u2454 : Upper (D 0) (R 0) [50,12,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2454
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2455 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 14 52 200 465 481 449 449 449), lower := (rows 51 14 52 200 16 32 64 128 256), losses := [] }

theorem u2455 : Upper (D 0) (R 0) [50,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2455
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2456 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 14 52 265 209 225 193 193 449), lower := (rows 51 14 52 265 16 32 64 128 256), losses := [] }

theorem u2456 : Upper (D 0) (R 0) [50,12,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2456
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2457 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 14 52 328 209 225 193 193 449), lower := (rows 51 14 52 328 16 32 64 128 256), losses := [] }

theorem u2457 : Upper (D 0) (R 0) [50,12,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2457
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2458 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 51 14 69 73 432 432 496 432 432), lower := (rows 51 14 69 73 16 32 64 128 256), losses := [] }

theorem u2458 : Upper (D 0) (R 0) [50,12,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2458
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2459 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 452, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 69 88 433 417 481 417 417), lower := (rows 51 14 69 88 16 32 64 128 256), losses := [] }

theorem u2459 : Upper (D 0) (R 0) [50,12,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2459
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2459
end Delivery.IrregularNine14.P00
