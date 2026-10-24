import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0017
import IrregularNine14P00C0018

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2340 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 328 177 177 241 177 433), lower := (rows 23 35 76 328 16 32 64 128 256), losses := [] }

theorem u2340 : Upper (D 0) (R 0) [22,33,72,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2340
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2341 : Route 9 := (fun mask => (mask,id))

def c2341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2341 : Upper (D 0) (R 0) [22,33,72,384] 13 := by
  apply FastRouting.sound _ _ [22,33,72,384] 13 (by decide) (choices 1) [1,32,64,128] r2341 c2341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1052
  · exact u1053
  · exact u1054
  · exact u1055

def b2342 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 196 25 504 488 488 488 488), lower := (rows 23 35 196 25 16 32 64 128 256), losses := [] }

theorem u2342 : Upper (D 0) (R 0) [22,33,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2342
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 196 41 472 504 472 472 472), lower := (rows 23 35 196 41 16 32 64 128 256), losses := [] }

theorem u2343 : Upper (D 0) (R 0) [22,33,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2343
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2344 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u2344 : Upper (D 0) (R 0) [22,33,192,48] 13 := by
  apply FastRouting.sound _ _ [22,33,192,48] 13 (by decide) (choices 1) [1,8,64,256] r2344 c2344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1056
  · exact u1057
  · exact u1058
  · exact u1059

def b2345 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 196 73 440 440 504 440 440), lower := (rows 23 35 196 73 16 32 64 128 256), losses := [] }

theorem u2345 : Upper (D 0) (R 0) [22,33,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2345
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2346 : Route 9 := (fun mask => (mask,id))

def c2346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u2346 : Upper (D 0) (R 0) [22,33,192,80] 13 := by
  apply FastRouting.sound _ _ [22,33,192,80] 13 (by decide) (choices 1) [1,8,32,128,256] r2346 c2346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1060
  · exact u1061
  · exact u1062
  · exact u1063
  · exact u1064

def r2347 : Route 9 := (fun mask => (mask,id))

def c2347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u2347 : Upper (D 0) (R 0) [22,33,192,96] 13 := by
  apply FastRouting.sound _ _ [22,33,192,96] 13 (by decide) (choices 1) [1,8,128,256] r2347 c2347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1065
  · exact u1066
  · exact u1067
  · exact u1068

def b2348 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 23 35 196 200 313 313 377 441 313), lower := (rows 23 35 196 200 16 32 64 128 256), losses := [] }

theorem u2348 : Upper (D 0) (R 0) [22,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2348
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2349 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 196 265 248 248 248 248 504), lower := (rows 23 35 196 265 16 32 64 128 256), losses := [] }

theorem u2349 : Upper (D 0) (R 0) [22,33,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2349
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2350 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2350 : Upper (D 0) (R 0) [22,33,192,272] 13 := by
  apply FastRouting.sound _ _ [22,33,192,272] 13 (by decide) (choices 1) [1,8,32,64] r2350 c2350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1069
  · exact u1070
  · exact u1071
  · exact u1072

def r2351 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2351 : Upper (D 0) (R 0) [22,33,192,288] 13 := by
  apply FastRouting.sound _ _ [22,33,192,288] 13 (by decide) (choices 1) [1,8,64] r2351 c2351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1073
  · exact u1074
  · exact u1075

def r2352 : Route 9 := (fun mask => (mask,id))

def c2352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2352 : Upper (D 0) (R 0) [22,33,192,320] 13 := by
  apply FastRouting.sound _ _ [22,33,192,320] 13 (by decide) (choices 1) [1,8,32,128] r2352 c2352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1076
  · exact u1077
  · exact u1078
  · exact u1079

def b2353 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 268 25 240 224 224 224 480), lower := (rows 23 35 268 25 16 32 64 128 256), losses := [] }

theorem u2353 : Upper (D 0) (R 0) [22,33,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2353
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2354 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 268 41 208 240 208 208 464), lower := (rows 23 35 268 41 16 32 64 128 256), losses := [] }

theorem u2354 : Upper (D 0) (R 0) [22,33,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2354
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2355 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 268 56 209 225 193 193 449), lower := (rows 23 35 268 56 16 32 64 128 256), losses := [] }

theorem u2355 : Upper (D 0) (R 0) [22,33,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2355
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2356 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 268 73 240 240 240 240 496), lower := (rows 23 35 268 73 16 32 64 128 256), losses := [] }

theorem u2356 : Upper (D 0) (R 0) [22,33,264,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2356
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2357 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 268 88 241 225 225 225 481), lower := (rows 23 35 268 88 16 32 64 128 256), losses := [] }

theorem u2357 : Upper (D 0) (R 0) [22,33,264,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2357
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2358 : Route 9 := (fun mask => (mask,id))

def c2358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2358 : Upper (D 0) (R 0) [22,33,264,96] 13 := by
  apply FastRouting.sound _ _ [22,33,264,96] 13 (by decide) (choices 1) [1,64,128] r2358 c2358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1080
  · exact u1081
  · exact u1082

def r2359 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2359 : Upper (D 0) (R 0) [22,33,264,192] 13 := by
  apply FastRouting.sound _ _ [22,33,264,192] 13 (by decide) (choices 1) [1,32,64] r2359 c2359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1083
  · exact u1084
  · exact u1085

def b2360 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 324 25 248 232 232 232 488), lower := (rows 23 35 324 25 16 32 64 128 256), losses := [] }

theorem u2360 : Upper (D 0) (R 0) [22,33,320,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2360
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2361 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 324 41 216 248 216 216 472), lower := (rows 23 35 324 41 16 32 64 128 256), losses := [] }

theorem u2361 : Upper (D 0) (R 0) [22,33,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2361
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2362 : Route 9 := (fun mask => (mask,id))

def c2362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2362 : Upper (D 0) (R 0) [22,33,320,48] 13 := by
  apply FastRouting.sound _ _ [22,33,320,48] 13 (by decide) (choices 1) [1,8,64,128] r2362 c2362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1086
  · exact u1087
  · exact u1088
  · exact u1089

def b2363 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 324 73 184 184 248 184 440), lower := (rows 23 35 324 73 16 32 64 128 256), losses := [] }

theorem u2363 : Upper (D 0) (R 0) [22,33,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2363
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2364 : Route 9 := (fun mask => (mask,id))

def c2364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2364 : Upper (D 0) (R 0) [22,33,320,80] 13 := by
  apply FastRouting.sound _ _ [22,33,320,80] 13 (by decide) (choices 1) [1,8,32,128] r2364 c2364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1090
  · exact u1091
  · exact u1092
  · exact u1093

def r2365 : Route 9 := (fun mask => (mask,id))

def c2365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2365 : Upper (D 0) (R 0) [22,33,320,96] 13 := by
  apply FastRouting.sound _ _ [22,33,320,96] 13 (by decide) (choices 1) [1,8,128] r2365 c2365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1094
  · exact u1095
  · exact u1096

def b2366 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 324 137 248 248 248 248 504), lower := (rows 23 35 324 137 16 32 64 128 256), losses := [] }

theorem u2366 : Upper (D 0) (R 0) [22,33,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2366
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2367 : Route 9 := (fun mask => (mask,id))

def c2367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2367 : Upper (D 0) (R 0) [22,33,320,144] 13 := by
  apply FastRouting.sound _ _ [22,33,320,144] 13 (by decide) (choices 1) [1,8,32,64,128] r2367 c2367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1097
  · exact u1098
  · exact u1099
  · exact u1100
  · exact u1101

def r2368 : Route 9 := (fun mask => (mask,id))

def c2368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2368 : Upper (D 0) (R 0) [22,33,320,160] 13 := by
  apply FastRouting.sound _ _ [22,33,320,160] 13 (by decide) (choices 1) [1,8,64,128] r2368 c2368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1102
  · exact u1103
  · exact u1104
  · exact u1105

def r2369 : Route 9 := (fun mask => (mask,id))

def c2369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2369 : Upper (D 0) (R 0) [22,33,320,192] 13 := by
  apply FastRouting.sound _ _ [22,33,320,192] 13 (by decide) (choices 1) [1,8,32,128] r2369 c2369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1106
  · exact u1107
  · exact u1108
  · exact u1109

def b2370 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 196 25 497 481 481 481 481), lower := (rows 23 42 196 25 16 32 64 128 256), losses := [] }

theorem u2370 : Upper (D 0) (R 0) [22,40,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2370
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2371 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 196 41 465 497 465 465 465), lower := (rows 23 42 196 41 16 32 64 128 256), losses := [] }

theorem u2371 : Upper (D 0) (R 0) [22,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2371
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2372 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 196 56 465 481 449 449 449), lower := (rows 23 42 196 56 16 32 64 128 256), losses := [] }

theorem u2372 : Upper (D 0) (R 0) [22,40,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2372
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 196 73 433 433 497 433 433), lower := (rows 23 42 196 73 16 32 64 128 256), losses := [] }

theorem u2373 : Upper (D 0) (R 0) [22,40,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2373
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2374 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 196 88 433 417 481 417 417), lower := (rows 23 42 196 88 16 32 64 128 256), losses := [] }

theorem u2374 : Upper (D 0) (R 0) [22,40,192,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2374
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2375 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 196 104 401 433 465 401 401), lower := (rows 23 42 196 104 16 32 64 128 256), losses := [] }

theorem u2375 : Upper (D 0) (R 0) [22,40,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2375
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2376 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 23 42 196 200 305 305 369 433 305), lower := (rows 23 42 196 200 16 32 64 128 256), losses := [] }

theorem u2376 : Upper (D 0) (R 0) [22,40,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2376
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2377 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2377 : Upper (D 0) (R 0) [22,40,192,257] 13 := by
  apply FastRouting.sound _ _ [22,40,192,257] 13 (by decide) (choices 1) [1,32,64] r2377 c2377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1110
  · exact u1111
  · exact u1112

def b2378 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 196 280 241 225 225 225 481), lower := (rows 23 42 196 280 16 32 64 128 256), losses := [] }

theorem u2378 : Upper (D 0) (R 0) [22,40,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2378
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2379 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 196 296 209 241 209 209 465), lower := (rows 23 42 196 296 16 32 64 128 256), losses := [] }

theorem u2379 : Upper (D 0) (R 0) [22,40,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2379
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2380 : Route 9 := (fun mask => (mask,id))

def c2380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2380 : Upper (D 0) (R 0) [22,40,192,320] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320] 13 (by decide) (choices 1) [1,32,128] r2380 c2380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1113
  · exact u1114
  · exact u1115

def b2381 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 261 25 240 224 224 224 480), lower := (rows 23 42 261 25 16 32 64 128 256), losses := [] }

theorem u2381 : Upper (D 0) (R 0) [22,40,257,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2381
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2382 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 261 41 208 240 208 208 464), lower := (rows 23 42 261 41 16 32 64 128 256), losses := [] }

theorem u2382 : Upper (D 0) (R 0) [22,40,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2382
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 261 56 209 225 193 193 449), lower := (rows 23 42 261 56 16 32 64 128 256), losses := [] }

theorem u2383 : Upper (D 0) (R 0) [22,40,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2383
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 261 73 240 240 240 240 496), lower := (rows 23 42 261 73 16 32 64 128 256), losses := [] }

theorem u2384 : Upper (D 0) (R 0) [22,40,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2384
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 261 88 241 225 225 225 481), lower := (rows 23 42 261 88 16 32 64 128 256), losses := [] }

theorem u2385 : Upper (D 0) (R 0) [22,40,257,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2385
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 261 104 209 241 209 209 465), lower := (rows 23 42 261 104 16 32 64 128 256), losses := [] }

theorem u2386 : Upper (D 0) (R 0) [22,40,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2386
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2387 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2387 : Upper (D 0) (R 0) [22,40,257,192] 13 := by
  apply FastRouting.sound _ _ [22,40,257,192] 13 (by decide) (choices 1) [1,32,64] r2387 c2387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1116
  · exact u1117
  · exact u1118

def b2388 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 324 25 241 225 225 225 481), lower := (rows 23 42 324 25 16 32 64 128 256), losses := [] }

theorem u2388 : Upper (D 0) (R 0) [22,40,320,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2388
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 324 41 209 241 209 209 465), lower := (rows 23 42 324 41 16 32 64 128 256), losses := [] }

theorem u2389 : Upper (D 0) (R 0) [22,40,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2389
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 324 56 209 225 193 193 449), lower := (rows 23 42 324 56 16 32 64 128 256), losses := [] }

theorem u2390 : Upper (D 0) (R 0) [22,40,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2390
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2391 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 324 73 177 177 241 177 433), lower := (rows 23 42 324 73 16 32 64 128 256), losses := [] }

theorem u2391 : Upper (D 0) (R 0) [22,40,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2391
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2392 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 324 88 177 161 225 161 417), lower := (rows 23 42 324 88 16 32 64 128 256), losses := [] }

theorem u2392 : Upper (D 0) (R 0) [22,40,320,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2392
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2393 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 324 104 145 177 209 145 401), lower := (rows 23 42 324 104 16 32 64 128 256), losses := [] }

theorem u2393 : Upper (D 0) (R 0) [22,40,320,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2393
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2394 : Route 9 := (fun mask => (mask,id))

def c2394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2394 : Upper (D 0) (R 0) [22,40,320,129] 13 := by
  apply FastRouting.sound _ _ [22,40,320,129] 13 (by decide) (choices 1) [1,32,64,128] r2394 c2394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1119
  · exact u1120
  · exact u1121
  · exact u1122

def b2395 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 324 152 241 225 225 225 481), lower := (rows 23 42 324 152 16 32 64 128 256), losses := [] }

theorem u2395 : Upper (D 0) (R 0) [22,40,320,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2395
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2396 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 324 168 209 241 209 209 465), lower := (rows 23 42 324 168 16 32 64 128 256), losses := [] }

theorem u2396 : Upper (D 0) (R 0) [22,40,320,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2396
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2397 : Route 9 := (fun mask => (mask,id))

def c2397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2397 : Upper (D 0) (R 0) [22,40,320,192] 13 := by
  apply FastRouting.sound _ _ [22,40,320,192] 13 (by decide) (choices 1) [1,32,128] r2397 c2397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1123
  · exact u1124
  · exact u1125

def b2398 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 261 25 248 232 232 232 488), lower := (rows 23 98 261 25 16 32 64 128 256), losses := [] }

theorem u2398 : Upper (D 0) (R 0) [22,96,257,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2398
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2399 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 23 98 261 41 216 248 216 216 472), lower := (rows 23 98 261 41 16 32 64 128 256), losses := [] }

theorem u2399 : Upper (D 0) (R 0) [22,96,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2399
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2399
end Delivery.IrregularNine14.P00
