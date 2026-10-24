import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0020
import IrregularNine14P03C0021

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3300 : Route 9 := (fun mask => (mask,id))

def c3300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3300 : Upper (D 3) (R 3) [34,65,129,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,320] 13 (by decide) (choices 1) [1,4,8,16] r3300 c3300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1217
  · exact u1218
  · exact u1219
  · exact u1220

def r3301 : Route 9 := (fun mask => (mask,id))

def c3301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3301 : Upper (D 3) (R 3) [34,65,129,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,257] 13 (by decide) (choices 1) [4,8,16] r3301 c3301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1221
  · exact u1222
  · exact u1223

def r3302 : Route 9 := (fun mask => (mask,id))

def c3302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3302 : Upper (D 3) (R 3) [34,65,129,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,260] 13 (by decide) (choices 1) [1,8,16] r3302 c3302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1224
  · exact u1225
  · exact u1226

def r3303 : Route 9 := (fun mask => (mask,id))

def c3303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3303 : Upper (D 3) (R 3) [34,65,129,192,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,264] 13 (by decide) (choices 1) [1,4,16] r3303 c3303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1227
  · exact u1228
  · exact u1229

def r3304 : Route 9 := (fun mask => (mask,id))

def c3304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3304 : Upper (D 3) (R 3) [34,65,129,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,288] 13 (by decide) (choices 1) [1,4,8,16] r3304 c3304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1230
  · exact u1231
  · exact u1232
  · exact u1233

def b3305 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 140 273 113 113 241 369), lower := (rows 35 67 140 140 273 32 64 128 256), losses := [] }

theorem u3305 : Upper (D 3) (R 3) [34,65,136,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3305
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3306 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 140 304 113 81 209 337), lower := (rows 35 67 140 140 304 32 64 128 256), losses := [] }

theorem u3306 : Upper (D 3) (R 3) [34,65,136,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3306
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3307 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 140 336 49 113 177 305), lower := (rows 35 67 140 140 336 32 64 128 256), losses := [] }

theorem u3307 : Upper (D 3) (R 3) [34,65,136,132,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3307
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3308 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 152 273 101 101 229 357), lower := (rows 35 67 140 152 273 32 64 128 256), losses := [] }

theorem u3308 : Upper (D 3) (R 3) [34,65,136,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3308
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3309 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 152 276 97 97 225 353), lower := (rows 35 67 140 152 276 32 64 128 256), losses := [] }

theorem u3309 : Upper (D 3) (R 3) [34,65,136,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3309
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3310 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 152 304 101 69 197 325), lower := (rows 35 67 140 152 304 32 64 128 256), losses := [] }

theorem u3310 : Upper (D 3) (R 3) [34,65,136,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3310
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3311 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 152 336 37 101 165 293), lower := (rows 35 67 140 152 336 32 64 128 256), losses := [] }

theorem u3311 : Upper (D 3) (R 3) [34,65,136,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3311
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3312 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 168 273 117 85 213 341), lower := (rows 35 67 140 168 273 32 64 128 256), losses := [] }

theorem u3312 : Upper (D 3) (R 3) [34,65,136,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3312
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3313 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 168 276 113 81 209 337), lower := (rows 35 67 140 168 276 32 64 128 256), losses := [] }

theorem u3313 : Upper (D 3) (R 3) [34,65,136,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3313
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3314 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 168 336 53 85 149 277), lower := (rows 35 67 140 168 336 32 64 128 256), losses := [] }

theorem u3314 : Upper (D 3) (R 3) [34,65,136,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3314
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3315 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 200 273 53 117 181 309), lower := (rows 35 67 140 200 273 32 64 128 256), losses := [] }

theorem u3315 : Upper (D 3) (R 3) [34,65,136,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3315
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 200 276 49 113 177 305), lower := (rows 35 67 140 200 276 32 64 128 256), losses := [] }

theorem u3316 : Upper (D 3) (R 3) [34,65,136,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3316
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3317 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 200 304 53 85 149 277), lower := (rows 35 67 140 200 304 32 64 128 256), losses := [] }

theorem u3317 : Upper (D 3) (R 3) [34,65,136,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3317
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3318 : Route 9 := (fun mask => (mask,id))

def c3318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3318 : Upper (D 3) (R 3) [34,65,136,257,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,160] 13 (by decide) (choices 1) [1,4,16,64] r3318 c3318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1234
  · exact u1235
  · exact u1236
  · exact u1237

def r3319 : Route 9 := (fun mask => (mask,id))

def c3319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3319 : Upper (D 3) (R 3) [34,65,136,257,192] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,192] 13 (by decide) (choices 1) [1,4,16] r3319 c3319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1238
  · exact u1239
  · exact u1240

def b3320 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 268 176 113 81 209 337), lower := (rows 35 67 140 268 176 32 64 128 256), losses := [] }

theorem u3320 : Upper (D 3) (R 3) [34,65,136,260,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3320
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3321 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 268 208 49 113 177 305), lower := (rows 35 67 140 268 208 32 64 128 256), losses := [] }

theorem u3321 : Upper (D 3) (R 3) [34,65,136,260,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3321
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3322 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 280 176 101 69 197 325), lower := (rows 35 67 140 280 176 32 64 128 256), losses := [] }

theorem u3322 : Upper (D 3) (R 3) [34,65,136,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3322
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3323 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 280 208 37 101 165 293), lower := (rows 35 67 140 280 208 32 64 128 256), losses := [] }

theorem u3323 : Upper (D 3) (R 3) [34,65,136,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3323
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3324 : Route 9 := (fun mask => (mask,id))

def c3324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3324 : Upper (D 3) (R 3) [34,65,136,288,192] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,192] 13 (by decide) (choices 1) [1,4,16] r3324 c3324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1241
  · exact u1242
  · exact u1243

def r3325 : Route 9 := (fun mask => (mask,id))

def c3325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3325 : Upper (D 3) (R 3) [34,65,136,320,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,160] 13 (by decide) (choices 1) [1,4,16] r3325 c3325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1244
  · exact u1245
  · exact u1246

def r3326 : Route 9 := (fun mask => (mask,id))

def c3326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3326 : Upper (D 3) (R 3) [34,65,160,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,257] 13 (by decide) (choices 1) [1,4,8,16] r3326 c3326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1247
  · exact u1248
  · exact u1249
  · exact u1250

def r3327 : Route 9 := (fun mask => (mask,id))

def c3327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3327 : Upper (D 3) (R 3) [34,65,160,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,260] 13 (by decide) (choices 1) [1,8,16] r3327 c3327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1251
  · exact u1252
  · exact u1253

def r3328 : Route 9 := (fun mask => (mask,id))

def c3328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3328 : Upper (D 3) (R 3) [34,65,160,192,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,264] 13 (by decide) (choices 1) [1,4,16] r3328 c3328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1254
  · exact u1255
  · exact u1256

def b3329 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 152 49 481 449 449 449), lower := (rows 35 70 13 152 49 32 64 128 256), losses := [] }

theorem u3329 : Upper (D 3) (R 3) [34,68,9,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3329
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3330 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 152 81 417 481 417 417), lower := (rows 35 70 13 152 81 32 64 128 256), losses := [] }

theorem u3330 : Upper (D 3) (R 3) [34,68,9,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3330
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3331 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 152 112 417 449 385 385), lower := (rows 35 70 13 152 112 32 64 128 256), losses := [] }

theorem u3331 : Upper (D 3) (R 3) [34,68,9,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3331
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3332 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 13 152 145 353 353 481 353), lower := (rows 35 70 13 152 145 32 64 128 256), losses := [] }

theorem u3332 : Upper (D 3) (R 3) [34,68,9,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3332
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3333 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 152 176 353 321 449 321), lower := (rows 35 70 13 152 176 32 64 128 256), losses := [] }

theorem u3333 : Upper (D 3) (R 3) [34,68,9,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3333
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3334 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 152 208 289 353 417 289), lower := (rows 35 70 13 152 208 32 64 128 256), losses := [] }

theorem u3334 : Upper (D 3) (R 3) [34,68,9,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3334
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3335 : Route 9 := (fun mask => (mask,id))

def c3335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3335 : Upper (D 3) (R 3) [34,68,9,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,257] 13 (by decide) (choices 1) [1,64,128] r3335 c3335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1257
  · exact u1258
  · exact u1259

def b3336 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 152 304 225 193 193 449), lower := (rows 35 70 13 152 304 32 64 128 256), losses := [] }

theorem u3336 : Upper (D 3) (R 3) [34,68,9,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3336
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3337 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 152 336 161 225 161 417), lower := (rows 35 70 13 152 336 32 64 128 256), losses := [] }

theorem u3337 : Upper (D 3) (R 3) [34,68,9,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3337
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3338 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 152 400 97 97 225 353), lower := (rows 35 70 13 152 400 32 64 128 256), losses := [] }

theorem u3338 : Upper (D 3) (R 3) [34,68,9,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3338
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3339 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 280 49 225 193 193 449), lower := (rows 35 70 13 280 49 32 64 128 256), losses := [] }

theorem u3339 : Upper (D 3) (R 3) [34,68,9,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3339
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3340 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 280 81 161 225 161 417), lower := (rows 35 70 13 280 81 32 64 128 256), losses := [] }

theorem u3340 : Upper (D 3) (R 3) [34,68,9,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3340
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3341 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 280 112 161 193 129 385), lower := (rows 35 70 13 280 112 32 64 128 256), losses := [] }

theorem u3341 : Upper (D 3) (R 3) [34,68,9,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3341
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3342 : Route 9 := (fun mask => (mask,id))

def c3342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3342 : Upper (D 3) (R 3) [34,68,9,272,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,129] 13 (by decide) (choices 1) [1,64,128] r3342 c3342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1260
  · exact u1261
  · exact u1262

def b3343 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 280 176 225 193 193 449), lower := (rows 35 70 13 280 176 32 64 128 256), losses := [] }

theorem u3343 : Upper (D 3) (R 3) [34,68,9,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3343
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3344 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 280 208 161 225 161 417), lower := (rows 35 70 13 280 208 32 64 128 256), losses := [] }

theorem u3344 : Upper (D 3) (R 3) [34,68,9,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3344
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3345 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 392 49 241 209 209 465), lower := (rows 35 70 13 392 49 32 64 128 256), losses := [] }

theorem u3345 : Upper (D 3) (R 3) [34,68,9,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3345
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3346 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 392 81 177 241 177 433), lower := (rows 35 70 13 392 81 32 64 128 256), losses := [] }

theorem u3346 : Upper (D 3) (R 3) [34,68,9,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3346
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3347 : Route 9 := (fun mask => (mask,id))

def c3347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3347 : Upper (D 3) (R 3) [34,68,9,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,96] 13 (by decide) (choices 1) [1,16,128] r3347 c3347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1263
  · exact u1264
  · exact u1265

def r3348 : Route 9 := (fun mask => (mask,id))

def c3348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3348 : Upper (D 3) (R 3) [34,68,9,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,129] 13 (by decide) (choices 1) [1,16,64] r3348 c3348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1266
  · exact u1267
  · exact u1268

def r3349 : Route 9 := (fun mask => (mask,id))

def c3349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3349 : Upper (D 3) (R 3) [34,68,9,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,160] 13 (by decide) (choices 1) [1,16,64] r3349 c3349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1269
  · exact u1270
  · exact u1271

def r3350 : Route 9 := (fun mask => (mask,id))

def c3350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3350 : Upper (D 3) (R 3) [34,68,9,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,192] 13 (by decide) (choices 1) [1,16] r3350 c3350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1272
  · exact u1273

def b3351 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 28 41 145 481 449 449 449), lower := (rows 35 70 28 41 145 32 64 128 256), losses := [] }

theorem u3351 : Upper (D 3) (R 3) [34,68,24,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3351
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3352 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 28 41 273 225 193 193 449), lower := (rows 35 70 28 41 273 32 64 128 256), losses := [] }

theorem u3352 : Upper (D 3) (R 3) [34,68,24,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3352
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3353 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 28 41 400 225 193 193 449), lower := (rows 35 70 28 41 400 32 64 128 256), losses := [] }

theorem u3353 : Upper (D 3) (R 3) [34,68,24,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3353
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3354 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 145 417 481 417 417), lower := (rows 35 70 28 73 145 32 64 128 256), losses := [] }

theorem u3354 : Upper (D 3) (R 3) [34,68,24,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3354
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3355 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 273 161 225 161 417), lower := (rows 35 70 28 73 273 32 64 128 256), losses := [] }

theorem u3355 : Upper (D 3) (R 3) [34,68,24,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3355
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3356 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 400 161 225 161 417), lower := (rows 35 70 28 73 400 32 64 128 256), losses := [] }

theorem u3356 : Upper (D 3) (R 3) [34,68,24,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3356
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3357 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 145 417 449 385 385), lower := (rows 35 70 28 104 145 32 64 128 256), losses := [] }

theorem u3357 : Upper (D 3) (R 3) [34,68,24,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3357
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3358 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 273 161 193 129 385), lower := (rows 35 70 28 104 273 32 64 128 256), losses := [] }

theorem u3358 : Upper (D 3) (R 3) [34,68,24,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3358
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3359 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 400 161 193 129 385), lower := (rows 35 70 28 104 400 32 64 128 256), losses := [] }

theorem u3359 : Upper (D 3) (R 3) [34,68,24,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3359
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3359
end Delivery.IrregularNine14.P03
