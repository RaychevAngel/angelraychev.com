import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0020
import IrregularNine14P06C0021

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10320 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 265 112 34 84 212 340), lower := (rows 7 42 133 265 112 34 64 128 256), losses := [] }

theorem u10320 : Upper (D 6) (R 6) [6,40,129,257,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10320
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10321 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 42 133 265 112 36 82 210 338), lower := (rows 7 42 133 265 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 31 37 75 139 267), good := (rows 502 506 500 506 112 52 64 128 256) }] }

theorem u10321 : Upper (D 6) (R 6) [6,40,129,257,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10321
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10322 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 265 112 48 70 198 326), lower := (rows 7 42 133 265 112 48 64 128 256), losses := [] }

theorem u10322 : Upper (D 6) (R 6) [6,40,129,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10322
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10323 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 133 265 112 96 86 150 278), lower := (rows 7 42 133 265 112 96 64 128 256), losses := [] }

theorem u10323 : Upper (D 6) (R 6) [6,40,129,257,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10323
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10324 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 266 52 33 80 208 336), lower := (rows 7 42 133 266 52 33 64 128 256), losses := [] }

theorem u10324 : Upper (D 6) (R 6) [6,40,129,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10324
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10325 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 266 52 48 65 193 321), lower := (rows 7 42 133 266 52 48 64 128 256), losses := [] }

theorem u10325 : Upper (D 6) (R 6) [6,40,129,258,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10325
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10326 : Route 9 := (fun mask => (mask,id))

def c10326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10326 : Upper (D 6) (R 6) [6,40,129,258,36,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,36,64] 13 (by decide) (choices 1) [1,16] r10326 c10326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1231
  · exact u1232

def b10327 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 133 266 81 36 112 240 368), lower := (rows 7 42 133 266 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 80 144 272), good := (rows 38 42 164 266 506 36 64 128 256) }] }

theorem u10327 : Upper (D 6) (R 6) [6,40,129,258,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10327
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10328 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 133 266 81 48 100 228 356), lower := (rows 7 42 133 266 81 48 64 128 256), losses := [] }

theorem u10328 : Upper (D 6) (R 6) [6,40,129,258,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10328
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10329 : Route 9 := (fun mask => (mask,id))

def c10329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10329 : Upper (D 6) (R 6) [6,40,129,258,65,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,65,64] 13 (by decide) (choices 1) [4,16,32] r10329 c10329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1233
  · exact u1234
  · exact u1235

def b10330 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 133 266 84 33 112 240 368), lower := (rows 7 42 133 266 84 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 37 80 144 272), good := (rows 35 42 161 266 506 33 64 128 256) }] }

theorem u10330 : Upper (D 6) (R 6) [6,40,129,258,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10330
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10331 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 133 266 84 48 97 225 353), lower := (rows 7 42 133 266 84 48 64 128 256), losses := [] }

theorem u10331 : Upper (D 6) (R 6) [6,40,129,258,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10331
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10332 : Route 9 := (fun mask => (mask,id))

def c10332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10332 : Upper (D 6) (R 6) [6,40,129,258,68,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,68,64] 13 (by decide) (choices 1) [1,16,32] r10332 c10332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1236
  · exact u1237
  · exact u1238

def r10333 : Route 9 := (fun mask => (mask,id))

def c10333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10333 : Upper (D 6) (R 6) [6,40,129,258,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,96,1] 13 (by decide) (choices 1) [4,16] r10333 c10333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1239
  · exact u1240

def r10334 : Route 9 := (fun mask => (mask,id))

def c10334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10334 : Upper (D 6) (R 6) [6,40,129,258,96,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,96,4] 13 (by decide) (choices 1) [1,16] r10334 c10334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1241
  · exact u1242

def b10335 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 266 112 48 69 197 325), lower := (rows 7 42 133 266 112 48 64 128 256), losses := [] }

theorem u10335 : Upper (D 6) (R 6) [6,40,129,258,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10335
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10336 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 133 266 112 96 85 149 277), lower := (rows 7 42 133 266 112 96 64 128 256), losses := [] }

theorem u10336 : Upper (D 6) (R 6) [6,40,129,258,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10336
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10337 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 42 133 268 49 34 80 208 336), lower := (rows 7 42 133 268 49 34 64 128 256), losses := [] }

theorem u10337 : Upper (D 6) (R 6) [6,40,129,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10337
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10338 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 268 49 48 66 194 322), lower := (rows 7 42 133 268 49 48 64 128 256), losses := [] }

theorem u10338 : Upper (D 6) (R 6) [6,40,129,260,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10338
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10339 : Route 9 := (fun mask => (mask,id))

def c10339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10339 : Upper (D 6) (R 6) [6,40,129,260,33,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,260,33,64] 13 (by decide) (choices 1) [2,16] r10339 c10339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1243
  · exact u1244

def b10340 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 133 268 81 34 112 240 368), lower := (rows 7 42 133 268 81 34 64 128 256), losses := [] }

theorem u10340 : Upper (D 6) (R 6) [6,40,129,260,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10340
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10341 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(4,2)], upper := (rows 7 42 133 268 81 48 98 226 354), lower := (rows 7 42 133 268 81 48 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 9 16 48 114 178 306), good := (rows 462 490 140 268 506 498 64 128 256) }] }

theorem u10341 : Upper (D 6) (R 6) [6,40,129,260,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10341
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10342 : Route 9 := (fun mask => (mask,id))

def c10342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10342 : Upper (D 6) (R 6) [6,40,129,260,65,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,260,65,64] 13 (by decide) (choices 1) [2,16,32] r10342 c10342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1245
  · exact u1246
  · exact u1247

def b10343 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 7 42 133 268 82 33 112 240 368), lower := (rows 7 42 133 268 82 33 64 128 256), losses := [] }

theorem u10343 : Upper (D 6) (R 6) [6,40,129,260,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10343
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10344 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 42 133 268 82 48 97 225 353), lower := (rows 7 42 133 268 82 48 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 63 69 133 261), good := (rows 499 58 497 506 114 48 64 128 256) }] }

theorem u10344 : Upper (D 6) (R 6) [6,40,129,260,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10344
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10345 : Route 9 := (fun mask => (mask,id))

def c10345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10345 : Upper (D 6) (R 6) [6,40,129,260,66,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,260,66,64] 13 (by decide) (choices 1) [1,16,32] r10345 c10345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1248
  · exact u1249
  · exact u1250

def b10346 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 7 42 133 268 112 33 82 210 338), lower := (rows 7 42 133 268 112 33 64 128 256), losses := [] }

theorem u10346 : Upper (D 6) (R 6) [6,40,129,260,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10346
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10347 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 133 268 112 34 81 209 337), lower := (rows 7 42 133 268 112 34 64 128 256), losses := [] }

theorem u10347 : Upper (D 6) (R 6) [6,40,129,260,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10347
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10348 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 268 112 48 67 195 323), lower := (rows 7 42 133 268 112 48 64 128 256), losses := [] }

theorem u10348 : Upper (D 6) (R 6) [6,40,129,260,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10348
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10349 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 133 268 112 96 83 147 275), lower := (rows 7 42 133 268 112 96 64 128 256), losses := [] }

theorem u10349 : Upper (D 6) (R 6) [6,40,129,260,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10349
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10350 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 280 52 33 66 194 322), lower := (rows 7 42 133 280 52 33 64 128 256), losses := [] }

theorem u10350 : Upper (D 6) (R 6) [6,40,129,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10350
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10351 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 280 52 34 65 193 321), lower := (rows 7 42 133 280 52 34 64 128 256), losses := [] }

theorem u10351 : Upper (D 6) (R 6) [6,40,129,272,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10351
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10352 : Route 9 := (fun mask => (mask,id))

def c10352 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10352 : Upper (D 6) (R 6) [6,40,129,272,36,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,36,64] 13 (by decide) (choices 1) [1,2] r10352 c10352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1251
  · exact u1252

def b10353 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 280 81 34 100 228 356), lower := (rows 7 42 133 280 81 34 64 128 256), losses := [] }

theorem u10353 : Upper (D 6) (R 6) [6,40,129,272,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10353
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10354 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 42 133 280 81 36 98 226 354), lower := (rows 7 42 133 280 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 83 147 275), good := (rows 486 490 484 474 506 36 64 128 256) },{ target := 2, region := (rows 1 2 0 9 17 32 66 130 258), good := (rows 475 490 153 280 89 32 64 128 256) }] }

theorem u10354 : Upper (D 6) (R 6) [6,40,129,272,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10354
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10355 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 7 42 133 280 81 96 102 166 294), lower := (rows 7 42 133 280 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 26 4 24 16 117 65 129 257), good := (rows 486 42 484 314 506 96 96 128 256) }] }

theorem u10355 : Upper (D 6) (R 6) [6,40,129,272,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10355
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10356 : Route 9 := (fun mask => (mask,id))

def c10356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10356 : Upper (D 6) (R 6) [6,40,129,272,66,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,66,1] 13 (by decide) (choices 1) [4,32] r10356 c10356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1253
  · exact u1254

def r10357 : Route 9 := (fun mask => (mask,id))

def c10357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10357 : Upper (D 6) (R 6) [6,40,129,272,66,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,66,4] 13 (by decide) (choices 1) [1,32] r10357 c10357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1255
  · exact u1256

def b10358 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 7 42 133 280 82 96 101 165 293), lower := (rows 7 42 133 280 82 96 64 128 256), losses := [] }

theorem u10358 : Upper (D 6) (R 6) [6,40,129,272,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10358
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10359 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 133 280 84 33 98 226 354), lower := (rows 7 42 133 280 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 41 17 32 98 162 290), good := (rows 478 490 156 280 84 506 64 128 256) }] }

theorem u10359 : Upper (D 6) (R 6) [6,40,129,272,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10359
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10360 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 280 84 34 97 225 353), lower := (rows 7 42 133 280 84 34 64 128 256), losses := [] }

theorem u10360 : Upper (D 6) (R 6) [6,40,129,272,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10360
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10361 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 7 42 133 280 84 96 99 163 291), lower := (rows 7 42 133 280 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 112 64 128 256), good := (rows 6 42 132 314 116 96 96 128 256) }] }

theorem u10361 : Upper (D 6) (R 6) [6,40,129,272,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10361
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10362 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 133 280 112 33 70 198 326), lower := (rows 7 42 133 280 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 50 4 40 48 32 65 129 257), good := (rows 454 58 452 282 122 506 64 128 256) }] }

theorem u10362 : Upper (D 6) (R 6) [6,40,129,272,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10362
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10363 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 280 112 34 69 197 325), lower := (rows 7 42 133 280 112 34 64 128 256), losses := [] }

theorem u10363 : Upper (D 6) (R 6) [6,40,129,272,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10363
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10364 : Route 9 := (fun mask => (mask,id))

def c10364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10364 : Upper (D 6) (R 6) [6,40,129,272,96,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,96,4] 13 (by decide) (choices 1) [1,2] r10364 c10364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1257
  · exact u1258

def b10365 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 133 280 112 96 71 135 263), lower := (rows 7 42 133 280 112 96 64 128 256), losses := [] }

theorem u10365 : Upper (D 6) (R 6) [6,40,129,272,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10365
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10366 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 42 133 328 49 34 84 212 340), lower := (rows 7 42 133 328 49 34 64 128 256), losses := [] }

theorem u10366 : Upper (D 6) (R 6) [6,40,129,320,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10366
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10367 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 328 49 36 82 210 338), lower := (rows 7 42 133 328 49 36 64 128 256), losses := [] }

theorem u10367 : Upper (D 6) (R 6) [6,40,129,320,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10367
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10368 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 42 133 328 49 48 70 198 326), lower := (rows 7 42 133 328 49 48 64 128 256), losses := [] }

theorem u10368 : Upper (D 6) (R 6) [6,40,129,320,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10368
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10369 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 149, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 328 49 96 86 150 278), lower := (rows 7 42 133 328 49 96 64 128 256), losses := [] }

theorem u10369 : Upper (D 6) (R 6) [6,40,129,320,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10369
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10370 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 328 52 33 82 210 338), lower := (rows 7 42 133 328 52 33 64 128 256), losses := [] }

theorem u10370 : Upper (D 6) (R 6) [6,40,129,320,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10370
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10371 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 328 52 34 81 209 337), lower := (rows 7 42 133 328 52 34 64 128 256), losses := [] }

theorem u10371 : Upper (D 6) (R 6) [6,40,129,320,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10371
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10372 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 328 52 48 67 195 323), lower := (rows 7 42 133 328 52 48 64 128 256), losses := [] }

theorem u10372 : Upper (D 6) (R 6) [6,40,129,320,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10372
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10373 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 149, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 328 52 96 83 147 275), lower := (rows 7 42 133 328 52 96 64 128 256), losses := [] }

theorem u10373 : Upper (D 6) (R 6) [6,40,129,320,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10373
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10374 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 328 81 34 116 180 308), lower := (rows 7 42 133 328 81 34 64 128 256), losses := [] }

theorem u10374 : Upper (D 6) (R 6) [6,40,129,320,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10374
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10375 : Route 9 := (fun mask => (mask,id))

def c10375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10375 : Upper (D 6) (R 6) [6,40,129,320,65,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,65,4] 13 (by decide) (choices 1) [2,16,32] r10375 c10375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1259
  · exact u1260
  · exact u1261

def b10376 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 133 328 81 48 102 166 294), lower := (rows 7 42 133 328 81 48 64 128 256), losses := [] }

theorem u10376 : Upper (D 6) (R 6) [6,40,129,320,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10376
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10377 : Route 9 := (fun mask => (mask,id))

def c10377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10377 : Upper (D 6) (R 6) [6,40,129,320,66,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,66,1] 13 (by decide) (choices 1) [4,16,32] r10377 c10377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1262
  · exact u1263
  · exact u1264

def r10378 : Route 9 := (fun mask => (mask,id))

def c10378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10378 : Upper (D 6) (R 6) [6,40,129,320,66,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,66,4] 13 (by decide) (choices 1) [1,16,32] r10378 c10378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1265
  · exact u1266
  · exact u1267

def b10379 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 328 82 48 101 165 293), lower := (rows 7 42 133 328 82 48 64 128 256), losses := [] }

theorem u10379 : Upper (D 6) (R 6) [6,40,129,320,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10379
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10379
end Delivery.IrregularNine14.P06
