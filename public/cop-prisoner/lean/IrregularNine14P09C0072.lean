import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0020
import IrregularNine14P09C0021

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4320 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 56 208 33 448 384 384), lower := (rows 35 70 13 56 208 33 64 128 256), losses := [] }

theorem u4320 : Upper (D 9) (R 9) [34,68,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4320 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4321 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 13 56 208 160 321 385 257), lower := (rows 35 70 13 56 208 160 64 128 256), losses := [] }

theorem u4321 : Upper (D 9) (R 9) [34,68,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4321 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4322 : Route 9 := (fun mask => (mask,id))

def c4322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4322 : Upper (D 9) (R 9) [34,68,9,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,192,256] 13 (by decide) (choices 1) [1,128,256] r4322 c4322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1248
  · exact u1249
  · exact u1250

def b4323 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 56 400 33 448 448 448), lower := (rows 35 70 13 56 400 33 64 128 256), losses := [] }

theorem u4323 : Upper (D 9) (R 9) [34,68,9,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4323 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4324 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 56 400 96 449 385 385), lower := (rows 35 70 13 56 400 96 64 128 256), losses := [] }

theorem u4324 : Upper (D 9) (R 9) [34,68,9,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4324 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4325 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 35 70 13 56 400 160 321 449 321), lower := (rows 35 70 13 56 400 160 64 128 256), losses := [] }

theorem u4325 : Upper (D 9) (R 9) [34,68,9,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4325 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4326 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(1,0),(1,7),(3,0),(4,6)], upper := (rows 35 70 13 88 145 160 352 416 288), lower := (rows 35 70 13 88 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 30 20 24 16 32 97 0 289), good := (rows 355 70 335 94 351 352 64 0 256) }] }

theorem u4326 : Upper (D 9) (R 9) [34,68,9,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4326 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4327 : Route 9 := (fun mask => (mask,id))

def c4327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u4327 : Upper (D 9) (R 9) [34,68,9,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,129,256] 13 (by decide) (choices 1) [32,128,256] r4327 c4327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1251
  · exact u1252
  · exact u1253

def b4328 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 88 176 33 448 384 384), lower := (rows 35 70 13 88 176 33 64 128 256), losses := [] }

theorem u4328 : Upper (D 9) (R 9) [34,68,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4328 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4329 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 70 13 88 176 160 321 385 257), lower := (rows 35 70 13 88 176 160 64 128 256), losses := [] }

theorem u4329 : Upper (D 9) (R 9) [34,68,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4329 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4330 : Route 9 := (fun mask => (mask,id))

def c4330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4330 : Upper (D 9) (R 9) [34,68,9,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,160,256] 13 (by decide) (choices 1) [1,128,256] r4330 c4330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1254
  · exact u1255
  · exact u1256

def b4331 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 88 400 33 480 416 416), lower := (rows 35 70 13 88 400 33 64 128 256), losses := [] }

theorem u4331 : Upper (D 9) (R 9) [34,68,9,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4331 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4332 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(1,7),(1,8),(4,6)], upper := (rows 35 70 13 88 400 160 353 417 289), lower := (rows 35 70 13 88 400 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 32 65 0 257), good := (rows 355 70 335 88 272 32 64 0 256) },{ target := 8, region := (rows 9 10 12 8 16 176 64 128 0), good := (rows 35 70 15 127 176 160 64 160 0) }] }

theorem u4332 : Upper (D 9) (R 9) [34,68,9,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4332 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4333 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(4,7),(4,8)], upper := (rows 35 70 13 152 112 33 448 384 384), lower := (rows 35 70 13 152 112 33 64 128 256), losses := [] }

theorem u4333 : Upper (D 9) (R 9) [34,68,9,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4333 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4334 : Route 9 := (fun mask => (mask,id))

def c4334 : Nat → Fin 9 := (fun mask => match mask with | 1 => 8 | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4334 : Upper (D 9) (R 9) [34,68,9,144,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,96,128] 13 (by decide) (choices 1) [256] r4334 c4334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u1257

def r4335 : Route 9 := (fun mask => (mask,id))

def c4335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4335 : Upper (D 9) (R 9) [34,68,9,144,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,96,256] 13 (by decide) (choices 1) [1,128,256] r4335 c4335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1258
  · exact u1259
  · exact u1260

def b4336 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 152 273 96 480 416 416), lower := (rows 35 70 13 152 273 96 64 128 256), losses := [] }

theorem u4336 : Upper (D 9) (R 9) [34,68,9,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4336 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4337 : Route 9 := (fun mask => (mask,id))

def c4337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4337 : Upper (D 9) (R 9) [34,68,9,144,257,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,257,128] 13 (by decide) (choices 1) [32,256] r4337 c4337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1261
  · exact u1262

def b4338 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 232, targets := 1 }], pairs := [(1,0),(1,8),(2,8),(3,0),(3,8)], upper := (rows 35 70 13 152 273 288 224 224 480), lower := (rows 35 70 13 152 273 288 64 128 256), losses := [{ target := 8, region := (rows 1 22 20 24 16 32 97 161 0), good := (rows 227 70 207 158 223 224 64 128 0) }] }

theorem u4338 : Upper (D 9) (R 9) [34,68,9,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4338 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4339 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 13 152 304 33 448 448 448), lower := (rows 35 70 13 152 304 33 64 128 256), losses := [] }

theorem u4339 : Upper (D 9) (R 9) [34,68,9,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4339 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4340 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 152 304 96 449 385 385), lower := (rows 35 70 13 152 304 96 64 128 256), losses := [] }

theorem u4340 : Upper (D 9) (R 9) [34,68,9,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4340 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4341 : Route 9 := (fun mask => (mask,id))

def c4341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4341 : Upper (D 9) (R 9) [34,68,9,144,288,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,288,128] 13 (by decide) (choices 1) [1,256] r4341 c4341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1263
  · exact u1264

def b4342 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 13 152 304 288 193 193 449), lower := (rows 35 70 13 152 304 288 64 128 256), losses := [] }

theorem u4342 : Upper (D 9) (R 9) [34,68,9,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4342 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4343 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 13 152 336 33 480 416 416), lower := (rows 35 70 13 152 336 33 64 128 256), losses := [] }

theorem u4343 : Upper (D 9) (R 9) [34,68,9,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4343 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4344 : Route 9 := (fun mask => (mask,id))

def c4344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4344 : Upper (D 9) (R 9) [34,68,9,144,320,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,320,128] 13 (by decide) (choices 1) [1,32,256] r4344 c4344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1265
  · exact u1266
  · exact u1267

def r4345 : Route 9 := (fun mask => (mask,id))

def c4345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4345 : Upper (D 9) (R 9) [34,68,9,144,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,320,256] 13 (by decide) (choices 1) [1,32,128] r4345 c4345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1268
  · exact u1269
  · exact u1270

def b4346 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 44, targets := 320 }], pairs := [(2,6),(2,8),(3,6),(3,8)], upper := (rows 35 70 13 168 145 48 320 448 320), lower := (rows 35 70 13 168 145 48 64 128 256), losses := [] }

theorem u4346 : Upper (D 9) (R 9) [34,68,9,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4346 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4347 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 168 145 96 336 400 272), lower := (rows 35 70 13 168 145 96 64 128 256), losses := [] }

theorem u4347 : Upper (D 9) (R 9) [34,68,9,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4347 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4348 : Route 9 := (fun mask => (mask,id))

def c4348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4348 : Upper (D 9) (R 9) [34,68,9,160,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,129,256] 13 (by decide) (choices 1) [16,256] r4348 c4348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1271
  · exact u1272

def b4349 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 168 208 33 336 400 272), lower := (rows 35 70 13 168 208 33 64 128 256), losses := [] }

theorem u4349 : Upper (D 9) (R 9) [34,68,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4349 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4350 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 13 168 208 48 321 385 257), lower := (rows 35 70 13 168 208 48 64 128 256), losses := [] }

theorem u4350 : Upper (D 9) (R 9) [34,68,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4350 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4351 : Route 9 := (fun mask => (mask,id))

def c4351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4351 : Upper (D 9) (R 9) [34,68,9,160,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,192,256] 13 (by decide) (choices 1) [1,16,256] r4351 c4351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1273
  · exact u1274
  · exact u1275

def b4352 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 456, targets := 1 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 35 70 13 168 273 48 448 448 448), lower := (rows 35 70 13 168 273 48 64 128 256), losses := [] }

theorem u4352 : Upper (D 9) (R 9) [34,68,9,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4352 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4353 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 168 273 96 464 400 400), lower := (rows 35 70 13 168 273 96 64 128 256), losses := [] }

theorem u4353 : Upper (D 9) (R 9) [34,68,9,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4353 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4354 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 70 13 168 273 160 336 464 336), lower := (rows 35 70 13 168 273 160 64 128 256), losses := [] }

theorem u4354 : Upper (D 9) (R 9) [34,68,9,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4354 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4355 : Route 9 := (fun mask => (mask,id))

def c4355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4355 : Upper (D 9) (R 9) [34,68,9,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,257,256] 13 (by decide) (choices 1) [16,128] r4355 c4355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1276
  · exact u1277

def b4356 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 168 336 33 464 400 400), lower := (rows 35 70 13 168 336 33 64 128 256), losses := [] }

theorem u4356 : Upper (D 9) (R 9) [34,68,9,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4356 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4357 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,5)], upper := (rows 35 70 13 168 336 48 449 385 385), lower := (rows 35 70 13 168 336 48 64 128 256), losses := [] }

theorem u4357 : Upper (D 9) (R 9) [34,68,9,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4357 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4358 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 70 13 168 336 160 337 401 273), lower := (rows 35 70 13 168 336 160 64 128 256), losses := [] }

theorem u4358 : Upper (D 9) (R 9) [34,68,9,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4358 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4359 : Route 9 := (fun mask => (mask,id))

def c4359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4359 : Upper (D 9) (R 9) [34,68,9,160,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,320,256] 13 (by decide) (choices 1) [1,16,128] r4359 c4359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1278
  · exact u1279
  · exact u1280

def b4360 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 168 400 33 336 464 336), lower := (rows 35 70 13 168 400 33 64 128 256), losses := [] }

theorem u4360 : Upper (D 9) (R 9) [34,68,9,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4360 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4361 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 168 400 48 321 449 321), lower := (rows 35 70 13 168 400 48 64 128 256), losses := [] }

theorem u4361 : Upper (D 9) (R 9) [34,68,9,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4361 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4362 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 168 400 96 337 401 273), lower := (rows 35 70 13 168 400 96 64 128 256), losses := [] }

theorem u4362 : Upper (D 9) (R 9) [34,68,9,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4362 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4363 : Route 9 := (fun mask => (mask,id))

def c4363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4363 : Upper (D 9) (R 9) [34,68,9,160,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,384,256] 13 (by decide) (choices 1) [1,16] r4363 c4363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1281
  · exact u1282

def b4364 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 200 145 48 352 416 288), lower := (rows 35 70 13 200 145 48 64 128 256), losses := [] }

theorem u4364 : Upper (D 9) (R 9) [34,68,9,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4364 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4365 : Route 9 := (fun mask => (mask,id))

def c4365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u4365 : Upper (D 9) (R 9) [34,68,9,192,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,129,256] 13 (by decide) (choices 1) [16,32,256] r4365 c4365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1283
  · exact u1284
  · exact u1285

def b4366 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 200 176 33 336 400 272), lower := (rows 35 70 13 200 176 33 64 128 256), losses := [] }

theorem u4366 : Upper (D 9) (R 9) [34,68,9,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4366 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4367 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 200 176 48 321 385 257), lower := (rows 35 70 13 200 176 48 64 128 256), losses := [] }

theorem u4367 : Upper (D 9) (R 9) [34,68,9,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4367 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4368 : Route 9 := (fun mask => (mask,id))

def c4368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4368 : Upper (D 9) (R 9) [34,68,9,192,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,160,256] 13 (by decide) (choices 1) [1,16,256] r4368 c4368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1286
  · exact u1287
  · exact u1288

def b4369 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,6)], upper := (rows 35 70 13 200 273 48 480 416 416), lower := (rows 35 70 13 200 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 61 16 48 113 177 305), good := (rows 490 78 462 200 504 504 64 128 256) }] }

theorem u4369 : Upper (D 9) (R 9) [34,68,9,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4369 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4370 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,6)], upper := (rows 35 70 13 200 273 160 368 432 304), lower := (rows 35 70 13 200 273 160 64 128 256), losses := [] }

theorem u4370 : Upper (D 9) (R 9) [34,68,9,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4370 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4371 : Route 9 := (fun mask => (mask,id))

def c4371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4371 : Upper (D 9) (R 9) [34,68,9,192,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,257,256] 13 (by decide) (choices 1) [16,32,128] r4371 c4371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1289
  · exact u1290
  · exact u1291

def b4372 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 200 304 33 464 400 400), lower := (rows 35 70 13 200 304 33 64 128 256), losses := [] }

theorem u4372 : Upper (D 9) (R 9) [34,68,9,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4372 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4373 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 13 200 304 48 449 385 385), lower := (rows 35 70 13 200 304 48 64 128 256), losses := [] }

theorem u4373 : Upper (D 9) (R 9) [34,68,9,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4373 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4374 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,6)], upper := (rows 35 70 13 200 304 160 337 401 273), lower := (rows 35 70 13 200 304 160 64 128 256), losses := [] }

theorem u4374 : Upper (D 9) (R 9) [34,68,9,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4374 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4375 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 13 200 304 288 209 145 401), lower := (rows 35 70 13 200 304 288 64 128 256), losses := [] }

theorem u4375 : Upper (D 9) (R 9) [34,68,9,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4375 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4376 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 200 400 33 368 432 304), lower := (rows 35 70 13 200 400 33 64 128 256), losses := [] }

theorem u4376 : Upper (D 9) (R 9) [34,68,9,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4376 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4377 : Route 9 := (fun mask => (mask,id))

def c4377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4377 : Upper (D 9) (R 9) [34,68,9,192,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,384,16] 13 (by decide) (choices 1) [1,32,256] r4377 c4377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1292
  · exact u1293
  · exact u1294

def r4378 : Route 9 := (fun mask => (mask,id))

def c4378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4378 : Upper (D 9) (R 9) [34,68,9,192,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,384,256] 13 (by decide) (choices 1) [1,16,32] r4378 c4378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1295
  · exact u1296
  · exact u1297

def b4379 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 70 13 392 81 48 480 416 416), lower := (rows 35 70 13 392 81 48 64 128 256), losses := [] }

theorem u4379 : Upper (D 9) (R 9) [34,68,9,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4379 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4379
end Delivery.IrregularNine14.P09
