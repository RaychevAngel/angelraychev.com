import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0021
import IrregularNine14P09C0022

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4380 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 428, targets := 64 },{ cop := 0, region := 336, targets := 128 },{ cop := 4, region := 424, targets := 1 }], pairs := [(1,7),(2,6),(3,0),(3,6),(4,7)], upper := (rows 35 70 13 392 81 160 368 432 304), lower := (rows 35 70 13 392 81 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 21 32 65 0 257), good := (rows 371 86 351 264 337 32 64 0 256) }] }

theorem u4380 : Upper (D 9) (R 9) [34,68,9,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4380 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4381 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(4,7),(4,8)], upper := (rows 35 70 13 392 112 33 464 400 400), lower := (rows 35 70 13 392 112 33 64 128 256), losses := [] }

theorem u4381 : Upper (D 9) (R 9) [34,68,9,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4381 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4382 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 70 13 392 112 48 449 385 385), lower := (rows 35 70 13 392 112 48 64 128 256), losses := [] }

theorem u4382 : Upper (D 9) (R 9) [34,68,9,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4382 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4383 : Route 9 := (fun mask => (mask,id))

def c4383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4383 : Upper (D 9) (R 9) [34,68,9,384,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,96,128] 13 (by decide) (choices 1) [1,16,256] r4383 c4383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1298
  · exact u1299
  · exact u1300

def r4384 : Route 9 := (fun mask => (mask,id))

def c4384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4384 : Upper (D 9) (R 9) [34,68,9,384,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,129,16] 13 (by decide) (choices 1) [32,256] r4384 c4384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1301
  · exact u1302

def b4385 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 392 145 96 368 432 304), lower := (rows 35 70 13 392 145 96 64 128 256), losses := [] }

theorem u4385 : Upper (D 9) (R 9) [34,68,9,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4385 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4386 : Route 9 := (fun mask => (mask,id))

def c4386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4386 : Upper (D 9) (R 9) [34,68,9,384,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,129,256] 13 (by decide) (choices 1) [16,32] r4386 c4386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1303
  · exact u1304

def b4387 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 13 392 176 33 336 464 336), lower := (rows 35 70 13 392 176 33 64 128 256), losses := [] }

theorem u4387 : Upper (D 9) (R 9) [34,68,9,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4387 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4388 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 13 392 176 48 321 449 321), lower := (rows 35 70 13 392 176 48 64 128 256), losses := [] }

theorem u4388 : Upper (D 9) (R 9) [34,68,9,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4388 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4389 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 392 176 96 337 401 273), lower := (rows 35 70 13 392 176 96 64 128 256), losses := [] }

theorem u4389 : Upper (D 9) (R 9) [34,68,9,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4389 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4390 : Route 9 := (fun mask => (mask,id))

def c4390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4390 : Upper (D 9) (R 9) [34,68,9,384,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,160,256] 13 (by decide) (choices 1) [1,16] r4390 c4390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1305
  · exact u1306

def b4391 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 13 392 208 33 368 432 304), lower := (rows 35 70 13 392 208 33 64 128 256), losses := [] }

theorem u4391 : Upper (D 9) (R 9) [34,68,9,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4391 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4392 : Route 9 := (fun mask => (mask,id))

def c4392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4392 : Upper (D 9) (R 9) [34,68,9,384,192,16] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,192,16] 13 (by decide) (choices 1) [1,32,256] r4392 c4392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1307
  · exact u1308
  · exact u1309

def r4393 : Route 9 := (fun mask => (mask,id))

def c4393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4393 : Upper (D 9) (R 9) [34,68,9,384,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,192,256] 13 (by decide) (choices 1) [1,16,32] r4393 c4393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1310
  · exact u1311
  · exact u1312

def b4394 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 },{ cop := 2, region := 482, targets := 1 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(3,7),(4,6)], upper := (rows 35 70 28 73 145 160 352 416 288), lower := (rows 35 70 28 73 145 160 64 128 256), losses := [] }

theorem u4394 : Upper (D 9) (R 9) [34,68,24,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4394 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4395 : Route 9 := (fun mask => (mask,id))

def c4395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u4395 : Upper (D 9) (R 9) [34,68,24,65,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,24,65,129,256] 13 (by decide) (choices 1) [32,128,256] r4395 c4395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1313
  · exact u1314
  · exact u1315

def b4396 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 28 73 400 33 480 416 416), lower := (rows 35 70 28 73 400 33 64 128 256), losses := [] }

theorem u4396 : Upper (D 9) (R 9) [34,68,24,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4396 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4397 : Route 9 := (fun mask => (mask,id))

def c4397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4397 : Upper (D 9) (R 9) [34,68,24,65,384,128] 13 := by
  apply FastRouting.sound _ _ [34,68,24,65,384,128] 13 (by decide) (choices 1) [1,32,256] r4397 c4397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1316
  · exact u1317
  · exact u1318

def b4398 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 28 104 145 33 448 384 384), lower := (rows 35 70 28 104 145 33 64 128 256), losses := [] }

theorem u4398 : Upper (D 9) (R 9) [34,68,24,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4398 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4399 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(1,5),(3,7),(4,5),(4,6)], upper := (rows 35 70 28 104 145 160 321 385 257), lower := (rows 35 70 28 104 145 160 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 17 0 81 145 273), good := (rows 467 70 478 72 465 128 64 128 256) }] }

theorem u4399 : Upper (D 9) (R 9) [34,68,24,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4399 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4400 : Route 9 := (fun mask => (mask,id))

def c4400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4400 : Upper (D 9) (R 9) [34,68,24,96,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96,129,256] 13 (by decide) (choices 1) [1,128,256] r4400 c4400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1319
  · exact u1320
  · exact u1321

def b4401 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 28 104 400 33 449 385 385), lower := (rows 35 70 28 104 400 33 64 128 256), losses := [] }

theorem u4401 : Upper (D 9) (R 9) [34,68,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4401 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4402 : Route 9 := (fun mask => (mask,id))

def c4402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4402 : Upper (D 9) (R 9) [34,68,24,96,384,128] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96,384,128] 13 (by decide) (choices 1) [1,256] r4402 c4402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1322
  · exact u1323

def b4403 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 52, targets := 320 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,6),(2,8),(4,6),(4,8)], upper := (rows 35 70 28 137 176 33 320 448 320), lower := (rows 35 70 28 137 176 33 64 128 256), losses := [] }

theorem u4403 : Upper (D 9) (R 9) [34,68,24,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4403 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4404 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 137 176 96 321 385 257), lower := (rows 35 70 28 137 176 96 64 128 256), losses := [] }

theorem u4404 : Upper (D 9) (R 9) [34,68,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4404 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4405 : Route 9 := (fun mask => (mask,id))

def c4405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4405 : Upper (D 9) (R 9) [34,68,24,129,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,160,256] 13 (by decide) (choices 1) [1,256] r4405 c4405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1324
  · exact u1325

def b4406 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 28 137 208 33 352 416 288), lower := (rows 35 70 28 137 208 33 64 128 256), losses := [] }

theorem u4406 : Upper (D 9) (R 9) [34,68,24,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4406 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4407 : Route 9 := (fun mask => (mask,id))

def c4407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4407 : Upper (D 9) (R 9) [34,68,24,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,192,256] 13 (by decide) (choices 1) [1,32,256] r4407 c4407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1326
  · exact u1327
  · exact u1328

def b4408 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 137 273 96 480 416 416), lower := (rows 35 70 28 137 273 96 64 128 256), losses := [] }

theorem u4408 : Upper (D 9) (R 9) [34,68,24,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4408 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4409 : Route 9 := (fun mask => (mask,id))

def c4409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4409 : Upper (D 9) (R 9) [34,68,24,129,257,128] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,257,128] 13 (by decide) (choices 1) [32,256] r4409 c4409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1329
  · exact u1330

def b4410 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,5)], upper := (rows 35 70 28 137 304 33 448 448 448), lower := (rows 35 70 28 137 304 33 64 128 256), losses := [] }

theorem u4410 : Upper (D 9) (R 9) [34,68,24,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4410 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4411 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 137 304 96 449 385 385), lower := (rows 35 70 28 137 304 96 64 128 256), losses := [] }

theorem u4411 : Upper (D 9) (R 9) [34,68,24,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4411 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4412 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,5),(1,7),(2,7),(3,5),(4,7)], upper := (rows 35 70 28 137 304 160 321 449 321), lower := (rows 35 70 28 137 304 160 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 16 0 73 137 265), good := (rows 459 70 478 457 272 128 64 128 256) },{ target := 7, region := (rows 1 14 12 8 17 32 73 0 265), good := (rows 371 70 350 351 304 32 64 0 256) }] }

theorem u4412 : Upper (D 9) (R 9) [34,68,24,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4412 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4413 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 28 137 304 288 193 193 449), lower := (rows 35 70 28 137 304 288 64 128 256), losses := [] }

theorem u4413 : Upper (D 9) (R 9) [34,68,24,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4413 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4414 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,6),(4,0)], upper := (rows 35 70 28 137 336 33 480 416 416), lower := (rows 35 70 28 137 336 33 64 128 256), losses := [] }

theorem u4414 : Upper (D 9) (R 9) [34,68,24,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4414 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4415 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(1,7),(2,7),(3,6),(4,7)], upper := (rows 35 70 28 137 336 160 353 417 289), lower := (rows 35 70 28 137 336 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 25 32 65 0 257), good := (rows 371 70 30 351 336 32 64 0 256) }] }

theorem u4415 : Upper (D 9) (R 9) [34,68,24,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4415 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4416 : Route 9 := (fun mask => (mask,id))

def c4416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4416 : Upper (D 9) (R 9) [34,68,24,129,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,320,256] 13 (by decide) (choices 1) [1,32,128] r4416 c4416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1331
  · exact u1332
  · exact u1333

def b4417 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,0)], upper := (rows 35 70 28 137 400 33 352 480 352), lower := (rows 35 70 28 137 400 33 64 128 256), losses := [] }

theorem u4417 : Upper (D 9) (R 9) [34,68,24,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4417 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4418 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 137 400 96 353 417 289), lower := (rows 35 70 28 137 400 96 64 128 256), losses := [] }

theorem u4418 : Upper (D 9) (R 9) [34,68,24,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4418 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4419 : Route 9 := (fun mask => (mask,id))

def c4419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4419 : Upper (D 9) (R 9) [34,68,24,129,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,384,256] 13 (by decide) (choices 1) [1,32] r4419 c4419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1334
  · exact u1335

def b4420 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,6),(4,5)], upper := (rows 35 70 28 168 336 33 449 385 385), lower := (rows 35 70 28 168 336 33 64 128 256), losses := [] }

theorem u4420 : Upper (D 9) (R 9) [34,68,24,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4420 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4421 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 70 28 168 336 160 321 385 257), lower := (rows 35 70 28 168 336 160 64 128 256), losses := [] }

theorem u4421 : Upper (D 9) (R 9) [34,68,24,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4421 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4422 : Route 9 := (fun mask => (mask,id))

def c4422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4422 : Upper (D 9) (R 9) [34,68,24,160,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,320,256] 13 (by decide) (choices 1) [1,128] r4422 c4422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1336
  · exact u1337

def b4423 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,5)], upper := (rows 35 70 28 168 400 33 321 449 321), lower := (rows 35 70 28 168 400 33 64 128 256), losses := [] }

theorem u4423 : Upper (D 9) (R 9) [34,68,24,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4423 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4424 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 168 400 96 321 385 257), lower := (rows 35 70 28 168 400 96 64 128 256), losses := [] }

theorem u4424 : Upper (D 9) (R 9) [34,68,24,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4424 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4425 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 65 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 70 28 168 400 288 65 193 321), lower := (rows 35 70 28 168 400 288 64 128 256), losses := [] }

theorem u4425 : Upper (D 9) (R 9) [34,68,24,160,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4425 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4426 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,6)], upper := (rows 35 70 28 200 400 33 353 417 289), lower := (rows 35 70 28 200 400 33 64 128 256), losses := [] }

theorem u4426 : Upper (D 9) (R 9) [34,68,24,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4426 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4427 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 200, targets := 256 }], pairs := [(0,6),(0,7),(1,7),(3,8),(4,6)], upper := (rows 35 70 28 200 400 288 97 161 289), lower := (rows 35 70 28 200 400 288 64 128 256), losses := [] }

theorem u4427 : Upper (D 9) (R 9) [34,68,24,192,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4427 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4428 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 25 400 33 448 448 448), lower := (rows 35 70 44 25 400 33 64 128 256), losses := [] }

theorem u4428 : Upper (D 9) (R 9) [34,68,40,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4428 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4429 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 44 25 400 96 449 385 385), lower := (rows 35 70 44 25 400 96 64 128 256), losses := [] }

theorem u4429 : Upper (D 9) (R 9) [34,68,40,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4429 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4430 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,5),(4,5)], upper := (rows 35 70 44 25 400 160 321 449 321), lower := (rows 35 70 44 25 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 70 44 60 432 160 64 160 256) }] }

theorem u4430 : Upper (D 9) (R 9) [34,68,40,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4430 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4431 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 44 88 400 33 449 385 385), lower := (rows 35 70 44 88 400 33 64 128 256), losses := [] }

theorem u4431 : Upper (D 9) (R 9) [34,68,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4431 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4432 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(3,5),(4,5),(4,6)], upper := (rows 35 70 44 88 400 160 321 385 257), lower := (rows 35 70 44 88 400 160 64 128 256), losses := [] }

theorem u4432 : Upper (D 9) (R 9) [34,68,40,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4432 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4433 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 137 208 33 336 400 272), lower := (rows 35 70 44 137 208 33 64 128 256), losses := [] }

theorem u4433 : Upper (D 9) (R 9) [34,68,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4433 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4434 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 44 137 208 48 321 385 257), lower := (rows 35 70 44 137 208 48 64 128 256), losses := [] }

theorem u4434 : Upper (D 9) (R 9) [34,68,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4434 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4435 : Route 9 := (fun mask => (mask,id))

def c4435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4435 : Upper (D 9) (R 9) [34,68,40,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,192,256] 13 (by decide) (choices 1) [1,16,256] r4435 c4435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1338
  · exact u1339
  · exact u1340

def b4436 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 450, targets := 33 }], pairs := [(1,0),(1,5),(3,5),(4,5)], upper := (rows 35 70 44 137 273 48 448 448 448), lower := (rows 35 70 44 137 273 48 64 128 256), losses := [] }

theorem u4436 : Upper (D 9) (R 9) [34,68,40,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4436 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4437 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 44 137 273 96 464 400 400), lower := (rows 35 70 44 137 273 96 64 128 256), losses := [] }

theorem u4437 : Upper (D 9) (R 9) [34,68,40,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4437 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4438 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 70 44 137 273 160 336 464 336), lower := (rows 35 70 44 137 273 160 64 128 256), losses := [] }

theorem u4438 : Upper (D 9) (R 9) [34,68,40,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4438 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4439 : Route 9 := (fun mask => (mask,id))

def c4439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4439 : Upper (D 9) (R 9) [34,68,40,129,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,257,256] 13 (by decide) (choices 1) [16,128] r4439 c4439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1341
  · exact u1342

#print axioms u4439
end Delivery.IrregularNine14.P09
