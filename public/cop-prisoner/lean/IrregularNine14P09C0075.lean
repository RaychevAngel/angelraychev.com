import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0022
import IrregularNine14P09C0023

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4500 : Route 9 := (fun mask => (mask,id))

def c4500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4500 : Upper (D 9) (R 9) [34,68,129,48,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,65,256] 13 (by decide) (choices 1) [8,128,256] r4500 c4500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1374
  · exact u1375
  · exact u1376

def b4501 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,7)], upper := (rows 35 70 133 56 88 33 448 384 384), lower := (rows 35 70 133 56 88 33 64 128 256), losses := [] }

theorem u4501 : Upper (D 9) (R 9) [34,68,129,48,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4501 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4502 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 133 56 88 160 321 385 257), lower := (rows 35 70 133 56 88 160 64 128 256), losses := [] }

theorem u4502 : Upper (D 9) (R 9) [34,68,129,48,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4502 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4503 : Route 9 := (fun mask => (mask,id))

def c4503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4503 : Upper (D 9) (R 9) [34,68,129,48,72,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,72,256] 13 (by decide) (choices 1) [1,128,256] r4503 c4503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1377
  · exact u1378
  · exact u1379

def b4504 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 56, targets := 320 },{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0),(3,6),(3,8),(4,6),(4,8)], upper := (rows 35 70 133 56 152 33 320 448 320), lower := (rows 35 70 133 56 152 33 64 128 256), losses := [] }

theorem u4504 : Upper (D 9) (R 9) [34,68,129,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4504 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4505 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 152 96 321 385 257), lower := (rows 35 70 133 56 152 96 64 128 256), losses := [] }

theorem u4505 : Upper (D 9) (R 9) [34,68,129,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4505 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4506 : Route 9 := (fun mask => (mask,id))

def c4506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4506 : Upper (D 9) (R 9) [34,68,129,48,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,136,256] 13 (by decide) (choices 1) [1,256] r4506 c4506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1380
  · exact u1381

def b4507 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 35 70 133 56 208 33 328 392 264), lower := (rows 35 70 133 56 208 33 64 128 256), losses := [] }

theorem u4507 : Upper (D 9) (R 9) [34,68,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4507 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4508 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 56 208 40 321 385 257), lower := (rows 35 70 133 56 208 40 64 128 256), losses := [] }

theorem u4508 : Upper (D 9) (R 9) [34,68,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4508 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4509 : Route 9 := (fun mask => (mask,id))

def c4509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4509 : Upper (D 9) (R 9) [34,68,129,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,192,256] 13 (by decide) (choices 1) [1,8,256] r4509 c4509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1382
  · exact u1383
  · exact u1384

def b4510 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 40, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,5)], upper := (rows 35 70 133 56 273 40 448 448 448), lower := (rows 35 70 133 56 273 40 64 128 256), losses := [] }

theorem u4510 : Upper (D 9) (R 9) [34,68,129,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4510 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4511 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 273 96 456 392 392), lower := (rows 35 70 133 56 273 96 64 128 256), losses := [] }

theorem u4511 : Upper (D 9) (R 9) [34,68,129,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4511 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4512 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,6),(1,7),(3,0),(3,7),(4,7)], upper := (rows 35 70 133 56 273 160 328 456 328), lower := (rows 35 70 133 56 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 56 273 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 21 32 93 0 285), good := (rows 379 342 351 376 345 32 64 0 256) }] }

theorem u4512 : Upper (D 9) (R 9) [34,68,129,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4512 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4513 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 192 }], pairs := [(0,8),(1,8),(2,8),(3,6),(3,7)], upper := (rows 35 70 133 56 273 288 200 200 456), lower := (rows 35 70 133 56 273 288 64 128 256), losses := [] }

theorem u4513 : Upper (D 9) (R 9) [34,68,129,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4513 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4514 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 56 280 33 448 448 448), lower := (rows 35 70 133 56 280 33 64 128 256), losses := [] }

theorem u4514 : Upper (D 9) (R 9) [34,68,129,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4514 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4515 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 280 96 449 385 385), lower := (rows 35 70 133 56 280 96 64 128 256), losses := [] }

theorem u4515 : Upper (D 9) (R 9) [34,68,129,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4515 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4516 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 344, targets := 128 },{ cop := 2, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5),(3,7),(4,7)], upper := (rows 35 70 133 56 280 160 321 449 321), lower := (rows 35 70 133 56 280 160 64 128 256), losses := [] }

theorem u4516 : Upper (D 9) (R 9) [34,68,129,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4516 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4517 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0),(4,6)], upper := (rows 35 70 133 56 280 288 193 193 449), lower := (rows 35 70 133 56 280 288 64 128 256), losses := [] }

theorem u4517 : Upper (D 9) (R 9) [34,68,129,48,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4517 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4518 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 56 336 33 456 392 392), lower := (rows 35 70 133 56 336 33 64 128 256), losses := [] }

theorem u4518 : Upper (D 9) (R 9) [34,68,129,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4518 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4519 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 40, targets := 449 }], pairs := [(3,0),(3,6),(3,7),(3,8)], upper := (rows 35 70 133 56 336 40 449 385 385), lower := (rows 35 70 133 56 336 40 64 128 256), losses := [] }

theorem u4519 : Upper (D 9) (R 9) [34,68,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4519 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4520 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 56 336 160 329 393 265), lower := (rows 35 70 133 56 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 56 272 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 23 32 69 0 261), good := (rows 379 342 351 56 336 32 64 0 256) },{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 165 56 80 160 64 160 0) }] }

theorem u4520 : Upper (D 9) (R 9) [34,68,129,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4520 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4521 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 35 70 133 56 336 288 201 137 393), lower := (rows 35 70 133 56 336 288 64 128 256), losses := [] }

theorem u4521 : Upper (D 9) (R 9) [34,68,129,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4521 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4522 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 56 400 33 328 456 328), lower := (rows 35 70 133 56 400 33 64 128 256), losses := [] }

theorem u4522 : Upper (D 9) (R 9) [34,68,129,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4522 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4523 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 40, targets := 449 }], pairs := [(3,0),(3,6),(3,7),(3,8)], upper := (rows 35 70 133 56 400 40 321 449 321), lower := (rows 35 70 133 56 400 40 64 128 256), losses := [] }

theorem u4523 : Upper (D 9) (R 9) [34,68,129,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4523 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4524 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 400 96 329 393 265), lower := (rows 35 70 133 56 400 96 64 128 256), losses := [] }

theorem u4524 : Upper (D 9) (R 9) [34,68,129,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4524 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4525 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 35 70 133 56 400 288 73 201 329), lower := (rows 35 70 133 56 400 288 64 128 256), losses := [] }

theorem u4525 : Upper (D 9) (R 9) [34,68,129,48,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4525 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4526 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 0, region := 328, targets := 128 },{ cop := 3, region := 432, targets := 1 }], pairs := [(2,6),(3,7),(4,0),(4,6)], upper := (rows 35 70 133 73 152 48 352 416 288), lower := (rows 35 70 133 73 152 48 64 128 256), losses := [] }

theorem u4526 : Upper (D 9) (R 9) [34,68,129,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4526 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4527 : Route 9 := (fun mask => (mask,id))

def c4527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u4527 : Upper (D 9) (R 9) [34,68,129,65,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,136,256] 13 (by decide) (choices 1) [16,32,256] r4527 c4527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1385
  · exact u1386
  · exact u1387

def b4528 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 133 73 176 40 336 400 272), lower := (rows 35 70 133 73 176 40 64 128 256), losses := [] }

theorem u4528 : Upper (D 9) (R 9) [34,68,129,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4528 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4529 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 133 73 176 48 328 392 264), lower := (rows 35 70 133 73 176 48 64 128 256), losses := [] }

theorem u4529 : Upper (D 9) (R 9) [34,68,129,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4529 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4530 : Route 9 := (fun mask => (mask,id))

def c4530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4530 : Upper (D 9) (R 9) [34,68,129,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,160,256] 13 (by decide) (choices 1) [8,16,256] r4530 c4530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1388
  · exact u1389
  · exact u1390

def b4531 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 432, targets := 1 }], pairs := [(1,0),(2,6),(4,0),(4,6)], upper := (rows 35 70 133 73 280 48 480 416 416), lower := (rows 35 70 133 73 280 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 56 121 185 313), good := (rows 482 70 454 504 504 496 64 128 256) }] }

theorem u4531 : Upper (D 9) (R 9) [34,68,129,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4531 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4532 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 432, targets := 1 }], pairs := [(2,6),(3,7),(4,0),(4,6),(4,7)], upper := (rows 35 70 133 73 280 160 368 432 304), lower := (rows 35 70 133 73 280 160 64 128 256), losses := [] }

theorem u4532 : Upper (D 9) (R 9) [34,68,129,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4532 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4533 : Route 9 := (fun mask => (mask,id))

def c4533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4533 : Upper (D 9) (R 9) [34,68,129,65,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,264,256] 13 (by decide) (choices 1) [16,32,128] r4533 c4533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1391
  · exact u1392
  · exact u1393

def b4534 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 133 73 304 40 464 400 400), lower := (rows 35 70 133 73 304 40 64 128 256), losses := [] }

theorem u4534 : Upper (D 9) (R 9) [34,68,129,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4534 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4535 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 133 73 304 48 456 392 392), lower := (rows 35 70 133 73 304 48 64 128 256), losses := [] }

theorem u4535 : Upper (D 9) (R 9) [34,68,129,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4535 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4536 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 432, targets := 1 }], pairs := [(2,6),(3,7),(4,0),(4,6),(4,7)], upper := (rows 35 70 133 73 304 160 344 408 280), lower := (rows 35 70 133 73 304 160 64 128 256), losses := [] }

theorem u4536 : Upper (D 9) (R 9) [34,68,129,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4536 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4537 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 133 73 304 288 216 152 408), lower := (rows 35 70 133 73 304 288 64 128 256), losses := [] }

theorem u4537 : Upper (D 9) (R 9) [34,68,129,65,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4537 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4538 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 133 73 400 40 368 432 304), lower := (rows 35 70 133 73 400 40 64 128 256), losses := [] }

theorem u4538 : Upper (D 9) (R 9) [34,68,129,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4538 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4539 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 0, region := 328, targets := 128 },{ cop := 3, region := 432, targets := 1 }], pairs := [(2,6),(3,7),(4,0),(4,6)], upper := (rows 35 70 133 73 400 48 360 424 296), lower := (rows 35 70 133 73 400 48 64 128 256), losses := [] }

theorem u4539 : Upper (D 9) (R 9) [34,68,129,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4539 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4540 : Route 9 := (fun mask => (mask,id))

def c4540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4540 : Upper (D 9) (R 9) [34,68,129,65,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,384,256] 13 (by decide) (choices 1) [8,16,32] r4540 c4540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1394
  · exact u1395
  · exact u1396

def b4541 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,0),(4,0)], upper := (rows 35 70 133 88 152 33 352 416 288), lower := (rows 35 70 133 88 152 33 64 128 256), losses := [] }

theorem u4541 : Upper (D 9) (R 9) [34,68,129,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4541 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4542 : Route 9 := (fun mask => (mask,id))

def c4542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4542 : Upper (D 9) (R 9) [34,68,129,80,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,136,256] 13 (by decide) (choices 1) [1,32,256] r4542 c4542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1397
  · exact u1398
  · exact u1399

def b4543 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 88 176 33 328 392 264), lower := (rows 35 70 133 88 176 33 64 128 256), losses := [] }

theorem u4543 : Upper (D 9) (R 9) [34,68,129,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4543 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4544 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(1,5),(2,5),(2,6),(4,6)], upper := (rows 35 70 133 88 176 40 321 385 257), lower := (rows 35 70 133 88 176 40 64 128 256), losses := [] }

theorem u4544 : Upper (D 9) (R 9) [34,68,129,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4544 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4545 : Route 9 := (fun mask => (mask,id))

def c4545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4545 : Upper (D 9) (R 9) [34,68,129,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,160,256] 13 (by decide) (choices 1) [1,8,256] r4545 c4545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1400
  · exact u1401
  · exact u1402

def b4546 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 4, region := 232, targets := 1 }], pairs := [(1,0),(2,6),(3,0),(4,6)], upper := (rows 35 70 133 88 273 40 480 416 416), lower := (rows 35 70 133 88 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 56 121 185 313), good := (rows 482 70 454 504 504 488 64 128 256) }] }

theorem u4546 : Upper (D 9) (R 9) [34,68,129,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4546 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4547 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,6),(1,7),(3,0),(3,7),(4,7)], upper := (rows 35 70 133 88 273 160 360 424 296), lower := (rows 35 70 133 88 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 172 0 136 264), good := (rows 35 39 165 440 273 160 0 160 256) },{ target := 7, region := (rows 1 6 4 31 21 32 65 0 257), good := (rows 379 94 351 88 345 32 64 0 256) }] }

theorem u4547 : Upper (D 9) (R 9) [34,68,129,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4547 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4548 : Route 9 := (fun mask => (mask,id))

def c4548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4548 : Upper (D 9) (R 9) [34,68,129,80,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,257,256] 13 (by decide) (choices 1) [8,32,128] r4548 c4548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1403
  · exact u1404
  · exact u1405

def b4549 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 421, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,0),(4,0)], upper := (rows 35 70 133 88 280 33 480 416 416), lower := (rows 35 70 133 88 280 33 64 128 256), losses := [] }

theorem u4549 : Upper (D 9) (R 9) [34,68,129,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4549 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4550 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,7),(2,6),(3,7),(4,7)], upper := (rows 35 70 133 88 280 160 353 417 289), lower := (rows 35 70 133 88 280 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 15 21 32 65 0 257), good := (rows 379 94 351 88 280 32 64 0 256) }] }

theorem u4550 : Upper (D 9) (R 9) [34,68,129,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4550 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4551 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,6),(2,8)], upper := (rows 35 70 133 88 280 288 225 161 417), lower := (rows 35 70 133 88 280 288 64 128 256), losses := [] }

theorem u4551 : Upper (D 9) (R 9) [34,68,129,80,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4551 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4552 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 88 304 33 456 392 392), lower := (rows 35 70 133 88 304 33 64 128 256), losses := [] }

theorem u4552 : Upper (D 9) (R 9) [34,68,129,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4552 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4553 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(1,5),(2,5),(2,6),(4,6)], upper := (rows 35 70 133 88 304 40 449 385 385), lower := (rows 35 70 133 88 304 40 64 128 256), losses := [] }

theorem u4553 : Upper (D 9) (R 9) [34,68,129,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4553 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4554 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 88 304 160 329 393 265), lower := (rows 35 70 133 88 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 24 304 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 17 32 69 0 261), good := (rows 379 334 351 88 304 32 64 0 256) },{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 165 88 48 160 64 160 0) }] }

theorem u4554 : Upper (D 9) (R 9) [34,68,129,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4554 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4555 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 133 88 304 288 201 137 393), lower := (rows 35 70 133 88 304 288 64 128 256), losses := [] }

theorem u4555 : Upper (D 9) (R 9) [34,68,129,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4555 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4556 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 88 400 33 360 424 296), lower := (rows 35 70 133 88 400 33 64 128 256), losses := [] }

theorem u4556 : Upper (D 9) (R 9) [34,68,129,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4556 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4557 : Route 9 := (fun mask => (mask,id))

def c4557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4557 : Upper (D 9) (R 9) [34,68,129,80,384,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,384,8] 13 (by decide) (choices 1) [1,32,256] r4557 c4557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1406
  · exact u1407
  · exact u1408

def r4558 : Route 9 := (fun mask => (mask,id))

def c4558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4558 : Upper (D 9) (R 9) [34,68,129,80,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,384,256] 13 (by decide) (choices 1) [1,8,32] r4558 c4558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1409
  · exact u1410
  · exact u1411

def b4559 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 35 70 133 104 152 33 336 400 272), lower := (rows 35 70 133 104 152 33 64 128 256), losses := [] }

theorem u4559 : Upper (D 9) (R 9) [34,68,129,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4559 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4559
end Delivery.IrregularNine14.P09
