import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0023
import IrregularNine14P09C0024

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4560 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 388, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(1,5),(2,5),(2,6),(3,7)], upper := (rows 35 70 133 104 152 48 321 385 257), lower := (rows 35 70 133 104 152 48 64 128 256), losses := [] }

theorem u4560 : Upper (D 9) (R 9) [34,68,129,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4560 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4561 : Route 9 := (fun mask => (mask,id))

def c4561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4561 : Upper (D 9) (R 9) [34,68,129,96,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,136,256] 13 (by decide) (choices 1) [1,16,256] r4561 c4561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1412
  · exact u1413
  · exact u1414

def b4562 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 133 104 273 40 464 400 400), lower := (rows 35 70 133 104 273 40 64 128 256), losses := [] }

theorem u4562 : Upper (D 9) (R 9) [34,68,129,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4562 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4563 : Route 9 := (fun mask => (mask,id))

def c4563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4563 : Upper (D 9) (R 9) [34,68,129,96,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,257,16] 13 (by decide) (choices 1) [8,128,256] r4563 c4563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1415
  · exact u1416
  · exact u1417

def b4564 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,6),(1,7),(3,0),(3,7),(4,7)], upper := (rows 35 70 133 104 273 160 344 408 280), lower := (rows 35 70 133 104 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 40 273 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 21 32 85 0 277), good := (rows 379 342 351 104 345 32 64 0 256) }] }

theorem u4564 : Upper (D 9) (R 9) [34,68,129,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4564 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4565 : Route 9 := (fun mask => (mask,id))

def c4565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4565 : Upper (D 9) (R 9) [34,68,129,96,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,257,256] 13 (by decide) (choices 1) [8,16,128] r4565 c4565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1418
  · exact u1419
  · exact u1420

def b4566 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 35 70 133 104 280 33 464 400 400), lower := (rows 35 70 133 104 280 33 64 128 256), losses := [] }

theorem u4566 : Upper (D 9) (R 9) [34,68,129,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4566 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4567 : Route 9 := (fun mask => (mask,id))

def c4567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4567 : Upper (D 9) (R 9) [34,68,129,96,264,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264,16] 13 (by decide) (choices 1) [1,128,256] r4567 c4567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1421
  · exact u1422
  · exact u1423

def b4568 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,0),(3,7),(4,7)], upper := (rows 35 70 133 104 280 160 337 401 273), lower := (rows 35 70 133 104 280 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 42 110 164 104 280 160 64 160 256) },{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 40 280 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 21 32 69 0 261), good := (rows 379 342 351 104 280 32 64 0 256) }] }

theorem u4568 : Upper (D 9) (R 9) [34,68,129,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4568 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4569 : Route 9 := (fun mask => (mask,id))

def c4569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4569 : Upper (D 9) (R 9) [34,68,129,96,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264,256] 13 (by decide) (choices 1) [1,16,128] r4569 c4569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1424
  · exact u1425
  · exact u1426

def b4570 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 35 70 133 104 400 33 344 408 280), lower := (rows 35 70 133 104 400 33 64 128 256), losses := [] }

theorem u4570 : Upper (D 9) (R 9) [34,68,129,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4570 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4571 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 133 104 400 40 337 401 273), lower := (rows 35 70 133 104 400 40 64 128 256), losses := [] }

theorem u4571 : Upper (D 9) (R 9) [34,68,129,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4571 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4572 : Route 9 := (fun mask => (mask,id))

def c4572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4572 : Upper (D 9) (R 9) [34,68,129,96,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,384,16] 13 (by decide) (choices 1) [1,8,256] r4572 c4572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1427
  · exact u1428
  · exact u1429

def r4573 : Route 9 := (fun mask => (mask,id))

def c4573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4573 : Upper (D 9) (R 9) [34,68,129,96,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,384,256] 13 (by decide) (choices 1) [1,8,16] r4573 c4573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1430
  · exact u1431
  · exact u1432

def b4574 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 336, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 35 70 133 152 273 40 352 480 352), lower := (rows 35 70 133 152 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 56 121 185 313), good := (rows 482 70 454 504 504 488 64 128 256) },{ target := 7, region := (rows 1 6 4 8 21 40 105 0 297), good := (rows 371 86 343 376 337 360 64 0 256) }] }

theorem u4574 : Upper (D 9) (R 9) [34,68,129,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4574 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4575 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 152 273 96 360 424 296), lower := (rows 35 70 133 152 273 96 64 128 256), losses := [] }

theorem u4575 : Upper (D 9) (R 9) [34,68,129,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4575 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4576 : Route 9 := (fun mask => (mask,id))

def c4576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4576 : Upper (D 9) (R 9) [34,68,129,144,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,257,256] 13 (by decide) (choices 1) [8,32] r4576 c4576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1433
  · exact u1434

def b4577 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 152 280 33 352 480 352), lower := (rows 35 70 133 152 280 33 64 128 256), losses := [] }

theorem u4577 : Upper (D 9) (R 9) [34,68,129,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4577 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4578 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 152 280 96 353 417 289), lower := (rows 35 70 133 152 280 96 64 128 256), losses := [] }

theorem u4578 : Upper (D 9) (R 9) [34,68,129,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4578 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4579 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,8)], upper := (rows 35 70 133 152 280 288 97 225 353), lower := (rows 35 70 133 152 280 288 64 128 256), losses := [] }

theorem u4579 : Upper (D 9) (R 9) [34,68,129,144,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4579 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4580 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 152 304 33 328 456 328), lower := (rows 35 70 133 152 304 33 64 128 256), losses := [] }

theorem u4580 : Upper (D 9) (R 9) [34,68,129,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4580 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4581 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 336, targets := 128 },{ cop := 2, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5),(4,7)], upper := (rows 35 70 133 152 304 40 321 449 321), lower := (rows 35 70 133 152 304 40 64 128 256), losses := [] }

theorem u4581 : Upper (D 9) (R 9) [34,68,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4581 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4582 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 152 304 96 329 393 265), lower := (rows 35 70 133 152 304 96 64 128 256), losses := [] }

theorem u4582 : Upper (D 9) (R 9) [34,68,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4582 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4583 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 133 152 304 288 73 201 329), lower := (rows 35 70 133 152 304 288 64 128 256), losses := [] }

theorem u4583 : Upper (D 9) (R 9) [34,68,129,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4583 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4584 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 152 336 33 360 424 296), lower := (rows 35 70 133 152 336 33 64 128 256), losses := [] }

theorem u4584 : Upper (D 9) (R 9) [34,68,129,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4584 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4585 : Route 9 := (fun mask => (mask,id))

def c4585 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4585 : Upper (D 9) (R 9) [34,68,129,144,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,320,8] 13 (by decide) (choices 1) [1,32,256] r4585 c4585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1435
  · exact u1436
  · exact u1437

def r4586 : Route 9 := (fun mask => (mask,id))

def c4586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4586 : Upper (D 9) (R 9) [34,68,129,144,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,320,256] 13 (by decide) (choices 1) [1,8,32] r4586 c4586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1438
  · exact u1439
  · exact u1440

def b4587 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 70 133 168 273 40 336 464 336), lower := (rows 35 70 133 168 273 40 64 128 256), losses := [] }

theorem u4587 : Upper (D 9) (R 9) [34,68,129,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4587 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4588 : Route 9 := (fun mask => (mask,id))

def c4588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4588 : Upper (D 9) (R 9) [34,68,129,160,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,257,16] 13 (by decide) (choices 1) [8,256] r4588 c4588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1441
  · exact u1442

def b4589 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 168 273 96 344 408 280), lower := (rows 35 70 133 168 273 96 64 128 256), losses := [] }

theorem u4589 : Upper (D 9) (R 9) [34,68,129,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4589 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4590 : Route 9 := (fun mask => (mask,id))

def c4590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4590 : Upper (D 9) (R 9) [34,68,129,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,257,256] 13 (by decide) (choices 1) [8,16] r4590 c4590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1443
  · exact u1444

def b4591 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 168 280 33 336 464 336), lower := (rows 35 70 133 168 280 33 64 128 256), losses := [] }

theorem u4591 : Upper (D 9) (R 9) [34,68,129,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4591 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4592 : Route 9 := (fun mask => (mask,id))

def c4592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4592 : Upper (D 9) (R 9) [34,68,129,160,264,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264,16] 13 (by decide) (choices 1) [1,256] r4592 c4592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1445
  · exact u1446

def b4593 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 168 280 96 337 401 273), lower := (rows 35 70 133 168 280 96 64 128 256), losses := [] }

theorem u4593 : Upper (D 9) (R 9) [34,68,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4593 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4594 : Route 9 := (fun mask => (mask,id))

def c4594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4594 : Upper (D 9) (R 9) [34,68,129,160,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264,256] 13 (by decide) (choices 1) [1,16] r4594 c4594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1447
  · exact u1448

def b4595 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 168 336 33 344 408 280), lower := (rows 35 70 133 168 336 33 64 128 256), losses := [] }

theorem u4595 : Upper (D 9) (R 9) [34,68,129,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4595 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4596 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 70 133 168 336 40 337 401 273), lower := (rows 35 70 133 168 336 40 64 128 256), losses := [] }

theorem u4596 : Upper (D 9) (R 9) [34,68,129,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4596 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4597 : Route 9 := (fun mask => (mask,id))

def c4597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4597 : Upper (D 9) (R 9) [34,68,129,160,320,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,320,16] 13 (by decide) (choices 1) [1,8,256] r4597 c4597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1449
  · exact u1450
  · exact u1451

def r4598 : Route 9 := (fun mask => (mask,id))

def c4598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4598 : Upper (D 9) (R 9) [34,68,129,160,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,320,256] 13 (by decide) (choices 1) [1,8,16] r4598 c4598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1452
  · exact u1453
  · exact u1454

def b4599 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 404, targets := 64 }], pairs := [(0,8),(1,8),(2,6),(2,8)], upper := (rows 35 70 133 200 273 40 368 432 304), lower := (rows 35 70 133 200 273 40 64 128 256), losses := [] }

theorem u4599 : Upper (D 9) (R 9) [34,68,129,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4599 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4600 : Route 9 := (fun mask => (mask,id))

def c4600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4600 : Upper (D 9) (R 9) [34,68,129,192,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,257,16] 13 (by decide) (choices 1) [8,32,256] r4600 c4600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1455
  · exact u1456
  · exact u1457

def r4601 : Route 9 := (fun mask => (mask,id))

def c4601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4601 : Upper (D 9) (R 9) [34,68,129,192,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,257,256] 13 (by decide) (choices 1) [8,16,32] r4601 c4601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1458
  · exact u1459
  · exact u1460

def b4602 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 200 280 33 368 432 304), lower := (rows 35 70 133 200 280 33 64 128 256), losses := [] }

theorem u4602 : Upper (D 9) (R 9) [34,68,129,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4602 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4603 : Route 9 := (fun mask => (mask,id))

def c4603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4603 : Upper (D 9) (R 9) [34,68,129,192,264,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,264,16] 13 (by decide) (choices 1) [1,32,256] r4603 c4603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1461
  · exact u1462
  · exact u1463

def r4604 : Route 9 := (fun mask => (mask,id))

def c4604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4604 : Upper (D 9) (R 9) [34,68,129,192,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,264,256] 13 (by decide) (choices 1) [1,16,32] r4604 c4604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1464
  · exact u1465
  · exact u1466

def b4605 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 200 304 33 344 408 280), lower := (rows 35 70 133 200 304 33 64 128 256), losses := [] }

theorem u4605 : Upper (D 9) (R 9) [34,68,129,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4605 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4606 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 404, targets := 64 }], pairs := [(0,8),(1,8),(2,6),(2,8)], upper := (rows 35 70 133 200 304 40 337 401 273), lower := (rows 35 70 133 200 304 40 64 128 256), losses := [] }

theorem u4606 : Upper (D 9) (R 9) [34,68,129,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4606 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4607 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 133 200 304 48 329 393 265), lower := (rows 35 70 133 200 304 48 64 128 256), losses := [] }

theorem u4607 : Upper (D 9) (R 9) [34,68,129,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4607 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4608 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 133 200 304 288 89 153 281), lower := (rows 35 70 133 200 304 288 64 128 256), losses := [] }

theorem u4608 : Upper (D 9) (R 9) [34,68,129,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4608 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4609 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 199, targets := 256 },{ cop := 3, region := 48, targets := 64 }], pairs := [(0,8),(1,8),(2,8),(4,6)], upper := (rows 35 70 133 265 304 40 208 208 464), lower := (rows 35 70 133 265 304 40 64 128 256), losses := [] }

theorem u4609 : Upper (D 9) (R 9) [34,68,129,257,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4609 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4610 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 133 265 304 48 200 200 456), lower := (rows 35 70 133 265 304 48 64 128 256), losses := [] }

theorem u4610 : Upper (D 9) (R 9) [34,68,129,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4610 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4611 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 265 304 96 216 152 408), lower := (rows 35 70 133 265 304 96 64 128 256), losses := [] }

theorem u4611 : Upper (D 9) (R 9) [34,68,129,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4611 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4612 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 240, targets := 1 }], pairs := [(0,6),(1,7),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 265 304 160 88 216 344), lower := (rows 35 70 133 265 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 265 304 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 17 32 77 0 269), good := (rows 379 334 351 345 304 32 64 0 256) }] }

theorem u4612 : Upper (D 9) (R 9) [34,68,129,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4612 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4613 : Route 9 := (fun mask => (mask,id))

def c4613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4613 : Upper (D 9) (R 9) [34,68,129,257,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,320,8] 13 (by decide) (choices 1) [16,32,128] r4613 c4613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1467
  · exact u1468
  · exact u1469

def r4614 : Route 9 := (fun mask => (mask,id))

def c4614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4614 : Upper (D 9) (R 9) [34,68,129,257,320,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,320,16] 13 (by decide) (choices 1) [8,32,128] r4614 c4614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1470
  · exact u1471
  · exact u1472

def b4615 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 240, targets := 1 }], pairs := [(0,6),(1,7),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 265 336 160 120 184 312), lower := (rows 35 70 133 265 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 265 272 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 29 32 65 0 257), good := (rows 379 94 351 345 336 32 64 0 256) }] }

theorem u4615 : Upper (D 9) (R 9) [34,68,129,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4615 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4616 : Route 9 := (fun mask => (mask,id))

def c4616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4616 : Upper (D 9) (R 9) [34,68,129,257,384,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,384,8] 13 (by decide) (choices 1) [16,32] r4616 c4616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1473
  · exact u1474

def r4617 : Route 9 := (fun mask => (mask,id))

def c4617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4617 : Upper (D 9) (R 9) [34,68,129,257,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,384,16] 13 (by decide) (choices 1) [8,32] r4617 c4617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1475
  · exact u1476

def b4618 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 265 400 96 120 184 312), lower := (rows 35 70 133 265 400 96 64 128 256), losses := [] }

theorem u4618 : Upper (D 9) (R 9) [34,68,129,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4618 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4619 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 296 336 33 216 152 408), lower := (rows 35 70 133 296 336 33 64 128 256), losses := [] }

theorem u4619 : Upper (D 9) (R 9) [34,68,129,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4619 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4619
end Delivery.IrregularNine14.P09
