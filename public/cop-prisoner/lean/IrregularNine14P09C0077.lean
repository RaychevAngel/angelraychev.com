import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0024
import IrregularNine14P09C0025

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4620 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 70 133 296 336 40 209 145 401), lower := (rows 35 70 133 296 336 40 64 128 256), losses := [] }

theorem u4620 : Upper (D 9) (R 9) [34,68,129,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4620 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4621 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 133 296 336 48 201 137 393), lower := (rows 35 70 133 296 336 48 64 128 256), losses := [] }

theorem u4621 : Upper (D 9) (R 9) [34,68,129,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4621 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4622 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 296 336 160 89 153 281), lower := (rows 35 70 133 296 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 296 272 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 23 32 69 0 261), good := (rows 379 342 351 296 336 32 64 0 256) },{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 165 40 80 160 64 160 0) }] }

theorem u4622 : Upper (D 9) (R 9) [34,68,129,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4622 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4623 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 296 400 33 88 216 344), lower := (rows 35 70 133 296 400 33 64 128 256), losses := [] }

theorem u4623 : Upper (D 9) (R 9) [34,68,129,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4623 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4624 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 70 133 296 400 40 81 209 337), lower := (rows 35 70 133 296 400 40 64 128 256), losses := [] }

theorem u4624 : Upper (D 9) (R 9) [34,68,129,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4624 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4625 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 133 296 400 48 73 201 329), lower := (rows 35 70 133 296 400 48 64 128 256), losses := [] }

theorem u4625 : Upper (D 9) (R 9) [34,68,129,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4625 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4626 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 296 400 96 89 153 281), lower := (rows 35 70 133 296 400 96 64 128 256), losses := [] }

theorem u4626 : Upper (D 9) (R 9) [34,68,129,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4626 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4627 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 70 133 328 400 33 120 184 312), lower := (rows 35 70 133 328 400 33 64 128 256), losses := [] }

theorem u4627 : Upper (D 9) (R 9) [34,68,129,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4627 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4628 : Route 9 := (fun mask => (mask,id))

def c4628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4628 : Upper (D 9) (R 9) [34,68,129,320,384,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,320,384,8] 13 (by decide) (choices 1) [1,16,32] r4628 c4628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1477
  · exact u1478
  · exact u1479

def r4629 : Route 9 := (fun mask => (mask,id))

def c4629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4629 : Upper (D 9) (R 9) [34,68,129,320,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,320,384,16] 13 (by decide) (choices 1) [1,8,32] r4629 c4629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1480
  · exact u1481
  · exact u1482

def b4630 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,7)], upper := (rows 35 70 140 25 112 33 448 384 384), lower := (rows 35 70 140 25 112 33 64 128 256), losses := [] }

theorem u4630 : Upper (D 9) (R 9) [34,68,136,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4630 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4631 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 140 25 112 160 321 385 257), lower := (rows 35 70 140 25 112 160 64 128 256), losses := [] }

theorem u4631 : Upper (D 9) (R 9) [34,68,136,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4631 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4632 : Route 9 := (fun mask => (mask,id))

def c4632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4632 : Upper (D 9) (R 9) [34,68,136,17,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,96,256] 13 (by decide) (choices 1) [1,128,256] r4632 c4632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1483
  · exact u1484
  · exact u1485

def b4633 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 454, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 25 176 33 320 448 320), lower := (rows 35 70 140 25 176 33 64 128 256), losses := [] }

theorem u4633 : Upper (D 9) (R 9) [34,68,136,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4633 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4634 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 176 96 321 385 257), lower := (rows 35 70 140 25 176 96 64 128 256), losses := [] }

theorem u4634 : Upper (D 9) (R 9) [34,68,136,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4634 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4635 : Route 9 := (fun mask => (mask,id))

def c4635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4635 : Upper (D 9) (R 9) [34,68,136,17,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,160,256] 13 (by decide) (choices 1) [1,256] r4635 c4635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1486
  · exact u1487

def b4636 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 140 25 208 33 352 416 288), lower := (rows 35 70 140 25 208 33 64 128 256), losses := [] }

theorem u4636 : Upper (D 9) (R 9) [34,68,136,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4636 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4637 : Route 9 := (fun mask => (mask,id))

def c4637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4637 : Upper (D 9) (R 9) [34,68,136,17,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,192,256] 13 (by decide) (choices 1) [1,32,256] r4637 c4637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1488
  · exact u1489
  · exact u1490

def b4638 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 454, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 25 304 33 448 448 448), lower := (rows 35 70 140 25 304 33 64 128 256), losses := [] }

theorem u4638 : Upper (D 9) (R 9) [34,68,136,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4638 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4639 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 304 96 449 385 385), lower := (rows 35 70 140 25 304 96 64 128 256), losses := [] }

theorem u4639 : Upper (D 9) (R 9) [34,68,136,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4639 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4640 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,6),(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 140 25 304 160 321 449 321), lower := (rows 35 70 140 25 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 25 304 160 0 160 256) }] }

theorem u4640 : Upper (D 9) (R 9) [34,68,136,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4640 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4641 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 140 25 304 288 193 193 449), lower := (rows 35 70 140 25 304 288 64 128 256), losses := [] }

theorem u4641 : Upper (D 9) (R 9) [34,68,136,17,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4641 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4642 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 464, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 3, region := 420, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(2,6),(4,0)], upper := (rows 35 70 140 25 336 33 480 416 416), lower := (rows 35 70 140 25 336 33 64 128 256), losses := [] }

theorem u4642 : Upper (D 9) (R 9) [34,68,136,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4642 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4643 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 417, targets := 64 },{ cop := 3, region := 420, targets := 64 }], pairs := [(0,6),(0,8),(2,6),(3,7),(4,7)], upper := (rows 35 70 140 25 336 160 353 417 289), lower := (rows 35 70 140 25 336 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 172 25 80 160 64 160 0) }] }

theorem u4643 : Upper (D 9) (R 9) [34,68,136,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4643 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4644 : Route 9 := (fun mask => (mask,id))

def c4644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4644 : Upper (D 9) (R 9) [34,68,136,17,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,320,256] 13 (by decide) (choices 1) [1,32,128] r4644 c4644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1491
  · exact u1492
  · exact u1493

def b4645 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,0)], upper := (rows 35 70 140 25 400 33 352 480 352), lower := (rows 35 70 140 25 400 33 64 128 256), losses := [] }

theorem u4645 : Upper (D 9) (R 9) [34,68,136,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4645 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4646 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 400 96 353 417 289), lower := (rows 35 70 140 25 400 96 64 128 256), losses := [] }

theorem u4646 : Upper (D 9) (R 9) [34,68,136,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4646 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4647 : Route 9 := (fun mask => (mask,id))

def c4647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4647 : Upper (D 9) (R 9) [34,68,136,17,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,384,256] 13 (by decide) (choices 1) [1,32] r4647 c4647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1494
  · exact u1495

def b4648 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 140 56 208 33 321 385 257), lower := (rows 35 70 140 56 208 33 64 128 256), losses := [] }

theorem u4648 : Upper (D 9) (R 9) [34,68,136,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4648 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4649 : Route 9 := (fun mask => (mask,id))

def c4649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4649 : Upper (D 9) (R 9) [34,68,136,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,192,256] 13 (by decide) (choices 1) [1,256] r4649 c4649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1496
  · exact u1497

def b4650 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 454, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 56 273 33 448 448 448), lower := (rows 35 70 140 56 273 33 64 128 256), losses := [] }

theorem u4650 : Upper (D 9) (R 9) [34,68,136,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4650 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4651 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 56 273 96 449 385 385), lower := (rows 35 70 140 56 273 96 64 128 256), losses := [] }

theorem u4651 : Upper (D 9) (R 9) [34,68,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4651 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4652 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,5),(2,5),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 56 273 160 321 449 321), lower := (rows 35 70 140 56 273 160 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 17 0 81 145 273), good := (rows 467 70 142 478 465 128 64 128 256) }] }

theorem u4652 : Upper (D 9) (R 9) [34,68,136,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4652 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4653 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 35 70 140 56 273 288 193 193 449), lower := (rows 35 70 140 56 273 288 64 128 256), losses := [] }

theorem u4653 : Upper (D 9) (R 9) [34,68,136,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4653 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4654 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,5),(4,5)], upper := (rows 35 70 140 56 336 33 449 385 385), lower := (rows 35 70 140 56 336 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 57 0 97 161 289), good := (rows 467 70 158 478 336 465 64 128 256) }] }

theorem u4654 : Upper (D 9) (R 9) [34,68,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4654 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4655 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,8),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 56 336 160 321 385 257), lower := (rows 35 70 140 56 336 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 172 56 80 160 64 160 0) }] }

theorem u4655 : Upper (D 9) (R 9) [34,68,136,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4655 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4656 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 35 70 140 56 336 288 193 129 385), lower := (rows 35 70 140 56 336 288 64 128 256), losses := [] }

theorem u4656 : Upper (D 9) (R 9) [34,68,136,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4656 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4657 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,5)], upper := (rows 35 70 140 56 400 33 321 449 321), lower := (rows 35 70 140 56 400 33 64 128 256), losses := [] }

theorem u4657 : Upper (D 9) (R 9) [34,68,136,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4657 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4658 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 56 400 96 321 385 257), lower := (rows 35 70 140 56 400 96 64 128 256), losses := [] }

theorem u4658 : Upper (D 9) (R 9) [34,68,136,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4658 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4659 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 65 },{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 70 140 56 400 288 65 193 321), lower := (rows 35 70 140 56 400 288 64 128 256), losses := [] }

theorem u4659 : Upper (D 9) (R 9) [34,68,136,48,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4659 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4660 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,6)], upper := (rows 35 70 140 73 145 48 352 416 288), lower := (rows 35 70 140 73 145 48 64 128 256), losses := [] }

theorem u4660 : Upper (D 9) (R 9) [34,68,136,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4660 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4661 : Route 9 := (fun mask => (mask,id))

def c4661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u4661 : Upper (D 9) (R 9) [34,68,136,65,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,129,256] 13 (by decide) (choices 1) [16,32,256] r4661 c4661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1498
  · exact u1499
  · exact u1500

def b4662 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 140 73 176 33 336 400 272), lower := (rows 35 70 140 73 176 33 64 128 256), losses := [] }

theorem u4662 : Upper (D 9) (R 9) [34,68,136,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4662 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4663 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 140 73 176 48 321 385 257), lower := (rows 35 70 140 73 176 48 64 128 256), losses := [] }

theorem u4663 : Upper (D 9) (R 9) [34,68,136,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4663 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4664 : Route 9 := (fun mask => (mask,id))

def c4664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4664 : Upper (D 9) (R 9) [34,68,136,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,160,256] 13 (by decide) (choices 1) [1,16,256] r4664 c4664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1501
  · exact u1502
  · exact u1503

def b4665 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 35 70 140 73 273 48 480 416 416), lower := (rows 35 70 140 73 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 113 177 305), good := (rows 482 70 142 462 496 496 64 128 256) }] }

theorem u4665 : Upper (D 9) (R 9) [34,68,136,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4665 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4666 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 73 273 160 368 432 304), lower := (rows 35 70 140 73 273 160 64 128 256), losses := [] }

theorem u4666 : Upper (D 9) (R 9) [34,68,136,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4666 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4667 : Route 9 := (fun mask => (mask,id))

def c4667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4667 : Upper (D 9) (R 9) [34,68,136,65,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,257,256] 13 (by decide) (choices 1) [16,32,128] r4667 c4667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1504
  · exact u1505
  · exact u1506

def b4668 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 140 73 304 33 464 400 400), lower := (rows 35 70 140 73 304 33 64 128 256), losses := [] }

theorem u4668 : Upper (D 9) (R 9) [34,68,136,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4668 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4669 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 140 73 304 48 449 385 385), lower := (rows 35 70 140 73 304 48 64 128 256), losses := [] }

theorem u4669 : Upper (D 9) (R 9) [34,68,136,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4669 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4670 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 73 304 160 337 401 273), lower := (rows 35 70 140 73 304 160 64 128 256), losses := [] }

theorem u4670 : Upper (D 9) (R 9) [34,68,136,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4670 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4671 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 140 73 304 288 209 145 401), lower := (rows 35 70 140 73 304 288 64 128 256), losses := [] }

theorem u4671 : Upper (D 9) (R 9) [34,68,136,65,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4671 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4672 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 140 73 400 33 368 432 304), lower := (rows 35 70 140 73 400 33 64 128 256), losses := [] }

theorem u4672 : Upper (D 9) (R 9) [34,68,136,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4672 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4673 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,6)], upper := (rows 35 70 140 73 400 48 353 417 289), lower := (rows 35 70 140 73 400 48 64 128 256), losses := [] }

theorem u4673 : Upper (D 9) (R 9) [34,68,136,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4673 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4674 : Route 9 := (fun mask => (mask,id))

def c4674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4674 : Upper (D 9) (R 9) [34,68,136,65,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,384,256] 13 (by decide) (choices 1) [1,16,32] r4674 c4674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1507
  · exact u1508
  · exact u1509

def b4675 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,6)], upper := (rows 35 70 140 88 176 33 321 385 257), lower := (rows 35 70 140 88 176 33 64 128 256), losses := [] }

theorem u4675 : Upper (D 9) (R 9) [34,68,136,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4675 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4676 : Route 9 := (fun mask => (mask,id))

def c4676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4676 : Upper (D 9) (R 9) [34,68,136,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,160,256] 13 (by decide) (choices 1) [1,256] r4676 c4676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1510
  · exact u1511

def b4677 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,6)], upper := (rows 35 70 140 88 273 33 480 416 416), lower := (rows 35 70 140 88 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 26 20 24 16 32 97 161 289), good := (rows 482 70 142 94 478 480 64 128 256) }] }

theorem u4677 : Upper (D 9) (R 9) [34,68,136,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4677 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4678 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 88 273 160 353 417 289), lower := (rows 35 70 140 88 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 19 191 0 147 275), good := (rows 435 439 172 444 433 160 0 160 256) }] }

theorem u4678 : Upper (D 9) (R 9) [34,68,136,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4678 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4679 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,8),(2,6),(2,8),(4,6)], upper := (rows 35 70 140 88 273 288 225 161 417), lower := (rows 35 70 140 88 273 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 19 315 0 147 275), good := (rows 435 439 172 444 433 288 0 128 288) },{ target := 8, region := (rows 1 26 20 24 16 32 65 129 0), good := (rows 227 70 142 94 223 32 64 128 0) }] }

theorem u4679 : Upper (D 9) (R 9) [34,68,136,80,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4679 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4679
end Delivery.IrregularNine14.P09
