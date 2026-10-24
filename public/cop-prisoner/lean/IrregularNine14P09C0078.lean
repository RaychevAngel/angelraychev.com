import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0025

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4680 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,6),(0,7),(0,8),(1,5),(4,6)], upper := (rows 35 70 140 88 304 33 449 385 385), lower := (rows 35 70 140 88 304 33 64 128 256), losses := [{ target := 5, region := (rows 1 26 20 24 16 0 97 161 289), good := (rows 451 70 142 94 478 449 64 128 256) }] }

theorem u4680 : Upper (D 9) (R 9) [34,68,136,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4680 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4681 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 88 304 160 321 385 257), lower := (rows 35 70 140 88 304 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 172 88 48 160 64 160 0) }] }

theorem u4681 : Upper (D 9) (R 9) [34,68,136,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4681 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4682 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 140 88 304 288 193 129 385), lower := (rows 35 70 140 88 304 288 64 128 256), losses := [] }

theorem u4682 : Upper (D 9) (R 9) [34,68,136,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4682 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4683 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,6)], upper := (rows 35 70 140 88 400 33 353 417 289), lower := (rows 35 70 140 88 400 33 64 128 256), losses := [] }

theorem u4683 : Upper (D 9) (R 9) [34,68,136,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4683 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4684 : Route 9 := (fun mask => (mask,id))

def c4684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4684 : Upper (D 9) (R 9) [34,68,136,80,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,384,256] 13 (by decide) (choices 1) [1,32] r4684 c4684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1512
  · exact u1513

def b4685 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 140 104 145 33 336 400 272), lower := (rows 35 70 140 104 145 33 64 128 256), losses := [] }

theorem u4685 : Upper (D 9) (R 9) [34,68,136,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4685 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4686 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(3,7),(4,5),(4,6)], upper := (rows 35 70 140 104 145 48 321 385 257), lower := (rows 35 70 140 104 145 48 64 128 256), losses := [] }

theorem u4686 : Upper (D 9) (R 9) [34,68,136,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4686 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4687 : Route 9 := (fun mask => (mask,id))

def c4687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4687 : Upper (D 9) (R 9) [34,68,136,96,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,129,256] 13 (by decide) (choices 1) [1,16,256] r4687 c4687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1514
  · exact u1515
  · exact u1516

def b4688 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 140 104 273 33 464 400 400), lower := (rows 35 70 140 104 273 33 64 128 256), losses := [] }

theorem u4688 : Upper (D 9) (R 9) [34,68,136,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4688 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4689 : Route 9 := (fun mask => (mask,id))

def c4689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4689 : Upper (D 9) (R 9) [34,68,136,96,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,257,16] 13 (by decide) (choices 1) [1,128,256] r4689 c4689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1517
  · exact u1518
  · exact u1519

def b4690 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 272, targets := 32 }], pairs := [(0,6),(3,7),(4,5),(4,6),(4,7)], upper := (rows 35 70 140 104 273 160 337 401 273), lower := (rows 35 70 140 104 273 160 64 128 256), losses := [] }

theorem u4690 : Upper (D 9) (R 9) [34,68,136,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4690 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4691 : Route 9 := (fun mask => (mask,id))

def c4691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4691 : Upper (D 9) (R 9) [34,68,136,96,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,257,256] 13 (by decide) (choices 1) [1,16,128] r4691 c4691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1520
  · exact u1521
  · exact u1522

def b4692 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 140 104 400 33 337 401 273), lower := (rows 35 70 140 104 400 33 64 128 256), losses := [] }

theorem u4692 : Upper (D 9) (R 9) [34,68,136,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4692 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4693 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(3,7),(4,5),(4,6)], upper := (rows 35 70 140 104 400 48 321 385 257), lower := (rows 35 70 140 104 400 48 64 128 256), losses := [] }

theorem u4693 : Upper (D 9) (R 9) [34,68,136,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4693 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4694 : Route 9 := (fun mask => (mask,id))

def c4694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4694 : Upper (D 9) (R 9) [34,68,136,96,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,384,256] 13 (by decide) (choices 1) [1,16] r4694 c4694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1523
  · exact u1524

def b4695 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 70 140 265 81 48 480 416 416), lower := (rows 35 70 140 265 81 48 64 128 256), losses := [] }

theorem u4695 : Upper (D 9) (R 9) [34,68,136,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4695 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4696 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 4, region := 428, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(3,7),(4,7)], upper := (rows 35 70 140 265 81 160 368 432 304), lower := (rows 35 70 140 265 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 180 0 144 272), good := (rows 35 39 172 265 445 160 0 160 256) }] }

theorem u4696 : Upper (D 9) (R 9) [34,68,136,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4696 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4697 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 },{ cop := 0, region := 208, targets := 256 }], pairs := [(1,8),(2,6),(2,8),(3,6),(4,8)], upper := (rows 35 70 140 265 81 288 240 176 432), lower := (rows 35 70 140 265 81 288 64 128 256), losses := [{ target := 8, region := (rows 1 10 12 8 25 32 65 129 0), good := (rows 243 70 158 223 209 32 64 128 0) }] }

theorem u4697 : Upper (D 9) (R 9) [34,68,136,257,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4697 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4698 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 35 70 140 265 112 33 464 400 400), lower := (rows 35 70 140 265 112 33 64 128 256), losses := [] }

theorem u4698 : Upper (D 9) (R 9) [34,68,136,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4698 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4699 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 70 140 265 112 48 449 385 385), lower := (rows 35 70 140 265 112 48 64 128 256), losses := [] }

theorem u4699 : Upper (D 9) (R 9) [34,68,136,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4699 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4700 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,0),(4,7)], upper := (rows 35 70 140 265 112 160 337 401 273), lower := (rows 35 70 140 265 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 64 128 256), good := (rows 50 118 172 264 112 160 64 160 256) },{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 265 48 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 17 32 73 0 265), good := (rows 379 70 334 345 112 32 64 0 256) }] }

theorem u4700 : Upper (D 9) (R 9) [34,68,136,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4700 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4701 : Route 9 := (fun mask => (mask,id))

def c4701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4701 : Upper (D 9) (R 9) [34,68,136,257,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,96,256] 13 (by decide) (choices 1) [1,16,128] r4701 c4701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1525
  · exact u1526
  · exact u1527

def r4702 : Route 9 := (fun mask => (mask,id))

def c4702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4702 : Upper (D 9) (R 9) [34,68,136,257,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,129,16] 13 (by decide) (choices 1) [32,256] r4702 c4702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1528
  · exact u1529

def b4703 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 145 96 368 432 304), lower := (rows 35 70 140 265 145 96 64 128 256), losses := [] }

theorem u4703 : Upper (D 9) (R 9) [34,68,136,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4703 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4704 : Route 9 := (fun mask => (mask,id))

def c4704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4704 : Upper (D 9) (R 9) [34,68,136,257,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,129,256] 13 (by decide) (choices 1) [16,32] r4704 c4704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1530
  · exact u1531

def b4705 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,0)], upper := (rows 35 70 140 265 176 33 336 464 336), lower := (rows 35 70 140 265 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 14 12 8 49 32 121 185 313), good := (rows 498 70 462 478 496 496 64 128 256) }] }

theorem u4705 : Upper (D 9) (R 9) [34,68,136,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4705 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4706 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 140 265 176 48 321 449 321), lower := (rows 35 70 140 265 176 48 64 128 256), losses := [] }

theorem u4706 : Upper (D 9) (R 9) [34,68,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4706 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4707 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 176 96 337 401 273), lower := (rows 35 70 140 265 176 96 64 128 256), losses := [] }

theorem u4707 : Upper (D 9) (R 9) [34,68,136,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4707 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4708 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 256 }], pairs := [(1,8),(2,8),(4,0),(4,6),(4,8)], upper := (rows 35 70 140 265 176 288 81 209 337), lower := (rows 35 70 140 265 176 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 64 128 256), good := (rows 34 86 188 296 176 288 64 128 288) },{ target := 6, region := (rows 1 2 4 8 20 296 0 128 256), good := (rows 35 22 188 297 176 288 0 128 288) },{ target := 8, region := (rows 1 14 12 8 17 32 73 137 0), good := (rows 243 70 206 223 176 32 64 128 0) }] }

theorem u4708 : Upper (D 9) (R 9) [34,68,136,257,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4708 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4709 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,0)], upper := (rows 35 70 140 265 208 33 368 432 304), lower := (rows 35 70 140 265 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 57 32 97 161 289), good := (rows 498 70 158 478 208 496 64 128 256) }] }

theorem u4709 : Upper (D 9) (R 9) [34,68,136,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4709 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4710 : Route 9 := (fun mask => (mask,id))

def c4710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4710 : Upper (D 9) (R 9) [34,68,136,257,192,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,192,16] 13 (by decide) (choices 1) [1,32,256] r4710 c4710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1532
  · exact u1533
  · exact u1534

def r4711 : Route 9 := (fun mask => (mask,id))

def c4711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4711 : Upper (D 9) (R 9) [34,68,136,257,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,192,256] 13 (by decide) (choices 1) [1,16,32] r4711 c4711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1535
  · exact u1536
  · exact u1537

def b4712 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 3, region := 48, targets := 192 }], pairs := [(0,6),(0,7),(0,8),(4,6),(4,7)], upper := (rows 35 70 140 265 304 33 208 208 464), lower := (rows 35 70 140 265 304 33 64 128 256), losses := [] }

theorem u4712 : Upper (D 9) (R 9) [34,68,136,257,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4712 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4713 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 140 265 304 48 193 193 449), lower := (rows 35 70 140 265 304 48 64 128 256), losses := [] }

theorem u4713 : Upper (D 9) (R 9) [34,68,136,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4713 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4714 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 304 96 209 145 401), lower := (rows 35 70 140 265 304 96 64 128 256), losses := [] }

theorem u4714 : Upper (D 9) (R 9) [34,68,136,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4714 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4715 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,7),(3,7),(4,7)], upper := (rows 35 70 140 265 304 160 81 209 337), lower := (rows 35 70 140 265 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 265 304 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 17 32 73 0 265), good := (rows 379 70 334 345 304 32 64 0 256) },{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 172 9 48 160 64 160 0) }] }

theorem u4715 : Upper (D 9) (R 9) [34,68,136,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4715 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4716 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,0)], upper := (rows 35 70 140 265 336 33 240 176 432), lower := (rows 35 70 140 265 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 57 32 97 161 289), good := (rows 498 70 158 478 336 496 64 128 256) }] }

theorem u4716 : Upper (D 9) (R 9) [34,68,136,257,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4716 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4717 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(1,8),(2,6),(2,8),(3,6)], upper := (rows 35 70 140 265 336 48 225 161 417), lower := (rows 35 70 140 265 336 48 64 128 256), losses := [{ target := 8, region := (rows 1 10 12 8 16 48 65 129 0), good := (rows 227 70 142 207 112 48 64 128 0) }] }

theorem u4717 : Upper (D 9) (R 9) [34,68,136,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4717 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4718 : Route 9 := (fun mask => (mask,id))

def c4718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4718 : Upper (D 9) (R 9) [34,68,136,257,320,128] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,320,128] 13 (by decide) (choices 1) [1,16,32] r4718 c4718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1538
  · exact u1539
  · exact u1540

def b4719 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,0)], upper := (rows 35 70 140 265 400 33 112 240 368), lower := (rows 35 70 140 265 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 57 32 97 161 289), good := (rows 498 70 158 478 400 496 64 128 256) }] }

theorem u4719 : Upper (D 9) (R 9) [34,68,136,257,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4719 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4720 : Route 9 := (fun mask => (mask,id))

def c4720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4720 : Upper (D 9) (R 9) [34,68,136,257,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,384,16] 13 (by decide) (choices 1) [1,32] r4720 c4720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1541
  · exact u1542

def b4721 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 400 96 113 177 305), lower := (rows 35 70 140 265 400 96 64 128 256), losses := [] }

theorem u4721 : Upper (D 9) (R 9) [34,68,136,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4721 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4722 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 4, region := 428, targets := 64 }], pairs := [(0,7),(0,8),(2,6),(4,7),(4,8)], upper := (rows 35 70 140 280 81 33 480 416 416), lower := (rows 35 70 140 280 81 33 64 128 256), losses := [] }

theorem u4722 : Upper (D 9) (R 9) [34,68,136,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4722 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4723 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 4, region := 428, targets := 64 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(3,7),(4,7)], upper := (rows 35 70 140 280 81 160 353 417 289), lower := (rows 35 70 140 280 81 160 64 128 256), losses := [] }

theorem u4723 : Upper (D 9) (R 9) [34,68,136,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4723 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4724 : Route 9 := (fun mask => (mask,id))

def c4724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4724 : Upper (D 9) (R 9) [34,68,136,272,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,65,256] 13 (by decide) (choices 1) [1,32,128] r4724 c4724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1543
  · exact u1544
  · exact u1545

def b4725 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 70 140 280 112 33 449 385 385), lower := (rows 35 70 140 280 112 33 64 128 256), losses := [] }

theorem u4725 : Upper (D 9) (R 9) [34,68,136,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4725 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4726 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,8),(3,7),(4,0),(4,7)], upper := (rows 35 70 140 280 112 160 321 385 257), lower := (rows 35 70 140 280 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 64 128 256), good := (rows 50 118 172 280 112 160 64 160 256) },{ target := 8, region := (rows 3 2 4 8 18 164 64 128 0), good := (rows 51 119 172 24 112 160 64 160 0) }] }

theorem u4726 : Upper (D 9) (R 9) [34,68,136,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4726 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4727 : Route 9 := (fun mask => (mask,id))

def c4727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4727 : Upper (D 9) (R 9) [34,68,136,272,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,96,256] 13 (by decide) (choices 1) [1,128] r4727 c4727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1546
  · exact u1547

def b4728 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,7),(3,7)], upper := (rows 35 70 140 280 145 33 352 480 352), lower := (rows 35 70 140 280 145 33 64 128 256), losses := [] }

theorem u4728 : Upper (D 9) (R 9) [34,68,136,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4728 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4729 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 280 145 96 353 417 289), lower := (rows 35 70 140 280 145 96 64 128 256), losses := [] }

theorem u4729 : Upper (D 9) (R 9) [34,68,136,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4729 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4730 : Route 9 := (fun mask => (mask,id))

def c4730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4730 : Upper (D 9) (R 9) [34,68,136,272,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,129,256] 13 (by decide) (choices 1) [1,32] r4730 c4730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1548
  · exact u1549

def b4731 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,5),(1,7)], upper := (rows 35 70 140 280 176 33 321 449 321), lower := (rows 35 70 140 280 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 20 24 16 0 97 161 289), good := (rows 451 70 140 286 478 449 64 128 256) }] }

theorem u4731 : Upper (D 9) (R 9) [34,68,136,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4731 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4732 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 280 176 96 321 385 257), lower := (rows 35 70 140 280 176 96 64 128 256), losses := [] }

theorem u4732 : Upper (D 9) (R 9) [34,68,136,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4732 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4733 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 256 }], pairs := [(0,7),(1,7),(4,0),(4,6),(4,8)], upper := (rows 35 70 140 280 176 288 65 193 321), lower := (rows 35 70 140 280 176 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 64 128 256), good := (rows 34 86 188 312 176 288 64 128 288) },{ target := 6, region := (rows 1 2 4 8 20 296 0 128 256), good := (rows 35 22 188 312 176 288 0 128 288) }] }

theorem u4733 : Upper (D 9) (R 9) [34,68,136,272,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4733 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4734 : Route 9 := (fun mask => (mask,id))

def c4734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4734 : Upper (D 9) (R 9) [34,68,136,272,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,192,1] 13 (by decide) (choices 1) [1,32,256] r4734 c4734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1550
  · exact u1551
  · exact u1552

def r4735 : Route 9 := (fun mask => (mask,id))

def c4735 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4735 : Upper (D 9) (R 9) [34,68,136,272,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,192,256] 13 (by decide) (choices 1) [1,32] r4735 c4735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1553
  · exact u1554

def b4736 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 4, region := 428, targets := 64 }], pairs := [(0,7),(0,8),(2,6),(4,7),(4,8)], upper := (rows 35 70 140 296 81 33 464 400 400), lower := (rows 35 70 140 296 81 33 64 128 256), losses := [] }

theorem u4736 : Upper (D 9) (R 9) [34,68,136,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4736 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4737 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 70 140 296 81 48 449 385 385), lower := (rows 35 70 140 296 81 48 64 128 256), losses := [] }

theorem u4737 : Upper (D 9) (R 9) [34,68,136,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4737 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4738 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 4, region := 428, targets := 64 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,6),(3,6),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 296 81 160 337 401 273), lower := (rows 35 70 140 296 81 160 64 128 256), losses := [] }

theorem u4738 : Upper (D 9) (R 9) [34,68,136,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4738 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4739 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 70 140 296 81 288 209 145 401), lower := (rows 35 70 140 296 81 288 64 128 256), losses := [] }

theorem u4739 : Upper (D 9) (R 9) [34,68,136,288,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4739 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4739
end Delivery.IrregularNine14.P09
