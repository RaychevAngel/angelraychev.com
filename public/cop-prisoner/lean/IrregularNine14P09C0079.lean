import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0025
import IrregularNine14P09C0026

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4740 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(3,7),(4,5)], upper := (rows 35 70 140 296 145 33 336 464 336), lower := (rows 35 70 140 296 145 33 64 128 256), losses := [] }

theorem u4740 : Upper (D 9) (R 9) [34,68,136,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4740 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4741 : Route 9 := (fun mask => (mask,id))

def c4741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4741 : Upper (D 9) (R 9) [34,68,136,288,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,129,16] 13 (by decide) (choices 1) [1,256] r4741 c4741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1555
  · exact u1556

def b4742 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 296 145 96 337 401 273), lower := (rows 35 70 140 296 145 96 64 128 256), losses := [] }

theorem u4742 : Upper (D 9) (R 9) [34,68,136,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4742 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4743 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 70 140 296 145 288 81 209 337), lower := (rows 35 70 140 296 145 288 64 128 256), losses := [] }

theorem u4743 : Upper (D 9) (R 9) [34,68,136,288,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4743 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4744 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(1,5),(4,5)], upper := (rows 35 70 140 296 208 33 337 401 273), lower := (rows 35 70 140 296 208 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 57 0 97 161 289), good := (rows 467 70 158 478 208 465 64 128 256) }] }

theorem u4744 : Upper (D 9) (R 9) [34,68,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4744 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4745 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 264, targets := 128 }], pairs := [(2,6),(3,6),(3,7),(4,5)], upper := (rows 35 70 140 296 208 48 321 385 257), lower := (rows 35 70 140 296 208 48 64 128 256), losses := [] }

theorem u4745 : Upper (D 9) (R 9) [34,68,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4745 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4746 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 70 140 296 208 288 81 145 273), lower := (rows 35 70 140 296 208 288 64 128 256), losses := [] }

theorem u4746 : Upper (D 9) (R 9) [34,68,136,288,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4746 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4747 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 4, region := 40, targets := 192 }], pairs := [(0,6),(0,7),(0,8),(3,6),(3,7)], upper := (rows 35 70 140 296 273 33 208 208 464), lower := (rows 35 70 140 296 273 33 64 128 256), losses := [] }

theorem u4747 : Upper (D 9) (R 9) [34,68,136,288,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4747 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4748 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 140 296 273 48 193 193 449), lower := (rows 35 70 140 296 273 48 64 128 256), losses := [] }

theorem u4748 : Upper (D 9) (R 9) [34,68,136,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4748 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4749 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 296 273 96 209 145 401), lower := (rows 35 70 140 296 273 96 64 128 256), losses := [] }

theorem u4749 : Upper (D 9) (R 9) [34,68,136,288,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4749 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4750 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,6),(0,8),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 296 273 160 81 209 337), lower := (rows 35 70 140 296 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 296 273 160 0 160 256) },{ target := 8, region := (rows 3 2 4 8 16 180 80 144 0), good := (rows 35 103 172 40 241 160 64 160 0) }] }

theorem u4750 : Upper (D 9) (R 9) [34,68,136,288,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4750 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4751 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(1,5),(4,5)], upper := (rows 35 70 140 296 336 33 209 145 401), lower := (rows 35 70 140 296 336 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 57 0 97 161 289), good := (rows 467 70 158 478 336 465 64 128 256) }] }

theorem u4751 : Upper (D 9) (R 9) [34,68,136,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4751 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4752 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 140 296 336 48 193 129 385), lower := (rows 35 70 140 296 336 48 64 128 256), losses := [] }

theorem u4752 : Upper (D 9) (R 9) [34,68,136,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4752 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4753 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,6),(0,8),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 296 336 160 81 145 273), lower := (rows 35 70 140 296 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 296 272 160 0 160 256) },{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 172 40 80 160 64 160 0) }] }

theorem u4753 : Upper (D 9) (R 9) [34,68,136,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4753 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4754 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(1,5),(4,5)], upper := (rows 35 70 140 296 400 33 81 209 337), lower := (rows 35 70 140 296 400 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 57 0 97 161 289), good := (rows 467 70 158 478 400 465 64 128 256) }] }

theorem u4754 : Upper (D 9) (R 9) [34,68,136,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4754 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4755 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 70 140 296 400 48 65 193 321), lower := (rows 35 70 140 296 400 48 64 128 256), losses := [] }

theorem u4755 : Upper (D 9) (R 9) [34,68,136,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4755 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4756 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 296 400 96 81 145 273), lower := (rows 35 70 140 296 400 96 64 128 256), losses := [] }

theorem u4756 : Upper (D 9) (R 9) [34,68,136,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4756 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4757 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(3,7),(4,6)], upper := (rows 35 70 140 328 145 33 368 432 304), lower := (rows 35 70 140 328 145 33 64 128 256), losses := [] }

theorem u4757 : Upper (D 9) (R 9) [34,68,136,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4757 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4758 : Route 9 := (fun mask => (mask,id))

def c4758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4758 : Upper (D 9) (R 9) [34,68,136,320,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,129,16] 13 (by decide) (choices 1) [1,32,256] r4758 c4758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1557
  · exact u1558
  · exact u1559

def r4759 : Route 9 := (fun mask => (mask,id))

def c4759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4759 : Upper (D 9) (R 9) [34,68,136,320,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,129,256] 13 (by decide) (choices 1) [1,16,32] r4759 c4759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1560
  · exact u1561
  · exact u1562

def r4760 : Route 9 := (fun mask => (mask,id))

def c4760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4760 : Upper (D 9) (R 9) [34,68,136,320,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,160,1] 13 (by decide) (choices 1) [1,16,256] r4760 c4760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1563
  · exact u1564
  · exact u1565

def b4761 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 140 328 176 48 321 385 257), lower := (rows 35 70 140 328 176 48 64 128 256), losses := [] }

theorem u4761 : Upper (D 9) (R 9) [34,68,136,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4761 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4762 : Route 9 := (fun mask => (mask,id))

def c4762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4762 : Upper (D 9) (R 9) [34,68,136,320,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,160,256] 13 (by decide) (choices 1) [1,16] r4762 c4762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1566
  · exact u1567

def r4763 : Route 9 := (fun mask => (mask,id))

def c4763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4763 : Upper (D 9) (R 9) [34,68,136,320,257,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,257,1] 13 (by decide) (choices 1) [16,32,128] r4763 c4763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1568
  · exact u1569
  · exact u1570

def r4764 : Route 9 := (fun mask => (mask,id))

def c4764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4764 : Upper (D 9) (R 9) [34,68,136,320,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,257,16] 13 (by decide) (choices 1) [1,32,128] r4764 c4764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1571
  · exact u1572
  · exact u1573

def b4765 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 328 273 160 113 177 305), lower := (rows 35 70 140 328 273 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 8 16 180 80 144 0), good := (rows 35 103 172 72 241 160 64 160 0) }] }

theorem u4765 : Upper (D 9) (R 9) [34,68,136,320,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4765 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4766 : Route 9 := (fun mask => (mask,id))

def c4766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4766 : Upper (D 9) (R 9) [34,68,136,320,288,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,288,1] 13 (by decide) (choices 1) [1,16,128] r4766 c4766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1574
  · exact u1575
  · exact u1576

def b4767 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 140 328 304 48 193 129 385), lower := (rows 35 70 140 328 304 48 64 128 256), losses := [] }

theorem u4767 : Upper (D 9) (R 9) [34,68,136,320,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4767 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4768 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 328 304 160 81 145 273), lower := (rows 35 70 140 328 304 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 8 16 164 64 128 0), good := (rows 35 103 172 72 48 160 64 160 0) }] }

theorem u4768 : Upper (D 9) (R 9) [34,68,136,320,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4768 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4769 : Route 9 := (fun mask => (mask,id))

def c4769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4769 : Upper (D 9) (R 9) [34,68,136,320,384,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,384,1] 13 (by decide) (choices 1) [1,16,32] r4769 c4769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1577
  · exact u1578
  · exact u1579

def r4770 : Route 9 := (fun mask => (mask,id))

def c4770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4770 : Upper (D 9) (R 9) [34,68,136,320,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,384,16] 13 (by decide) (choices 1) [1,32] r4770 c4770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1580
  · exact u1581

def b4771 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,7)], upper := (rows 35 70 164 25 88 33 448 384 384), lower := (rows 35 70 164 25 88 33 64 128 256), losses := [] }

theorem u4771 : Upper (D 9) (R 9) [34,68,160,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4771 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4772 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 70 164 25 88 160 321 385 257), lower := (rows 35 70 164 25 88 160 64 128 256), losses := [] }

theorem u4772 : Upper (D 9) (R 9) [34,68,160,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4772 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4773 : Route 9 := (fun mask => (mask,id))

def c4773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4773 : Upper (D 9) (R 9) [34,68,160,17,72,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,72,256] 13 (by decide) (choices 1) [1,128,256] r4773 c4773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1582
  · exact u1583
  · exact u1584

def b4774 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(3,5),(4,5)], upper := (rows 35 70 164 25 152 33 320 448 320), lower := (rows 35 70 164 25 152 33 64 128 256), losses := [] }

theorem u4774 : Upper (D 9) (R 9) [34,68,160,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4774 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4775 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 164 25 152 96 321 385 257), lower := (rows 35 70 164 25 152 96 64 128 256), losses := [] }

theorem u4775 : Upper (D 9) (R 9) [34,68,160,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4775 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4776 : Route 9 := (fun mask => (mask,id))

def c4776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4776 : Upper (D 9) (R 9) [34,68,160,17,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,136,256] 13 (by decide) (choices 1) [1,256] r4776 c4776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1585
  · exact u1586

def b4777 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(3,8)], upper := (rows 35 70 164 25 208 33 328 392 264), lower := (rows 35 70 164 25 208 33 64 128 256), losses := [] }

theorem u4777 : Upper (D 9) (R 9) [34,68,160,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4777 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4778 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 164 25 208 40 321 385 257), lower := (rows 35 70 164 25 208 40 64 128 256), losses := [] }

theorem u4778 : Upper (D 9) (R 9) [34,68,160,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4778 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4779 : Route 9 := (fun mask => (mask,id))

def c4779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4779 : Upper (D 9) (R 9) [34,68,160,17,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,192,256] 13 (by decide) (choices 1) [1,8,256] r4779 c4779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1587
  · exact u1588
  · exact u1589

def b4780 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 454, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(2,0)], upper := (rows 35 70 164 25 280 33 448 448 448), lower := (rows 35 70 164 25 280 33 64 128 256), losses := [] }

theorem u4780 : Upper (D 9) (R 9) [34,68,160,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4780 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4781 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 164 25 280 96 449 385 385), lower := (rows 35 70 164 25 280 96 64 128 256), losses := [] }

theorem u4781 : Upper (D 9) (R 9) [34,68,160,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4781 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4782 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 70 164 25 280 160 321 449 321), lower := (rows 35 70 164 25 280 160 64 128 256), losses := [] }

theorem u4782 : Upper (D 9) (R 9) [34,68,160,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4782 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4783 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 35 70 164 25 280 288 193 193 449), lower := (rows 35 70 164 25 280 288 64 128 256), losses := [] }

theorem u4783 : Upper (D 9) (R 9) [34,68,160,17,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4783 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4784 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 25 336 33 456 392 392), lower := (rows 35 70 164 25 336 33 64 128 256), losses := [] }

theorem u4784 : Upper (D 9) (R 9) [34,68,160,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4784 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4785 : Route 9 := (fun mask => (mask,id))

def c4785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4785 : Upper (D 9) (R 9) [34,68,160,17,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,320,8] 13 (by decide) (choices 1) [1,128,256] r4785 c4785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1590
  · exact u1591
  · exact u1592

def b4786 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 70 164 25 336 160 329 393 265), lower := (rows 35 70 164 25 336 160 64 128 256), losses := [] }

theorem u4786 : Upper (D 9) (R 9) [34,68,160,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4786 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4787 : Route 9 := (fun mask => (mask,id))

def c4787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4787 : Upper (D 9) (R 9) [34,68,160,17,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,320,256] 13 (by decide) (choices 1) [1,8,128] r4787 c4787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1593
  · exact u1594
  · exact u1595

def b4788 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 25 400 33 328 456 328), lower := (rows 35 70 164 25 400 33 64 128 256), losses := [] }

theorem u4788 : Upper (D 9) (R 9) [34,68,160,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4788 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4789 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 164 25 400 40 321 449 321), lower := (rows 35 70 164 25 400 40 64 128 256), losses := [] }

theorem u4789 : Upper (D 9) (R 9) [34,68,160,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4789 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4790 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 164 25 400 96 329 393 265), lower := (rows 35 70 164 25 400 96 64 128 256), losses := [] }

theorem u4790 : Upper (D 9) (R 9) [34,68,160,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4790 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4791 : Route 9 := (fun mask => (mask,id))

def c4791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4791 : Upper (D 9) (R 9) [34,68,160,17,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,384,256] 13 (by decide) (choices 1) [1,8] r4791 c4791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1596
  · exact u1597

def b4792 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(3,5),(3,7),(3,8)], upper := (rows 35 70 164 73 152 33 336 400 272), lower := (rows 35 70 164 73 152 33 64 128 256), losses := [] }

theorem u4792 : Upper (D 9) (R 9) [34,68,160,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4792 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4793 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 35 70 164 73 152 48 321 385 257), lower := (rows 35 70 164 73 152 48 64 128 256), losses := [] }

theorem u4793 : Upper (D 9) (R 9) [34,68,160,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4793 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4794 : Route 9 := (fun mask => (mask,id))

def c4794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4794 : Upper (D 9) (R 9) [34,68,160,65,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,136,256] 13 (by decide) (choices 1) [1,16,256] r4794 c4794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1598
  · exact u1599
  · exact u1600

def b4795 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 164 73 273 40 464 400 400), lower := (rows 35 70 164 73 273 40 64 128 256), losses := [] }

theorem u4795 : Upper (D 9) (R 9) [34,68,160,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4795 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4796 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 164 73 273 48 456 392 392), lower := (rows 35 70 164 73 273 48 64 128 256), losses := [] }

theorem u4796 : Upper (D 9) (R 9) [34,68,160,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4796 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4797 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 70 164 73 273 160 344 408 280), lower := (rows 35 70 164 73 273 160 64 128 256), losses := [] }

theorem u4797 : Upper (D 9) (R 9) [34,68,160,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4797 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4798 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 200, targets := 256 }], pairs := [(2,6),(3,5),(3,8),(4,5),(4,6)], upper := (rows 35 70 164 73 273 288 216 152 408), lower := (rows 35 70 164 73 273 288 64 128 256), losses := [] }

theorem u4798 : Upper (D 9) (R 9) [34,68,160,65,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4798 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4799 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(3,5),(3,7),(3,8)], upper := (rows 35 70 164 73 280 33 464 400 400), lower := (rows 35 70 164 73 280 33 64 128 256), losses := [] }

theorem u4799 : Upper (D 9) (R 9) [34,68,160,65,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4799 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4799
end Delivery.IrregularNine14.P09
