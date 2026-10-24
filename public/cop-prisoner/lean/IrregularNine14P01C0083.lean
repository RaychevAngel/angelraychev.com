import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0025
import IrregularNine14P01C0026

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4980 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 69 138 18 240 240 240 496), lower := (rows 277 42 69 138 18 32 64 128 256), losses := [] }

theorem u4980 : Upper (D 1) (R 1) [276,40,65,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4980
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4981 : Route 9 := (fun mask => (mask,id))

def c4981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4981 : Upper (D 1) (R 1) [276,40,65,130,32] 13 := by
  apply FastRouting.sound _ _ [276,40,65,130,32] 13 (by decide) (choices 1) [2,16,64,128] r4981 c4981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1556
  · exact u1557
  · exact u1558
  · exact u1559

def b4982 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 69 138 80 178 242 178 434), lower := (rows 277 42 69 138 80 32 64 128 256), losses := [] }

theorem u4982 : Upper (D 1) (R 1) [276,40,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4983 : Route 9 := (fun mask => (mask,id))

def c4983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4983 : Upper (D 1) (R 1) [276,40,65,130,128] 13 := by
  apply FastRouting.sound _ _ [276,40,65,130,128] 13 (by decide) (choices 1) [2,16,64] r4983 c4983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1560
  · exact u1561
  · exact u1562

def b4984 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 70 137 18 240 240 240 496), lower := (rows 277 42 70 137 18 32 64 128 256), losses := [] }

theorem u4984 : Upper (D 1) (R 1) [276,40,66,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4985 : Route 9 := (fun mask => (mask,id))

def c4985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4985 : Upper (D 1) (R 1) [276,40,66,129,32] 13 := by
  apply FastRouting.sound _ _ [276,40,66,129,32] 13 (by decide) (choices 1) [2,16,64,128] r4985 c4985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1563
  · exact u1564
  · exact u1565
  · exact u1566

def b4986 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 70 137 80 178 242 178 434), lower := (rows 277 42 70 137 80 32 64 128 256), losses := [] }

theorem u4986 : Upper (D 1) (R 1) [276,40,66,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4986
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4987 : Route 9 := (fun mask => (mask,id))

def c4987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4987 : Upper (D 1) (R 1) [276,40,66,129,128] 13 := by
  apply FastRouting.sound _ _ [276,40,66,129,128] 13 (by decide) (choices 1) [2,16,64] r4987 c4987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1567
  · exact u1568
  · exact u1569

def b4988 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 277 42 70 152 17 226 226 226 482), lower := (rows 277 42 70 152 17 32 64 128 256), losses := [] }

theorem u4988 : Upper (D 1) (R 1) [276,40,66,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4988
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4989 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 70 152 18 225 225 225 481), lower := (rows 277 42 70 152 18 32 64 128 256), losses := [] }

theorem u4989 : Upper (D 1) (R 1) [276,40,66,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4989
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4990 : Route 9 := (fun mask => (mask,id))

def c4990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4990 : Upper (D 1) (R 1) [276,40,66,144,32] 13 := by
  apply FastRouting.sound _ _ [276,40,66,144,32] 13 (by decide) (choices 1) [1,2,64,128] r4990 c4990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1570
  · exact u1571
  · exact u1572
  · exact u1573

def b4991 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 70 152 80 163 227 163 419), lower := (rows 277 42 70 152 80 32 64 128 256), losses := [] }

theorem u4991 : Upper (D 1) (R 1) [276,40,66,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4991
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4992 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 277 42 70 152 144 99 99 227 355), lower := (rows 277 42 70 152 144 32 64 128 256), losses := [] }

theorem u4992 : Upper (D 1) (R 1) [276,40,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4992
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4993 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 100 11 18 240 208 208 464), lower := (rows 277 42 100 11 18 32 64 128 256), losses := [] }

theorem u4993 : Upper (D 1) (R 1) [276,40,96,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4993
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4994 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 11 80 178 210 146 402), lower := (rows 277 42 100 11 80 32 64 128 256), losses := [] }

theorem u4994 : Upper (D 1) (R 1) [276,40,96,3,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4994
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4995 : Route 9 := (fun mask => (mask,id))

def c4995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4995 : Upper (D 1) (R 1) [276,40,96,3,128] 13 := by
  apply FastRouting.sound _ _ [276,40,96,3,128] 13 (by decide) (choices 1) [2,16,64,128] r4995 c4995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1574
  · exact u1575
  · exact u1576
  · exact u1577

def b4996 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 42 100 26 17 226 194 194 450), lower := (rows 277 42 100 26 17 32 64 128 256), losses := [] }

theorem u4996 : Upper (D 1) (R 1) [276,40,96,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4996
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4997 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 26, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 26 18 225 193 193 449), lower := (rows 277 42 100 26 18 32 64 128 256), losses := [] }

theorem u4997 : Upper (D 1) (R 1) [276,40,96,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4997
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4998 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 26 80 163 195 131 387), lower := (rows 277 42 100 26 80 32 64 128 256), losses := [] }

theorem u4998 : Upper (D 1) (R 1) [276,40,96,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4998
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4999 : Route 9 := (fun mask => (mask,id))

def c4999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4999 : Upper (D 1) (R 1) [276,40,96,18,128] 13 := by
  apply FastRouting.sound _ _ [276,40,96,18,128] 13 (by decide) (choices 1) [1,2,64,128] r4999 c4999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1578
  · exact u1579
  · exact u1580
  · exact u1581

def b5000 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 277 42 100 88 17 162 194 130 386), lower := (rows 277 42 100 88 17 32 64 128 256), losses := [] }

theorem u5000 : Upper (D 1) (R 1) [276,40,96,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5000
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5001 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 26, targets := 128 }], pairs := [(1,7)], upper := (rows 277 42 100 88 18 163 195 131 387), lower := (rows 277 42 100 88 18 32 64 128 256), losses := [] }

theorem u5001 : Upper (D 1) (R 1) [276,40,96,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5001
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5002 : Route 9 := (fun mask => (mask,id))

def c5002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5002 : Upper (D 1) (R 1) [276,40,96,80,128] 13 := by
  apply FastRouting.sound _ _ [276,40,96,80,128] 13 (by decide) (choices 1) [1,2,128] r5002 c5002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1582
  · exact u1583
  · exact u1584

def b5003 : PairBound 9 := { available := 210, camps := [], pairs := [(3,5)], upper := (rows 277 42 100 137 18 242 210 210 466), lower := (rows 277 42 100 137 18 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 18 0 82 146 274), good := (rows 477 474 68 137 466 0 64 128 256) }] }

theorem u5003 : Upper (D 1) (R 1) [276,40,96,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5003
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5004 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 137 80 178 210 146 402), lower := (rows 277 42 100 137 80 32 64 128 256), losses := [] }

theorem u5004 : Upper (D 1) (R 1) [276,40,96,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5004
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5005 : Route 9 := (fun mask => (mask,id))

def c5005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5005 : Upper (D 1) (R 1) [276,40,96,129,128] 13 := by
  apply FastRouting.sound _ _ [276,40,96,129,128] 13 (by decide) (choices 1) [2,16,64] r5005 c5005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1585
  · exact u1586
  · exact u1587

def b5006 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 277 42 100 138 17 242 210 210 466), lower := (rows 277 42 100 138 17 32 64 128 256), losses := [] }

theorem u5006 : Upper (D 1) (R 1) [276,40,96,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5006
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5007 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 100 138 18 241 209 209 465), lower := (rows 277 42 100 138 18 32 64 128 256), losses := [] }

theorem u5007 : Upper (D 1) (R 1) [276,40,96,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5007
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5008 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 138 80 179 211 147 403), lower := (rows 277 42 100 138 80 32 64 128 256), losses := [] }

theorem u5008 : Upper (D 1) (R 1) [276,40,96,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5008
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5009 : Route 9 := (fun mask => (mask,id))

def c5009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5009 : Upper (D 1) (R 1) [276,40,96,130,128] 13 := by
  apply FastRouting.sound _ _ [276,40,96,130,128] 13 (by decide) (choices 1) [1,2,16,64] r5009 c5009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1588
  · exact u1589
  · exact u1590
  · exact u1591

def b5010 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 42 100 152 17 226 194 194 450), lower := (rows 277 42 100 152 17 32 64 128 256), losses := [] }

theorem u5010 : Upper (D 1) (R 1) [276,40,96,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5010
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5011 : Route 9 := (fun mask => (mask,id))

def c5011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5011 : Upper (D 1) (R 1) [276,40,96,144,2] 13 := by
  apply FastRouting.sound _ _ [276,40,96,144,2] 13 (by decide) (choices 1) [1,2,64,128] r5011 c5011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1592
  · exact u1593
  · exact u1594
  · exact u1595

def b5012 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 152 80 163 195 131 387), lower := (rows 277 42 100 152 80 32 64 128 256), losses := [] }

theorem u5012 : Upper (D 1) (R 1) [276,40,96,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5012
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5013 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 277 42 100 152 144 99 67 195 323), lower := (rows 277 42 100 152 144 32 64 128 256), losses := [] }

theorem u5013 : Upper (D 1) (R 1) [276,40,96,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5013
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5014 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 42 100 200 17 178 210 146 402), lower := (rows 277 42 100 200 17 32 64 128 256), losses := [] }

theorem u5014 : Upper (D 1) (R 1) [276,40,96,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5014
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5015 : Route 9 := (fun mask => (mask,id))

def c5015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5015 : Upper (D 1) (R 1) [276,40,96,192,2] 13 := by
  apply FastRouting.sound _ _ [276,40,96,192,2] 13 (by decide) (choices 1) [1,2,16,128] r5015 c5015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1596
  · exact u1597
  · exact u1598
  · exact u1599

def r5016 : Route 9 := (fun mask => (mask,id))

def c5016 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5016 : Upper (D 1) (R 1) [276,40,96,192,128] 13 := by
  apply FastRouting.sound _ _ [276,40,96,192,128] 13 (by decide) (choices 1) [1,2,16] r5016 c5016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1600
  · exact u1601
  · exact u1602

def b5017 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 196 11 18 240 240 240 496), lower := (rows 277 42 196 11 18 32 64 128 256), losses := [] }

theorem u5017 : Upper (D 1) (R 1) [276,40,192,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5017
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5018 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5018 : Upper (D 1) (R 1) [276,40,192,3,32] 13 := by
  apply FastRouting.sound _ _ [276,40,192,3,32] 13 (by decide) (choices 1) [2,16,64] r5018 c5018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1603
  · exact u1604
  · exact u1605

def b5019 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 196 11 80 178 242 178 434), lower := (rows 277 42 196 11 80 32 64 128 256), losses := [] }

theorem u5019 : Upper (D 1) (R 1) [276,40,192,3,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5019
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5020 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 277 42 196 26 17 226 226 226 482), lower := (rows 277 42 196 26 17 32 64 128 256), losses := [] }

theorem u5020 : Upper (D 1) (R 1) [276,40,192,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5020
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5021 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 26, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 196 26 18 225 225 225 481), lower := (rows 277 42 196 26 18 32 64 128 256), losses := [] }

theorem u5021 : Upper (D 1) (R 1) [276,40,192,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5021
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5022 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 196 26 48 227 195 195 451), lower := (rows 277 42 196 26 48 32 64 128 256), losses := [] }

theorem u5022 : Upper (D 1) (R 1) [276,40,192,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5022
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5023 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 196 26 80 163 227 163 419), lower := (rows 277 42 196 26 80 32 64 128 256), losses := [] }

theorem u5023 : Upper (D 1) (R 1) [276,40,192,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5023
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5024 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 277 42 196 74 17 178 242 178 434), lower := (rows 277 42 196 74 17 32 64 128 256), losses := [] }

theorem u5024 : Upper (D 1) (R 1) [276,40,192,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5024
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5025 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 196 74 18 177 241 177 433), lower := (rows 277 42 196 74 18 32 64 128 256), losses := [] }

theorem u5025 : Upper (D 1) (R 1) [276,40,192,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5025
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5026 : Route 9 := (fun mask => (mask,id))

def c5026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5026 : Upper (D 1) (R 1) [276,40,192,66,32] 13 := by
  apply FastRouting.sound _ _ [276,40,192,66,32] 13 (by decide) (choices 1) [1,2,16,128] r5026 c5026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1606
  · exact u1607
  · exact u1608
  · exact u1609

def b5027 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 42 196 74 144 51 115 179 307), lower := (rows 277 42 196 74 144 32 64 128 256), losses := [] }

theorem u5027 : Upper (D 1) (R 1) [276,40,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5027
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5028 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 277 42 196 88 17 162 226 162 418), lower := (rows 277 42 196 88 17 32 64 128 256), losses := [] }

theorem u5028 : Upper (D 1) (R 1) [276,40,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5029 : Route 9 := (fun mask => (mask,id))

def c5029 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5029 : Upper (D 1) (R 1) [276,40,192,80,2] 13 := by
  apply FastRouting.sound _ _ [276,40,192,80,2] 13 (by decide) (choices 1) [1,2,128] r5029 c5029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1610
  · exact u1611
  · exact u1612

def r5030 : Route 9 := (fun mask => (mask,id))

def c5030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5030 : Upper (D 1) (R 1) [276,40,192,80,32] 13 := by
  apply FastRouting.sound _ _ [276,40,192,80,32] 13 (by decide) (choices 1) [1,2,128] r5030 c5030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1613
  · exact u1614
  · exact u1615

def b5031 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 42 196 88 144 35 99 163 291), lower := (rows 277 42 196 88 144 32 64 128 256), losses := [] }

theorem u5031 : Upper (D 1) (R 1) [276,40,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5031
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5032 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 277 50 14 200 17 226 226 226 482), lower := (rows 277 50 14 200 17 32 64 128 256), losses := [] }

theorem u5032 : Upper (D 1) (R 1) [276,48,10,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5032
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5033 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 50 14 200 18 225 225 225 481), lower := (rows 277 50 14 200 18 32 64 128 256), losses := [] }

theorem u5033 : Upper (D 1) (R 1) [276,48,10,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5033
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5034 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 14 200 48 227 195 195 451), lower := (rows 277 50 14 200 48 32 64 128 256), losses := [] }

theorem u5034 : Upper (D 1) (R 1) [276,48,10,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5034
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5035 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 14 200 80 163 227 163 419), lower := (rows 277 50 14 200 80 32 64 128 256), losses := [] }

theorem u5035 : Upper (D 1) (R 1) [276,48,10,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5035
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5036 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 44 73 18 226 194 194 450), lower := (rows 277 50 44 73 18 32 64 128 256), losses := [] }

theorem u5036 : Upper (D 1) (R 1) [276,48,40,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5037 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 44 73 80 162 194 130 386), lower := (rows 277 50 44 73 80 32 64 128 256), losses := [] }

theorem u5037 : Upper (D 1) (R 1) [276,48,40,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5037
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5038 : Route 9 := (fun mask => (mask,id))

def c5038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5038 : Upper (D 1) (R 1) [276,48,40,65,128] 13 := by
  apply FastRouting.sound _ _ [276,48,40,65,128] 13 (by decide) (choices 1) [2,64,128] r5038 c5038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1616
  · exact u1617
  · exact u1618

def b5039 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 50 44 74 17 226 194 194 450), lower := (rows 277 50 44 74 17 32 64 128 256), losses := [] }

theorem u5039 : Upper (D 1) (R 1) [276,48,40,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5039
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5039
end Delivery.IrregularNine14.P01
