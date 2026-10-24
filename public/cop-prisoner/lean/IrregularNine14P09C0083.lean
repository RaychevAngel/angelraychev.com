import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0028
import IrregularNine14P09C0029

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4980 : Route 9 := (fun mask => (mask,id))

def c4980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u4980 : Upper (D 9) (R 9) [34,192,9,80,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,257,4] 13 (by decide) (choices 1) [32,128,256] r4980 c4980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1721
  · exact u1722
  · exact u1723

def b4981 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 273 160 356 420 292), lower := (rows 35 194 13 88 273 160 64 128 256), losses := [] }

theorem u4981 : Upper (D 9) (R 9) [34,192,9,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4981 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4982 : Route 9 := (fun mask => (mask,id))

def c4982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4982 : Upper (D 9) (R 9) [34,192,9,80,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,257,256] 13 (by decide) (choices 1) [4,32,128] r4982 c4982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1724
  · exact u1725
  · exact u1726

def b4983 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 450, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,6)], upper := (rows 35 194 13 88 276 33 480 416 416), lower := (rows 35 194 13 88 276 33 64 128 256), losses := [] }

theorem u4983 : Upper (D 9) (R 9) [34,192,9,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4983 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4984 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 276 160 353 417 289), lower := (rows 35 194 13 88 276 160 64 128 256), losses := [] }

theorem u4984 : Upper (D 9) (R 9) [34,192,9,80,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4984 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4985 : Route 9 := (fun mask => (mask,id))

def c4985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4985 : Upper (D 9) (R 9) [34,192,9,80,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,260,256] 13 (by decide) (choices 1) [1,32,128] r4985 c4985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1727
  · exact u1728
  · exact u1729

def b4986 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,5)], upper := (rows 35 194 13 88 304 33 452 388 388), lower := (rows 35 194 13 88 304 33 64 128 256), losses := [] }

theorem u4986 : Upper (D 9) (R 9) [34,192,9,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4986 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4987 : Route 9 := (fun mask => (mask,id))

def c4987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4987 : Upper (D 9) (R 9) [34,192,9,80,288,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,288,4] 13 (by decide) (choices 1) [1,128,256] r4987 c4987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1730
  · exact u1731
  · exact u1732

def b4988 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 304 160 325 389 261), lower := (rows 35 194 13 88 304 160 64 128 256), losses := [] }

theorem u4988 : Upper (D 9) (R 9) [34,192,9,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4988 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4989 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 13 88 304 288 197 133 389), lower := (rows 35 194 13 88 304 288 64 128 256), losses := [] }

theorem u4989 : Upper (D 9) (R 9) [34,192,9,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4989 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4990 : Route 9 := (fun mask => (mask,id))

def c4990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4990 : Upper (D 9) (R 9) [34,192,9,80,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384,1] 13 (by decide) (choices 1) [4,32,256] r4990 c4990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1733
  · exact u1734
  · exact u1735

def r4991 : Route 9 := (fun mask => (mask,id))

def c4991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4991 : Upper (D 9) (R 9) [34,192,9,80,384,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384,4] 13 (by decide) (choices 1) [1,32,256] r4991 c4991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1736
  · exact u1737
  · exact u1738

def r4992 : Route 9 := (fun mask => (mask,id))

def c4992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4992 : Upper (D 9) (R 9) [34,192,9,80,384,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384,256] 13 (by decide) (choices 1) [1,4,32] r4992 c4992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1739
  · exact u1740
  · exact u1741

def b4993 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 2, region := 466, targets := 1 }], pairs := [(0,8),(1,0),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 104 148 33 336 400 272), lower := (rows 35 194 13 104 148 33 64 128 256), losses := [] }

theorem u4993 : Upper (D 9) (R 9) [34,192,9,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4993 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4994 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 104 148 48 321 385 257), lower := (rows 35 194 13 104 148 48 64 128 256), losses := [] }

theorem u4994 : Upper (D 9) (R 9) [34,192,9,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4994 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4995 : Route 9 := (fun mask => (mask,id))

def c4995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4995 : Upper (D 9) (R 9) [34,192,9,96,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,132,256] 13 (by decide) (choices 1) [1,16,256] r4995 c4995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1742
  · exact u1743
  · exact u1744

def b4996 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 13 104 273 36 464 400 400), lower := (rows 35 194 13 104 273 36 64 128 256), losses := [] }

theorem u4996 : Upper (D 9) (R 9) [34,192,9,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4996 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4997 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 },{ cop := 2, region := 400, targets := 64 }], pairs := [(1,0),(1,5),(4,5),(4,6)], upper := (rows 35 194 13 104 273 48 452 388 388), lower := (rows 35 194 13 104 273 48 64 128 256), losses := [] }

theorem u4997 : Upper (D 9) (R 9) [34,192,9,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4997 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4998 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 13 104 273 160 340 404 276), lower := (rows 35 194 13 104 273 160 64 128 256), losses := [] }

theorem u4998 : Upper (D 9) (R 9) [34,192,9,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4998 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4999 : Route 9 := (fun mask => (mask,id))

def c4999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4999 : Upper (D 9) (R 9) [34,192,9,96,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,257,256] 13 (by decide) (choices 1) [4,16,128] r4999 c4999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1745
  · exact u1746
  · exact u1747

def b5000 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 13 104 276 33 464 400 400), lower := (rows 35 194 13 104 276 33 64 128 256), losses := [] }

theorem u5000 : Upper (D 9) (R 9) [34,192,9,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5000 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5001 : Route 9 := (fun mask => (mask,id))

def c5001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5001 : Upper (D 9) (R 9) [34,192,9,96,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,260,16] 13 (by decide) (choices 1) [1,128,256] r5001 c5001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1748
  · exact u1749
  · exact u1750

def b5002 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 13 104 276 160 337 401 273), lower := (rows 35 194 13 104 276 160 64 128 256), losses := [] }

theorem u5002 : Upper (D 9) (R 9) [34,192,9,96,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5002 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5003 : Route 9 := (fun mask => (mask,id))

def c5003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5003 : Upper (D 9) (R 9) [34,192,9,96,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,260,256] 13 (by decide) (choices 1) [1,16,128] r5003 c5003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1751
  · exact u1752
  · exact u1753

def b5004 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 13 104 400 33 340 404 276), lower := (rows 35 194 13 104 400 33 64 128 256), losses := [] }

theorem u5004 : Upper (D 9) (R 9) [34,192,9,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5004 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5005 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 13 104 400 36 337 401 273), lower := (rows 35 194 13 104 400 36 64 128 256), losses := [] }

theorem u5005 : Upper (D 9) (R 9) [34,192,9,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5005 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5006 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,5)], upper := (rows 35 194 13 104 400 48 325 389 261), lower := (rows 35 194 13 104 400 48 64 128 256), losses := [] }

theorem u5006 : Upper (D 9) (R 9) [34,192,9,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5006 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5007 : Route 9 := (fun mask => (mask,id))

def c5007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5007 : Upper (D 9) (R 9) [34,192,9,96,384,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,384,256] 13 (by decide) (choices 1) [1,4,16] r5007 c5007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1754
  · exact u1755
  · exact u1756

def b5008 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 194 13 268 81 48 480 416 416), lower := (rows 35 194 13 268 81 48 64 128 256), losses := [] }

theorem u5008 : Upper (D 9) (R 9) [34,192,9,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5008 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5009 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 49, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(4,7),(4,8)], upper := (rows 35 194 13 268 81 160 368 432 304), lower := (rows 35 194 13 268 81 160 64 128 256), losses := [] }

theorem u5009 : Upper (D 9) (R 9) [34,192,9,260,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5009 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5010 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 211, targets := 256 },{ cop := 4, region := 428, targets := 64 }], pairs := [(0,8),(1,8),(2,6),(3,6),(4,8)], upper := (rows 35 194 13 268 81 288 240 176 432), lower := (rows 35 194 13 268 81 288 64 128 256), losses := [] }

theorem u5010 : Upper (D 9) (R 9) [34,192,9,260,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5010 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5011 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(4,7),(4,8)], upper := (rows 35 194 13 268 112 33 464 400 400), lower := (rows 35 194 13 268 112 33 64 128 256), losses := [] }

theorem u5011 : Upper (D 9) (R 9) [34,192,9,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5011 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5012 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 194 13 268 112 48 449 385 385), lower := (rows 35 194 13 268 112 48 64 128 256), losses := [] }

theorem u5012 : Upper (D 9) (R 9) [34,192,9,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5012 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5013 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 49, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(4,7),(4,8)], upper := (rows 35 194 13 268 112 160 337 401 273), lower := (rows 35 194 13 268 112 160 64 128 256), losses := [] }

theorem u5013 : Upper (D 9) (R 9) [34,192,9,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5013 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5014 : Route 9 := (fun mask => (mask,id))

def c5014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5014 : Upper (D 9) (R 9) [34,192,9,260,96,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,96,256] 13 (by decide) (choices 1) [1,16,128] r5014 c5014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1757
  · exact u1758
  · exact u1759

def b5015 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,0)], upper := (rows 35 194 13 268 304 33 208 208 464), lower := (rows 35 194 13 268 304 33 64 128 256), losses := [] }

theorem u5015 : Upper (D 9) (R 9) [34,192,9,260,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5015 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5016 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 13 268 304 48 193 193 449), lower := (rows 35 194 13 268 304 48 64 128 256), losses := [] }

theorem u5016 : Upper (D 9) (R 9) [34,192,9,260,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5016 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5017 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 268 304 96 209 145 401), lower := (rows 35 194 13 268 304 96 64 128 256), losses := [] }

theorem u5017 : Upper (D 9) (R 9) [34,192,9,260,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5017 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5018 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,0)], upper := (rows 35 194 13 268 336 33 240 176 432), lower := (rows 35 194 13 268 336 33 64 128 256), losses := [] }

theorem u5018 : Upper (D 9) (R 9) [34,192,9,260,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5018 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5019 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 163, targets := 256 }], pairs := [(0,8),(1,8),(2,6),(3,6)], upper := (rows 35 194 13 268 336 48 225 161 417), lower := (rows 35 194 13 268 336 48 64 128 256), losses := [] }

theorem u5019 : Upper (D 9) (R 9) [34,192,9,260,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5019 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5020 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 268 336 160 113 177 305), lower := (rows 35 194 13 268 336 160 64 128 256), losses := [] }

theorem u5020 : Upper (D 9) (R 9) [34,192,9,260,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5020 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5021 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 458, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 280 52 33 448 448 448), lower := (rows 35 194 13 280 52 33 64 128 256), losses := [] }

theorem u5021 : Upper (D 9) (R 9) [34,192,9,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5021 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5022 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 280 52 96 449 385 385), lower := (rows 35 194 13 280 52 96 64 128 256), losses := [] }

theorem u5022 : Upper (D 9) (R 9) [34,192,9,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5022 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5023 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 195, targets := 256 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(3,5),(4,0)], upper := (rows 35 194 13 280 52 288 193 193 449), lower := (rows 35 194 13 280 52 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 64 128 256), good := (rows 34 194 60 312 52 288 64 128 288) },{ target := 5, region := (rows 1 23 4 24 16 0 69 133 261), good := (rows 451 194 463 282 478 256 64 128 256) }] }

theorem u5023 : Upper (D 9) (R 9) [34,192,9,272,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5023 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5024 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 428, targets := 64 },{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(2,6),(3,0),(3,6)], upper := (rows 35 194 13 280 81 36 480 416 416), lower := (rows 35 194 13 280 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 55 4 24 16 36 101 165 293), good := (rows 482 194 494 282 474 486 64 128 256) }] }

theorem u5024 : Upper (D 9) (R 9) [34,192,9,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5024 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5025 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 49, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(4,7),(4,8)], upper := (rows 35 194 13 280 81 160 356 420 292), lower := (rows 35 194 13 280 81 160 64 128 256), losses := [] }

theorem u5025 : Upper (D 9) (R 9) [34,192,9,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5025 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5026 : Route 9 := (fun mask => (mask,id))

def c5026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5026 : Upper (D 9) (R 9) [34,192,9,272,65,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,65,256] 13 (by decide) (choices 1) [4,32,128] r5026 c5026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1760
  · exact u1761
  · exact u1762

def b5027 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 450, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,0),(3,0)], upper := (rows 35 194 13 280 84 33 480 416 416), lower := (rows 35 194 13 280 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 194 478 280 94 482 64 128 256) }] }

theorem u5027 : Upper (D 9) (R 9) [34,192,9,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5027 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5028 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 280 84 160 353 417 289), lower := (rows 35 194 13 280 84 160 64 128 256), losses := [] }

theorem u5028 : Upper (D 9) (R 9) [34,192,9,272,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5028 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5029 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 195, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(3,6),(4,8)], upper := (rows 35 194 13 280 84 288 225 161 417), lower := (rows 35 194 13 280 84 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 24 16 319 0 135 263), good := (rows 419 419 429 312 444 288 0 128 288) },{ target := 8, region := (rows 33 39 4 8 20 32 97 161 0), good := (rows 227 194 223 24 86 227 64 128 0) }] }

theorem u5029 : Upper (D 9) (R 9) [34,192,9,272,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5029 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5030 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 2, region := 450, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(4,7),(4,8)], upper := (rows 35 194 13 280 112 33 452 388 388), lower := (rows 35 194 13 280 112 33 64 128 256), losses := [] }

theorem u5030 : Upper (D 9) (R 9) [34,192,9,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5030 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5031 : Route 9 := (fun mask => (mask,id))

def c5031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5031 : Upper (D 9) (R 9) [34,192,9,272,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,96,4] 13 (by decide) (choices 1) [1,128,256] r5031 c5031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1763
  · exact u1764
  · exact u1765

def b5032 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 49, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(4,7),(4,8)], upper := (rows 35 194 13 280 112 160 325 389 261), lower := (rows 35 194 13 280 112 160 64 128 256), losses := [] }

theorem u5032 : Upper (D 9) (R 9) [34,192,9,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5032 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5033 : Route 9 := (fun mask => (mask,id))

def c5033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5033 : Upper (D 9) (R 9) [34,192,9,272,96,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,96,256] 13 (by decide) (choices 1) [1,4,128] r5033 c5033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1766
  · exact u1767
  · exact u1768

def b5034 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 428, targets := 64 }], pairs := [(1,5),(2,6),(3,6),(4,5)], upper := (rows 35 194 13 296 81 36 464 400 400), lower := (rows 35 194 13 296 81 36 64 128 256), losses := [] }

theorem u5034 : Upper (D 9) (R 9) [34,192,9,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5034 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5035 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 194 13 296 81 48 452 388 388), lower := (rows 35 194 13 296 81 48 64 128 256), losses := [] }

theorem u5035 : Upper (D 9) (R 9) [34,192,9,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5035 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5036 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 49, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(4,7),(4,8)], upper := (rows 35 194 13 296 81 160 340 404 276), lower := (rows 35 194 13 296 81 160 64 128 256), losses := [] }

theorem u5036 : Upper (D 9) (R 9) [34,192,9,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5036 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5037 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 194 13 296 81 288 212 148 404), lower := (rows 35 194 13 296 81 288 64 128 256), losses := [] }

theorem u5037 : Upper (D 9) (R 9) [34,192,9,288,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5037 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5038 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 296 84 33 464 400 400), lower := (rows 35 194 13 296 84 33 64 128 256), losses := [] }

theorem u5038 : Upper (D 9) (R 9) [34,192,9,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5038 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5039 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,5)], upper := (rows 35 194 13 296 84 48 449 385 385), lower := (rows 35 194 13 296 84 48 64 128 256), losses := [] }

theorem u5039 : Upper (D 9) (R 9) [34,192,9,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5039 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5039
end Delivery.IrregularNine14.P09
