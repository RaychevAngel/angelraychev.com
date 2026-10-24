import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0029
import IrregularNine14P09C0030

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5040 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 296 84 160 337 401 273), lower := (rows 35 194 13 296 84 160 64 128 256), losses := [] }

theorem u5040 : Upper (D 9) (R 9) [34,192,9,288,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5040 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5041 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 194 13 296 84 288 209 145 401), lower := (rows 35 194 13 296 84 288 64 128 256), losses := [] }

theorem u5041 : Upper (D 9) (R 9) [34,192,9,288,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5041 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5042 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 296 273 36 208 208 464), lower := (rows 35 194 13 296 273 36 64 128 256), losses := [] }

theorem u5042 : Upper (D 9) (R 9) [34,192,9,288,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5042 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5043 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 296 273 48 196 196 452), lower := (rows 35 194 13 296 273 48 64 128 256), losses := [] }

theorem u5043 : Upper (D 9) (R 9) [34,192,9,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5043 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5044 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 296 273 96 212 148 404), lower := (rows 35 194 13 296 273 96 64 128 256), losses := [] }

theorem u5044 : Upper (D 9) (R 9) [34,192,9,288,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5044 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5045 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 296 276 33 208 208 464), lower := (rows 35 194 13 296 276 33 64 128 256), losses := [] }

theorem u5045 : Upper (D 9) (R 9) [34,192,9,288,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5045 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5046 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 194 13 296 276 48 193 193 449), lower := (rows 35 194 13 296 276 48 64 128 256), losses := [] }

theorem u5046 : Upper (D 9) (R 9) [34,192,9,288,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5046 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5047 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 296 276 96 209 145 401), lower := (rows 35 194 13 296 276 96 64 128 256), losses := [] }

theorem u5047 : Upper (D 9) (R 9) [34,192,9,288,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5047 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5048 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 296 336 33 212 148 404), lower := (rows 35 194 13 296 336 33 64 128 256), losses := [] }

theorem u5048 : Upper (D 9) (R 9) [34,192,9,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5048 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5049 : Route 9 := (fun mask => (mask,id))

def c5049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5049 : Upper (D 9) (R 9) [34,192,9,288,320,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,320,4] 13 (by decide) (choices 1) [1,16,128] r5049 c5049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1769
  · exact u1770
  · exact u1771

def b5050 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 194 13 296 336 48 197 133 389), lower := (rows 35 194 13 296 336 48 64 128 256), losses := [] }

theorem u5050 : Upper (D 9) (R 9) [34,192,9,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5050 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5051 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 296 336 160 85 149 277), lower := (rows 35 194 13 296 336 160 64 128 256), losses := [] }

theorem u5051 : Upper (D 9) (R 9) [34,192,9,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5051 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5052 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 458, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 328 52 33 464 400 400), lower := (rows 35 194 13 328 52 33 64 128 256), losses := [] }

theorem u5052 : Upper (D 9) (R 9) [34,192,9,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5052 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5053 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 13 328 52 48 449 385 385), lower := (rows 35 194 13 328 52 48 64 128 256), losses := [] }

theorem u5053 : Upper (D 9) (R 9) [34,192,9,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5053 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5054 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 52 160 337 401 273), lower := (rows 35 194 13 328 52 160 64 128 256), losses := [] }

theorem u5054 : Upper (D 9) (R 9) [34,192,9,320,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5054 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5055 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 195, targets := 256 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,8),(1,8),(4,0),(4,6),(4,7)], upper := (rows 35 194 13 328 52 288 209 145 401), lower := (rows 35 194 13 328 52 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 64 128 256), good := (rows 34 194 60 360 52 288 64 128 288) },{ target := 7, region := (rows 1 2 4 8 20 296 64 0 256), good := (rows 35 66 61 360 52 288 64 0 288) }] }

theorem u5055 : Upper (D 9) (R 9) [34,192,9,320,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5055 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5056 : Route 9 := (fun mask => (mask,id))

def c5056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u5056 : Upper (D 9) (R 9) [34,192,9,320,129,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,129,4] 13 (by decide) (choices 1) [16,32,256] r5056 c5056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1772
  · exact u1773
  · exact u1774

def b5057 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 49, targets := 320 }], pairs := [(0,6),(0,8),(4,6),(4,8)], upper := (rows 35 194 13 328 145 48 356 420 292), lower := (rows 35 194 13 328 145 48 64 128 256), losses := [] }

theorem u5057 : Upper (D 9) (R 9) [34,192,9,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5057 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5058 : Route 9 := (fun mask => (mask,id))

def c5058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5058 : Upper (D 9) (R 9) [34,192,9,320,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,129,256] 13 (by decide) (choices 1) [4,16,32] r5058 c5058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1775
  · exact u1776
  · exact u1777

def b5059 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(4,6)], upper := (rows 35 194 13 328 148 33 368 432 304), lower := (rows 35 194 13 328 148 33 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 24 16 39 80 0 272), good := (rows 35 99 45 328 380 33 64 0 256) }] }

theorem u5059 : Upper (D 9) (R 9) [34,192,9,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5059 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5060 : Route 9 := (fun mask => (mask,id))

def c5060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5060 : Upper (D 9) (R 9) [34,192,9,320,132,16] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,132,16] 13 (by decide) (choices 1) [1,32,256] r5060 c5060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1778
  · exact u1779
  · exact u1780

def r5061 : Route 9 := (fun mask => (mask,id))

def c5061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5061 : Upper (D 9) (R 9) [34,192,9,320,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,132,256] 13 (by decide) (choices 1) [1,16,32] r5061 c5061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1781
  · exact u1782
  · exact u1783

def b5062 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 49, targets := 320 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(4,6),(4,8)], upper := (rows 35 194 13 328 176 33 340 404 276), lower := (rows 35 194 13 328 176 33 64 128 256), losses := [] }

theorem u5062 : Upper (D 9) (R 9) [34,192,9,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5062 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5063 : Route 9 := (fun mask => (mask,id))

def c5063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5063 : Upper (D 9) (R 9) [34,192,9,320,160,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,160,4] 13 (by decide) (choices 1) [1,16,256] r5063 c5063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1784
  · exact u1785
  · exact u1786

def b5064 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 49, targets := 320 }], pairs := [(0,6),(0,8),(4,6),(4,8)], upper := (rows 35 194 13 328 176 48 325 389 261), lower := (rows 35 194 13 328 176 48 64 128 256), losses := [] }

theorem u5064 : Upper (D 9) (R 9) [34,192,9,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5064 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5065 : Route 9 := (fun mask => (mask,id))

def c5065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5065 : Upper (D 9) (R 9) [34,192,9,320,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,160,256] 13 (by decide) (choices 1) [1,4,16] r5065 c5065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1787
  · exact u1788
  · exact u1789

def r5066 : Route 9 := (fun mask => (mask,id))

def c5066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5066 : Upper (D 9) (R 9) [34,192,9,320,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,257,4] 13 (by decide) (choices 1) [16,32,128] r5066 c5066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1790
  · exact u1791
  · exact u1792

def r5067 : Route 9 := (fun mask => (mask,id))

def c5067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5067 : Upper (D 9) (R 9) [34,192,9,320,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,257,16] 13 (by decide) (choices 1) [4,32,128] r5067 c5067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1793
  · exact u1794
  · exact u1795

def b5068 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 273 160 116 180 308), lower := (rows 35 194 13 328 273 160 64 128 256), losses := [] }

theorem u5068 : Upper (D 9) (R 9) [34,192,9,320,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5068 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5069 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 432, targets := 64 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,8),(4,6)], upper := (rows 35 194 13 328 276 33 240 176 432), lower := (rows 35 194 13 328 276 33 64 128 256), losses := [] }

theorem u5069 : Upper (D 9) (R 9) [34,192,9,320,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5069 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5070 : Route 9 := (fun mask => (mask,id))

def c5070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5070 : Upper (D 9) (R 9) [34,192,9,320,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,260,16] 13 (by decide) (choices 1) [1,32,128] r5070 c5070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1796
  · exact u1797
  · exact u1798

def b5071 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 276 160 113 177 305), lower := (rows 35 194 13 328 276 160 64 128 256), losses := [] }

theorem u5071 : Upper (D 9) (R 9) [34,192,9,320,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5071 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5072 : Route 9 := (fun mask => (mask,id))

def c5072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5072 : Upper (D 9) (R 9) [34,192,9,320,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,288,1] 13 (by decide) (choices 1) [4,16,128] r5072 c5072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1799
  · exact u1800
  · exact u1801

def r5073 : Route 9 := (fun mask => (mask,id))

def c5073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5073 : Upper (D 9) (R 9) [34,192,9,320,288,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,288,4] 13 (by decide) (choices 1) [1,16,128] r5073 c5073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1802
  · exact u1803
  · exact u1804

def b5074 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 13 328 304 48 197 133 389), lower := (rows 35 194 13 328 304 48 64 128 256), losses := [] }

theorem u5074 : Upper (D 9) (R 9) [34,192,9,320,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5074 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5075 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 304 160 85 149 277), lower := (rows 35 194 13 328 304 160 64 128 256), losses := [] }

theorem u5075 : Upper (D 9) (R 9) [34,192,9,320,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5075 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5076 : Route 9 := (fun mask => (mask,id))

def c5076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5076 : Upper (D 9) (R 9) [34,192,9,320,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,384,1] 13 (by decide) (choices 1) [4,16,32] r5076 c5076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1805
  · exact u1806
  · exact u1807

def r5077 : Route 9 := (fun mask => (mask,id))

def c5077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5077 : Upper (D 9) (R 9) [34,192,9,320,384,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,384,4] 13 (by decide) (choices 1) [1,16,32] r5077 c5077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1808
  · exact u1809
  · exact u1810

def r5078 : Route 9 := (fun mask => (mask,id))

def c5078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5078 : Upper (D 9) (R 9) [34,192,9,320,384,16] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,384,16] 13 (by decide) (choices 1) [1,4,32] r5078 c5078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1811
  · exact u1812
  · exact u1813

def b5079 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 44, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 28 44 273 33 448 448 448), lower := (rows 35 194 28 44 273 33 64 128 256), losses := [] }

theorem u5079 : Upper (D 9) (R 9) [34,192,24,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5079 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5080 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 194 28 44 273 96 449 385 385), lower := (rows 35 194 28 44 273 96 64 128 256), losses := [] }

theorem u5080 : Upper (D 9) (R 9) [34,192,24,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5080 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5081 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0),(3,6)], upper := (rows 35 194 28 44 273 288 193 193 449), lower := (rows 35 194 28 44 273 288 64 128 256), losses := [] }

theorem u5081 : Upper (D 9) (R 9) [34,192,24,36,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5081 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5082 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,5),(4,5)], upper := (rows 35 194 28 44 336 33 449 385 385), lower := (rows 35 194 28 44 336 33 64 128 256), losses := [] }

theorem u5082 : Upper (D 9) (R 9) [34,192,24,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5082 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5083 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,5),(4,7)], upper := (rows 35 194 28 44 336 160 321 385 257), lower := (rows 35 194 28 44 336 160 64 128 256), losses := [] }

theorem u5083 : Upper (D 9) (R 9) [34,192,24,36,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5083 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5084 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0),(3,6)], upper := (rows 35 194 28 44 336 288 193 129 385), lower := (rows 35 194 28 44 336 288 64 128 256), losses := [] }

theorem u5084 : Upper (D 9) (R 9) [34,192,24,36,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5084 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5085 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 28 73 176 33 324 388 260), lower := (rows 35 194 28 73 176 33 64 128 256), losses := [] }

theorem u5085 : Upper (D 9) (R 9) [34,192,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5085 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5086 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 28 73 176 36 321 385 257), lower := (rows 35 194 28 73 176 36 64 128 256), losses := [] }

theorem u5086 : Upper (D 9) (R 9) [34,192,24,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5086 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5087 : Route 9 := (fun mask => (mask,id))

def c5087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5087 : Upper (D 9) (R 9) [34,192,24,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,160,256] 13 (by decide) (choices 1) [1,4,256] r5087 c5087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1814
  · exact u1815
  · exact u1816

def r5088 : Route 9 := (fun mask => (mask,id))

def c5088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u5088 : Upper (D 9) (R 9) [34,192,24,65,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,257,4] 13 (by decide) (choices 1) [32,128,256] r5088 c5088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1817
  · exact u1818
  · exact u1819

def b5089 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 41, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(3,8),(4,7)], upper := (rows 35 194 28 73 273 160 356 420 292), lower := (rows 35 194 28 73 273 160 64 128 256), losses := [] }

theorem u5089 : Upper (D 9) (R 9) [34,192,24,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5089 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5090 : Route 9 := (fun mask => (mask,id))

def c5090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5090 : Upper (D 9) (R 9) [34,192,24,65,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,257,256] 13 (by decide) (choices 1) [4,32,128] r5090 c5090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1820
  · exact u1821
  · exact u1822

def b5091 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,7),(0,8),(2,6),(3,7),(3,8)], upper := (rows 35 194 28 73 276 33 480 416 416), lower := (rows 35 194 28 73 276 33 64 128 256), losses := [] }

theorem u5091 : Upper (D 9) (R 9) [34,192,24,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5091 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5092 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 41, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(3,8),(4,7)], upper := (rows 35 194 28 73 276 160 353 417 289), lower := (rows 35 194 28 73 276 160 64 128 256), losses := [] }

theorem u5092 : Upper (D 9) (R 9) [34,192,24,65,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5092 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5093 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 203, targets := 256 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,8),(1,8),(2,6),(3,8),(4,6)], upper := (rows 35 194 28 73 276 288 225 161 417), lower := (rows 35 194 28 73 276 288 64 128 256), losses := [] }

theorem u5093 : Upper (D 9) (R 9) [34,192,24,65,260,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5093 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5094 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 2, region := 450, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(3,7),(3,8)], upper := (rows 35 194 28 73 304 33 452 388 388), lower := (rows 35 194 28 73 304 33 64 128 256), losses := [] }

theorem u5094 : Upper (D 9) (R 9) [34,192,24,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5094 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5095 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 436, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,6)], upper := (rows 35 194 28 73 304 36 449 385 385), lower := (rows 35 194 28 73 304 36 64 128 256), losses := [] }

theorem u5095 : Upper (D 9) (R 9) [34,192,24,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5095 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5096 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 41, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(3,8),(4,7)], upper := (rows 35 194 28 73 304 160 325 389 261), lower := (rows 35 194 28 73 304 160 64 128 256), losses := [] }

theorem u5096 : Upper (D 9) (R 9) [34,192,24,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5096 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5097 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 28 73 304 288 197 133 389), lower := (rows 35 194 28 73 304 288 64 128 256), losses := [] }

theorem u5097 : Upper (D 9) (R 9) [34,192,24,65,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5097 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5098 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,7),(0,8),(2,6),(3,7),(3,8)], upper := (rows 35 194 28 73 400 33 356 420 292), lower := (rows 35 194 28 73 400 33 64 128 256), losses := [] }

theorem u5098 : Upper (D 9) (R 9) [34,192,24,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5098 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5099 : Route 9 := (fun mask => (mask,id))

def c5099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5099 : Upper (D 9) (R 9) [34,192,24,65,384,4] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,384,4] 13 (by decide) (choices 1) [1,32,256] r5099 c5099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1823
  · exact u1824
  · exact u1825

#print axioms u5099
end Delivery.IrregularNine14.P09
