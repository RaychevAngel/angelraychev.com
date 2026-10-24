import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0025
import IrregularNine14P06C0026

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11040 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 41 112 96 86 150 278), lower := (rows 7 131 268 41 112 96 64 128 256), losses := [] }

theorem u11040 : Upper (D 6) (R 6) [6,129,264,33,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11040
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11041 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 131 268 42 49 36 80 208 336), lower := (rows 7 131 268 42 49 36 64 128 256), losses := [] }

theorem u11041 : Upper (D 6) (R 6) [6,129,264,34,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11041
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11042 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 131 268 42 49 48 68 196 324), lower := (rows 7 131 268 42 49 48 64 128 256), losses := [] }

theorem u11042 : Upper (D 6) (R 6) [6,129,264,34,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11042
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11043 : Route 9 := (fun mask => (mask,id))

def c11043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11043 : Upper (D 6) (R 6) [6,129,264,34,33,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,34,33,64] 13 (by decide) (choices 1) [4,16] r11043 c11043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1551
  · exact u1552

def b11044 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 40, targets := 1 },{ cop := 0, region := 112, targets := 2 },{ cop := 0, region := 40, targets := 64 }], pairs := [(3,0),(3,6),(4,1)], upper := (rows 7 131 268 42 81 36 112 240 368), lower := (rows 7 131 268 42 81 36 64 128 256), losses := [] }

theorem u11044 : Upper (D 6) (R 6) [6,129,264,34,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11044
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11045 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 268 42 81 48 100 228 356), lower := (rows 7 131 268 42 81 48 64 128 256), losses := [] }

theorem u11045 : Upper (D 6) (R 6) [6,129,264,34,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11045
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11046 : Route 9 := (fun mask => (mask,id))

def c11046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11046 : Upper (D 6) (R 6) [6,129,264,34,65,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,34,65,64] 13 (by decide) (choices 1) [4,16,32] r11046 c11046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1553
  · exact u1554
  · exact u1555

def b11047 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 268 42 84 33 112 240 368), lower := (rows 7 131 268 42 84 33 64 128 256), losses := [] }

theorem u11047 : Upper (D 6) (R 6) [6,129,264,34,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11047
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11048 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 131 268 42 84 48 97 225 353), lower := (rows 7 131 268 42 84 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 63 67 131 259), good := (rows 501 497 316 508 116 48 64 128 256) }] }

theorem u11048 : Upper (D 6) (R 6) [6,129,264,34,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11048
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11049 : Route 9 := (fun mask => (mask,id))

def c11049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11049 : Upper (D 6) (R 6) [6,129,264,34,68,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,34,68,64] 13 (by decide) (choices 1) [1,16,32] r11049 c11049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1556
  · exact u1557
  · exact u1558

def b11050 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 268 42 112 33 84 212 340), lower := (rows 7 131 268 42 112 33 64 128 256), losses := [] }

theorem u11050 : Upper (D 6) (R 6) [6,129,264,34,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11050
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11051 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 40, targets := 1 },{ cop := 0, region := 112, targets := 2 },{ cop := 0, region := 40, targets := 64 }], pairs := [(3,0),(3,6),(4,1)], upper := (rows 7 131 268 42 112 36 81 209 337), lower := (rows 7 131 268 42 112 36 64 128 256), losses := [] }

theorem u11051 : Upper (D 6) (R 6) [6,129,264,34,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11051
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11052 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 268 42 112 48 69 197 325), lower := (rows 7 131 268 42 112 48 64 128 256), losses := [] }

theorem u11052 : Upper (D 6) (R 6) [6,129,264,34,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11052
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11053 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 42 112 96 85 149 277), lower := (rows 7 131 268 42 112 96 64 128 256), losses := [] }

theorem u11053 : Upper (D 6) (R 6) [6,129,264,34,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11053
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11054 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 44 50 33 80 208 336), lower := (rows 7 131 268 44 50 33 64 128 256), losses := [] }

theorem u11054 : Upper (D 6) (R 6) [6,129,264,36,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11054
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11055 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 268 44 50 48 65 193 321), lower := (rows 7 131 268 44 50 48 64 128 256), losses := [] }

theorem u11055 : Upper (D 6) (R 6) [6,129,264,36,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11055
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11056 : Route 9 := (fun mask => (mask,id))

def c11056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11056 : Upper (D 6) (R 6) [6,129,264,36,34,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,36,34,64] 13 (by decide) (choices 1) [1,16] r11056 c11056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1559
  · exact u1560

def b11057 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 242, targets := 4 },{ cop := 0, region := 40, targets := 1 }], pairs := [(1,2),(3,0),(4,2)], upper := (rows 7 131 268 44 81 34 112 240 368), lower := (rows 7 131 268 44 81 34 64 128 256), losses := [] }

theorem u11057 : Upper (D 6) (R 6) [6,129,264,36,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11057
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11058 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 242, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 131 268 44 81 48 98 226 354), lower := (rows 7 131 268 44 81 48 64 128 256), losses := [] }

theorem u11058 : Upper (D 6) (R 6) [6,129,264,36,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11058
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11059 : Route 9 := (fun mask => (mask,id))

def c11059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11059 : Upper (D 6) (R 6) [6,129,264,36,65,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,36,65,64] 13 (by decide) (choices 1) [2,16,32] r11059 c11059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1561
  · exact u1562
  · exact u1563

def b11060 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 0, region := 242, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 131 268 44 82 33 112 240 368), lower := (rows 7 131 268 44 82 33 64 128 256), losses := [] }

theorem u11060 : Upper (D 6) (R 6) [6,129,264,36,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11060
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11061 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 242, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 131 268 44 82 48 97 225 353), lower := (rows 7 131 268 44 82 48 64 128 256), losses := [] }

theorem u11061 : Upper (D 6) (R 6) [6,129,264,36,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11061
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11062 : Route 9 := (fun mask => (mask,id))

def c11062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11062 : Upper (D 6) (R 6) [6,129,264,36,66,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,36,66,64] 13 (by decide) (choices 1) [1,16,32] r11062 c11062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1564
  · exact u1565
  · exact u1566

def b11063 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 0, region := 242, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 131 268 44 112 33 82 210 338), lower := (rows 7 131 268 44 112 33 64 128 256), losses := [] }

theorem u11063 : Upper (D 6) (R 6) [6,129,264,36,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11063
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11064 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 242, targets := 4 },{ cop := 0, region := 40, targets := 1 }], pairs := [(1,2),(3,0),(4,2)], upper := (rows 7 131 268 44 112 34 81 209 337), lower := (rows 7 131 268 44 112 34 64 128 256), losses := [] }

theorem u11064 : Upper (D 6) (R 6) [6,129,264,36,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11064
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11065 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 268 44 112 48 67 195 323), lower := (rows 7 131 268 44 112 48 64 128 256), losses := [] }

theorem u11065 : Upper (D 6) (R 6) [6,129,264,36,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11065
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11066 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 44 112 96 83 147 275), lower := (rows 7 131 268 44 112 96 64 128 256), losses := [] }

theorem u11066 : Upper (D 6) (R 6) [6,129,264,36,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11066
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11067 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 56 81 34 100 228 356), lower := (rows 7 131 268 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 35 89 153 281), good := (rows 486 482 460 508 508 34 64 128 256) }] }

theorem u11067 : Upper (D 6) (R 6) [6,129,264,48,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11067
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11068 : PairBound 9 := { available := 98, camps := [], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 131 268 56 81 36 98 226 354), lower := (rows 7 131 268 56 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 61 67 131 259), good := (rows 486 482 300 60 508 36 64 128 256) },{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 37 161 300 56 121 36 64 128 256) }] }

theorem u11068 : Upper (D 6) (R 6) [6,129,264,48,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11068
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11069 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 56 81 96 102 166 294), lower := (rows 7 131 268 56 81 96 64 128 256), losses := [] }

theorem u11069 : Upper (D 6) (R 6) [6,129,264,48,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11069
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11070 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 131 268 56 82 33 100 228 356), lower := (rows 7 131 268 56 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 28 24 16 35 89 153 281), good := (rows 485 481 460 508 508 481 64 128 256) }] }

theorem u11070 : Upper (D 6) (R 6) [6,129,264,48,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11070
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11071 : Route 9 := (fun mask => (mask,id))

def c11071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11071 : Upper (D 6) (R 6) [6,129,264,48,66,4] 13 := by
  apply FastRouting.sound _ _ [6,129,264,48,66,4] 13 (by decide) (choices 1) [1,32] r11071 c11071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1567
  · exact u1568

def b11072 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 56 82 96 101 165 293), lower := (rows 7 131 268 56 82 96 64 128 256), losses := [] }

theorem u11072 : Upper (D 6) (R 6) [6,129,264,48,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11072
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11073 : Route 9 := (fun mask => (mask,id))

def c11073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11073 : Upper (D 6) (R 6) [6,129,264,48,68,1] 13 := by
  apply FastRouting.sound _ _ [6,129,264,48,68,1] 13 (by decide) (choices 1) [2,32] r11073 c11073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1569
  · exact u1570

def r11074 : Route 9 := (fun mask => (mask,id))

def c11074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11074 : Upper (D 6) (R 6) [6,129,264,48,68,2] 13 := by
  apply FastRouting.sound _ _ [6,129,264,48,68,2] 13 (by decide) (choices 1) [1,32] r11074 c11074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1571
  · exact u1572

def b11075 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 56 84 96 99 163 291), lower := (rows 7 131 268 56 84 96 64 128 256), losses := [] }

theorem u11075 : Upper (D 6) (R 6) [6,129,264,48,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11075
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11076 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 104 49 34 84 212 340), lower := (rows 7 131 268 104 49 34 64 128 256), losses := [] }

theorem u11076 : Upper (D 6) (R 6) [6,129,264,96,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11076
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11077 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 131 268 104 49 36 82 210 338), lower := (rows 7 131 268 104 49 36 64 128 256), losses := [] }

theorem u11077 : Upper (D 6) (R 6) [6,129,264,96,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11077
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11078 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 131 268 104 49 48 70 198 326), lower := (rows 7 131 268 104 49 48 64 128 256), losses := [] }

theorem u11078 : Upper (D 6) (R 6) [6,129,264,96,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11078
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11079 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 104 49 96 86 150 278), lower := (rows 7 131 268 104 49 96 64 128 256), losses := [] }

theorem u11079 : Upper (D 6) (R 6) [6,129,264,96,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11079
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11080 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 104 50 33 84 212 340), lower := (rows 7 131 268 104 50 33 64 128 256), losses := [] }

theorem u11080 : Upper (D 6) (R 6) [6,129,264,96,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11080
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11081 : Route 9 := (fun mask => (mask,id))

def c11081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11081 : Upper (D 6) (R 6) [6,129,264,96,34,4] 13 := by
  apply FastRouting.sound _ _ [6,129,264,96,34,4] 13 (by decide) (choices 1) [1,16] r11081 c11081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1573
  · exact u1574

def b11082 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 131 268 104 50 48 69 197 325), lower := (rows 7 131 268 104 50 48 64 128 256), losses := [] }

theorem u11082 : Upper (D 6) (R 6) [6,129,264,96,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11082
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11083 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 104 50 96 85 149 277), lower := (rows 7 131 268 104 50 96 64 128 256), losses := [] }

theorem u11083 : Upper (D 6) (R 6) [6,129,264,96,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11083
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11084 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 4, region := 195, targets := 32 }], pairs := [(0,5),(4,1),(4,6)], upper := (rows 7 131 268 104 52 33 82 210 338), lower := (rows 7 131 268 104 52 33 64 128 256), losses := [] }

theorem u11084 : Upper (D 6) (R 6) [6,129,264,96,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11084
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11085 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 195, targets := 32 },{ cop := 0, region := 48, targets := 1 }], pairs := [(0,5),(1,5),(4,0)], upper := (rows 7 131 268 104 52 34 81 209 337), lower := (rows 7 131 268 104 52 34 64 128 256), losses := [] }

theorem u11085 : Upper (D 6) (R 6) [6,129,264,96,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11085
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11086 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 131 268 104 52 48 67 195 323), lower := (rows 7 131 268 104 52 48 64 128 256), losses := [] }

theorem u11086 : Upper (D 6) (R 6) [6,129,264,96,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11086
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11087 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 104 52 96 83 147 275), lower := (rows 7 131 268 104 52 96 64 128 256), losses := [] }

theorem u11087 : Upper (D 6) (R 6) [6,129,264,96,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11087
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11088 : PairBound 9 := { available := 72, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 25 50 36 72 200 328), lower := (rows 7 131 292 25 50 36 64 128 256), losses := [] }

theorem u11088 : Upper (D 6) (R 6) [6,129,288,17,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11088
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11089 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 131 292 25 50 40 68 196 324), lower := (rows 7 131 292 25 50 40 64 128 256), losses := [] }

theorem u11089 : Upper (D 6) (R 6) [6,129,288,17,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11089
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11090 : Route 9 := (fun mask => (mask,id))

def c11090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11090 : Upper (D 6) (R 6) [6,129,288,17,34,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,34,64] 13 (by decide) (choices 1) [4,8] r11090 c11090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1575
  · exact u1576

def b11091 : PairBound 9 := { available := 104, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 25 82 36 104 232 360), lower := (rows 7 131 292 25 82 36 64 128 256), losses := [] }

theorem u11091 : Upper (D 6) (R 6) [6,129,288,17,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11091
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11092 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 25 82 40 100 228 356), lower := (rows 7 131 292 25 82 40 64 128 256), losses := [] }

theorem u11092 : Upper (D 6) (R 6) [6,129,288,17,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11092
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11093 : Route 9 := (fun mask => (mask,id))

def c11093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11093 : Upper (D 6) (R 6) [6,129,288,17,66,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,66,64] 13 (by decide) (choices 1) [4,8,32] r11093 c11093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1577
  · exact u1578
  · exact u1579

def b11094 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 226, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 131 292 25 84 34 104 232 360), lower := (rows 7 131 292 25 84 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 162 292 508 84 34 64 128 256) }] }

theorem u11094 : Upper (D 6) (R 6) [6,129,288,17,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11094
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11095 : Route 9 := (fun mask => (mask,id))

def c11095 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11095 : Upper (D 6) (R 6) [6,129,288,17,68,8] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,68,8] 13 (by decide) (choices 1) [2,32] r11095 c11095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1580
  · exact u1581

def r11096 : Route 9 := (fun mask => (mask,id))

def c11096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11096 : Upper (D 6) (R 6) [6,129,288,17,68,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,68,64] 13 (by decide) (choices 1) [2,8,32] r11096 c11096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1582
  · exact u1583
  · exact u1584

def b11097 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 25 88 34 100 228 356), lower := (rows 7 131 292 25 88 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 47 8 24 35 111 175 303), good := (rows 486 486 484 508 476 486 64 128 256) }] }

theorem u11097 : Upper (D 6) (R 6) [6,129,288,17,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11097
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11098 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 25 88 36 98 226 354), lower := (rows 7 131 292 25 88 36 64 128 256), losses := [] }

theorem u11098 : Upper (D 6) (R 6) [6,129,288,17,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11098
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11099 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 25 88 96 102 166 294), lower := (rows 7 131 292 25 88 96 64 128 256), losses := [] }

theorem u11099 : Upper (D 6) (R 6) [6,129,288,17,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11099
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11099
end Delivery.IrregularNine14.P06
