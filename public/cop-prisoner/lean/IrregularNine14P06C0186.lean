import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0027

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11160 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 42 88 36 81 209 337), lower := (rows 7 131 292 42 88 36 64 128 256), losses := [] }

theorem u11160 : Upper (D 6) (R 6) [6,129,288,34,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11160
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11161 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 42 88 48 69 197 325), lower := (rows 7 131 292 42 88 48 64 128 256), losses := [] }

theorem u11161 : Upper (D 6) (R 6) [6,129,288,34,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11161
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11162 : Route 9 := (fun mask => (mask,id))

def c11162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11162 : Upper (D 6) (R 6) [6,129,288,34,72,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,34,72,64] 13 (by decide) (choices 1) [1,4,16] r11162 c11162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1636
  · exact u1637
  · exact u1638

def b11163 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 56 81 34 76 204 332), lower := (rows 7 131 292 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 35 88 152 280), good := (rows 38 162 292 508 508 34 64 128 256) }] }

theorem u11163 : Upper (D 6) (R 6) [6,129,288,48,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11163
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11164 : PairBound 9 := { available := 74, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 56 81 36 74 202 330), lower := (rows 7 131 292 56 81 36 64 128 256), losses := [] }

theorem u11164 : Upper (D 6) (R 6) [6,129,288,48,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11164
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11165 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 56 81 40 70 198 326), lower := (rows 7 131 292 56 81 40 64 128 256), losses := [] }

theorem u11165 : Upper (D 6) (R 6) [6,129,288,48,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11165
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11166 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 56 81 96 78 142 270), lower := (rows 7 131 292 56 81 96 64 128 256), losses := [] }

theorem u11166 : Upper (D 6) (R 6) [6,129,288,48,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11166
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11167 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 56 82 33 76 204 332), lower := (rows 7 131 292 56 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 17 32 108 172 300), good := (rows 470 146 492 508 82 508 64 128 256) }] }

theorem u11167 : Upper (D 6) (R 6) [6,129,288,48,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11167
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11168 : PairBound 9 := { available := 73, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 56 82 36 73 201 329), lower := (rows 7 131 292 56 82 36 64 128 256), losses := [] }

theorem u11168 : Upper (D 6) (R 6) [6,129,288,48,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11168
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11169 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 56 82 40 69 197 325), lower := (rows 7 131 292 56 82 40 64 128 256), losses := [] }

theorem u11169 : Upper (D 6) (R 6) [6,129,288,48,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11169
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11170 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 56 82 96 77 141 269), lower := (rows 7 131 292 56 82 96 64 128 256), losses := [] }

theorem u11170 : Upper (D 6) (R 6) [6,129,288,48,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11170
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11171 : PairBound 9 := { available := 74, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 131 292 56 84 33 74 202 330), lower := (rows 7 131 292 56 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 49 32 65 129 257), good := (rows 478 466 316 60 92 508 64 128 256) }] }

theorem u11171 : Upper (D 6) (R 6) [6,129,288,48,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11171
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11172 : Route 9 := (fun mask => (mask,id))

def c11172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11172 : Upper (D 6) (R 6) [6,129,288,48,68,2] 13 := by
  apply FastRouting.sound _ _ [6,129,288,48,68,2] 13 (by decide) (choices 1) [1,8] r11172 c11172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1639
  · exact u1640

def b11173 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 56 84 40 67 195 323), lower := (rows 7 131 292 56 84 40 64 128 256), losses := [] }

theorem u11173 : Upper (D 6) (R 6) [6,129,288,48,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11173
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11174 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 56 84 96 75 139 267), lower := (rows 7 131 292 56 84 96 64 128 256), losses := [] }

theorem u11174 : Upper (D 6) (R 6) [6,129,288,48,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11174
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11175 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 195, targets := 32 }], pairs := [(0,5),(1,5),(2,0)], upper := (rows 7 131 292 56 88 33 70 198 326), lower := (rows 7 131 292 56 88 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 49 32 65 129 257), good := (rows 478 466 316 60 88 508 64 128 256) }] }

theorem u11175 : Upper (D 6) (R 6) [6,129,288,48,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11175
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11176 : Route 9 := (fun mask => (mask,id))

def c11176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11176 : Upper (D 6) (R 6) [6,129,288,48,72,2] 13 := by
  apply FastRouting.sound _ _ [6,129,288,48,72,2] 13 (by decide) (choices 1) [1,4] r11176 c11176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1641
  · exact u1642

def b11177 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 56 88 36 67 195 323), lower := (rows 7 131 292 56 88 36 64 128 256), losses := [] }

theorem u11177 : Upper (D 6) (R 6) [6,129,288,48,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11177
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11178 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 292 56 88 96 71 135 263), lower := (rows 7 131 292 56 88 96 64 128 256), losses := [] }

theorem u11178 : Upper (D 6) (R 6) [6,129,288,48,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11178
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11179 : PairBound 9 := { available := 56, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 73 82 36 120 184 312), lower := (rows 7 131 292 73 82 36 64 128 256), losses := [] }

theorem u11179 : Upper (D 6) (R 6) [6,129,288,65,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11179
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11180 : Route 9 := (fun mask => (mask,id))

def c11180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11180 : Upper (D 6) (R 6) [6,129,288,65,66,8] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65,66,8] 13 (by decide) (choices 1) [4,16,32] r11180 c11180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1643
  · exact u1644
  · exact u1645

def r11181 : Route 9 := (fun mask => (mask,id))

def c11181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11181 : Upper (D 6) (R 6) [6,129,288,65,66,16] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65,66,16] 13 (by decide) (choices 1) [4,8,32] r11181 c11181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1646
  · exact u1647
  · exact u1648

def r11182 : Route 9 := (fun mask => (mask,id))

def c11182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11182 : Upper (D 6) (R 6) [6,129,288,65,68,2] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65,68,2] 13 (by decide) (choices 1) [8,16,32] r11182 c11182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1649
  · exact u1650
  · exact u1651

def r11183 : Route 9 := (fun mask => (mask,id))

def c11183 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11183 : Upper (D 6) (R 6) [6,129,288,65,68,8] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65,68,8] 13 (by decide) (choices 1) [2,16,32] r11183 c11183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1652
  · exact u1653
  · exact u1654

def r11184 : Route 9 := (fun mask => (mask,id))

def c11184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11184 : Upper (D 6) (R 6) [6,129,288,65,68,16] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65,68,16] 13 (by decide) (choices 1) [2,8,32] r11184 c11184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1655
  · exact u1656
  · exact u1657

def b11185 : PairBound 9 := { available := 28, camps := [], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 73 112 34 92 156 284), lower := (rows 7 131 292 73 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 162 292 508 112 34 64 128 256) },{ target := 1, region := (rows 1 0 52 11 52 32 97 161 289), good := (rows 477 457 500 457 500 508 64 128 256) }] }

theorem u11185 : Upper (D 6) (R 6) [6,129,288,65,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11185
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11186 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 73 112 36 90 154 282), lower := (rows 7 131 292 73 112 36 64 128 256), losses := [] }

theorem u11186 : Upper (D 6) (R 6) [6,129,288,65,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11186
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11187 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 131 292 73 112 40 86 150 278), lower := (rows 7 131 292 73 112 40 64 128 256), losses := [] }

theorem u11187 : Upper (D 6) (R 6) [6,129,288,65,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11187
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11188 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 73 112 48 78 142 270), lower := (rows 7 131 292 73 112 48 64 128 256), losses := [] }

theorem u11188 : Upper (D 6) (R 6) [6,129,288,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11188
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11189 : Route 9 := (fun mask => (mask,id))

def c11189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11189 : Upper (D 6) (R 6) [6,129,288,66,68,1] 13 := by
  apply FastRouting.sound _ _ [6,129,288,66,68,1] 13 (by decide) (choices 1) [8,16,32] r11189 c11189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1658
  · exact u1659
  · exact u1660

def r11190 : Route 9 := (fun mask => (mask,id))

def c11190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11190 : Upper (D 6) (R 6) [6,129,288,66,68,8] 13 := by
  apply FastRouting.sound _ _ [6,129,288,66,68,8] 13 (by decide) (choices 1) [1,16,32] r11190 c11190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1661
  · exact u1662
  · exact u1663

def r11191 : Route 9 := (fun mask => (mask,id))

def c11191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11191 : Upper (D 6) (R 6) [6,129,288,66,68,16] 13 := by
  apply FastRouting.sound _ _ [6,129,288,66,68,16] 13 (by decide) (choices 1) [1,8,32] r11191 c11191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1664
  · exact u1665
  · exact u1666

def b11192 : PairBound 9 := { available := 28, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 131 292 74 112 33 92 156 284), lower := (rows 7 131 292 74 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 52 11 52 32 97 161 289), good := (rows 478 458 500 74 500 508 64 128 256) }] }

theorem u11192 : Upper (D 6) (R 6) [6,129,288,66,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11192
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11193 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 74 112 36 89 153 281), lower := (rows 7 131 292 74 112 36 64 128 256), losses := [] }

theorem u11193 : Upper (D 6) (R 6) [6,129,288,66,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11193
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11194 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 131 292 74 112 40 85 149 277), lower := (rows 7 131 292 74 112 40 64 128 256), losses := [] }

theorem u11194 : Upper (D 6) (R 6) [6,129,288,66,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11194
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11195 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 74 112 48 77 141 269), lower := (rows 7 131 292 74 112 48 64 128 256), losses := [] }

theorem u11195 : Upper (D 6) (R 6) [6,129,288,66,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11195
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11196 : Route 9 := (fun mask => (mask,id))

def c11196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11196 : Upper (D 6) (R 6) [6,129,288,68,96,1] 13 := by
  apply FastRouting.sound _ _ [6,129,288,68,96,1] 13 (by decide) (choices 1) [2,8,16] r11196 c11196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1667
  · exact u1668
  · exact u1669

def r11197 : Route 9 := (fun mask => (mask,id))

def c11197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11197 : Upper (D 6) (R 6) [6,129,288,68,96,2] 13 := by
  apply FastRouting.sound _ _ [6,129,288,68,96,2] 13 (by decide) (choices 1) [1,8,16] r11197 c11197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1670
  · exact u1671
  · exact u1672

def b11198 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 131 292 76 112 40 83 147 275), lower := (rows 7 131 292 76 112 40 64 128 256), losses := [] }

theorem u11198 : Upper (D 6) (R 6) [6,129,288,68,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11198
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11199 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 76 112 48 75 139 267), lower := (rows 7 131 292 76 112 48 64 128 256), losses := [] }

theorem u11199 : Upper (D 6) (R 6) [6,129,288,68,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11199
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11200 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 40, targets := 68 },{ cop := 3, region := 340, targets := 2 }], pairs := [(2,1),(3,2),(3,6)], upper := (rows 7 138 276 41 81 34 100 228 356), lower := (rows 7 138 276 41 81 34 64 128 256), losses := [] }

theorem u11200 : Upper (D 6) (R 6) [6,136,272,33,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11200
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11201 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 194, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 138 276 41 81 36 98 226 354), lower := (rows 7 138 276 41 81 36 64 128 256), losses := [] }

theorem u11201 : Upper (D 6) (R 6) [6,136,272,33,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11201
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11202 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 40, targets := 6 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 7 138 276 41 81 96 102 166 294), lower := (rows 7 138 276 41 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 121 65 129 257), good := (rows 486 170 308 490 500 96 96 128 256) }] }

theorem u11202 : Upper (D 6) (R 6) [6,136,272,33,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11202
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11203 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 138 276 41 82 33 100 228 356), lower := (rows 7 138 276 41 82 33 64 128 256), losses := [] }

theorem u11203 : Upper (D 6) (R 6) [6,136,272,33,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11203
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11204 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 210, targets := 4 },{ cop := 0, region := 40, targets := 2 }], pairs := [(1,2),(3,1),(4,2)], upper := (rows 7 138 276 41 82 36 97 225 353), lower := (rows 7 138 276 41 82 36 64 128 256), losses := [] }

theorem u11204 : Upper (D 6) (R 6) [6,136,272,33,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11204
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11205 : Route 9 := (fun mask => (mask,id))

def c11205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11205 : Upper (D 6) (R 6) [6,136,272,33,66,64] 13 := by
  apply FastRouting.sound _ _ [6,136,272,33,66,64] 13 (by decide) (choices 1) [1,4,32] r11205 c11205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1673
  · exact u1674
  · exact u1675

def b11206 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 138 276 41 84 33 98 226 354), lower := (rows 7 138 276 41 84 33 64 128 256), losses := [] }

theorem u11206 : Upper (D 6) (R 6) [6,136,272,33,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11206
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11207 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 3, region := 340, targets := 2 }], pairs := [(1,2),(2,1),(3,2)], upper := (rows 7 138 276 41 84 34 97 225 353), lower := (rows 7 138 276 41 84 34 64 128 256), losses := [] }

theorem u11207 : Upper (D 6) (R 6) [6,136,272,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11207
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11208 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 3, region := 130, targets := 64 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 138 276 41 84 96 99 163 291), lower := (rows 7 138 276 41 84 96 64 128 256), losses := [] }

theorem u11208 : Upper (D 6) (R 6) [6,136,272,33,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11208
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11209 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 138 276 41 112 33 70 198 326), lower := (rows 7 138 276 41 112 33 64 128 256), losses := [] }

theorem u11209 : Upper (D 6) (R 6) [6,136,272,33,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11209
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11210 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 40, targets := 68 },{ cop := 3, region := 340, targets := 2 }], pairs := [(2,1),(3,2),(3,6)], upper := (rows 7 138 276 41 112 34 69 197 325), lower := (rows 7 138 276 41 112 34 64 128 256), losses := [] }

theorem u11210 : Upper (D 6) (R 6) [6,136,272,33,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11210
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11211 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 194, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 138 276 41 112 36 67 195 323), lower := (rows 7 138 276 41 112 36 64 128 256), losses := [] }

theorem u11211 : Upper (D 6) (R 6) [6,136,272,33,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11211
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11212 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 138 276 41 112 96 71 135 263), lower := (rows 7 138 276 41 112 96 64 128 256), losses := [] }

theorem u11212 : Upper (D 6) (R 6) [6,136,272,33,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11212
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11213 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 138 276 42 112 33 69 197 325), lower := (rows 7 138 276 42 112 33 64 128 256), losses := [] }

theorem u11213 : Upper (D 6) (R 6) [6,136,272,34,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11213
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11214 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 40, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 138 276 42 112 36 65 193 321), lower := (rows 7 138 276 42 112 36 64 128 256), losses := [] }

theorem u11214 : Upper (D 6) (R 6) [6,136,272,34,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11214
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11215 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 138 276 42 112 96 69 133 261), lower := (rows 7 138 276 42 112 96 64 128 256), losses := [] }

theorem u11215 : Upper (D 6) (R 6) [6,136,272,34,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11215
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11216 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 112, targets := 4 },{ cop := 0, region := 40, targets := 64 }], pairs := [(3,1),(3,6),(4,2)], upper := (rows 7 138 276 44 82 33 97 225 353), lower := (rows 7 138 276 44 82 33 64 128 256), losses := [] }

theorem u11216 : Upper (D 6) (R 6) [6,136,272,36,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11216
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11217 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 131, targets := 64 },{ cop := 0, region := 104, targets := 2 }], pairs := [(0,6),(1,6),(3,1)], upper := (rows 7 138 276 44 82 96 97 161 289), lower := (rows 7 138 276 44 82 96 64 128 256), losses := [] }

theorem u11217 : Upper (D 6) (R 6) [6,136,272,36,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11217
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11218 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 138 292 25 50 33 68 196 324), lower := (rows 7 138 292 25 50 33 64 128 256), losses := [] }

theorem u11218 : Upper (D 6) (R 6) [6,136,288,17,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11218
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11219 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 25 50 36 65 193 321), lower := (rows 7 138 292 25 50 36 64 128 256), losses := [] }

theorem u11219 : Upper (D 6) (R 6) [6,136,288,17,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11219
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11219
end Delivery.IrregularNine14.P06
