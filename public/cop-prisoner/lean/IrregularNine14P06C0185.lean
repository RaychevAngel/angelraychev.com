import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0026
import IrregularNine14P06C0027

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11100 : Route 9 := (fun mask => (mask,id))

def c11100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11100 : Upper (D 6) (R 6) [6,129,288,17,96,2] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,96,2] 13 (by decide) (choices 1) [4,8] r11100 c11100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1585
  · exact u1586

def b11101 : PairBound 9 := { available := 74, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 25 112 36 74 202 330), lower := (rows 7 131 292 25 112 36 64 128 256), losses := [] }

theorem u11101 : Upper (D 6) (R 6) [6,129,288,17,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11101
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11102 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 25 112 40 70 198 326), lower := (rows 7 131 292 25 112 40 64 128 256), losses := [] }

theorem u11102 : Upper (D 6) (R 6) [6,129,288,17,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11102
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11103 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 25 112 96 78 142 270), lower := (rows 7 131 292 25 112 96 64 128 256), losses := [] }

theorem u11103 : Upper (D 6) (R 6) [6,129,288,17,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11103
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11104 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 131 292 26 49 36 72 200 328), lower := (rows 7 131 292 26 49 36 64 128 256), losses := [] }

theorem u11104 : Upper (D 6) (R 6) [6,129,288,18,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11104
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11105 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 131 292 26 49 40 68 196 324), lower := (rows 7 131 292 26 49 40 64 128 256), losses := [] }

theorem u11105 : Upper (D 6) (R 6) [6,129,288,18,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11105
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11106 : Route 9 := (fun mask => (mask,id))

def c11106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11106 : Upper (D 6) (R 6) [6,129,288,18,33,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,33,64] 13 (by decide) (choices 1) [4,8] r11106 c11106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1587
  · exact u1588

def b11107 : PairBound 9 := { available := 104, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 26 81 36 104 232 360), lower := (rows 7 131 292 26 81 36 64 128 256), losses := [] }

theorem u11107 : Upper (D 6) (R 6) [6,129,288,18,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11107
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11108 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 26 81 40 100 228 356), lower := (rows 7 131 292 26 81 40 64 128 256), losses := [] }

theorem u11108 : Upper (D 6) (R 6) [6,129,288,18,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11108
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11109 : Route 9 := (fun mask => (mask,id))

def c11109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11109 : Upper (D 6) (R 6) [6,129,288,18,65,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,65,64] 13 (by decide) (choices 1) [4,8,32] r11109 c11109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1589
  · exact u1590
  · exact u1591

def b11110 : PairBound 9 := { available := 104, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 131 292 26 84 33 104 232 360), lower := (rows 7 131 292 26 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 9 52 32 96 160 288), good := (rows 30 138 500 26 84 508 64 128 256) }] }

theorem u11110 : Upper (D 6) (R 6) [6,129,288,18,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11110
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11111 : Route 9 := (fun mask => (mask,id))

def c11111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11111 : Upper (D 6) (R 6) [6,129,288,18,68,8] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,68,8] 13 (by decide) (choices 1) [1,32] r11111 c11111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1592
  · exact u1593

def r11112 : Route 9 := (fun mask => (mask,id))

def c11112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11112 : Upper (D 6) (R 6) [6,129,288,18,68,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,68,64] 13 (by decide) (choices 1) [1,8,32] r11112 c11112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1594
  · exact u1595
  · exact u1596

def b11113 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 26 88 33 100 228 356), lower := (rows 7 131 292 26 88 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 11 49 32 100 164 292), good := (rows 478 154 500 26 88 508 64 128 256) }] }

theorem u11113 : Upper (D 6) (R 6) [6,129,288,18,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11113
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11114 : PairBound 9 := { available := 97, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 26 88 36 97 225 353), lower := (rows 7 131 292 26 88 36 64 128 256), losses := [] }

theorem u11114 : Upper (D 6) (R 6) [6,129,288,18,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11114
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11115 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 26 88 96 101 165 293), lower := (rows 7 131 292 26 88 96 64 128 256), losses := [] }

theorem u11115 : Upper (D 6) (R 6) [6,129,288,18,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11115
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11116 : PairBound 9 := { available := 76, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 131 292 26 112 33 76 204 332), lower := (rows 7 131 292 26 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 52 9 52 32 105 169 297), good := (rows 478 458 500 478 500 508 64 128 256) }] }

theorem u11116 : Upper (D 6) (R 6) [6,129,288,18,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11116
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11117 : PairBound 9 := { available := 73, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 26 112 36 73 201 329), lower := (rows 7 131 292 26 112 36 64 128 256), losses := [] }

theorem u11117 : Upper (D 6) (R 6) [6,129,288,18,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11117
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11118 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 26 112 40 69 197 325), lower := (rows 7 131 292 26 112 40 64 128 256), losses := [] }

theorem u11118 : Upper (D 6) (R 6) [6,129,288,18,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11118
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11119 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 26 112 96 77 141 269), lower := (rows 7 131 292 26 112 96 64 128 256), losses := [] }

theorem u11119 : Upper (D 6) (R 6) [6,129,288,18,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11119
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11120 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 28 49 34 72 200 328), lower := (rows 7 131 292 28 49 34 64 128 256), losses := [] }

theorem u11120 : Upper (D 6) (R 6) [6,129,288,20,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11120
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11121 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 7 131 292 28 49 40 66 194 322), lower := (rows 7 131 292 28 49 40 64 128 256), losses := [] }

theorem u11121 : Upper (D 6) (R 6) [6,129,288,20,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11121
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11122 : Route 9 := (fun mask => (mask,id))

def c11122 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11122 : Upper (D 6) (R 6) [6,129,288,20,33,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,33,64] 13 (by decide) (choices 1) [2,8] r11122 c11122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1597
  · exact u1598

def b11123 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 28 50 33 72 200 328), lower := (rows 7 131 292 28 50 33 64 128 256), losses := [] }

theorem u11123 : Upper (D 6) (R 6) [6,129,288,20,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11123
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11124 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 292 28 50 40 65 193 321), lower := (rows 7 131 292 28 50 40 64 128 256), losses := [] }

theorem u11124 : Upper (D 6) (R 6) [6,129,288,20,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11124
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11125 : Route 9 := (fun mask => (mask,id))

def c11125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11125 : Upper (D 6) (R 6) [6,129,288,20,34,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,34,64] 13 (by decide) (choices 1) [1,8] r11125 c11125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1599
  · exact u1600

def r11126 : Route 9 := (fun mask => (mask,id))

def c11126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11126 : Upper (D 6) (R 6) [6,129,288,20,65,2] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,65,2] 13 (by decide) (choices 1) [8,32] r11126 c11126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1601
  · exact u1602

def r11127 : Route 9 := (fun mask => (mask,id))

def c11127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11127 : Upper (D 6) (R 6) [6,129,288,20,65,8] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,65,8] 13 (by decide) (choices 1) [2,32] r11127 c11127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1603
  · exact u1604

def r11128 : Route 9 := (fun mask => (mask,id))

def c11128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11128 : Upper (D 6) (R 6) [6,129,288,20,65,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,65,64] 13 (by decide) (choices 1) [2,8,32] r11128 c11128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1605
  · exact u1606
  · exact u1607

def b11129 : PairBound 9 := { available := 104, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 131 292 28 82 33 104 232 360), lower := (rows 7 131 292 28 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 17 32 100 164 292), good := (rows 478 154 492 476 82 508 64 128 256) }] }

theorem u11129 : Upper (D 6) (R 6) [6,129,288,20,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11129
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11130 : Route 9 := (fun mask => (mask,id))

def c11130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11130 : Upper (D 6) (R 6) [6,129,288,20,66,8] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,66,8] 13 (by decide) (choices 1) [1,32] r11130 c11130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1608
  · exact u1609

def r11131 : Route 9 := (fun mask => (mask,id))

def c11131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11131 : Upper (D 6) (R 6) [6,129,288,20,66,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,66,64] 13 (by decide) (choices 1) [1,8,32] r11131 c11131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1610
  · exact u1611
  · exact u1612

def r11132 : Route 9 := (fun mask => (mask,id))

def c11132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11132 : Upper (D 6) (R 6) [6,129,288,20,72,1] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,72,1] 13 (by decide) (choices 1) [2,32] r11132 c11132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1613
  · exact u1614

def r11133 : Route 9 := (fun mask => (mask,id))

def c11133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11133 : Upper (D 6) (R 6) [6,129,288,20,72,2] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,72,2] 13 (by decide) (choices 1) [1,32] r11133 c11133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1615
  · exact u1616

def b11134 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 28 88 96 99 163 291), lower := (rows 7 131 292 28 88 96 64 128 256), losses := [] }

theorem u11134 : Upper (D 6) (R 6) [6,129,288,20,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11134
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11135 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5),(2,0)], upper := (rows 7 131 292 28 112 33 74 202 330), lower := (rows 7 131 292 28 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 60 48 32 65 129 257), good := (rows 462 450 316 28 124 508 64 128 256) }] }

theorem u11135 : Upper (D 6) (R 6) [6,129,288,20,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11135
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11136 : Route 9 := (fun mask => (mask,id))

def c11136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11136 : Upper (D 6) (R 6) [6,129,288,20,96,2] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,96,2] 13 (by decide) (choices 1) [1,8] r11136 c11136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1617
  · exact u1618

def b11137 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 131 292 28 112 40 67 195 323), lower := (rows 7 131 292 28 112 40 64 128 256), losses := [] }

theorem u11137 : Upper (D 6) (R 6) [6,129,288,20,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11137
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11138 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 292 28 112 96 75 139 267), lower := (rows 7 131 292 28 112 96 64 128 256), losses := [] }

theorem u11138 : Upper (D 6) (R 6) [6,129,288,20,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11138
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11139 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 7 131 292 41 82 36 88 216 344), lower := (rows 7 131 292 41 82 36 64 128 256), losses := [] }

theorem u11139 : Upper (D 6) (R 6) [6,129,288,33,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11139
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11140 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 131 292 41 82 40 84 212 340), lower := (rows 7 131 292 41 82 40 64 128 256), losses := [] }

theorem u11140 : Upper (D 6) (R 6) [6,129,288,33,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11140
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11141 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 41 82 48 76 204 332), lower := (rows 7 131 292 41 82 48 64 128 256), losses := [] }

theorem u11141 : Upper (D 6) (R 6) [6,129,288,33,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11141
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11142 : Route 9 := (fun mask => (mask,id))

def c11142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11142 : Upper (D 6) (R 6) [6,129,288,33,66,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,33,66,64] 13 (by decide) (choices 1) [4,8,16] r11142 c11142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1619
  · exact u1620
  · exact u1621

def b11143 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 41 84 34 88 216 344), lower := (rows 7 131 292 41 84 34 64 128 256), losses := [] }

theorem u11143 : Upper (D 6) (R 6) [6,129,288,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11143
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11144 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 131 292 41 84 40 82 210 338), lower := (rows 7 131 292 41 84 40 64 128 256), losses := [] }

theorem u11144 : Upper (D 6) (R 6) [6,129,288,33,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11144
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11145 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 131 292 41 84 48 74 202 330), lower := (rows 7 131 292 41 84 48 64 128 256), losses := [] }

theorem u11145 : Upper (D 6) (R 6) [6,129,288,33,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11145
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11146 : Route 9 := (fun mask => (mask,id))

def c11146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11146 : Upper (D 6) (R 6) [6,129,288,33,68,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,33,68,64] 13 (by decide) (choices 1) [2,8,16] r11146 c11146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1622
  · exact u1623
  · exact u1624

def b11147 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 41 88 34 84 212 340), lower := (rows 7 131 292 41 88 34 64 128 256), losses := [] }

theorem u11147 : Upper (D 6) (R 6) [6,129,288,33,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11147
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11148 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 7 131 292 41 88 36 82 210 338), lower := (rows 7 131 292 41 88 36 64 128 256), losses := [] }

theorem u11148 : Upper (D 6) (R 6) [6,129,288,33,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11148
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11149 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 41 88 48 70 198 326), lower := (rows 7 131 292 41 88 48 64 128 256), losses := [] }

theorem u11149 : Upper (D 6) (R 6) [6,129,288,33,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11149
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11150 : Route 9 := (fun mask => (mask,id))

def c11150 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11150 : Upper (D 6) (R 6) [6,129,288,33,72,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,33,72,64] 13 (by decide) (choices 1) [2,4,16] r11150 c11150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1625
  · exact u1626
  · exact u1627

def b11151 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 131 292 42 81 36 88 216 344), lower := (rows 7 131 292 42 81 36 64 128 256), losses := [] }

theorem u11151 : Upper (D 6) (R 6) [6,129,288,34,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11151
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11152 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 131 292 42 81 40 84 212 340), lower := (rows 7 131 292 42 81 40 64 128 256), losses := [] }

theorem u11152 : Upper (D 6) (R 6) [6,129,288,34,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11152
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11153 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 42 81 48 76 204 332), lower := (rows 7 131 292 42 81 48 64 128 256), losses := [] }

theorem u11153 : Upper (D 6) (R 6) [6,129,288,34,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11153
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11154 : Route 9 := (fun mask => (mask,id))

def c11154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11154 : Upper (D 6) (R 6) [6,129,288,34,65,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,34,65,64] 13 (by decide) (choices 1) [4,8,16] r11154 c11154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1628
  · exact u1629
  · exact u1630

def b11155 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 42 84 33 88 216 344), lower := (rows 7 131 292 42 84 33 64 128 256), losses := [] }

theorem u11155 : Upper (D 6) (R 6) [6,129,288,34,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11155
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11156 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 131 292 42 84 40 81 209 337), lower := (rows 7 131 292 42 84 40 64 128 256), losses := [] }

theorem u11156 : Upper (D 6) (R 6) [6,129,288,34,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11156
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11157 : Route 9 := (fun mask => (mask,id))

def c11157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11157 : Upper (D 6) (R 6) [6,129,288,34,68,16] 13 := by
  apply FastRouting.sound _ _ [6,129,288,34,68,16] 13 (by decide) (choices 1) [1,8] r11157 c11157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1631
  · exact u1632

def r11158 : Route 9 := (fun mask => (mask,id))

def c11158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11158 : Upper (D 6) (R 6) [6,129,288,34,68,64] 13 := by
  apply FastRouting.sound _ _ [6,129,288,34,68,64] 13 (by decide) (choices 1) [1,8,16] r11158 c11158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1633
  · exact u1634
  · exact u1635

def b11159 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 42 88 33 84 212 340), lower := (rows 7 131 292 42 88 33 64 128 256), losses := [] }

theorem u11159 : Upper (D 6) (R 6) [6,129,288,34,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11159
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11159
end Delivery.IrregularNine14.P06
