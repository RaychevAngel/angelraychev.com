import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0000

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 137 276 34 88 152 280), lower := (rows 7 35 76 137 276 34 64 128 256), losses := [] }

theorem u120 : Upper (D 4) (R 4) [6,33,72,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b120
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b121 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 76 137 276 40 82 146 274), lower := (rows 7 35 76 137 276 40 64 128 256), losses := [] }

theorem u121 : Upper (D 4) (R 4) [6,33,72,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b121
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 137 276 48 90 154 282), lower := (rows 7 35 76 137 276 48 64 128 256), losses := [] }

theorem u122 : Upper (D 4) (R 4) [6,33,72,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b122
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 137 280 34 84 148 276), lower := (rows 7 35 76 137 280 34 64 128 256), losses := [] }

theorem u123 : Upper (D 4) (R 4) [6,33,72,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b123
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 137 280 36 82 146 274), lower := (rows 7 35 76 137 280 36 64 128 256), losses := [] }

theorem u124 : Upper (D 4) (R 4) [6,33,72,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b124
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r125 : Route 9 := (fun mask => (mask,id))

def c125 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u125 : Upper (D 4) (R 4) [6,33,72,129,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,264,16] 13 (by decide) (choices 1) [2,4,16] r125 c125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8
  · exact u9
  · exact u10

def b126 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 138 273 36 88 152 280), lower := (rows 7 35 76 138 273 36 64 128 256), losses := [] }

theorem u126 : Upper (D 4) (R 4) [6,33,72,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b126
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 35 76 138 273 40 84 148 276), lower := (rows 7 35 76 138 273 40 64 128 256), losses := [] }

theorem u127 : Upper (D 4) (R 4) [6,33,72,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b127
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 138 273 48 92 156 284), lower := (rows 7 35 76 138 273 48 64 128 256), losses := [] }

theorem u128 : Upper (D 4) (R 4) [6,33,72,130,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b128
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 138 276 33 88 152 280), lower := (rows 7 35 76 138 276 33 64 128 256), losses := [] }

theorem u129 : Upper (D 4) (R 4) [6,33,72,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b129
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 35 76 138 276 40 81 145 273), lower := (rows 7 35 76 138 276 40 64 128 256), losses := [] }

theorem u130 : Upper (D 4) (R 4) [6,33,72,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b130
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 138 276 48 89 153 281), lower := (rows 7 35 76 138 276 48 64 128 256), losses := [] }

theorem u131 : Upper (D 4) (R 4) [6,33,72,130,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b131
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 138 280 33 84 148 276), lower := (rows 7 35 76 138 280 33 64 128 256), losses := [] }

theorem u132 : Upper (D 4) (R 4) [6,33,72,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b132
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 138 280 36 81 145 273), lower := (rows 7 35 76 138 280 36 64 128 256), losses := [] }

theorem u133 : Upper (D 4) (R 4) [6,33,72,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b133
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r134 : Route 9 := (fun mask => (mask,id))

def c134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u134 : Upper (D 4) (R 4) [6,33,72,130,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,264,16] 13 (by decide) (choices 1) [1,4,16] r134 c134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11
  · exact u12
  · exact u13

def b135 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 140 26 33 336 400 272), lower := (rows 7 35 76 140 26 33 64 128 256), losses := [] }

theorem u135 : Upper (D 4) (R 4) [6,33,72,132,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b135
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r136 : Route 9 := (fun mask => (mask,id))

def c136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u136 : Upper (D 4) (R 4) [6,33,72,132,10,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,10,16] 13 (by decide) (choices 1) [1,16,256] r136 c136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14
  · exact u15
  · exact u16

def b137 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 35 76 140 26 288 81 145 273), lower := (rows 7 35 76 140 26 288 64 128 256), losses := [] }

theorem u137 : Upper (D 4) (R 4) [6,33,72,132,10,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b137
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 140 273 34 88 152 280), lower := (rows 7 35 76 140 273 34 64 128 256), losses := [] }

theorem u138 : Upper (D 4) (R 4) [6,33,72,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b138
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 272, targets := 4 }], pairs := [(4,2)], upper := (rows 7 35 76 140 273 40 82 146 274), lower := (rows 7 35 76 140 273 40 64 128 256), losses := [] }

theorem u139 : Upper (D 4) (R 4) [6,33,72,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b139
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 140 273 48 90 154 282), lower := (rows 7 35 76 140 273 48 64 128 256), losses := [] }

theorem u140 : Upper (D 4) (R 4) [6,33,72,132,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b140
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 140 274 33 88 152 280), lower := (rows 7 35 76 140 274 33 64 128 256), losses := [] }

theorem u141 : Upper (D 4) (R 4) [6,33,72,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b141
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 4 }], pairs := [(4,2)], upper := (rows 7 35 76 140 274 40 81 145 273), lower := (rows 7 35 76 140 274 40 64 128 256), losses := [] }

theorem u142 : Upper (D 4) (R 4) [6,33,72,132,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b142
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r143 : Route 9 := (fun mask => (mask,id))

def c143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u143 : Upper (D 4) (R 4) [6,33,72,132,258,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,258,16] 13 (by decide) (choices 1) [1,8,16] r143 c143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17
  · exact u18
  · exact u19

def b144 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 140 280 33 82 146 274), lower := (rows 7 35 76 140 280 33 64 128 256), losses := [] }

theorem u144 : Upper (D 4) (R 4) [6,33,72,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b144
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 140 280 34 81 145 273), lower := (rows 7 35 76 140 280 34 64 128 256), losses := [] }

theorem u145 : Upper (D 4) (R 4) [6,33,72,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b145
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r146 : Route 9 := (fun mask => (mask,id))

def c146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u146 : Upper (D 4) (R 4) [6,33,72,132,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,264,16] 13 (by decide) (choices 1) [1,2,16] r146 c146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20
  · exact u21
  · exact u22

def b147 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 273 34 92 156 284), lower := (rows 7 35 76 152 273 34 64 128 256), losses := [] }

theorem u147 : Upper (D 4) (R 4) [6,33,72,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b147
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 273 36 90 154 282), lower := (rows 7 35 76 152 273 36 64 128 256), losses := [] }

theorem u148 : Upper (D 4) (R 4) [6,33,72,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b148
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 76 152 273 40 86 150 278), lower := (rows 7 35 76 152 273 40 64 128 256), losses := [] }

theorem u149 : Upper (D 4) (R 4) [6,33,72,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b149
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 152 273 48 78 142 270), lower := (rows 7 35 76 152 273 48 64 128 256), losses := [] }

theorem u150 : Upper (D 4) (R 4) [6,33,72,144,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b150
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 274 33 92 156 284), lower := (rows 7 35 76 152 274 33 64 128 256), losses := [] }

theorem u151 : Upper (D 4) (R 4) [6,33,72,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b151
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 274 36 89 153 281), lower := (rows 7 35 76 152 274 36 64 128 256), losses := [] }

theorem u152 : Upper (D 4) (R 4) [6,33,72,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b152
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 76 152 274 40 85 149 277), lower := (rows 7 35 76 152 274 40 64 128 256), losses := [] }

theorem u153 : Upper (D 4) (R 4) [6,33,72,144,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b153
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 13, camps := [], pairs := [(0,3)], upper := (rows 7 35 76 152 274 48 77 141 269), lower := (rows 7 35 76 152 274 48 64 128 256), losses := [{ target := 3, region := (rows 5 6 4 0 16 56 64 128 256), good := (rows 7 35 103 176 306 48 64 128 256) }] }

theorem u154 : Upper (D 4) (R 4) [6,33,72,144,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b154
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 276 33 90 154 282), lower := (rows 7 35 76 152 276 33 64 128 256), losses := [] }

theorem u155 : Upper (D 4) (R 4) [6,33,72,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b155
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 276 34 89 153 281), lower := (rows 7 35 76 152 276 34 64 128 256), losses := [] }

theorem u156 : Upper (D 4) (R 4) [6,33,72,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b156
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 76 152 276 40 83 147 275), lower := (rows 7 35 76 152 276 40 64 128 256), losses := [] }

theorem u157 : Upper (D 4) (R 4) [6,33,72,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b157
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 276 48 75 139 267), lower := (rows 7 35 76 152 276 48 64 128 256), losses := [] }

theorem u158 : Upper (D 4) (R 4) [6,33,72,144,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b158
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 280 33 86 150 278), lower := (rows 7 35 76 152 280 33 64 128 256), losses := [] }

theorem u159 : Upper (D 4) (R 4) [6,33,72,144,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b159
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 280 34 85 149 277), lower := (rows 7 35 76 152 280 34 64 128 256), losses := [] }

theorem u160 : Upper (D 4) (R 4) [6,33,72,144,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b160
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 152 280 36 83 147 275), lower := (rows 7 35 76 152 280 36 64 128 256), losses := [] }

theorem u161 : Upper (D 4) (R 4) [6,33,72,144,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b161
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 7, camps := [], pairs := [(0,3)], upper := (rows 7 35 76 152 280 48 71 135 263), lower := (rows 7 35 76 152 280 48 64 128 256), losses := [{ target := 3, region := (rows 5 6 4 0 16 56 69 133 261), good := (rows 455 483 487 176 304 48 64 128 256) }] }

theorem u162 : Upper (D 4) (R 4) [6,33,72,144,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b162
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 392 26 33 84 148 276), lower := (rows 7 35 76 392 26 33 64 128 256), losses := [] }

theorem u163 : Upper (D 4) (R 4) [6,33,72,384,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b163
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 392 26 36 81 145 273), lower := (rows 7 35 76 392 26 36 64 128 256), losses := [] }

theorem u164 : Upper (D 4) (R 4) [6,33,72,384,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b164
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r165 : Route 9 := (fun mask => (mask,id))

def c165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u165 : Upper (D 4) (R 4) [6,33,72,384,10,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,10,16] 13 (by decide) (choices 1) [1,4,16] r165 c165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23
  · exact u24
  · exact u25

def b166 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 26 276 33 88 152 280), lower := (rows 7 35 196 26 276 33 64 128 256), losses := [] }

theorem u166 : Upper (D 4) (R 4) [6,33,192,18,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b166
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r167 : Route 9 := (fun mask => (mask,id))

def c167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u167 : Upper (D 4) (R 4) [6,33,192,18,260,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,260,8] 13 (by decide) (choices 1) [1,8,16] r167 c167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26
  · exact u27
  · exact u28

def b168 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 197, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 196 26 276 48 73 137 265), lower := (rows 7 35 196 26 276 48 64 128 256), losses := [] }

theorem u168 : Upper (D 4) (R 4) [6,33,192,18,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b168
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 28 273 34 88 152 280), lower := (rows 7 35 196 28 273 34 64 128 256), losses := [] }

theorem u169 : Upper (D 4) (R 4) [6,33,192,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b169
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 196 28 273 40 90 154 282), lower := (rows 7 35 196 28 273 40 64 128 256), losses := [] }

theorem u170 : Upper (D 4) (R 4) [6,33,192,20,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b170
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 28 273 48 74 138 266), lower := (rows 7 35 196 28 273 48 64 128 256), losses := [] }

theorem u171 : Upper (D 4) (R 4) [6,33,192,20,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b171
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 28 274 33 88 152 280), lower := (rows 7 35 196 28 274 33 64 128 256), losses := [] }

theorem u172 : Upper (D 4) (R 4) [6,33,192,20,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b172
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 196 28 274 40 89 153 281), lower := (rows 7 35 196 28 274 40 64 128 256), losses := [] }

theorem u173 : Upper (D 4) (R 4) [6,33,192,20,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b173
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 28 274 48 73 137 265), lower := (rows 7 35 196 28 274 48 64 128 256), losses := [] }

theorem u174 : Upper (D 4) (R 4) [6,33,192,20,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b174
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 28 280 33 90 154 282), lower := (rows 7 35 196 28 280 33 64 128 256), losses := [] }

theorem u175 : Upper (D 4) (R 4) [6,33,192,20,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b175
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 28 280 34 89 153 281), lower := (rows 7 35 196 28 280 34 64 128 256), losses := [] }

theorem u176 : Upper (D 4) (R 4) [6,33,192,20,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b176
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 35 196 28 280 40 83 147 275), lower := (rows 7 35 196 28 280 40 64 128 256), losses := [] }

theorem u177 : Upper (D 4) (R 4) [6,33,192,20,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b177
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 28 280 48 75 139 267), lower := (rows 7 35 196 28 280 48 64 128 256), losses := [] }

theorem u178 : Upper (D 4) (R 4) [6,33,192,20,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b178
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1)], upper := (rows 7 42 84 137 273 34 92 156 284), lower := (rows 7 42 84 137 273 34 64 128 256), losses := [] }

theorem u179 : Upper (D 4) (R 4) [6,40,80,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b179
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P04
