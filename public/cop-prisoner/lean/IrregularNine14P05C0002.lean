import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r120 : Route 9 := (fun mask => (mask,id))

def c120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u120 : Upper (D 5) (R 5) [6,17,40,68,136,2,256] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68,136,2,256] 13 (by decide) (choices 1) [1,32] r120 c120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b121 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 44 76 152 288 65 162 290), lower := (rows 7 19 44 76 152 288 65 128 256), losses := [] }

theorem u121 : Upper (D 5) (R 5) [6,17,40,68,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 7 19 44 76 152 288 66 161 289), lower := (rows 7 19 44 76 152 288 66 128 256), losses := [] }

theorem u122 : Upper (D 5) (R 5) [6,17,40,68,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 7 19 44 76 152 288 96 131 259), lower := (rows 7 19 44 76 152 288 96 128 256), losses := [] }

theorem u123 : Upper (D 5) (R 5) [6,17,40,68,136,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 44 76 400 34 65 168 296), lower := (rows 7 19 44 76 400 34 65 128 256), losses := [] }

theorem u124 : Upper (D 5) (R 5) [6,17,40,68,384,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b124
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 434, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 44 76 400 34 72 161 289), lower := (rows 7 19 44 76 400 34 72 128 256), losses := [] }

theorem u125 : Upper (D 5) (R 5) [6,17,40,68,384,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b125
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 76 400 34 96 137 265), lower := (rows 7 19 44 76 400 34 96 128 256), losses := [] }

theorem u126 : Upper (D 5) (R 5) [6,17,40,68,384,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b126
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 200 280 33 66 164 292), lower := (rows 7 19 44 200 280 33 66 128 256), losses := [] }

theorem u127 : Upper (D 5) (R 5) [6,17,40,192,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b127
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 34, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 19 44 200 280 33 68 162 290), lower := (rows 7 19 44 200 280 33 68 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 20 35 64 163 291), good := (rows 435 435 440 200 280 419 80 128 256) }] }

theorem u128 : Upper (D 5) (R 5) [6,17,40,192,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 275, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 200 280 33 96 134 262), lower := (rows 7 19 44 200 280 33 96 128 256), losses := [] }

theorem u129 : Upper (D 5) (R 5) [6,17,40,192,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 200 280 34 65 164 292), lower := (rows 7 19 44 200 280 34 65 128 256), losses := [] }

theorem u130 : Upper (D 5) (R 5) [6,17,40,192,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b130
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m131_1 : Upper (D 5) (R 5) [6,17,40,192,264,2,4,1] 13 :=
  permutation_upper _ _ _ [6,17,40,192,264,2,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8

def r131 : Route 9 := (fun mask => (mask,id))

def c131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u131 : Upper (D 5) (R 5) [6,17,40,192,264,2,4] 13 := by
  apply FastRouting.sound _ _ [6,17,40,192,264,2,4] 13 (by decide) (choices 1) [1,32] r131 c131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m131_1
  · exact u9

def b132 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 275, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 200 280 34 96 133 261), lower := (rows 7 19 44 200 280 34 96 128 256), losses := [] }

theorem u132 : Upper (D 5) (R 5) [6,17,40,192,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b132
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 76 41 176 288 66 140 268), lower := (rows 7 19 76 41 176 288 66 128 256), losses := [] }

theorem u133 : Upper (D 5) (R 5) [6,17,72,33,160,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 19 76 41 176 288 68 138 266), lower := (rows 7 19 76 41 176 288 68 128 256), losses := [] }

theorem u134 : Upper (D 5) (R 5) [6,17,72,33,160,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 435, targets := 8 }], pairs := [(0,3)], upper := (rows 7 19 76 41 176 288 72 134 262), lower := (rows 7 19 76 41 176 288 72 128 256), losses := [] }

theorem u135 : Upper (D 5) (R 5) [6,17,72,33,160,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b135
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5)], upper := (rows 7 19 76 42 152 288 65 164 292), lower := (rows 7 19 76 42 152 288 65 128 256), losses := [] }

theorem u136 : Upper (D 5) (R 5) [6,17,72,34,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b136
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 19 76 42 152 288 68 161 289), lower := (rows 7 19 76 42 152 288 68 128 256), losses := [] }

theorem u137 : Upper (D 5) (R 5) [6,17,72,34,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b137
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 147, targets := 32 }], pairs := [(0,5)], upper := (rows 7 19 76 42 152 288 96 133 261), lower := (rows 7 19 76 42 152 288 96 128 256), losses := [] }

theorem u138 : Upper (D 5) (R 5) [6,17,72,34,136,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 42 400 36 65 168 296), lower := (rows 7 19 76 42 400 36 65 128 256), losses := [] }

theorem u139 : Upper (D 5) (R 5) [6,17,72,34,384,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b139
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 435, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 76 42 400 36 72 161 289), lower := (rows 7 19 76 42 400 36 72 128 256), losses := [] }

theorem u140 : Upper (D 5) (R 5) [6,17,72,34,384,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 42 400 36 96 137 265), lower := (rows 7 19 76 42 400 36 96 128 256), losses := [] }

theorem u141 : Upper (D 5) (R 5) [6,17,72,34,384,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 44 152 33 66 416 288), lower := (rows 7 19 76 44 152 33 66 128 256), losses := [] }

theorem u142 : Upper (D 5) (R 5) [6,17,72,36,136,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b142
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 258, camps := [{ cop := 5, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 44 152 33 96 386 258), lower := (rows 7 19 76 44 152 33 96 128 256), losses := [] }

theorem u143 : Upper (D 5) (R 5) [6,17,72,36,136,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b143
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 76 44 152 33 320 162 290), lower := (rows 7 19 76 44 152 33 320 128 256), losses := [] }

theorem u144 : Upper (D 5) (R 5) [6,17,72,36,136,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b144
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 44 152 34 65 416 288), lower := (rows 7 19 76 44 152 34 65 128 256), losses := [] }

theorem u145 : Upper (D 5) (R 5) [6,17,72,36,136,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b145
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 44 152 34 96 385 257), lower := (rows 7 19 76 44 152 34 96 128 256), losses := [] }

theorem u146 : Upper (D 5) (R 5) [6,17,72,36,136,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 19 76 44 152 34 320 161 289), lower := (rows 7 19 76 44 152 34 320 128 256), losses := [] }

theorem u147 : Upper (D 5) (R 5) [6,17,72,36,136,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b147
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5)], upper := (rows 7 19 76 44 152 288 65 162 290), lower := (rows 7 19 76 44 152 288 65 128 256), losses := [] }

theorem u148 : Upper (D 5) (R 5) [6,17,72,36,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b148
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5)], upper := (rows 7 19 76 44 152 288 66 161 289), lower := (rows 7 19 76 44 152 288 66 128 256), losses := [] }

theorem u149 : Upper (D 5) (R 5) [6,17,72,36,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 7 19 76 44 152 288 96 131 259), lower := (rows 7 19 76 44 152 288 96 128 256), losses := [] }

theorem u150 : Upper (D 5) (R 5) [6,17,72,36,136,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 264, camps := [{ cop := 3, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 44 176 33 66 392 264), lower := (rows 7 19 76 44 176 33 66 128 256), losses := [] }

theorem u151 : Upper (D 5) (R 5) [6,17,72,36,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 434, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 44 176 33 72 386 258), lower := (rows 7 19 76 44 176 33 72 128 256), losses := [] }

theorem u152 : Upper (D 5) (R 5) [6,17,72,36,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b152
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 76 44 176 33 320 138 266), lower := (rows 7 19 76 44 176 33 320 128 256), losses := [] }

theorem u153 : Upper (D 5) (R 5) [6,17,72,36,160,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b153
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(3,0)], upper := (rows 7 19 76 44 176 288 65 138 266), lower := (rows 7 19 76 44 176 288 65 128 256), losses := [] }

theorem u154 : Upper (D 5) (R 5) [6,17,72,36,160,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b154
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 76 44 176 288 66 137 265), lower := (rows 7 19 76 44 176 288 66 128 256), losses := [] }

theorem u155 : Upper (D 5) (R 5) [6,17,72,36,160,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b155
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 4 }], pairs := [(1,2)], upper := (rows 7 19 76 44 176 288 72 131 259), lower := (rows 7 19 76 44 176 288 72 128 256), losses := [] }

theorem u156 : Upper (D 5) (R 5) [6,17,72,36,160,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b156
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 44 400 33 66 168 296), lower := (rows 7 19 76 44 400 33 66 128 256), losses := [] }

theorem u157 : Upper (D 5) (R 5) [6,17,72,36,384,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b157
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 434, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 44 400 33 72 162 290), lower := (rows 7 19 76 44 400 33 72 128 256), losses := [] }

theorem u158 : Upper (D 5) (R 5) [6,17,72,36,384,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 44 400 33 96 138 266), lower := (rows 7 19 76 44 400 33 96 128 256), losses := [] }

theorem u159 : Upper (D 5) (R 5) [6,17,72,36,384,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b159
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 44 400 34 65 168 296), lower := (rows 7 19 76 44 400 34 65 128 256), losses := [] }

theorem u160 : Upper (D 5) (R 5) [6,17,72,36,384,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b160
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 434, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 44 400 34 72 161 289), lower := (rows 7 19 76 44 400 34 72 128 256), losses := [] }

theorem u161 : Upper (D 5) (R 5) [6,17,72,36,384,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b161
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 44 400 34 96 137 265), lower := (rows 7 19 76 44 400 34 96 128 256), losses := [] }

theorem u162 : Upper (D 5) (R 5) [6,17,72,36,384,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b162
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 76 137 304 36 66 168 296), lower := (rows 7 19 76 137 304 36 66 128 256), losses := [] }

theorem u163 : Upper (D 5) (R 5) [6,17,72,129,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b163
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 307, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 76 137 304 36 72 162 290), lower := (rows 7 19 76 137 304 36 72 128 256), losses := [] }

theorem u164 : Upper (D 5) (R 5) [6,17,72,129,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b164
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 19 76 137 304 36 96 138 266), lower := (rows 7 19 76 137 304 36 96 128 256), losses := [] }

theorem u165 : Upper (D 5) (R 5) [6,17,72,129,288,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 76 138 304 36 65 168 296), lower := (rows 7 19 76 138 304 36 65 128 256), losses := [] }

theorem u166 : Upper (D 5) (R 5) [6,17,72,130,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b166
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 76 138 304 36 72 161 289), lower := (rows 7 19 76 138 304 36 72 128 256), losses := [] }

theorem u167 : Upper (D 5) (R 5) [6,17,72,130,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b167
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 19 76 138 304 36 96 137 265), lower := (rows 7 19 76 138 304 36 96 128 256), losses := [] }

theorem u168 : Upper (D 5) (R 5) [6,17,72,130,288,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b168
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 76 138 304 40 65 164 292), lower := (rows 7 19 76 138 304 40 65 128 256), losses := [] }

theorem u169 : Upper (D 5) (R 5) [6,17,72,130,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b169
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 76 138 304 40 68 161 289), lower := (rows 7 19 76 138 304 40 68 128 256), losses := [] }

theorem u170 : Upper (D 5) (R 5) [6,17,72,130,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b170
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 138 304 40 96 133 261), lower := (rows 7 19 76 138 304 40 96 128 256), losses := [] }

theorem u171 : Upper (D 5) (R 5) [6,17,72,130,288,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b171
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 140 56 33 66 416 288), lower := (rows 7 19 76 140 56 33 66 128 256), losses := [] }

theorem u172 : Upper (D 5) (R 5) [6,17,72,132,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b172
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 140 56 33 96 386 258), lower := (rows 7 19 76 140 56 33 96 128 256), losses := [] }

theorem u173 : Upper (D 5) (R 5) [6,17,72,132,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b173
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r174 : Route 9 := (fun mask => (mask,id))

def c174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u174 : Upper (D 5) (R 5) [6,17,72,132,40,1,256] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,40,1,256] 13 (by decide) (choices 1) [2,32] r174 c174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10
  · exact u11

def b175 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 140 56 34 65 416 288), lower := (rows 7 19 76 140 56 34 65 128 256), losses := [] }

theorem u175 : Upper (D 5) (R 5) [6,17,72,132,40,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b175
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 392, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 76 140 56 34 96 385 257), lower := (rows 7 19 76 140 56 34 96 128 256), losses := [] }

theorem u176 : Upper (D 5) (R 5) [6,17,72,132,40,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r177 : Route 9 := (fun mask => (mask,id))

def c177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u177 : Upper (D 5) (R 5) [6,17,72,132,40,2,256] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,40,2,256] 13 (by decide) (choices 1) [1,32] r177 c177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12
  · exact u13

def b178 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5)], upper := (rows 7 19 76 140 56 288 65 162 290), lower := (rows 7 19 76 140 56 288 65 128 256), losses := [] }

theorem u178 : Upper (D 5) (R 5) [6,17,72,132,40,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b178
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5)], upper := (rows 7 19 76 140 56 288 66 161 289), lower := (rows 7 19 76 140 56 288 66 128 256), losses := [] }

theorem u179 : Upper (D 5) (R 5) [6,17,72,132,40,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b179
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P05
