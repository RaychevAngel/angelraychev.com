import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0000

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 23 35 100 392 144 96 344 408 280), lower := (rows 23 35 100 392 144 96 64 128 256), losses := [] }

theorem u120 : Upper (D 2) (R 2) [22,33,96,384,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b120
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r121 : Route 9 := (fun mask => (mask,id))

def c121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u121 : Upper (D 2) (R 2) [22,33,96,384,128,256] 13 := by
  apply FastRouting.sound _ _ [22,33,96,384,128,256] 13 (by decide) (choices 1) [8,16] r121 c121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11
  · exact u12

def b122 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 452, targets := 16 }], pairs := [(2,4)], upper := (rows 23 35 196 88 272 40 480 416 416), lower := (rows 23 35 196 88 272 40 64 128 256), losses := [] }

theorem u122 : Upper (D 2) (R 2) [22,33,192,80,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b122
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 3, region := 420, targets := 16 }], pairs := [(2,4),(3,7)], upper := (rows 23 35 196 88 272 160 360 424 296), lower := (rows 23 35 196 88 272 160 64 128 256), losses := [] }

theorem u123 : Upper (D 2) (R 2) [22,33,192,80,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b123
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 420, targets := 16 }], pairs := [(1,4),(2,4)], upper := (rows 23 35 196 88 272 288 232 168 424), lower := (rows 23 35 196 88 272 288 64 128 256), losses := [{ target := 4, region := (rows 1 3 12 8 0 312 72 136 264), good := (rows 39 35 196 492 288 288 64 128 288) }] }

theorem u124 : Upper (D 2) (R 2) [22,33,192,80,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b124
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 196 104 272 40 464 400 400), lower := (rows 23 35 196 104 272 40 64 128 256), losses := [] }

theorem u125 : Upper (D 2) (R 2) [22,33,192,96,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b125
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 35 196 104 272 48 456 392 392), lower := (rows 23 35 196 104 272 48 64 128 256), losses := [] }

theorem u126 : Upper (D 2) (R 2) [22,33,192,96,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b126
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 40, targets := 272 }], pairs := [(3,4),(3,8)], upper := (rows 23 35 196 104 272 160 344 408 280), lower := (rows 23 35 196 104 272 160 64 128 256), losses := [] }

theorem u127 : Upper (D 2) (R 2) [22,33,192,96,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b127
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 404, targets := 32 }], pairs := [(1,4),(2,5)], upper := (rows 23 35 196 104 272 288 216 152 408), lower := (rows 23 35 196 104 272 288 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 304 64 128 256), good := (rows 39 35 196 104 288 288 64 128 288) }] }

theorem u128 : Upper (D 2) (R 2) [22,33,192,96,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b128
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 23 35 196 296 272 40 208 208 464), lower := (rows 23 35 196 296 272 40 64 128 256), losses := [] }

theorem u129 : Upper (D 2) (R 2) [22,33,192,288,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b129
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 35 196 296 272 48 200 200 456), lower := (rows 23 35 196 296 272 48 64 128 256), losses := [] }

theorem u130 : Upper (D 2) (R 2) [22,33,192,288,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b130
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5),(3,6)], upper := (rows 23 35 196 296 272 96 216 152 408), lower := (rows 23 35 196 296 272 96 64 128 256), losses := [] }

theorem u131 : Upper (D 2) (R 2) [22,33,192,288,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b131
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r132 : Route 9 := (fun mask => (mask,id))

def c132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u132 : Upper (D 2) (R 2) [22,33,192,320,256,8] 13 := by
  apply FastRouting.sound _ _ [22,33,192,320,256,8] 13 (by decide) (choices 1) [16,32,128] r132 c132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13
  · exact u14
  · exact u15

def b133 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 35 196 328 272 48 232 168 424), lower := (rows 23 35 196 328 272 48 64 128 256), losses := [] }

theorem u133 : Upper (D 2) (R 2) [22,33,192,320,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b133
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(1,4),(3,7)], upper := (rows 23 35 196 328 272 160 120 184 312), lower := (rows 23 35 196 328 272 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 164 64 128 256), good := (rows 39 35 228 328 256 160 64 160 256) }] }

theorem u134 : Upper (D 2) (R 2) [22,33,192,320,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b134
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,4),(3,5)], upper := (rows 23 42 100 137 272 48 448 448 448), lower := (rows 23 42 100 137 272 48 64 128 256), losses := [] }

theorem u135 : Upper (D 2) (R 2) [22,40,96,129,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b135
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 23 42 100 137 272 96 464 400 400), lower := (rows 23 42 100 137 272 96 64 128 256), losses := [] }

theorem u136 : Upper (D 2) (R 2) [22,40,96,129,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b136
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 34, targets := 80 }], pairs := [(1,4),(1,6)], upper := (rows 23 42 100 137 272 160 336 464 336), lower := (rows 23 42 100 137 272 160 64 128 256), losses := [] }

theorem u137 : Upper (D 2) (R 2) [22,40,96,129,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b137
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 200, targets := 256 }], pairs := [(3,5),(3,8)], upper := (rows 23 42 100 137 272 288 208 208 464), lower := (rows 23 42 100 137 272 288 64 128 256), losses := [] }

theorem u138 : Upper (D 2) (R 2) [22,40,96,129,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b138
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 100 200 272 33 464 400 400), lower := (rows 23 42 100 200 272 33 64 128 256), losses := [] }

theorem u139 : Upper (D 2) (R 2) [22,40,96,192,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b139
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,4),(3,5)], upper := (rows 23 42 100 200 272 48 449 385 385), lower := (rows 23 42 100 200 272 48 64 128 256), losses := [] }

theorem u140 : Upper (D 2) (R 2) [22,40,96,192,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b140
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 34, targets := 272 }], pairs := [(1,4),(1,8)], upper := (rows 23 42 100 200 272 160 337 401 273), lower := (rows 23 42 100 200 272 160 64 128 256), losses := [] }

theorem u141 : Upper (D 2) (R 2) [22,40,96,192,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b141
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 200, targets := 256 }], pairs := [(3,5),(3,8)], upper := (rows 23 42 100 200 272 288 209 145 401), lower := (rows 23 42 100 200 272 288 64 128 256), losses := [] }

theorem u142 : Upper (D 2) (R 2) [22,40,96,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b142
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 452, targets := 16 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,4)], upper := (rows 23 42 196 73 272 48 480 416 416), lower := (rows 23 42 196 73 272 48 64 128 256), losses := [] }

theorem u143 : Upper (D 2) (R 2) [22,40,192,65,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b143
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,7)], upper := (rows 23 42 196 73 272 160 368 432 304), lower := (rows 23 42 196 73 272 160 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 307 32 98 0 290), good := (rows 351 378 68 89 272 368 64 0 272) }] }

theorem u144 : Upper (D 2) (R 2) [22,40,192,65,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b144
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r145 : Route 9 := (fun mask => (mask,id))

def c145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u145 : Upper (D 2) (R 2) [22,40,192,65,256,256] 13 := by
  apply FastRouting.sound _ _ [22,40,192,65,256,256] 13 (by decide) (choices 1) [16,32,128] r145 c145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16
  · exact u17
  · exact u18

def b146 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 196 88 272 33 480 416 416), lower := (rows 23 42 196 88 272 33 64 128 256), losses := [] }

theorem u146 : Upper (D 2) (R 2) [22,40,192,80,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b146
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r147 : Route 9 := (fun mask => (mask,id))

def c147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u147 : Upper (D 2) (R 2) [22,40,192,80,256,128] 13 := by
  apply FastRouting.sound _ _ [22,40,192,80,256,128] 13 (by decide) (choices 1) [1,32,256] r147 c147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19
  · exact u20
  · exact u21

def b148 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(1,4),(2,4)], upper := (rows 23 42 196 88 272 288 225 161 417), lower := (rows 23 42 196 88 272 288 64 128 256), losses := [{ target := 4, region := (rows 1 10 5 8 0 305 65 129 257), good := (rows 487 42 196 106 288 288 64 128 288) }] }

theorem u148 : Upper (D 2) (R 2) [22,40,192,80,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b148
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 328 17 48 480 416 416), lower := (rows 23 42 196 328 17 48 64 128 256), losses := [] }

theorem u149 : Upper (D 2) (R 2) [22,40,192,320,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b149
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r150 : Route 9 := (fun mask => (mask,id))

def c150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u150 : Upper (D 2) (R 2) [22,40,192,320,1,128] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320,1,128] 13 (by decide) (choices 1) [16,32,256] r150 c150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22
  · exact u23
  · exact u24

def b151 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 328 17 288 240 176 432), lower := (rows 23 42 196 328 17 288 64 128 256), losses := [] }

theorem u151 : Upper (D 2) (R 2) [22,40,192,320,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b151
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 228, targets := 256 }], pairs := [(2,8)], upper := (rows 23 42 196 328 272 33 240 176 432), lower := (rows 23 42 196 328 272 33 64 128 256), losses := [] }

theorem u152 : Upper (D 2) (R 2) [22,40,192,320,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b152
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 23 42 196 328 272 48 225 161 417), lower := (rows 23 42 196 328 272 48 64 128 256), losses := [] }

theorem u153 : Upper (D 2) (R 2) [22,40,192,320,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b153
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r154 : Route 9 := (fun mask => (mask,id))

def c154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u154 : Upper (D 2) (R 2) [22,40,192,320,256,128] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320,256,128] 13 (by decide) (choices 1) [1,16,32] r154 c154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25
  · exact u26
  · exact u27

def b155 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 88 272 33 456 392 392), lower := (rows 23 98 164 88 272 33 64 128 256), losses := [] }

theorem u155 : Upper (D 2) (R 2) [22,96,160,80,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b155
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 164 88 272 40 449 385 385), lower := (rows 23 98 164 88 272 40 64 128 256), losses := [] }

theorem u156 : Upper (D 2) (R 2) [22,96,160,80,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b156
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 23 98 164 88 272 160 329 393 265), lower := (rows 23 98 164 88 272 160 64 128 256), losses := [] }

theorem u157 : Upper (D 2) (R 2) [22,96,160,80,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b157
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 200, targets := 256 }], pairs := [(3,5),(3,8)], upper := (rows 23 98 164 88 272 288 201 137 393), lower := (rows 23 98 164 88 272 288 64 128 256), losses := [] }

theorem u158 : Upper (D 2) (R 2) [22,96,160,80,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b158
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 200 272 33 344 408 280), lower := (rows 23 98 164 200 272 33 64 128 256), losses := [] }

theorem u159 : Upper (D 2) (R 2) [22,96,160,192,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b159
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 164 200 272 40 337 401 273), lower := (rows 23 98 164 200 272 40 64 128 256), losses := [] }

theorem u160 : Upper (D 2) (R 2) [22,96,160,192,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b160
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,4),(3,5)], upper := (rows 23 98 164 200 272 48 329 393 265), lower := (rows 23 98 164 200 272 48 64 128 256), losses := [] }

theorem u161 : Upper (D 2) (R 2) [22,96,160,192,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b161
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 200, targets := 256 }], pairs := [(3,5),(3,8)], upper := (rows 23 98 164 200 272 288 89 153 281), lower := (rows 23 98 164 200 272 288 64 128 256), losses := [] }

theorem u162 : Upper (D 2) (R 2) [22,96,160,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b162
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 265 272 40 208 208 464), lower := (rows 23 98 164 265 272 40 64 128 256), losses := [] }

theorem u163 : Upper (D 2) (R 2) [22,96,160,257,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b163
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,4),(3,5)], upper := (rows 23 98 164 265 272 48 200 200 456), lower := (rows 23 98 164 265 272 48 64 128 256), losses := [] }

theorem u164 : Upper (D 2) (R 2) [22,96,160,257,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b164
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 23 98 164 265 272 96 216 152 408), lower := (rows 23 98 164 265 272 96 64 128 256), losses := [] }

theorem u165 : Upper (D 2) (R 2) [22,96,160,257,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b165
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 328 272 33 216 152 408), lower := (rows 23 98 164 328 272 33 64 128 256), losses := [] }

theorem u166 : Upper (D 2) (R 2) [22,96,160,320,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b166
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 164 328 272 40 209 145 401), lower := (rows 23 98 164 328 272 40 64 128 256), losses := [] }

theorem u167 : Upper (D 2) (R 2) [22,96,160,320,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b167
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,4),(3,5)], upper := (rows 23 98 164 328 272 48 201 137 393), lower := (rows 23 98 164 328 272 48 64 128 256), losses := [] }

theorem u168 : Upper (D 2) (R 2) [22,96,160,320,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b168
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 23 98 164 328 272 160 89 153 281), lower := (rows 23 98 164 328 272 160 64 128 256), losses := [] }

theorem u169 : Upper (D 2) (R 2) [22,96,160,320,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b169
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 336, camps := [], pairs := [], upper := (rows 23 98 388 168 17 40 336 464 336), lower := (rows 23 98 388 168 17 40 64 128 256), losses := [] }

theorem u170 : Upper (D 2) (R 2) [22,96,384,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b170
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 328, camps := [{ cop := 5, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 388 168 17 48 328 456 328), lower := (rows 23 98 388 168 17 48 64 128 256), losses := [] }

theorem u171 : Upper (D 2) (R 2) [22,96,384,160,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b171
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 388 168 17 96 344 408 280), lower := (rows 23 98 388 168 17 96 64 128 256), losses := [] }

theorem u172 : Upper (D 2) (R 2) [22,96,384,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b172
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 388 168 17 288 88 216 344), lower := (rows 23 98 388 168 17 288 64 128 256), losses := [] }

theorem u173 : Upper (D 2) (R 2) [22,96,384,160,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b173
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(0,7),(3,4)], upper := (rows 51 7 28 200 272 96 480 416 416), lower := (rows 51 7 28 200 272 96 64 128 256), losses := [{ target := 7, region := (rows 5 6 4 8 272 104 64 0 256), good := (rows 51 7 63 104 272 96 96 0 272) }] }

theorem u174 : Upper (D 2) (R 2) [50,5,24,192,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b174
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 7 28 200 272 288 224 224 480), lower := (rows 51 7 28 200 272 288 64 128 256), losses := [] }

theorem u175 : Upper (D 2) (R 2) [50,5,24,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b175
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 392, targets := 64 },{ cop := 3, region := 356, targets := 16 }], pairs := [(2,4),(3,6)], upper := (rows 51 7 76 152 272 96 480 416 416), lower := (rows 51 7 76 152 272 96 64 128 256), losses := [] }

theorem u176 : Upper (D 2) (R 2) [50,5,72,144,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b176
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r177 : Route 9 := (fun mask => (mask,id))

def c177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u177 : Upper (D 2) (R 2) [50,5,72,144,256,128] 13 := by
  apply FastRouting.sound _ _ [50,5,72,144,256,128] 13 (by decide) (choices 1) [32,256] r177 c177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28
  · exact u29

def b178 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 7 76 152 272 288 224 224 480), lower := (rows 51 7 76 152 272 288 64 128 256), losses := [] }

theorem u178 : Upper (D 2) (R 2) [50,5,72,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b178
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 51 7 76 392 48 96 464 400 400), lower := (rows 51 7 76 392 48 96 64 128 256), losses := [] }

theorem u179 : Upper (D 2) (R 2) [50,5,72,384,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b179
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P02
