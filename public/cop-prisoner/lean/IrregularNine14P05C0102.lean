import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0043
import IrregularNine14P05C0044

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6120 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 196 280 19 45 109 173 301), lower := (rows 7 42 196 280 19 32 64 128 256), losses := [] }

theorem u6120 : Upper (D 5) (R 5) [6,40,192,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6120
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6121 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 280 21 43 107 171 299), lower := (rows 7 42 196 280 21 32 64 128 256), losses := [] }

theorem u6121 : Upper (D 5) (R 5) [6,40,192,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6122 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 42 196 280 22 41 105 169 297), lower := (rows 7 42 196 280 22 32 64 128 256), losses := [] }

theorem u6122 : Upper (D 5) (R 5) [6,40,192,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6123 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 280 25 39 103 167 295), lower := (rows 7 42 196 280 25 32 64 128 256), losses := [] }

theorem u6123 : Upper (D 5) (R 5) [6,40,192,272,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6124 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 280 26 37 101 165 293), lower := (rows 7 42 196 280 26 32 64 128 256), losses := [] }

theorem u6124 : Upper (D 5) (R 5) [6,40,192,272,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6124
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6125 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 280 28 35 99 163 291), lower := (rows 7 42 196 280 28 32 64 128 256), losses := [] }

theorem u6125 : Upper (D 5) (R 5) [6,40,192,272,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6125
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6126 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 280 49 47 79 143 271), lower := (rows 7 42 196 280 49 32 64 128 256), losses := [] }

theorem u6126 : Upper (D 5) (R 5) [6,40,192,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6126
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6127 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 280 50 45 77 141 269), lower := (rows 7 42 196 280 50 32 64 128 256), losses := [] }

theorem u6127 : Upper (D 5) (R 5) [6,40,192,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6127
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6128 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 280 52 43 75 139 267), lower := (rows 7 42 196 280 52 32 64 128 256), losses := [] }

theorem u6128 : Upper (D 5) (R 5) [6,40,192,272,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6129 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 280 56 39 71 135 263), lower := (rows 7 42 196 280 56 32 64 128 256), losses := [] }

theorem u6129 : Upper (D 5) (R 5) [6,40,192,272,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6130 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 41 22 424 456 392 392), lower := (rows 7 50 69 41 22 32 64 128 256), losses := [] }

theorem u6130 : Upper (D 5) (R 5) [6,48,65,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6130
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6131 : PairBound 9 := { available := 396, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 41 26 428 460 396 396), lower := (rows 7 50 69 41 26 32 64 128 256), losses := [] }

theorem u6131 : Upper (D 5) (R 5) [6,48,65,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6131
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6132 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 418, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 41 28 426 458 394 394), lower := (rows 7 50 69 41 28 32 64 128 256), losses := [] }

theorem u6132 : Upper (D 5) (R 5) [6,48,65,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6132
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6133 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 41 146 300 332 396 268), lower := (rows 7 50 69 41 146 32 64 128 256), losses := [] }

theorem u6133 : Upper (D 5) (R 5) [6,48,65,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6134 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 50 69 41 148 298 330 394 266), lower := (rows 7 50 69 41 148 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 13 16 49 81 145 273), good := (rows 491 498 489 489 506 32 64 128 256) }] }

theorem u6134 : Upper (D 5) (R 5) [6,48,65,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6135 : Route 9 := (fun mask => (mask,id))

def c6135 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6135 : Upper (D 5) (R 5) [6,48,65,33,136] 13 := by
  apply FastRouting.sound _ _ [6,48,65,33,136] 13 (by decide) (choices 1) [2,4,8,256] r6135 c6135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2615
  · exact u2616
  · exact u2617
  · exact u2618

def r6136 : Route 9 := (fun mask => (mask,id))

def c6136 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6136 : Upper (D 5) (R 5) [6,48,65,33,384] 13 := by
  apply FastRouting.sound _ _ [6,48,65,33,384] 13 (by decide) (choices 1) [2,4,8] r6136 c6136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2619
  · exact u2620
  · exact u2621

def b6137 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 69 44 19 424 456 392 392), lower := (rows 7 50 69 44 19 32 64 128 256), losses := [] }

theorem u6137 : Upper (D 5) (R 5) [6,48,65,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6137
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6138 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 418, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 44 25 426 458 394 394), lower := (rows 7 50 69 44 25 32 64 128 256), losses := [] }

theorem u6138 : Upper (D 5) (R 5) [6,48,65,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6139 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 44 26 425 457 393 393), lower := (rows 7 50 69 44 26 32 64 128 256), losses := [] }

theorem u6139 : Upper (D 5) (R 5) [6,48,65,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6139
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6140 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 50 69 44 145 298 330 394 266), lower := (rows 7 50 69 44 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 13 16 49 81 145 273), good := (rows 494 498 492 44 506 32 64 128 256) }] }

theorem u6140 : Upper (D 5) (R 5) [6,48,65,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6141 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 44 146 297 329 393 265), lower := (rows 7 50 69 44 146 32 64 128 256), losses := [] }

theorem u6141 : Upper (D 5) (R 5) [6,48,65,36,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6142 : Route 9 := (fun mask => (mask,id))

def c6142 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6142 : Upper (D 5) (R 5) [6,48,65,36,136] 13 := by
  apply FastRouting.sound _ _ [6,48,65,36,136] 13 (by decide) (choices 1) [1,2,8,256] r6142 c6142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2622
  · exact u2623
  · exact u2624
  · exact u2625

def r6143 : Route 9 := (fun mask => (mask,id))

def c6143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6143 : Upper (D 5) (R 5) [6,48,65,36,384] 13 := by
  apply FastRouting.sound _ _ [6,48,65,36,384] 13 (by decide) (choices 1) [1,2,8] r6143 c6143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2626
  · exact u2627
  · exact u2628

def b6144 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 137 22 296 360 424 296), lower := (rows 7 50 69 137 22 32 64 128 256), losses := [] }

theorem u6144 : Upper (D 5) (R 5) [6,48,65,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6144
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6145 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 137 26 300 364 428 300), lower := (rows 7 50 69 137 26 32 64 128 256), losses := [] }

theorem u6145 : Upper (D 5) (R 5) [6,48,65,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6145
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6146 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 137 28 298 362 426 298), lower := (rows 7 50 69 137 28 32 64 128 256), losses := [] }

theorem u6146 : Upper (D 5) (R 5) [6,48,65,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6147 : PairBound 9 := { available := 268, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 137 50 300 332 396 268), lower := (rows 7 50 69 137 50 32 64 128 256), losses := [] }

theorem u6147 : Upper (D 5) (R 5) [6,48,65,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6147
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6148 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 137 52 298 330 394 266), lower := (rows 7 50 69 137 52 32 64 128 256), losses := [] }

theorem u6148 : Upper (D 5) (R 5) [6,48,65,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6148
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6149 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 137 56 302 334 398 270), lower := (rows 7 50 69 137 56 32 64 128 256), losses := [] }

theorem u6149 : Upper (D 5) (R 5) [6,48,65,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6150 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 137 274 44 108 172 300), lower := (rows 7 50 69 137 274 32 64 128 256), losses := [] }

theorem u6150 : Upper (D 5) (R 5) [6,48,65,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6151 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 50 69 137 276 42 106 170 298), lower := (rows 7 50 69 137 276 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 13 16 49 81 145 273), good := (rows 491 498 489 489 506 32 64 128 256) }] }

theorem u6151 : Upper (D 5) (R 5) [6,48,65,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6152 : Route 9 := (fun mask => (mask,id))

def c6152 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6152 : Upper (D 5) (R 5) [6,48,65,129,264] 13 := by
  apply FastRouting.sound _ _ [6,48,65,129,264] 13 (by decide) (choices 1) [2,4,8] r6152 c6152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2629
  · exact u2630
  · exact u2631

def b6153 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 137 304 46 78 142 270), lower := (rows 7 50 69 137 304 32 64 128 256), losses := [] }

theorem u6153 : Upper (D 5) (R 5) [6,48,65,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6153
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6154 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 138 21 296 360 424 296), lower := (rows 7 50 69 138 21 32 64 128 256), losses := [] }

theorem u6154 : Upper (D 5) (R 5) [6,48,65,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6154
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6155 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 424, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(3,0)], upper := (rows 7 50 69 138 25 300 364 428 300), lower := (rows 7 50 69 138 25 32 64 128 256), losses := [] }

theorem u6155 : Upper (D 5) (R 5) [6,48,65,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6155
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6156 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 424, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 50 69 138 28 297 361 425 297), lower := (rows 7 50 69 138 28 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 25 16 37 69 133 261), good := (rows 491 58 489 138 506 32 64 128 256) }] }

theorem u6156 : Upper (D 5) (R 5) [6,48,65,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6156
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6157 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 138 49 300 332 396 268), lower := (rows 7 50 69 138 49 32 64 128 256), losses := [] }

theorem u6157 : Upper (D 5) (R 5) [6,48,65,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6157
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6158 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 138 52 297 329 393 265), lower := (rows 7 50 69 138 52 32 64 128 256), losses := [] }

theorem u6158 : Upper (D 5) (R 5) [6,48,65,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6159 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 138 56 301 333 397 269), lower := (rows 7 50 69 138 56 32 64 128 256), losses := [] }

theorem u6159 : Upper (D 5) (R 5) [6,48,65,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6159
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6160 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 50 69 138 273 44 108 172 300), lower := (rows 7 50 69 138 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 25 16 37 69 133 261), good := (rows 494 58 492 138 506 32 64 128 256) }] }

theorem u6160 : Upper (D 5) (R 5) [6,48,65,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6160
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6161 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 50 69 138 276 41 105 169 297), lower := (rows 7 50 69 138 276 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 25 16 37 69 133 261), good := (rows 491 58 489 138 506 32 64 128 256) }] }

theorem u6161 : Upper (D 5) (R 5) [6,48,65,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6161
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6162 : Route 9 := (fun mask => (mask,id))

def c6162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6162 : Upper (D 5) (R 5) [6,48,65,130,264] 13 := by
  apply FastRouting.sound _ _ [6,48,65,130,264] 13 (by decide) (choices 1) [1,4,8] r6162 c6162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2632
  · exact u2633
  · exact u2634

def b6163 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 138 304 45 77 141 269), lower := (rows 7 50 69 138 304 32 64 128 256), losses := [] }

theorem u6163 : Upper (D 5) (R 5) [6,48,65,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6163
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6164 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 69 140 19 296 360 424 296), lower := (rows 7 50 69 140 19 32 64 128 256), losses := [] }

theorem u6164 : Upper (D 5) (R 5) [6,48,65,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6164
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6165 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 140 25 298 362 426 298), lower := (rows 7 50 69 140 25 32 64 128 256), losses := [] }

theorem u6165 : Upper (D 5) (R 5) [6,48,65,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6166 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 140 26 297 361 425 297), lower := (rows 7 50 69 140 26 32 64 128 256), losses := [] }

theorem u6166 : Upper (D 5) (R 5) [6,48,65,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6166
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6167 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 140 49 298 330 394 266), lower := (rows 7 50 69 140 49 32 64 128 256), losses := [] }

theorem u6167 : Upper (D 5) (R 5) [6,48,65,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6167
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6168 : PairBound 9 := { available := 265, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 140 50 297 329 393 265), lower := (rows 7 50 69 140 50 32 64 128 256), losses := [] }

theorem u6168 : Upper (D 5) (R 5) [6,48,65,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6168
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6169 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 140 56 299 331 395 267), lower := (rows 7 50 69 140 56 32 64 128 256), losses := [] }

theorem u6169 : Upper (D 5) (R 5) [6,48,65,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6169
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6170 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 50 69 140 273 42 106 170 298), lower := (rows 7 50 69 140 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 13 16 49 81 145 273), good := (rows 494 498 492 140 506 32 64 128 256) }] }

theorem u6170 : Upper (D 5) (R 5) [6,48,65,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6170
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6171 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 140 274 41 105 169 297), lower := (rows 7 50 69 140 274 32 64 128 256), losses := [] }

theorem u6171 : Upper (D 5) (R 5) [6,48,65,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6171
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6172 : Route 9 := (fun mask => (mask,id))

def c6172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6172 : Upper (D 5) (R 5) [6,48,65,132,264] 13 := by
  apply FastRouting.sound _ _ [6,48,65,132,264] 13 (by decide) (choices 1) [1,2,8] r6172 c6172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2635
  · exact u2636
  · exact u2637

def b6173 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 140 304 43 75 139 267), lower := (rows 7 50 69 140 304 32 64 128 256), losses := [] }

theorem u6173 : Upper (D 5) (R 5) [6,48,65,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6173
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6174 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 69 168 19 300 332 396 268), lower := (rows 7 50 69 168 19 32 64 128 256), losses := [] }

theorem u6174 : Upper (D 5) (R 5) [6,48,65,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6174
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6175 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 168 21 298 330 394 266), lower := (rows 7 50 69 168 21 32 64 128 256), losses := [] }

theorem u6175 : Upper (D 5) (R 5) [6,48,65,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6175
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6176 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 168 22 297 329 393 265), lower := (rows 7 50 69 168 22 32 64 128 256), losses := [] }

theorem u6176 : Upper (D 5) (R 5) [6,48,65,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6177 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 50 69 168 25 302 334 398 270), lower := (rows 7 50 69 168 25 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 29 16 33 65 129 257), good := (rows 494 58 492 168 506 32 64 128 256) }] }

theorem u6177 : Upper (D 5) (R 5) [6,48,65,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6177
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6178 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 168 26 301 333 397 269), lower := (rows 7 50 69 168 26 32 64 128 256), losses := [] }

theorem u6178 : Upper (D 5) (R 5) [6,48,65,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6178
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6179 : Route 9 := (fun mask => (mask,id))

def c6179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6179 : Upper (D 5) (R 5) [6,48,65,160,12] 13 := by
  apply FastRouting.sound _ _ [6,48,65,160,12] 13 (by decide) (choices 1) [1,2,8,256] r6179 c6179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2638
  · exact u2639
  · exact u2640
  · exact u2641

#print axioms u6179
end Delivery.IrregularNine14.P05
