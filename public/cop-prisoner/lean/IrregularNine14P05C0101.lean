import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0042
import IrregularNine14P05C0043

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6060 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 392 50 45 77 141 269), lower := (rows 7 42 84 392 50 32 64 128 256), losses := [] }

theorem u6060 : Upper (D 5) (R 5) [6,40,80,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6060
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6061 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 392 52 43 75 139 267), lower := (rows 7 42 84 392 52 32 64 128 256), losses := [] }

theorem u6061 : Upper (D 5) (R 5) [6,40,80,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6061
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6062 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 392 56 39 71 135 263), lower := (rows 7 42 84 392 56 32 64 128 256), losses := [] }

theorem u6062 : Upper (D 5) (R 5) [6,40,80,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6062
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6063 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 196 25 19 300 364 428 300), lower := (rows 7 42 196 25 19 32 64 128 256), losses := [] }

theorem u6063 : Upper (D 5) (R 5) [6,40,192,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6064 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 42 196 25 21 298 362 426 298), lower := (rows 7 42 196 25 21 32 64 128 256), losses := [] }

theorem u6064 : Upper (D 5) (R 5) [6,40,192,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6064
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6065 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 196 25 22 297 361 425 297), lower := (rows 7 42 196 25 22 32 64 128 256), losses := [] }

theorem u6065 : Upper (D 5) (R 5) [6,40,192,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6065
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6066 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 42 196 25 25 294 358 422 294), lower := (rows 7 42 196 25 25 32 64 128 256), losses := [] }

theorem u6066 : Upper (D 5) (R 5) [6,40,192,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6066
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6067 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 196 25 26 293 357 421 293), lower := (rows 7 42 196 25 26 32 64 128 256), losses := [] }

theorem u6067 : Upper (D 5) (R 5) [6,40,192,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6067
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6068 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 42 196 25 28 291 355 419 291), lower := (rows 7 42 196 25 28 32 64 128 256), losses := [] }

theorem u6068 : Upper (D 5) (R 5) [6,40,192,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6068
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6069 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 25 49 302 334 398 270), lower := (rows 7 42 196 25 49 32 64 128 256), losses := [] }

theorem u6069 : Upper (D 5) (R 5) [6,40,192,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6069
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6070 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 25 50 301 333 397 269), lower := (rows 7 42 196 25 50 32 64 128 256), losses := [] }

theorem u6070 : Upper (D 5) (R 5) [6,40,192,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6070
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6071 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 25 52 299 331 395 267), lower := (rows 7 42 196 25 52 32 64 128 256), losses := [] }

theorem u6071 : Upper (D 5) (R 5) [6,40,192,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6071
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6072 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 25 56 295 327 391 263), lower := (rows 7 42 196 25 56 32 64 128 256), losses := [] }

theorem u6072 : Upper (D 5) (R 5) [6,40,192,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6072
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6073 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 8, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 42 196 25 273 46 110 174 302), lower := (rows 7 42 196 25 273 32 64 128 256), losses := [] }

theorem u6073 : Upper (D 5) (R 5) [6,40,192,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6073
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6074 : Route 9 := (fun mask => (mask,id))

def c6074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6074 : Upper (D 5) (R 5) [6,40,192,17,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,258] 13 (by decide) (choices 1) [1,4,8] r6074 c6074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2572
  · exact u2573
  · exact u2574

def r6075 : Route 9 := (fun mask => (mask,id))

def c6075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6075 : Upper (D 5) (R 5) [6,40,192,17,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,260] 13 (by decide) (choices 1) [1,2,8] r6075 c6075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2575
  · exact u2576
  · exact u2577

def b6076 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 25 280 39 103 167 295), lower := (rows 7 42 196 25 280 32 64 128 256), losses := [] }

theorem u6076 : Upper (D 5) (R 5) [6,40,192,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6076
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6077 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 25 304 47 79 143 271), lower := (rows 7 42 196 25 304 32 64 128 256), losses := [] }

theorem u6077 : Upper (D 5) (R 5) [6,40,192,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6077
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6078 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 26 21 297 361 425 297), lower := (rows 7 42 196 26 21 32 64 128 256), losses := [] }

theorem u6078 : Upper (D 5) (R 5) [6,40,192,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6078
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6079 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 196 26 25 293 357 421 293), lower := (rows 7 42 196 26 25 32 64 128 256), losses := [] }

theorem u6079 : Upper (D 5) (R 5) [6,40,192,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6079
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6080 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 42 196 26 28 289 353 417 289), lower := (rows 7 42 196 26 28 32 64 128 256), losses := [] }

theorem u6080 : Upper (D 5) (R 5) [6,40,192,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6080
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6081 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 26 49 301 333 397 269), lower := (rows 7 42 196 26 49 32 64 128 256), losses := [] }

theorem u6081 : Upper (D 5) (R 5) [6,40,192,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6081
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6082 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 26 52 297 329 393 265), lower := (rows 7 42 196 26 52 32 64 128 256), losses := [] }

theorem u6082 : Upper (D 5) (R 5) [6,40,192,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6082
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6083 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 26, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 26 56 293 325 389 261), lower := (rows 7 42 196 26 56 32 64 128 256), losses := [] }

theorem u6083 : Upper (D 5) (R 5) [6,40,192,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6083
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6084 : Route 9 := (fun mask => (mask,id))

def c6084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6084 : Upper (D 5) (R 5) [6,40,192,18,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,257] 13 (by decide) (choices 1) [1,4,8] r6084 c6084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2578
  · exact u2579
  · exact u2580

def r6085 : Route 9 := (fun mask => (mask,id))

def c6085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6085 : Upper (D 5) (R 5) [6,40,192,18,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,260] 13 (by decide) (choices 1) [1,8] r6085 c6085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2581
  · exact u2582

def b6086 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 228, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 42 196 26 280 37 101 165 293), lower := (rows 7 42 196 26 280 32 64 128 256), losses := [] }

theorem u6086 : Upper (D 5) (R 5) [6,40,192,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6086
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6087 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 26 304 45 77 141 269), lower := (rows 7 42 196 26 304 32 64 128 256), losses := [] }

theorem u6087 : Upper (D 5) (R 5) [6,40,192,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6087
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6088 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 196 28 19 297 361 425 297), lower := (rows 7 42 196 28 19 32 64 128 256), losses := [] }

theorem u6088 : Upper (D 5) (R 5) [6,40,192,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6088
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6089 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 42 196 28 25 291 355 419 291), lower := (rows 7 42 196 28 25 32 64 128 256), losses := [] }

theorem u6089 : Upper (D 5) (R 5) [6,40,192,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6089
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6090 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 28 26 289 353 417 289), lower := (rows 7 42 196 28 26 32 64 128 256), losses := [] }

theorem u6090 : Upper (D 5) (R 5) [6,40,192,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6090
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6091 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 28 49 299 331 395 267), lower := (rows 7 42 196 28 49 32 64 128 256), losses := [] }

theorem u6091 : Upper (D 5) (R 5) [6,40,192,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6091
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6092 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 28 50 297 329 393 265), lower := (rows 7 42 196 28 50 32 64 128 256), losses := [] }

theorem u6092 : Upper (D 5) (R 5) [6,40,192,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6092
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6093 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 28 56 291 323 387 259), lower := (rows 7 42 196 28 56 32 64 128 256), losses := [] }

theorem u6093 : Upper (D 5) (R 5) [6,40,192,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6093
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6094 : Route 9 := (fun mask => (mask,id))

def c6094 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6094 : Upper (D 5) (R 5) [6,40,192,20,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20,257] 13 (by decide) (choices 1) [1,2,8] r6094 c6094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2583
  · exact u2584
  · exact u2585

def r6095 : Route 9 := (fun mask => (mask,id))

def c6095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6095 : Upper (D 5) (R 5) [6,40,192,20,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20,258] 13 (by decide) (choices 1) [1,8] r6095 c6095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2586
  · exact u2587

def b6096 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 28 280 35 99 163 291), lower := (rows 7 42 196 28 280 32 64 128 256), losses := [] }

theorem u6096 : Upper (D 5) (R 5) [6,40,192,20,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6096
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6097 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 28 304 43 75 139 267), lower := (rows 7 42 196 28 304 32 64 128 256), losses := [] }

theorem u6097 : Upper (D 5) (R 5) [6,40,192,20,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6097
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6098 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 196 265 19 60 124 188 316), lower := (rows 7 42 196 265 19 32 64 128 256), losses := [] }

theorem u6098 : Upper (D 5) (R 5) [6,40,192,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6098
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6099 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 265 21 58 122 186 314), lower := (rows 7 42 196 265 21 32 64 128 256), losses := [] }

theorem u6099 : Upper (D 5) (R 5) [6,40,192,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6099
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6100 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 42 196 265 22 57 121 185 313), lower := (rows 7 42 196 265 22 32 64 128 256), losses := [] }

theorem u6100 : Upper (D 5) (R 5) [6,40,192,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6100
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6101 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 42 196 265 25 54 118 182 310), lower := (rows 7 42 196 265 25 32 64 128 256), losses := [] }

theorem u6101 : Upper (D 5) (R 5) [6,40,192,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6101
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6102 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 265 26 53 117 181 309), lower := (rows 7 42 196 265 26 32 64 128 256), losses := [] }

theorem u6102 : Upper (D 5) (R 5) [6,40,192,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6102
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6103 : Route 9 := (fun mask => (mask,id))

def c6103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6103 : Upper (D 5) (R 5) [6,40,192,257,12] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,12] 13 (by decide) (choices 1) [1,2,16] r6103 c6103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2588
  · exact u2589
  · exact u2590

def r6104 : Route 9 := (fun mask => (mask,id))

def c6104 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6104 : Upper (D 5) (R 5) [6,40,192,257,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,33] 13 (by decide) (choices 1) [2,4,8,16] r6104 c6104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2591
  · exact u2592
  · exact u2593
  · exact u2594

def b6105 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 265 50 61 93 157 285), lower := (rows 7 42 196 265 50 32 64 128 256), losses := [] }

theorem u6105 : Upper (D 5) (R 5) [6,40,192,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6105
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6106 : Route 9 := (fun mask => (mask,id))

def c6106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6106 : Upper (D 5) (R 5) [6,40,192,257,36] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,36] 13 (by decide) (choices 1) [1,2,8,16] r6106 c6106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2595
  · exact u2596
  · exact u2597
  · exact u2598

def b6107 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 265 56 55 87 151 279), lower := (rows 7 42 196 265 56 32 64 128 256), losses := [] }

theorem u6107 : Upper (D 5) (R 5) [6,40,192,257,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6107
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6108 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 266 21 57 121 185 313), lower := (rows 7 42 196 266 21 32 64 128 256), losses := [] }

theorem u6108 : Upper (D 5) (R 5) [6,40,192,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6109 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 228, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 42 196 266 25 53 117 181 309), lower := (rows 7 42 196 266 25 32 64 128 256), losses := [] }

theorem u6109 : Upper (D 5) (R 5) [6,40,192,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6109
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6110 : Route 9 := (fun mask => (mask,id))

def c6110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6110 : Upper (D 5) (R 5) [6,40,192,258,12] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,12] 13 (by decide) (choices 1) [1,16] r6110 c6110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2599
  · exact u2600

def r6111 : Route 9 := (fun mask => (mask,id))

def c6111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6111 : Upper (D 5) (R 5) [6,40,192,258,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,33] 13 (by decide) (choices 1) [1,4,8,16] r6111 c6111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2601
  · exact u2602
  · exact u2603
  · exact u2604

def r6112 : Route 9 := (fun mask => (mask,id))

def c6112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6112 : Upper (D 5) (R 5) [6,40,192,258,36] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,36] 13 (by decide) (choices 1) [1,8,16] r6112 c6112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2605
  · exact u2606
  · exact u2607

def b6113 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 266 56 53 85 149 277), lower := (rows 7 42 196 266 56 32 64 128 256), losses := [] }

theorem u6113 : Upper (D 5) (R 5) [6,40,192,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6114 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 196 268 19 57 121 185 313), lower := (rows 7 42 196 268 19 32 64 128 256), losses := [] }

theorem u6114 : Upper (D 5) (R 5) [6,40,192,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6114
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6115 : Route 9 := (fun mask => (mask,id))

def c6115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6115 : Upper (D 5) (R 5) [6,40,192,260,9] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,9] 13 (by decide) (choices 1) [1,2,16] r6115 c6115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2608
  · exact u2609
  · exact u2610

def b6116 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 268 26 49 113 177 305), lower := (rows 7 42 196 268 26 32 64 128 256), losses := [] }

theorem u6116 : Upper (D 5) (R 5) [6,40,192,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6116
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6117 : Route 9 := (fun mask => (mask,id))

def c6117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6117 : Upper (D 5) (R 5) [6,40,192,260,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,33] 13 (by decide) (choices 1) [1,2,8,16] r6117 c6117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2611
  · exact u2612
  · exact u2613
  · exact u2614

def b6118 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 268 50 57 89 153 281), lower := (rows 7 42 196 268 50 32 64 128 256), losses := [] }

theorem u6118 : Upper (D 5) (R 5) [6,40,192,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6118
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6119 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 268 56 51 83 147 275), lower := (rows 7 42 196 268 56 32 64 128 256), losses := [] }

theorem u6119 : Upper (D 5) (R 5) [6,40,192,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6119
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6119
end Delivery.IrregularNine14.P05
