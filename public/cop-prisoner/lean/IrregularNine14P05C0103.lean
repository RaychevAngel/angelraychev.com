import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0044

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6180 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 50 69 168 273 46 78 142 270), lower := (rows 7 50 69 168 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 29 16 33 65 129 257), good := (rows 494 58 492 168 506 32 64 128 256) }] }

theorem u6180 : Upper (D 5) (R 5) [6,48,65,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6180
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6181 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 168 274 45 77 141 269), lower := (rows 7 50 69 168 274 32 64 128 256), losses := [] }

theorem u6181 : Upper (D 5) (R 5) [6,48,65,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6181
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6182 : Route 9 := (fun mask => (mask,id))

def c6182 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6182 : Upper (D 5) (R 5) [6,48,65,160,260] 13 := by
  apply FastRouting.sound _ _ [6,48,65,160,260] 13 (by decide) (choices 1) [1,2,8] r6182 c6182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2642
  · exact u2643
  · exact u2644

def r6183 : Route 9 := (fun mask => (mask,id))

def c6183 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6183 : Upper (D 5) (R 5) [6,48,65,160,264] 13 := by
  apply FastRouting.sound _ _ [6,48,65,160,264] 13 (by decide) (choices 1) [1,2,4,8] r6183 c6183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2645
  · exact u2646
  · exact u2647
  · exact u2648

def b6184 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 69 392 19 44 108 172 300), lower := (rows 7 50 69 392 19 32 64 128 256), losses := [] }

theorem u6184 : Upper (D 5) (R 5) [6,48,65,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6184
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6185 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 392 21 42 106 170 298), lower := (rows 7 50 69 392 21 32 64 128 256), losses := [] }

theorem u6185 : Upper (D 5) (R 5) [6,48,65,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6185
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6186 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 392 22 41 105 169 297), lower := (rows 7 50 69 392 22 32 64 128 256), losses := [] }

theorem u6186 : Upper (D 5) (R 5) [6,48,65,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6186
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6187 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 50 69 392 25 46 110 174 302), lower := (rows 7 50 69 392 25 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 29 16 33 65 129 257), good := (rows 494 58 492 392 506 32 64 128 256) }] }

theorem u6187 : Upper (D 5) (R 5) [6,48,65,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6187
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6188 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 69 392 26 45 109 173 301), lower := (rows 7 50 69 392 26 32 64 128 256), losses := [] }

theorem u6188 : Upper (D 5) (R 5) [6,48,65,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6189 : Route 9 := (fun mask => (mask,id))

def c6189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6189 : Upper (D 5) (R 5) [6,48,65,384,12] 13 := by
  apply FastRouting.sound _ _ [6,48,65,384,12] 13 (by decide) (choices 1) [1,2,8] r6189 c6189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2649
  · exact u2650
  · exact u2651

def b6190 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 392 49 46 78 142 270), lower := (rows 7 50 69 392 49 32 64 128 256), losses := [] }

theorem u6190 : Upper (D 5) (R 5) [6,48,65,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6190
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6191 : PairBound 9 := { available := 13, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 392 50 45 77 141 269), lower := (rows 7 50 69 392 50 32 64 128 256), losses := [] }

theorem u6191 : Upper (D 5) (R 5) [6,48,65,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6192 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 392 52 43 75 139 267), lower := (rows 7 50 69 392 52 32 64 128 256), losses := [] }

theorem u6192 : Upper (D 5) (R 5) [6,48,65,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6192
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6193 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 392 56 47 79 143 271), lower := (rows 7 50 69 392 56 32 64 128 256), losses := [] }

theorem u6193 : Upper (D 5) (R 5) [6,48,65,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6193
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6194 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 76 41 19 428 460 396 396), lower := (rows 7 50 76 41 19 32 64 128 256), losses := [] }

theorem u6194 : Upper (D 5) (R 5) [6,48,72,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6194
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6195 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 76 41 21 426 458 394 394), lower := (rows 7 50 76 41 21 32 64 128 256), losses := [] }

theorem u6195 : Upper (D 5) (R 5) [6,48,72,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6195
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6196 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 41 22 425 457 393 393), lower := (rows 7 50 76 41 22 32 64 128 256), losses := [] }

theorem u6196 : Upper (D 5) (R 5) [6,48,72,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6196
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6197 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 16, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 50 76 41 25 422 454 390 390), lower := (rows 7 50 76 41 25 32 64 128 256), losses := [] }

theorem u6197 : Upper (D 5) (R 5) [6,48,72,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6198 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 41 26 421 453 389 389), lower := (rows 7 50 76 41 26 32 64 128 256), losses := [] }

theorem u6198 : Upper (D 5) (R 5) [6,48,72,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6198
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6199 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 50 76 41 28 419 451 387 387), lower := (rows 7 50 76 41 28 32 64 128 256), losses := [] }

theorem u6199 : Upper (D 5) (R 5) [6,48,72,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6199
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6200 : Route 9 := (fun mask => (mask,id))

def c6200 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6200 : Upper (D 5) (R 5) [6,48,72,33,129] 13 := by
  apply FastRouting.sound _ _ [6,48,72,33,129] 13 (by decide) (choices 1) [2,4,8,256] r6200 c6200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2652
  · exact u2653
  · exact u2654
  · exact u2655

def b6201 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 41 146 301 333 397 269), lower := (rows 7 50 76 41 146 32 64 128 256), losses := [] }

theorem u6201 : Upper (D 5) (R 5) [6,48,72,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6202 : Route 9 := (fun mask => (mask,id))

def c6202 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6202 : Upper (D 5) (R 5) [6,48,72,33,132] 13 := by
  apply FastRouting.sound _ _ [6,48,72,33,132] 13 (by decide) (choices 1) [1,2,8,256] r6202 c6202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2656
  · exact u2657
  · exact u2658
  · exact u2659

def b6203 : PairBound 9 := { available := 263, camps := [], pairs := [(2,5),(4,5)], upper := (rows 7 50 76 41 152 295 327 391 263), lower := (rows 7 50 76 41 152 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 24 0 65 129 257), good := (rows 455 18 92 477 156 0 64 128 256) }] }

theorem u6203 : Upper (D 5) (R 5) [6,48,72,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6204 : Route 9 := (fun mask => (mask,id))

def c6204 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6204 : Upper (D 5) (R 5) [6,48,72,33,384] 13 := by
  apply FastRouting.sound _ _ [6,48,72,33,384] 13 (by decide) (choices 1) [1,2,4,8] r6204 c6204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2660
  · exact u2661
  · exact u2662
  · exact u2663

def b6205 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 76 44 19 425 457 393 393), lower := (rows 7 50 76 44 19 32 64 128 256), losses := [] }

theorem u6205 : Upper (D 5) (R 5) [6,48,72,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6205
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6206 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 418, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 50 76 44 25 419 451 387 387), lower := (rows 7 50 76 44 25 32 64 128 256), losses := [] }

theorem u6206 : Upper (D 5) (R 5) [6,48,72,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6206
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6207 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 44 26 417 449 385 385), lower := (rows 7 50 76 44 26 32 64 128 256), losses := [] }

theorem u6207 : Upper (D 5) (R 5) [6,48,72,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6207
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6208 : Route 9 := (fun mask => (mask,id))

def c6208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6208 : Upper (D 5) (R 5) [6,48,72,36,129] 13 := by
  apply FastRouting.sound _ _ [6,48,72,36,129] 13 (by decide) (choices 1) [1,2,8,256] r6208 c6208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2664
  · exact u2665
  · exact u2666
  · exact u2667

def b6209 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 44 146 297 329 393 265), lower := (rows 7 50 76 44 146 32 64 128 256), losses := [] }

theorem u6209 : Upper (D 5) (R 5) [6,48,72,36,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6209
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6210 : Route 9 := (fun mask => (mask,id))

def c6210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6210 : Upper (D 5) (R 5) [6,48,72,36,136] 13 := by
  apply FastRouting.sound _ _ [6,48,72,36,136] 13 (by decide) (choices 1) [1,2,256] r6210 c6210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2668
  · exact u2669
  · exact u2670

def r6211 : Route 9 := (fun mask => (mask,id))

def c6211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6211 : Upper (D 5) (R 5) [6,48,72,36,384] 13 := by
  apply FastRouting.sound _ _ [6,48,72,36,384] 13 (by decide) (choices 1) [1,2,8] r6211 c6211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2671
  · exact u2672
  · exact u2673

def b6212 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 76 137 19 300 364 428 300), lower := (rows 7 50 76 137 19 32 64 128 256), losses := [] }

theorem u6212 : Upper (D 5) (R 5) [6,48,72,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6212
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6213 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 76 137 21 298 362 426 298), lower := (rows 7 50 76 137 21 32 64 128 256), losses := [] }

theorem u6213 : Upper (D 5) (R 5) [6,48,72,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6213
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6214 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 137 22 297 361 425 297), lower := (rows 7 50 76 137 22 32 64 128 256), losses := [] }

theorem u6214 : Upper (D 5) (R 5) [6,48,72,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6215 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 50 76 137 25 294 358 422 294), lower := (rows 7 50 76 137 25 32 64 128 256), losses := [] }

theorem u6215 : Upper (D 5) (R 5) [6,48,72,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6216 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 137 26 293 357 421 293), lower := (rows 7 50 76 137 26 32 64 128 256), losses := [] }

theorem u6216 : Upper (D 5) (R 5) [6,48,72,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6216
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6217 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 50 76 137 28 291 355 419 291), lower := (rows 7 50 76 137 28 32 64 128 256), losses := [] }

theorem u6217 : Upper (D 5) (R 5) [6,48,72,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6217
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6218 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 137 49 302 334 398 270), lower := (rows 7 50 76 137 49 32 64 128 256), losses := [] }

theorem u6218 : Upper (D 5) (R 5) [6,48,72,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6219 : PairBound 9 := { available := 269, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 137 50 301 333 397 269), lower := (rows 7 50 76 137 50 32 64 128 256), losses := [] }

theorem u6219 : Upper (D 5) (R 5) [6,48,72,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6219
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6220 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 137 52 299 331 395 267), lower := (rows 7 50 76 137 52 32 64 128 256), losses := [] }

theorem u6220 : Upper (D 5) (R 5) [6,48,72,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6220
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6221 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 137 56 295 327 391 263), lower := (rows 7 50 76 137 56 32 64 128 256), losses := [] }

theorem u6221 : Upper (D 5) (R 5) [6,48,72,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6221
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6222 : Route 9 := (fun mask => (mask,id))

def c6222 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6222 : Upper (D 5) (R 5) [6,48,72,129,257] 13 := by
  apply FastRouting.sound _ _ [6,48,72,129,257] 13 (by decide) (choices 1) [2,4,8] r6222 c6222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2674
  · exact u2675
  · exact u2676

def b6223 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 137 274 45 109 173 301), lower := (rows 7 50 76 137 274 32 64 128 256), losses := [] }

theorem u6223 : Upper (D 5) (R 5) [6,48,72,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6223
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6224 : Route 9 := (fun mask => (mask,id))

def c6224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6224 : Upper (D 5) (R 5) [6,48,72,129,260] 13 := by
  apply FastRouting.sound _ _ [6,48,72,129,260] 13 (by decide) (choices 1) [1,2,8] r6224 c6224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2677
  · exact u2678
  · exact u2679

def r6225 : Route 9 := (fun mask => (mask,id))

def c6225 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6225 : Upper (D 5) (R 5) [6,48,72,129,264] 13 := by
  apply FastRouting.sound _ _ [6,48,72,129,264] 13 (by decide) (choices 1) [1,2,4] r6225 c6225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2680
  · exact u2681
  · exact u2682

def b6226 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 137 304 47 79 143 271), lower := (rows 7 50 76 137 304 32 64 128 256), losses := [] }

theorem u6226 : Upper (D 5) (R 5) [6,48,72,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6226
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6227 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 76 138 21 297 361 425 297), lower := (rows 7 50 76 138 21 32 64 128 256), losses := [] }

theorem u6227 : Upper (D 5) (R 5) [6,48,72,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6228 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 356, targets := 2 }], pairs := [(1,3),(2,1)], upper := (rows 7 50 76 138 25 293 357 421 293), lower := (rows 7 50 76 138 25 32 64 128 256), losses := [{ target := 3, region := (rows 1 18 4 0 16 33 65 129 257), good := (rows 487 50 68 130 499 32 64 128 256) }] }

theorem u6228 : Upper (D 5) (R 5) [6,48,72,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6228
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6229 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 50 76 138 28 289 353 417 289), lower := (rows 7 50 76 138 28 32 64 128 256), losses := [] }

theorem u6229 : Upper (D 5) (R 5) [6,48,72,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6229
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6230 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 138 49 301 333 397 269), lower := (rows 7 50 76 138 49 32 64 128 256), losses := [] }

theorem u6230 : Upper (D 5) (R 5) [6,48,72,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6231 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 138 52 297 329 393 265), lower := (rows 7 50 76 138 52 32 64 128 256), losses := [] }

theorem u6231 : Upper (D 5) (R 5) [6,48,72,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6231
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6232 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 138 56 293 325 389 261), lower := (rows 7 50 76 138 56 32 64 128 256), losses := [] }

theorem u6232 : Upper (D 5) (R 5) [6,48,72,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6232
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6233 : Route 9 := (fun mask => (mask,id))

def c6233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6233 : Upper (D 5) (R 5) [6,48,72,130,257] 13 := by
  apply FastRouting.sound _ _ [6,48,72,130,257] 13 (by decide) (choices 1) [1,4,8] r6233 c6233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2683
  · exact u2684
  · exact u2685

def r6234 : Route 9 := (fun mask => (mask,id))

def c6234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6234 : Upper (D 5) (R 5) [6,48,72,130,260] 13 := by
  apply FastRouting.sound _ _ [6,48,72,130,260] 13 (by decide) (choices 1) [1,8] r6234 c6234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2686
  · exact u2687

def r6235 : Route 9 := (fun mask => (mask,id))

def c6235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6235 : Upper (D 5) (R 5) [6,48,72,130,264] 13 := by
  apply FastRouting.sound _ _ [6,48,72,130,264] 13 (by decide) (choices 1) [1,4] r6235 c6235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2688
  · exact u2689

def b6236 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 138 304 45 77 141 269), lower := (rows 7 50 76 138 304 32 64 128 256), losses := [] }

theorem u6236 : Upper (D 5) (R 5) [6,48,72,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6236
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6237 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 76 140 19 297 361 425 297), lower := (rows 7 50 76 140 19 32 64 128 256), losses := [] }

theorem u6237 : Upper (D 5) (R 5) [6,48,72,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6238 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 290, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 50 76 140 25 291 355 419 291), lower := (rows 7 50 76 140 25 32 64 128 256), losses := [] }

theorem u6238 : Upper (D 5) (R 5) [6,48,72,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6238
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6239 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 140 26 289 353 417 289), lower := (rows 7 50 76 140 26 32 64 128 256), losses := [] }

theorem u6239 : Upper (D 5) (R 5) [6,48,72,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6239
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6239
end Delivery.IrregularNine14.P05
