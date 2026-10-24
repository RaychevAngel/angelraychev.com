import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0044
import IrregularNine14P05C0045

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6240 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 140 49 299 331 395 267), lower := (rows 7 50 76 140 49 32 64 128 256), losses := [] }

theorem u6240 : Upper (D 5) (R 5) [6,48,72,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6240
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6241 : PairBound 9 := { available := 265, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 140 50 297 329 393 265), lower := (rows 7 50 76 140 50 32 64 128 256), losses := [] }

theorem u6241 : Upper (D 5) (R 5) [6,48,72,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6241
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6242 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 140 56 291 323 387 259), lower := (rows 7 50 76 140 56 32 64 128 256), losses := [] }

theorem u6242 : Upper (D 5) (R 5) [6,48,72,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6242
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6243 : Route 9 := (fun mask => (mask,id))

def c6243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6243 : Upper (D 5) (R 5) [6,48,72,132,257] 13 := by
  apply FastRouting.sound _ _ [6,48,72,132,257] 13 (by decide) (choices 1) [1,2,8] r6243 c6243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2690
  · exact u2691
  · exact u2692

def b6244 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 140 274 41 105 169 297), lower := (rows 7 50 76 140 274 32 64 128 256), losses := [] }

theorem u6244 : Upper (D 5) (R 5) [6,48,72,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6244
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6245 : Route 9 := (fun mask => (mask,id))

def c6245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6245 : Upper (D 5) (R 5) [6,48,72,132,264] 13 := by
  apply FastRouting.sound _ _ [6,48,72,132,264] 13 (by decide) (choices 1) [1,2] r6245 c6245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2693
  · exact u2694

def b6246 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 140 304 43 75 139 267), lower := (rows 7 50 76 140 304 32 64 128 256), losses := [] }

theorem u6246 : Upper (D 5) (R 5) [6,48,72,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6246
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6247 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 76 168 19 301 333 397 269), lower := (rows 7 50 76 168 19 32 64 128 256), losses := [] }

theorem u6247 : Upper (D 5) (R 5) [6,48,72,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6247
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6248 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 76 168 21 299 331 395 267), lower := (rows 7 50 76 168 21 32 64 128 256), losses := [] }

theorem u6248 : Upper (D 5) (R 5) [6,48,72,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6248
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6249 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 168 22 297 329 393 265), lower := (rows 7 50 76 168 22 32 64 128 256), losses := [] }

theorem u6249 : Upper (D 5) (R 5) [6,48,72,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6249
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6250 : PairBound 9 := { available := 263, camps := [], pairs := [(0,5),(1,3)], upper := (rows 7 50 76 168 25 295 327 391 263), lower := (rows 7 50 76 168 25 32 64 128 256), losses := [{ target := 3, region := (rows 1 18 4 0 16 33 65 129 257), good := (rows 487 50 68 160 499 32 64 128 256) },{ target := 5, region := (rows 3 2 20 8 16 0 67 131 259), good := (rows 455 471 76 136 477 0 64 128 256) }] }

theorem u6250 : Upper (D 5) (R 5) [6,48,72,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6250
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6251 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 168 26 293 325 389 261), lower := (rows 7 50 76 168 26 32 64 128 256), losses := [] }

theorem u6251 : Upper (D 5) (R 5) [6,48,72,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6251
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6252 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 50 76 168 28 291 323 387 259), lower := (rows 7 50 76 168 28 32 64 128 256), losses := [] }

theorem u6252 : Upper (D 5) (R 5) [6,48,72,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6252
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6253 : Route 9 := (fun mask => (mask,id))

def c6253 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6253 : Upper (D 5) (R 5) [6,48,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,48,72,160,257] 13 (by decide) (choices 1) [1,2,4,8] r6253 c6253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2695
  · exact u2696
  · exact u2697
  · exact u2698

def b6254 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 168 274 45 77 141 269), lower := (rows 7 50 76 168 274 32 64 128 256), losses := [] }

theorem u6254 : Upper (D 5) (R 5) [6,48,72,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6254
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6255 : Route 9 := (fun mask => (mask,id))

def c6255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6255 : Upper (D 5) (R 5) [6,48,72,160,260] 13 := by
  apply FastRouting.sound _ _ [6,48,72,160,260] 13 (by decide) (choices 1) [1,2,8] r6255 c6255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2699
  · exact u2700
  · exact u2701

def r6256 : Route 9 := (fun mask => (mask,id))

def c6256 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6256 : Upper (D 5) (R 5) [6,48,72,160,264] 13 := by
  apply FastRouting.sound _ _ [6,48,72,160,264] 13 (by decide) (choices 1) [1,2,4] r6256 c6256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2702
  · exact u2703
  · exact u2704

def b6257 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 76 392 19 45 109 173 301), lower := (rows 7 50 76 392 19 32 64 128 256), losses := [] }

theorem u6257 : Upper (D 5) (R 5) [6,48,72,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6257
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6258 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 76 392 21 43 107 171 299), lower := (rows 7 50 76 392 21 32 64 128 256), losses := [] }

theorem u6258 : Upper (D 5) (R 5) [6,48,72,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6258
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6259 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 392 22 41 105 169 297), lower := (rows 7 50 76 392 22 32 64 128 256), losses := [] }

theorem u6259 : Upper (D 5) (R 5) [6,48,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6259
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6260 : Route 9 := (fun mask => (mask,id))

def c6260 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6260 : Upper (D 5) (R 5) [6,48,72,384,9] 13 := by
  apply FastRouting.sound _ _ [6,48,72,384,9] 13 (by decide) (choices 1) [1,2,4] r6260 c6260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2705
  · exact u2706
  · exact u2707

def b6261 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 76 392 26 37 101 165 293), lower := (rows 7 50 76 392 26 32 64 128 256), losses := [] }

theorem u6261 : Upper (D 5) (R 5) [6,48,72,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6262 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 50 76 392 28 35 99 163 291), lower := (rows 7 50 76 392 28 32 64 128 256), losses := [] }

theorem u6262 : Upper (D 5) (R 5) [6,48,72,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6262
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6263 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 392 49 47 79 143 271), lower := (rows 7 50 76 392 49 32 64 128 256), losses := [] }

theorem u6263 : Upper (D 5) (R 5) [6,48,72,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6263
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6264 : PairBound 9 := { available := 13, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 392 50 45 77 141 269), lower := (rows 7 50 76 392 50 32 64 128 256), losses := [] }

theorem u6264 : Upper (D 5) (R 5) [6,48,72,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6265 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 392 52 43 75 139 267), lower := (rows 7 50 76 392 52 32 64 128 256), losses := [] }

theorem u6265 : Upper (D 5) (R 5) [6,48,72,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6265
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6266 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 392 56 39 71 135 263), lower := (rows 7 50 76 392 56 32 64 128 256), losses := [] }

theorem u6266 : Upper (D 5) (R 5) [6,48,72,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6266
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6267 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 196 41 19 300 332 396 268), lower := (rows 7 50 196 41 19 32 64 128 256), losses := [] }

theorem u6267 : Upper (D 5) (R 5) [6,48,192,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6268 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 196 41 21 298 330 394 266), lower := (rows 7 50 196 41 21 32 64 128 256), losses := [] }

theorem u6268 : Upper (D 5) (R 5) [6,48,192,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6269 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 196 41 22 297 329 393 265), lower := (rows 7 50 196 41 22 32 64 128 256), losses := [] }

theorem u6269 : Upper (D 5) (R 5) [6,48,192,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6270 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 16, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 50 196 41 25 302 334 398 270), lower := (rows 7 50 196 41 25 32 64 128 256), losses := [] }

theorem u6270 : Upper (D 5) (R 5) [6,48,192,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6271 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 41 26 301 333 397 269), lower := (rows 7 50 196 41 26 32 64 128 256), losses := [] }

theorem u6271 : Upper (D 5) (R 5) [6,48,192,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6272 : Route 9 := (fun mask => (mask,id))

def c6272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6272 : Upper (D 5) (R 5) [6,48,192,33,12] 13 := by
  apply FastRouting.sound _ _ [6,48,192,33,12] 13 (by decide) (choices 1) [1,2,8,256] r6272 c6272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2708
  · exact u2709
  · exact u2710
  · exact u2711

def r6273 : Route 9 := (fun mask => (mask,id))

def c6273 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6273 : Upper (D 5) (R 5) [6,48,192,33,257] 13 := by
  apply FastRouting.sound _ _ [6,48,192,33,257] 13 (by decide) (choices 1) [2,4,8] r6273 c6273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2712
  · exact u2713
  · exact u2714

def b6274 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 196 41 274 45 77 141 269), lower := (rows 7 50 196 41 274 32 64 128 256), losses := [] }

theorem u6274 : Upper (D 5) (R 5) [6,48,192,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6275 : Route 9 := (fun mask => (mask,id))

def c6275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6275 : Upper (D 5) (R 5) [6,48,192,33,260] 13 := by
  apply FastRouting.sound _ _ [6,48,192,33,260] 13 (by decide) (choices 1) [1,2,8] r6275 c6275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2715
  · exact u2716
  · exact u2717

def r6276 : Route 9 := (fun mask => (mask,id))

def c6276 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6276 : Upper (D 5) (R 5) [6,48,192,33,264] 13 := by
  apply FastRouting.sound _ _ [6,48,192,33,264] 13 (by decide) (choices 1) [1,2,4,8] r6276 c6276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2718
  · exact u2719
  · exact u2720
  · exact u2721

def b6277 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 196 44 19 297 329 393 265), lower := (rows 7 50 196 44 19 32 64 128 256), losses := [] }

theorem u6277 : Upper (D 5) (R 5) [6,48,192,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6277
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6278 : Route 9 := (fun mask => (mask,id))

def c6278 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6278 : Upper (D 5) (R 5) [6,48,192,36,9] 13 := by
  apply FastRouting.sound _ _ [6,48,192,36,9] 13 (by decide) (choices 1) [1,2,8,256] r6278 c6278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2722
  · exact u2723
  · exact u2724
  · exact u2725

def b6279 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 44 26 297 329 393 265), lower := (rows 7 50 196 44 26 32 64 128 256), losses := [] }

theorem u6279 : Upper (D 5) (R 5) [6,48,192,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6279
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6280 : Route 9 := (fun mask => (mask,id))

def c6280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6280 : Upper (D 5) (R 5) [6,48,192,36,257] 13 := by
  apply FastRouting.sound _ _ [6,48,192,36,257] 13 (by decide) (choices 1) [1,2,8] r6280 c6280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2726
  · exact u2727
  · exact u2728

def b6281 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 196 44 274 41 73 137 265), lower := (rows 7 50 196 44 274 32 64 128 256), losses := [] }

theorem u6281 : Upper (D 5) (R 5) [6,48,192,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6281
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6282 : Route 9 := (fun mask => (mask,id))

def c6282 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6282 : Upper (D 5) (R 5) [6,48,192,36,264] 13 := by
  apply FastRouting.sound _ _ [6,48,192,36,264] 13 (by decide) (choices 1) [1,2,8] r6282 c6282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2729
  · exact u2730
  · exact u2731

def b6283 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 196 265 19 44 108 172 300), lower := (rows 7 50 196 265 19 32 64 128 256), losses := [] }

theorem u6283 : Upper (D 5) (R 5) [6,48,192,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6283
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6284 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 196 265 21 42 106 170 298), lower := (rows 7 50 196 265 21 32 64 128 256), losses := [] }

theorem u6284 : Upper (D 5) (R 5) [6,48,192,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6284
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6285 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 196 265 22 41 105 169 297), lower := (rows 7 50 196 265 22 32 64 128 256), losses := [] }

theorem u6285 : Upper (D 5) (R 5) [6,48,192,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6285
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6286 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 50 196 265 25 46 110 174 302), lower := (rows 7 50 196 265 25 32 64 128 256), losses := [] }

theorem u6286 : Upper (D 5) (R 5) [6,48,192,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6286
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6287 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 196 265 26 45 109 173 301), lower := (rows 7 50 196 265 26 32 64 128 256), losses := [] }

theorem u6287 : Upper (D 5) (R 5) [6,48,192,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6287
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6288 : Route 9 := (fun mask => (mask,id))

def c6288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6288 : Upper (D 5) (R 5) [6,48,192,257,12] 13 := by
  apply FastRouting.sound _ _ [6,48,192,257,12] 13 (by decide) (choices 1) [1,2,8] r6288 c6288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2732
  · exact u2733
  · exact u2734

def b6289 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 265 49 46 78 142 270), lower := (rows 7 50 196 265 49 32 64 128 256), losses := [] }

theorem u6289 : Upper (D 5) (R 5) [6,48,192,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6289
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6290 : PairBound 9 := { available := 13, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 265 50 45 77 141 269), lower := (rows 7 50 196 265 50 32 64 128 256), losses := [] }

theorem u6290 : Upper (D 5) (R 5) [6,48,192,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6290
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6291 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 265 52 43 75 139 267), lower := (rows 7 50 196 265 52 32 64 128 256), losses := [] }

theorem u6291 : Upper (D 5) (R 5) [6,48,192,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6291
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6292 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 265 56 47 79 143 271), lower := (rows 7 50 196 265 56 32 64 128 256), losses := [] }

theorem u6292 : Upper (D 5) (R 5) [6,48,192,257,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6292
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6293 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 196 266 21 41 105 169 297), lower := (rows 7 50 196 266 21 32 64 128 256), losses := [] }

theorem u6293 : Upper (D 5) (R 5) [6,48,192,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6294 : Route 9 := (fun mask => (mask,id))

def c6294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6294 : Upper (D 5) (R 5) [6,48,192,258,9] 13 := by
  apply FastRouting.sound _ _ [6,48,192,258,9] 13 (by decide) (choices 1) [1,4,8] r6294 c6294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2735
  · exact u2736
  · exact u2737

def r6295 : Route 9 := (fun mask => (mask,id))

def c6295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6295 : Upper (D 5) (R 5) [6,48,192,258,12] 13 := by
  apply FastRouting.sound _ _ [6,48,192,258,12] 13 (by decide) (choices 1) [1,8] r6295 c6295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2738
  · exact u2739

def b6296 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 266 49 45 77 141 269), lower := (rows 7 50 196 266 49 32 64 128 256), losses := [] }

theorem u6296 : Upper (D 5) (R 5) [6,48,192,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6296
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6297 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 266 52 41 73 137 265), lower := (rows 7 50 196 266 52 32 64 128 256), losses := [] }

theorem u6297 : Upper (D 5) (R 5) [6,48,192,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6298 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 266 56 45 77 141 269), lower := (rows 7 50 196 266 56 32 64 128 256), losses := [] }

theorem u6298 : Upper (D 5) (R 5) [6,48,192,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6298
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6299 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 196 268 19 41 105 169 297), lower := (rows 7 50 196 268 19 32 64 128 256), losses := [] }

theorem u6299 : Upper (D 5) (R 5) [6,48,192,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6299
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6299
end Delivery.IrregularNine14.P05
