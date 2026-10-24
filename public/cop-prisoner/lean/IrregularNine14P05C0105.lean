import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0045
import IrregularNine14P05C0046

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6300 : Route 9 := (fun mask => (mask,id))

def c6300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6300 : Upper (D 5) (R 5) [6,48,192,260,9] 13 := by
  apply FastRouting.sound _ _ [6,48,192,260,9] 13 (by decide) (choices 1) [1,2,8] r6300 c6300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2740
  · exact u2741
  · exact u2742

def b6301 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 196 268 26 41 105 169 297), lower := (rows 7 50 196 268 26 32 64 128 256), losses := [] }

theorem u6301 : Upper (D 5) (R 5) [6,48,192,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6302 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 268 49 43 75 139 267), lower := (rows 7 50 196 268 49 32 64 128 256), losses := [] }

theorem u6302 : Upper (D 5) (R 5) [6,48,192,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6302
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6303 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 268 50 41 73 137 265), lower := (rows 7 50 196 268 50 32 64 128 256), losses := [] }

theorem u6303 : Upper (D 5) (R 5) [6,48,192,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6304 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 268 56 43 75 139 267), lower := (rows 7 50 196 268 56 32 64 128 256), losses := [] }

theorem u6304 : Upper (D 5) (R 5) [6,48,192,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6304
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6305 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 50 196 296 19 45 77 141 269), lower := (rows 7 50 196 296 19 32 64 128 256), losses := [] }

theorem u6305 : Upper (D 5) (R 5) [6,48,192,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6305
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6306 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 196 296 21 43 75 139 267), lower := (rows 7 50 196 296 21 32 64 128 256), losses := [] }

theorem u6306 : Upper (D 5) (R 5) [6,48,192,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6306
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6307 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 50 196 296 22 41 73 137 265), lower := (rows 7 50 196 296 22 32 64 128 256), losses := [] }

theorem u6307 : Upper (D 5) (R 5) [6,48,192,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6308 : Route 9 := (fun mask => (mask,id))

def c6308 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6308 : Upper (D 5) (R 5) [6,48,192,288,9] 13 := by
  apply FastRouting.sound _ _ [6,48,192,288,9] 13 (by decide) (choices 1) [1,2,4,8] r6308 c6308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2743
  · exact u2744
  · exact u2745
  · exact u2746

def b6309 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 296 26 45 77 141 269), lower := (rows 7 50 196 296 26 32 64 128 256), losses := [] }

theorem u6309 : Upper (D 5) (R 5) [6,48,192,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6310 : Route 9 := (fun mask => (mask,id))

def c6310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6310 : Upper (D 5) (R 5) [6,48,192,288,12] 13 := by
  apply FastRouting.sound _ _ [6,48,192,288,12] 13 (by decide) (choices 1) [1,2,8] r6310 c6310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2747
  · exact u2748
  · exact u2749

def b6311 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 140 25 22 296 360 424 296), lower := (rows 7 67 140 25 22 32 64 128 256), losses := [] }

theorem u6311 : Upper (D 5) (R 5) [6,65,136,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6312 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 67 140 25 26 292 356 420 292), lower := (rows 7 67 140 25 26 32 64 128 256), losses := [] }

theorem u6312 : Upper (D 5) (R 5) [6,65,136,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6312
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6313 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 140 25 28 290 354 418 290), lower := (rows 7 67 140 25 28 32 64 128 256), losses := [] }

theorem u6313 : Upper (D 5) (R 5) [6,65,136,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6313
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6314 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 25 50 300 364 428 300), lower := (rows 7 67 140 25 50 32 64 128 256), losses := [] }

theorem u6314 : Upper (D 5) (R 5) [6,65,136,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6315 : Route 9 := (fun mask => (mask,id))

def c6315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6315 : Upper (D 5) (R 5) [6,65,136,17,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,17,36] 13 (by decide) (choices 1) [2,8,256] r6315 c6315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2750
  · exact u2751
  · exact u2752

def b6316 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 355, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 25 56 294 358 422 294), lower := (rows 7 67 140 25 56 32 64 128 256), losses := [] }

theorem u6316 : Upper (D 5) (R 5) [6,65,136,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6316
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6317 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 25 274 44 108 172 300), lower := (rows 7 67 140 25 274 32 64 128 256), losses := [] }

theorem u6317 : Upper (D 5) (R 5) [6,65,136,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6318 : Route 9 := (fun mask => (mask,id))

def c6318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6318 : Upper (D 5) (R 5) [6,65,136,17,260] 13 := by
  apply FastRouting.sound _ _ [6,65,136,17,260] 13 (by decide) (choices 1) [2,8] r6318 c6318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2753
  · exact u2754

def b6319 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 25 280 38 102 166 294), lower := (rows 7 67 140 25 280 32 64 128 256), losses := [] }

theorem u6319 : Upper (D 5) (R 5) [6,65,136,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6319
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6320 : Route 9 := (fun mask => (mask,id))

def c6320 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6320 : Upper (D 5) (R 5) [6,65,136,17,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,17,288] 13 (by decide) (choices 1) [2,4,8] r6320 c6320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2755
  · exact u2756
  · exact u2757

def b6321 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 26 21 296 360 424 296), lower := (rows 7 67 140 26 21 32 64 128 256), losses := [] }

theorem u6321 : Upper (D 5) (R 5) [6,65,136,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6322 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 67 140 26 25 292 356 420 292), lower := (rows 7 67 140 26 25 32 64 128 256), losses := [] }

theorem u6322 : Upper (D 5) (R 5) [6,65,136,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6322
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6323 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 26 28 289 353 417 289), lower := (rows 7 67 140 26 28 32 64 128 256), losses := [] }

theorem u6323 : Upper (D 5) (R 5) [6,65,136,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6323
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6324 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 26 49 300 364 428 300), lower := (rows 7 67 140 26 49 32 64 128 256), losses := [] }

theorem u6324 : Upper (D 5) (R 5) [6,65,136,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6324
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6325 : Route 9 := (fun mask => (mask,id))

def c6325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6325 : Upper (D 5) (R 5) [6,65,136,18,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,18,36] 13 (by decide) (choices 1) [1,8,256] r6325 c6325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2758
  · exact u2759
  · exact u2760

def b6326 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 355, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 26 56 293 357 421 293), lower := (rows 7 67 140 26 56 32 64 128 256), losses := [] }

theorem u6326 : Upper (D 5) (R 5) [6,65,136,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6326
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6327 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 26 273 44 108 172 300), lower := (rows 7 67 140 26 273 32 64 128 256), losses := [] }

theorem u6327 : Upper (D 5) (R 5) [6,65,136,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6328 : Route 9 := (fun mask => (mask,id))

def c6328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6328 : Upper (D 5) (R 5) [6,65,136,18,260] 13 := by
  apply FastRouting.sound _ _ [6,65,136,18,260] 13 (by decide) (choices 1) [1,8] r6328 c6328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2761
  · exact u2762

def b6329 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 26 280 37 101 165 293), lower := (rows 7 67 140 26 280 32 64 128 256), losses := [] }

theorem u6329 : Upper (D 5) (R 5) [6,65,136,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6330 : Route 9 := (fun mask => (mask,id))

def c6330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6330 : Upper (D 5) (R 5) [6,65,136,18,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,18,288] 13 (by decide) (choices 1) [1,4,8] r6330 c6330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2763
  · exact u2764
  · exact u2765

def b6331 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 28 19 296 360 424 296), lower := (rows 7 67 140 28 19 32 64 128 256), losses := [] }

theorem u6331 : Upper (D 5) (R 5) [6,65,136,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6331
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6332 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 140 28 25 290 354 418 290), lower := (rows 7 67 140 28 25 32 64 128 256), losses := [] }

theorem u6332 : Upper (D 5) (R 5) [6,65,136,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6332
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6333 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 140 28 26 289 353 417 289), lower := (rows 7 67 140 28 26 32 64 128 256), losses := [] }

theorem u6333 : Upper (D 5) (R 5) [6,65,136,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6333
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6334 : Route 9 := (fun mask => (mask,id))

def c6334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6334 : Upper (D 5) (R 5) [6,65,136,20,33] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,33] 13 (by decide) (choices 1) [2,8,256] r6334 c6334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2766
  · exact u2767
  · exact u2768

def r6335 : Route 9 := (fun mask => (mask,id))

def c6335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6335 : Upper (D 5) (R 5) [6,65,136,20,34] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,34] 13 (by decide) (choices 1) [1,8,256] r6335 c6335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2769
  · exact u2770
  · exact u2771

def b6336 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 354, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 28 56 291 355 419 291), lower := (rows 7 67 140 28 56 32 64 128 256), losses := [] }

theorem u6336 : Upper (D 5) (R 5) [6,65,136,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6336
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6337 : Route 9 := (fun mask => (mask,id))

def c6337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6337 : Upper (D 5) (R 5) [6,65,136,20,257] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,257] 13 (by decide) (choices 1) [2,8] r6337 c6337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2772
  · exact u2773

def r6338 : Route 9 := (fun mask => (mask,id))

def c6338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6338 : Upper (D 5) (R 5) [6,65,136,20,258] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,258] 13 (by decide) (choices 1) [1,8] r6338 c6338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2774
  · exact u2775

def b6339 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 28 280 35 99 163 291), lower := (rows 7 67 140 28 280 32 64 128 256), losses := [] }

theorem u6339 : Upper (D 5) (R 5) [6,65,136,20,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6339
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6340 : Route 9 := (fun mask => (mask,id))

def c6340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6340 : Upper (D 5) (R 5) [6,65,136,20,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,288] 13 (by decide) (choices 1) [1,2,8] r6340 c6340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2776
  · exact u2777
  · exact u2778

def b6341 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 140 41 22 312 376 440 312), lower := (rows 7 67 140 41 22 32 64 128 256), losses := [] }

theorem u6341 : Upper (D 5) (R 5) [6,65,136,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6341
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6342 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 41 26 308 372 436 308), lower := (rows 7 67 140 41 26 32 64 128 256), losses := [] }

theorem u6342 : Upper (D 5) (R 5) [6,65,136,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6343 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 41 28 306 370 434 306), lower := (rows 7 67 140 41 28 32 64 128 256), losses := [] }

theorem u6343 : Upper (D 5) (R 5) [6,65,136,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6343
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6344 : Route 9 := (fun mask => (mask,id))

def c6344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6344 : Upper (D 5) (R 5) [6,65,136,33,34] 13 := by
  apply FastRouting.sound _ _ [6,65,136,33,34] 13 (by decide) (choices 1) [4,8,16,256] r6344 c6344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2779
  · exact u2780
  · exact u2781
  · exact u2782

def r6345 : Route 9 := (fun mask => (mask,id))

def c6345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6345 : Upper (D 5) (R 5) [6,65,136,33,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,33,36] 13 (by decide) (choices 1) [2,8,16,256] r6345 c6345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2783
  · exact u2784
  · exact u2785
  · exact u2786

def b6346 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 41 56 310 342 406 278), lower := (rows 7 67 140 41 56 32 64 128 256), losses := [] }

theorem u6346 : Upper (D 5) (R 5) [6,65,136,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6346
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6347 : Route 9 := (fun mask => (mask,id))

def c6347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6347 : Upper (D 5) (R 5) [6,65,136,33,258] 13 := by
  apply FastRouting.sound _ _ [6,65,136,33,258] 13 (by decide) (choices 1) [4,8,16] r6347 c6347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2787
  · exact u2788
  · exact u2789

def r6348 : Route 9 := (fun mask => (mask,id))

def c6348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6348 : Upper (D 5) (R 5) [6,65,136,33,260] 13 := by
  apply FastRouting.sound _ _ [6,65,136,33,260] 13 (by decide) (choices 1) [2,8,16] r6348 c6348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2790
  · exact u2791
  · exact u2792

def r6349 : Route 9 := (fun mask => (mask,id))

def c6349 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6349 : Upper (D 5) (R 5) [6,65,136,33,264] 13 := by
  apply FastRouting.sound _ _ [6,65,136,33,264] 13 (by decide) (choices 1) [2,4,16] r6349 c6349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2793
  · exact u2794
  · exact u2795

def r6350 : Route 9 := (fun mask => (mask,id))

def c6350 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6350 : Upper (D 5) (R 5) [6,65,136,33,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,33,288] 13 (by decide) (choices 1) [2,4,8,16] r6350 c6350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2796
  · exact u2797
  · exact u2798
  · exact u2799

def b6351 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 42 21 312 376 440 312), lower := (rows 7 67 140 42 21 32 64 128 256), losses := [] }

theorem u6351 : Upper (D 5) (R 5) [6,65,136,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6352 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 42 25 308 372 436 308), lower := (rows 7 67 140 42 25 32 64 128 256), losses := [] }

theorem u6352 : Upper (D 5) (R 5) [6,65,136,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6352
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6353 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 42 28 305 369 433 305), lower := (rows 7 67 140 42 28 32 64 128 256), losses := [] }

theorem u6353 : Upper (D 5) (R 5) [6,65,136,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6353
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6354 : Route 9 := (fun mask => (mask,id))

def c6354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6354 : Upper (D 5) (R 5) [6,65,136,34,33] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,33] 13 (by decide) (choices 1) [4,8,16,256] r6354 c6354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2800
  · exact u2801
  · exact u2802
  · exact u2803

def r6355 : Route 9 := (fun mask => (mask,id))

def c6355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6355 : Upper (D 5) (R 5) [6,65,136,34,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,36] 13 (by decide) (choices 1) [1,8,16,256] r6355 c6355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2804
  · exact u2805
  · exact u2806
  · exact u2807

def b6356 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 42 56 309 341 405 277), lower := (rows 7 67 140 42 56 32 64 128 256), losses := [] }

theorem u6356 : Upper (D 5) (R 5) [6,65,136,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6357 : Route 9 := (fun mask => (mask,id))

def c6357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6357 : Upper (D 5) (R 5) [6,65,136,34,257] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,257] 13 (by decide) (choices 1) [4,8,16] r6357 c6357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2808
  · exact u2809
  · exact u2810

def r6358 : Route 9 := (fun mask => (mask,id))

def c6358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6358 : Upper (D 5) (R 5) [6,65,136,34,260] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,260] 13 (by decide) (choices 1) [1,8,16] r6358 c6358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2811
  · exact u2812
  · exact u2813

def r6359 : Route 9 := (fun mask => (mask,id))

def c6359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6359 : Upper (D 5) (R 5) [6,65,136,34,264] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,264] 13 (by decide) (choices 1) [1,4,16] r6359 c6359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2814
  · exact u2815
  · exact u2816

#print axioms u6359
end Delivery.IrregularNine14.P05
