import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0046
import IrregularNine14P05C0047
import IrregularNine14P05C0048

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6360 : Route 9 := (fun mask => (mask,id))

def c6360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6360 : Upper (D 5) (R 5) [6,65,136,34,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,288] 13 (by decide) (choices 1) [1,4,8,16] r6360 c6360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2817
  · exact u2818
  · exact u2819
  · exact u2820

def b6361 : PairBound 9 := { available := 312, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 19 312 376 440 312), lower := (rows 7 67 140 44 19 32 64 128 256), losses := [] }

theorem u6361 : Upper (D 5) (R 5) [6,65,136,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6361
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6362 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 354, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 44 25 306 370 434 306), lower := (rows 7 67 140 44 25 32 64 128 256), losses := [] }

theorem u6362 : Upper (D 5) (R 5) [6,65,136,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6363 : Route 9 := (fun mask => (mask,id))

def c6363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6363 : Upper (D 5) (R 5) [6,65,136,36,10] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,10] 13 (by decide) (choices 1) [1,16,256] r6363 c6363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2821
  · exact u2822
  · exact u2823

def r6364 : Route 9 := (fun mask => (mask,id))

def c6364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6364 : Upper (D 5) (R 5) [6,65,136,36,33] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,33] 13 (by decide) (choices 1) [2,8,16,256] r6364 c6364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2824
  · exact u2825
  · exact u2826
  · exact u2827

def r6365 : Route 9 := (fun mask => (mask,id))

def c6365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6365 : Upper (D 5) (R 5) [6,65,136,36,34] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,34] 13 (by decide) (choices 1) [1,8,16,256] r6365 c6365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2828
  · exact u2829
  · exact u2830
  · exact u2831

def b6366 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 44 56 307 339 403 275), lower := (rows 7 67 140 44 56 32 64 128 256), losses := [] }

theorem u6366 : Upper (D 5) (R 5) [6,65,136,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6366
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6367 : Route 9 := (fun mask => (mask,id))

def c6367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6367 : Upper (D 5) (R 5) [6,65,136,36,257] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,257] 13 (by decide) (choices 1) [2,8,16] r6367 c6367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2832
  · exact u2833
  · exact u2834

def r6368 : Route 9 := (fun mask => (mask,id))

def c6368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6368 : Upper (D 5) (R 5) [6,65,136,36,258] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,258] 13 (by decide) (choices 1) [1,8,16] r6368 c6368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2835
  · exact u2836
  · exact u2837

def r6369 : Route 9 := (fun mask => (mask,id))

def c6369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6369 : Upper (D 5) (R 5) [6,65,136,36,264] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,264] 13 (by decide) (choices 1) [1,2,16] r6369 c6369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2838
  · exact u2839
  · exact u2840

def r6370 : Route 9 := (fun mask => (mask,id))

def c6370 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6370 : Upper (D 5) (R 5) [6,65,136,36,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,288] 13 (by decide) (choices 1) [1,2,8,16] r6370 c6370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2841
  · exact u2842
  · exact u2843
  · exact u2844

def b6371 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 56 19 300 364 428 300), lower := (rows 7 67 140 56 19 32 64 128 256), losses := [] }

theorem u6371 : Upper (D 5) (R 5) [6,65,136,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6372 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 56 21 298 362 426 298), lower := (rows 7 67 140 56 21 32 64 128 256), losses := [] }

theorem u6372 : Upper (D 5) (R 5) [6,65,136,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6373 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 140 56 22 297 361 425 297), lower := (rows 7 67 140 56 22 32 64 128 256), losses := [] }

theorem u6373 : Upper (D 5) (R 5) [6,65,136,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6373
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6374 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 355, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 56 25 294 358 422 294), lower := (rows 7 67 140 56 25 32 64 128 256), losses := [] }

theorem u6374 : Upper (D 5) (R 5) [6,65,136,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6374
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6375 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 355, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 56 26 293 357 421 293), lower := (rows 7 67 140 56 26 32 64 128 256), losses := [] }

theorem u6375 : Upper (D 5) (R 5) [6,65,136,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6375
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6376 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 56 28 291 355 419 291), lower := (rows 7 67 140 56 28 32 64 128 256), losses := [] }

theorem u6376 : Upper (D 5) (R 5) [6,65,136,48,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6377 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 140 56 49 302 334 398 270), lower := (rows 7 67 140 56 49 32 64 128 256), losses := [] }

theorem u6377 : Upper (D 5) (R 5) [6,65,136,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6378 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 140 56 50 301 333 397 269), lower := (rows 7 67 140 56 50 32 64 128 256), losses := [] }

theorem u6378 : Upper (D 5) (R 5) [6,65,136,48,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6379 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 140 56 52 299 331 395 267), lower := (rows 7 67 140 56 52 32 64 128 256), losses := [] }

theorem u6379 : Upper (D 5) (R 5) [6,65,136,48,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6379
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6380 : PairBound 9 := { available := 263, camps := [{ cop := 5, region := 24, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 140 56 56 295 327 391 263), lower := (rows 7 67 140 56 56 32 64 128 256), losses := [] }

theorem u6380 : Upper (D 5) (R 5) [6,65,136,48,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6380
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6381 : Route 9 := (fun mask => (mask,id))

def c6381 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6381 : Upper (D 5) (R 5) [6,65,136,48,257] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48,257] 13 (by decide) (choices 1) [2,4,8] r6381 c6381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2845
  · exact u2846
  · exact u2847

def r6382 : Route 9 := (fun mask => (mask,id))

def c6382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6382 : Upper (D 5) (R 5) [6,65,136,48,258] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48,258] 13 (by decide) (choices 1) [1,4,8] r6382 c6382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2848
  · exact u2849
  · exact u2850

def r6383 : Route 9 := (fun mask => (mask,id))

def c6383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6383 : Upper (D 5) (R 5) [6,65,136,48,260] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48,260] 13 (by decide) (choices 1) [1,2,8] r6383 c6383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2851
  · exact u2852
  · exact u2853

def b6384 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 56 280 39 103 167 295), lower := (rows 7 67 140 56 280 32 64 128 256), losses := [] }

theorem u6384 : Upper (D 5) (R 5) [6,65,136,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6384
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6385 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 199, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 140 56 304 47 79 143 271), lower := (rows 7 67 140 56 304 32 64 128 256), losses := [] }

theorem u6385 : Upper (D 5) (R 5) [6,65,136,48,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6386 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 140 265 22 56 120 184 312), lower := (rows 7 67 140 265 22 32 64 128 256), losses := [] }

theorem u6386 : Upper (D 5) (R 5) [6,65,136,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6387 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 265 26 52 116 180 308), lower := (rows 7 67 140 265 26 32 64 128 256), losses := [] }

theorem u6387 : Upper (D 5) (R 5) [6,65,136,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6388 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 265 28 50 114 178 306), lower := (rows 7 67 140 265 28 32 64 128 256), losses := [] }

theorem u6388 : Upper (D 5) (R 5) [6,65,136,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6388
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6389 : Route 9 := (fun mask => (mask,id))

def c6389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6389 : Upper (D 5) (R 5) [6,65,136,257,34] 13 := by
  apply FastRouting.sound _ _ [6,65,136,257,34] 13 (by decide) (choices 1) [4,8,16] r6389 c6389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2854
  · exact u2855
  · exact u2856

def r6390 : Route 9 := (fun mask => (mask,id))

def c6390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6390 : Upper (D 5) (R 5) [6,65,136,257,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,257,36] 13 (by decide) (choices 1) [2,8,16] r6390 c6390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2857
  · exact u2858
  · exact u2859

def r6391 : Route 9 := (fun mask => (mask,id))

def c6391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6391 : Upper (D 5) (R 5) [6,65,136,257,40] 13 := by
  apply FastRouting.sound _ _ [6,65,136,257,40] 13 (by decide) (choices 1) [2,4,16] r6391 c6391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2860
  · exact u2861
  · exact u2862

def b6392 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 266 21 56 120 184 312), lower := (rows 7 67 140 266 21 32 64 128 256), losses := [] }

theorem u6392 : Upper (D 5) (R 5) [6,65,136,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6393 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 266 25 52 116 180 308), lower := (rows 7 67 140 266 25 32 64 128 256), losses := [] }

theorem u6393 : Upper (D 5) (R 5) [6,65,136,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6394 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 266 28 49 113 177 305), lower := (rows 7 67 140 266 28 32 64 128 256), losses := [] }

theorem u6394 : Upper (D 5) (R 5) [6,65,136,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6395 : Route 9 := (fun mask => (mask,id))

def c6395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6395 : Upper (D 5) (R 5) [6,65,136,258,33] 13 := by
  apply FastRouting.sound _ _ [6,65,136,258,33] 13 (by decide) (choices 1) [4,8,16] r6395 c6395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2863
  · exact u2864
  · exact u2865

def r6396 : Route 9 := (fun mask => (mask,id))

def c6396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6396 : Upper (D 5) (R 5) [6,65,136,258,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,258,36] 13 (by decide) (choices 1) [1,8,16] r6396 c6396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2866
  · exact u2867
  · exact u2868

def r6397 : Route 9 := (fun mask => (mask,id))

def c6397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6397 : Upper (D 5) (R 5) [6,65,136,258,40] 13 := by
  apply FastRouting.sound _ _ [6,65,136,258,40] 13 (by decide) (choices 1) [1,4,16] r6397 c6397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2869
  · exact u2870
  · exact u2871

def b6398 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 268 19 56 120 184 312), lower := (rows 7 67 140 268 19 32 64 128 256), losses := [] }

theorem u6398 : Upper (D 5) (R 5) [6,65,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6399 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 268 25 50 114 178 306), lower := (rows 7 67 140 268 25 32 64 128 256), losses := [] }

theorem u6399 : Upper (D 5) (R 5) [6,65,136,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6399
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6400 : Route 9 := (fun mask => (mask,id))

def c6400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6400 : Upper (D 5) (R 5) [6,65,136,260,10] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,10] 13 (by decide) (choices 1) [1,16] r6400 c6400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2872
  · exact u2873

def r6401 : Route 9 := (fun mask => (mask,id))

def c6401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6401 : Upper (D 5) (R 5) [6,65,136,260,33] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,33] 13 (by decide) (choices 1) [2,8,16] r6401 c6401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2874
  · exact u2875
  · exact u2876

def r6402 : Route 9 := (fun mask => (mask,id))

def c6402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6402 : Upper (D 5) (R 5) [6,65,136,260,34] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,34] 13 (by decide) (choices 1) [1,8,16] r6402 c6402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2877
  · exact u2878
  · exact u2879

def r6403 : Route 9 := (fun mask => (mask,id))

def c6403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6403 : Upper (D 5) (R 5) [6,65,136,260,40] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,40] 13 (by decide) (choices 1) [1,2,16] r6403 c6403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2880
  · exact u2881
  · exact u2882

def b6404 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 280 19 44 108 172 300), lower := (rows 7 67 140 280 19 32 64 128 256), losses := [] }

theorem u6404 : Upper (D 5) (R 5) [6,65,136,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6404
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6405 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 280 21 42 106 170 298), lower := (rows 7 67 140 280 21 32 64 128 256), losses := [] }

theorem u6405 : Upper (D 5) (R 5) [6,65,136,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6406 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 140 280 22 41 105 169 297), lower := (rows 7 67 140 280 22 32 64 128 256), losses := [] }

theorem u6406 : Upper (D 5) (R 5) [6,65,136,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6406
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6407 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 280 25 38 102 166 294), lower := (rows 7 67 140 280 25 32 64 128 256), losses := [] }

theorem u6407 : Upper (D 5) (R 5) [6,65,136,272,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6408 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 280 26 37 101 165 293), lower := (rows 7 67 140 280 26 32 64 128 256), losses := [] }

theorem u6408 : Upper (D 5) (R 5) [6,65,136,272,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6409 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 280 28 35 99 163 291), lower := (rows 7 67 140 280 28 32 64 128 256), losses := [] }

theorem u6409 : Upper (D 5) (R 5) [6,65,136,272,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6409
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6410 : Route 9 := (fun mask => (mask,id))

def c6410 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6410 : Upper (D 5) (R 5) [6,65,136,272,33] 13 := by
  apply FastRouting.sound _ _ [6,65,136,272,33] 13 (by decide) (choices 1) [2,4,8] r6410 c6410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2883
  · exact u2884
  · exact u2885

def r6411 : Route 9 := (fun mask => (mask,id))

def c6411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6411 : Upper (D 5) (R 5) [6,65,136,272,34] 13 := by
  apply FastRouting.sound _ _ [6,65,136,272,34] 13 (by decide) (choices 1) [1,4,8] r6411 c6411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2886
  · exact u2887
  · exact u2888

def r6412 : Route 9 := (fun mask => (mask,id))

def c6412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6412 : Upper (D 5) (R 5) [6,65,136,272,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,272,36] 13 (by decide) (choices 1) [1,2,8] r6412 c6412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2889
  · exact u2890
  · exact u2891

def b6413 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 280 56 39 103 167 295), lower := (rows 7 67 140 280 56 32 64 128 256), losses := [] }

theorem u6413 : Upper (D 5) (R 5) [6,65,136,272,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6413
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6414 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 296 19 60 124 188 316), lower := (rows 7 67 140 296 19 32 64 128 256), losses := [] }

theorem u6414 : Upper (D 5) (R 5) [6,65,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6415 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 296 21 58 122 186 314), lower := (rows 7 67 140 296 21 32 64 128 256), losses := [] }

theorem u6415 : Upper (D 5) (R 5) [6,65,136,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6416 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 140 296 22 57 121 185 313), lower := (rows 7 67 140 296 22 32 64 128 256), losses := [] }

theorem u6416 : Upper (D 5) (R 5) [6,65,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6416
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6417 : Route 9 := (fun mask => (mask,id))

def c6417 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6417 : Upper (D 5) (R 5) [6,65,136,288,9] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,9] 13 (by decide) (choices 1) [2,4,16] r6417 c6417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2892
  · exact u2893
  · exact u2894

def r6418 : Route 9 := (fun mask => (mask,id))

def c6418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6418 : Upper (D 5) (R 5) [6,65,136,288,10] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,10] 13 (by decide) (choices 1) [1,4,16] r6418 c6418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2895
  · exact u2896
  · exact u2897

def b6419 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 296 28 51 115 179 307), lower := (rows 7 67 140 296 28 32 64 128 256), losses := [] }

theorem u6419 : Upper (D 5) (R 5) [6,65,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6419
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6419
end Delivery.IrregularNine14.P05
