import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0040
import IrregularNine14P05C0041

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5940 : Route 9 := (fun mask => (mask,id))

def c5940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5940 : Upper (D 5) (R 5) [6,40,65,130,36] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,36] 13 (by decide) (choices 1) [1,8,16,256] r5940 c5940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2443
  · exact u2444
  · exact u2445
  · exact u2446

def b5941 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 138 56 309 341 405 277), lower := (rows 7 42 69 138 56 32 64 128 256), losses := [] }

theorem u5941 : Upper (D 5) (R 5) [6,40,65,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5941
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5942 : Route 9 := (fun mask => (mask,id))

def c5942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5942 : Upper (D 5) (R 5) [6,40,65,130,257] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,257] 13 (by decide) (choices 1) [4,8,16] r5942 c5942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2447
  · exact u2448
  · exact u2449

def r5943 : Route 9 := (fun mask => (mask,id))

def c5943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5943 : Upper (D 5) (R 5) [6,40,65,130,260] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,260] 13 (by decide) (choices 1) [1,8,16] r5943 c5943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2450
  · exact u2451
  · exact u2452

def r5944 : Route 9 := (fun mask => (mask,id))

def c5944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5944 : Upper (D 5) (R 5) [6,40,65,130,264] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,264] 13 (by decide) (choices 1) [1,4,16] r5944 c5944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2453
  · exact u2454
  · exact u2455

def r5945 : Route 9 := (fun mask => (mask,id))

def c5945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5945 : Upper (D 5) (R 5) [6,40,65,130,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,288] 13 (by decide) (choices 1) [1,4,8,16] r5945 c5945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2456
  · exact u2457
  · exact u2458
  · exact u2459

def b5946 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 69 140 19 312 376 440 312), lower := (rows 7 42 69 140 19 32 64 128 256), losses := [] }

theorem u5946 : Upper (D 5) (R 5) [6,40,65,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5947 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 140 25 306 370 434 306), lower := (rows 7 42 69 140 25 32 64 128 256), losses := [] }

theorem u5947 : Upper (D 5) (R 5) [6,40,65,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5947
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5948 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 140 26 305 369 433 305), lower := (rows 7 42 69 140 26 32 64 128 256), losses := [] }

theorem u5948 : Upper (D 5) (R 5) [6,40,65,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5948
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5949 : Route 9 := (fun mask => (mask,id))

def c5949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5949 : Upper (D 5) (R 5) [6,40,65,132,33] 13 := by
  apply FastRouting.sound _ _ [6,40,65,132,33] 13 (by decide) (choices 1) [2,8,16,256] r5949 c5949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2460
  · exact u2461
  · exact u2462
  · exact u2463

def b5950 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 140 50 313 345 409 281), lower := (rows 7 42 69 140 50 32 64 128 256), losses := [] }

theorem u5950 : Upper (D 5) (R 5) [6,40,65,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5950
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5951 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 140 56 307 339 403 275), lower := (rows 7 42 69 140 56 32 64 128 256), losses := [] }

theorem u5951 : Upper (D 5) (R 5) [6,40,65,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5951
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5952 : Route 9 := (fun mask => (mask,id))

def c5952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5952 : Upper (D 5) (R 5) [6,40,65,132,257] 13 := by
  apply FastRouting.sound _ _ [6,40,65,132,257] 13 (by decide) (choices 1) [2,8,16] r5952 c5952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2464
  · exact u2465
  · exact u2466

def r5953 : Route 9 := (fun mask => (mask,id))

def c5953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5953 : Upper (D 5) (R 5) [6,40,65,132,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,132,258] 13 (by decide) (choices 1) [1,8,16] r5953 c5953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2467
  · exact u2468
  · exact u2469

def r5954 : Route 9 := (fun mask => (mask,id))

def c5954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5954 : Upper (D 5) (R 5) [6,40,65,132,264] 13 := by
  apply FastRouting.sound _ _ [6,40,65,132,264] 13 (by decide) (choices 1) [1,2,16] r5954 c5954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2470
  · exact u2471
  · exact u2472

def r5955 : Route 9 := (fun mask => (mask,id))

def c5955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5955 : Upper (D 5) (R 5) [6,40,65,132,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,132,288] 13 (by decide) (choices 1) [1,2,8,16] r5955 c5955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2473
  · exact u2474
  · exact u2475
  · exact u2476

def b5956 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 69 152 19 300 364 428 300), lower := (rows 7 42 69 152 19 32 64 128 256), losses := [] }

theorem u5956 : Upper (D 5) (R 5) [6,40,65,144,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5956
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5957 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 152 21 298 362 426 298), lower := (rows 7 42 69 152 21 32 64 128 256), losses := [] }

theorem u5957 : Upper (D 5) (R 5) [6,40,65,144,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5957
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5958 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 42 69 152 22 297 361 425 297), lower := (rows 7 42 69 152 22 32 64 128 256), losses := [] }

theorem u5958 : Upper (D 5) (R 5) [6,40,65,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5958
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5959 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 325, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 152 25 294 358 422 294), lower := (rows 7 42 69 152 25 32 64 128 256), losses := [] }

theorem u5959 : Upper (D 5) (R 5) [6,40,65,144,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5959
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5960 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 152 26 293 357 421 293), lower := (rows 7 42 69 152 26 32 64 128 256), losses := [] }

theorem u5960 : Upper (D 5) (R 5) [6,40,65,144,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5960
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5961 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 325, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 152 28 291 355 419 291), lower := (rows 7 42 69 152 28 32 64 128 256), losses := [] }

theorem u5961 : Upper (D 5) (R 5) [6,40,65,144,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5961
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5962 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 152 49 302 334 398 270), lower := (rows 7 42 69 152 49 32 64 128 256), losses := [] }

theorem u5962 : Upper (D 5) (R 5) [6,40,65,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5962
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5963 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 152 50 301 333 397 269), lower := (rows 7 42 69 152 50 32 64 128 256), losses := [] }

theorem u5963 : Upper (D 5) (R 5) [6,40,65,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5963
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5964 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 152 52 299 331 395 267), lower := (rows 7 42 69 152 52 32 64 128 256), losses := [] }

theorem u5964 : Upper (D 5) (R 5) [6,40,65,144,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5965 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 152 56 295 327 391 263), lower := (rows 7 42 69 152 56 32 64 128 256), losses := [] }

theorem u5965 : Upper (D 5) (R 5) [6,40,65,144,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5965
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5966 : Route 9 := (fun mask => (mask,id))

def c5966 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5966 : Upper (D 5) (R 5) [6,40,65,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,257] 13 (by decide) (choices 1) [2,4,8] r5966 c5966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2477
  · exact u2478
  · exact u2479

def r5967 : Route 9 := (fun mask => (mask,id))

def c5967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5967 : Upper (D 5) (R 5) [6,40,65,144,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,258] 13 (by decide) (choices 1) [1,4,8] r5967 c5967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2480
  · exact u2481
  · exact u2482

def r5968 : Route 9 := (fun mask => (mask,id))

def c5968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5968 : Upper (D 5) (R 5) [6,40,65,144,260] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,260] 13 (by decide) (choices 1) [1,2,8] r5968 c5968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2483
  · exact u2484
  · exact u2485

def b5969 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 152 280 39 103 167 295), lower := (rows 7 42 69 152 280 32 64 128 256), losses := [] }

theorem u5969 : Upper (D 5) (R 5) [6,40,65,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5969
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5970 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 152 304 47 79 143 271), lower := (rows 7 42 69 152 304 32 64 128 256), losses := [] }

theorem u5970 : Upper (D 5) (R 5) [6,40,65,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5970
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5971 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 69 392 19 60 124 188 316), lower := (rows 7 42 69 392 19 32 64 128 256), losses := [] }

theorem u5971 : Upper (D 5) (R 5) [6,40,65,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5971
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5972 : PairBound 9 := { available := 58, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 392 21 58 122 186 314), lower := (rows 7 42 69 392 21 32 64 128 256), losses := [] }

theorem u5972 : Upper (D 5) (R 5) [6,40,65,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5973 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 42 69 392 22 57 121 185 313), lower := (rows 7 42 69 392 22 32 64 128 256), losses := [] }

theorem u5973 : Upper (D 5) (R 5) [6,40,65,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5973
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5974 : Route 9 := (fun mask => (mask,id))

def c5974 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5974 : Upper (D 5) (R 5) [6,40,65,384,9] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,9] 13 (by decide) (choices 1) [2,4,16] r5974 c5974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2486
  · exact u2487
  · exact u2488

def b5975 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 392 26 53 117 181 309), lower := (rows 7 42 69 392 26 32 64 128 256), losses := [] }

theorem u5975 : Upper (D 5) (R 5) [6,40,65,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5975
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5976 : Route 9 := (fun mask => (mask,id))

def c5976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5976 : Upper (D 5) (R 5) [6,40,65,384,12] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,12] 13 (by decide) (choices 1) [1,2,16] r5976 c5976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2489
  · exact u2490
  · exact u2491

def r5977 : Route 9 := (fun mask => (mask,id))

def c5977 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5977 : Upper (D 5) (R 5) [6,40,65,384,33] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,33] 13 (by decide) (choices 1) [2,4,8,16] r5977 c5977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2492
  · exact u2493
  · exact u2494
  · exact u2495

def b5978 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 392 50 61 93 157 285), lower := (rows 7 42 69 392 50 32 64 128 256), losses := [] }

theorem u5978 : Upper (D 5) (R 5) [6,40,65,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5978
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5979 : Route 9 := (fun mask => (mask,id))

def c5979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5979 : Upper (D 5) (R 5) [6,40,65,384,36] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,36] 13 (by decide) (choices 1) [1,2,8,16] r5979 c5979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2496
  · exact u2497
  · exact u2498
  · exact u2499

def b5980 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 392 56 55 87 151 279), lower := (rows 7 42 69 392 56 32 64 128 256), losses := [] }

theorem u5980 : Upper (D 5) (R 5) [6,40,65,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5980
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5981 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 76 25 19 420 484 420 420), lower := (rows 7 42 76 25 19 32 64 128 256), losses := [] }

theorem u5981 : Upper (D 5) (R 5) [6,40,72,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5981
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5982 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 42 76 25 21 418 482 418 418), lower := (rows 7 42 76 25 21 32 64 128 256), losses := [] }

theorem u5982 : Upper (D 5) (R 5) [6,40,72,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5982
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5983 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 76 25 22 417 481 417 417), lower := (rows 7 42 76 25 22 32 64 128 256), losses := [] }

theorem u5983 : Upper (D 5) (R 5) [6,40,72,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5983
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5984 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 25 49 422 454 390 390), lower := (rows 7 42 76 25 49 32 64 128 256), losses := [] }

theorem u5984 : Upper (D 5) (R 5) [6,40,72,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5984
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5985 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 76 25 50 421 453 389 389), lower := (rows 7 42 76 25 50 32 64 128 256), losses := [] }

theorem u5985 : Upper (D 5) (R 5) [6,40,72,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5985
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5986 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 25 52 419 451 387 387), lower := (rows 7 42 76 25 52 32 64 128 256), losses := [] }

theorem u5986 : Upper (D 5) (R 5) [6,40,72,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5986
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5987 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 42 76 25 145 294 358 422 294), lower := (rows 7 42 76 25 145 32 64 128 256), losses := [] }

theorem u5987 : Upper (D 5) (R 5) [6,40,72,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5987
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5988 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 432, targets := 8 },{ cop := 3, region := 356, targets := 2 }], pairs := [(2,1),(4,3)], upper := (rows 7 42 76 25 146 293 357 421 293), lower := (rows 7 42 76 25 146 32 64 128 256), losses := [] }

theorem u5988 : Upper (D 5) (R 5) [6,40,72,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5988
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5989 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 432, targets := 8 },{ cop := 3, region := 290, targets := 4 }], pairs := [(1,2),(4,3)], upper := (rows 7 42 76 25 148 291 355 419 291), lower := (rows 7 42 76 25 148 32 64 128 256), losses := [] }

theorem u5989 : Upper (D 5) (R 5) [6,40,72,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5990 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 25 176 295 327 391 263), lower := (rows 7 42 76 25 176 32 64 128 256), losses := [] }

theorem u5990 : Upper (D 5) (R 5) [6,40,72,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5990
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5991 : Route 9 := (fun mask => (mask,id))

def c5991 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5991 : Upper (D 5) (R 5) [6,40,72,17,384] 13 := by
  apply FastRouting.sound _ _ [6,40,72,17,384] 13 (by decide) (choices 1) [1,2,4] r5991 c5991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2500
  · exact u2501
  · exact u2502

def b5992 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 42 76 137 19 308 372 436 308), lower := (rows 7 42 76 137 19 32 64 128 256), losses := [] }

theorem u5992 : Upper (D 5) (R 5) [6,40,72,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5992
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5993 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 16, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 42 76 137 21 306 370 434 306), lower := (rows 7 42 76 137 21 32 64 128 256), losses := [] }

theorem u5993 : Upper (D 5) (R 5) [6,40,72,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5993
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5994 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 42 76 137 22 305 369 433 305), lower := (rows 7 42 76 137 22 32 64 128 256), losses := [] }

theorem u5994 : Upper (D 5) (R 5) [6,40,72,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5994
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5995 : Route 9 := (fun mask => (mask,id))

def c5995 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5995 : Upper (D 5) (R 5) [6,40,72,129,33] 13 := by
  apply FastRouting.sound _ _ [6,40,72,129,33] 13 (by decide) (choices 1) [2,4,16,256] r5995 c5995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2503
  · exact u2504
  · exact u2505
  · exact u2506

def b5996 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 76 137 50 309 341 405 277), lower := (rows 7 42 76 137 50 32 64 128 256), losses := [] }

theorem u5996 : Upper (D 5) (R 5) [6,40,72,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5996
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5997 : Route 9 := (fun mask => (mask,id))

def c5997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5997 : Upper (D 5) (R 5) [6,40,72,129,36] 13 := by
  apply FastRouting.sound _ _ [6,40,72,129,36] 13 (by decide) (choices 1) [1,2,16,256] r5997 c5997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2507
  · exact u2508
  · exact u2509
  · exact u2510

def r5998 : Route 9 := (fun mask => (mask,id))

def c5998 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5998 : Upper (D 5) (R 5) [6,40,72,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,72,129,257] 13 (by decide) (choices 1) [2,4,16] r5998 c5998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2511
  · exact u2512
  · exact u2513

def r5999 : Route 9 := (fun mask => (mask,id))

def c5999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5999 : Upper (D 5) (R 5) [6,40,72,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,72,129,258] 13 (by decide) (choices 1) [1,4,16] r5999 c5999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2514
  · exact u2515
  · exact u2516

#print axioms u5999
end Delivery.IrregularNine14.P05
