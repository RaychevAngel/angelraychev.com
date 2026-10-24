import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0041
import IrregularNine14P05C0042

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6000 : Route 9 := (fun mask => (mask,id))

def c6000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6000 : Upper (D 5) (R 5) [6,40,72,129,260] 13 := by
  apply FastRouting.sound _ _ [6,40,72,129,260] 13 (by decide) (choices 1) [1,2,16] r6000 c6000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2517
  · exact u2518
  · exact u2519

def r6001 : Route 9 := (fun mask => (mask,id))

def c6001 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6001 : Upper (D 5) (R 5) [6,40,72,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,72,129,288] 13 (by decide) (choices 1) [1,2,4,16] r6001 c6001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2520
  · exact u2521
  · exact u2522
  · exact u2523

def b6002 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 42 76 152 19 293 357 421 293), lower := (rows 7 42 76 152 19 32 64 128 256), losses := [] }

theorem u6002 : Upper (D 5) (R 5) [6,40,72,144,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6002
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6003 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 16, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 42 76 152 21 291 355 419 291), lower := (rows 7 42 76 152 21 32 64 128 256), losses := [] }

theorem u6003 : Upper (D 5) (R 5) [6,40,72,144,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6003
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6004 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 42 76 152 22 289 353 417 289), lower := (rows 7 42 76 152 22 32 64 128 256), losses := [] }

theorem u6004 : Upper (D 5) (R 5) [6,40,72,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6004
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6005 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 152 49 295 327 391 263), lower := (rows 7 42 76 152 49 32 64 128 256), losses := [] }

theorem u6005 : Upper (D 5) (R 5) [6,40,72,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6005
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6006 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 76 152 50 293 325 389 261), lower := (rows 7 42 76 152 50 32 64 128 256), losses := [] }

theorem u6006 : Upper (D 5) (R 5) [6,40,72,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6006
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6007 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 152 52 291 323 387 259), lower := (rows 7 42 76 152 52 32 64 128 256), losses := [] }

theorem u6007 : Upper (D 5) (R 5) [6,40,72,144,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6007
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6008 : Route 9 := (fun mask => (mask,id))

def c6008 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6008 : Upper (D 5) (R 5) [6,40,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,72,144,257] 13 (by decide) (choices 1) [1,2,4] r6008 c6008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2524
  · exact u2525
  · exact u2526

def r6009 : Route 9 := (fun mask => (mask,id))

def c6009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6009 : Upper (D 5) (R 5) [6,40,72,144,258] 13 := by
  apply FastRouting.sound _ _ [6,40,72,144,258] 13 (by decide) (choices 1) [1,4] r6009 c6009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2527
  · exact u2528

def r6010 : Route 9 := (fun mask => (mask,id))

def c6010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6010 : Upper (D 5) (R 5) [6,40,72,144,260] 13 := by
  apply FastRouting.sound _ _ [6,40,72,144,260] 13 (by decide) (choices 1) [1,2] r6010 c6010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2529
  · exact u2530

def b6011 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 152 304 39 71 135 263), lower := (rows 7 42 76 152 304 32 64 128 256), losses := [] }

theorem u6011 : Upper (D 5) (R 5) [6,40,72,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6012 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 42 76 392 19 53 117 181 309), lower := (rows 7 42 76 392 19 32 64 128 256), losses := [] }

theorem u6012 : Upper (D 5) (R 5) [6,40,72,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6012
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6013 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 16, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 42 76 392 21 51 115 179 307), lower := (rows 7 42 76 392 21 32 64 128 256), losses := [] }

theorem u6013 : Upper (D 5) (R 5) [6,40,72,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6013
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6014 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 42 76 392 22 49 113 177 305), lower := (rows 7 42 76 392 22 32 64 128 256), losses := [] }

theorem u6014 : Upper (D 5) (R 5) [6,40,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6014
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6015 : Route 9 := (fun mask => (mask,id))

def c6015 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6015 : Upper (D 5) (R 5) [6,40,72,384,33] 13 := by
  apply FastRouting.sound _ _ [6,40,72,384,33] 13 (by decide) (choices 1) [1,2,4,16] r6015 c6015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2531
  · exact u2532
  · exact u2533
  · exact u2534

def b6016 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 76 392 50 53 85 149 277), lower := (rows 7 42 76 392 50 32 64 128 256), losses := [] }

theorem u6016 : Upper (D 5) (R 5) [6,40,72,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6016
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6017 : Route 9 := (fun mask => (mask,id))

def c6017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6017 : Upper (D 5) (R 5) [6,40,72,384,36] 13 := by
  apply FastRouting.sound _ _ [6,40,72,384,36] 13 (by decide) (choices 1) [1,2,16] r6017 c6017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2535
  · exact u2536
  · exact u2537

def b6018 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 84 137 19 300 364 428 300), lower := (rows 7 42 84 137 19 32 64 128 256), losses := [] }

theorem u6018 : Upper (D 5) (R 5) [6,40,80,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6018
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6019 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 84 137 21 298 362 426 298), lower := (rows 7 42 84 137 21 32 64 128 256), losses := [] }

theorem u6019 : Upper (D 5) (R 5) [6,40,80,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6019
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6020 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 137 22 297 361 425 297), lower := (rows 7 42 84 137 22 32 64 128 256), losses := [] }

theorem u6020 : Upper (D 5) (R 5) [6,40,80,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6020
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6021 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 42 84 137 25 294 358 422 294), lower := (rows 7 42 84 137 25 32 64 128 256), losses := [] }

theorem u6021 : Upper (D 5) (R 5) [6,40,80,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6021
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6022 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 137 26 293 357 421 293), lower := (rows 7 42 84 137 26 32 64 128 256), losses := [] }

theorem u6022 : Upper (D 5) (R 5) [6,40,80,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6022
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6023 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 137 28 291 355 419 291), lower := (rows 7 42 84 137 28 32 64 128 256), losses := [] }

theorem u6023 : Upper (D 5) (R 5) [6,40,80,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6023
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6024 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 7 42 84 137 49 302 334 398 270), lower := (rows 7 42 84 137 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 25 16 0 65 129 257), good := (rows 463 10 92 457 477 0 64 128 256) }] }

theorem u6024 : Upper (D 5) (R 5) [6,40,80,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6024
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6025 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 137 50 301 333 397 269), lower := (rows 7 42 84 137 50 32 64 128 256), losses := [] }

theorem u6025 : Upper (D 5) (R 5) [6,40,80,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6025
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6026 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 137 52 299 331 395 267), lower := (rows 7 42 84 137 52 32 64 128 256), losses := [] }

theorem u6026 : Upper (D 5) (R 5) [6,40,80,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6026
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6027 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 137 56 295 327 391 263), lower := (rows 7 42 84 137 56 32 64 128 256), losses := [] }

theorem u6027 : Upper (D 5) (R 5) [6,40,80,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6027
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6028 : Route 9 := (fun mask => (mask,id))

def c6028 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6028 : Upper (D 5) (R 5) [6,40,80,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257] 13 (by decide) (choices 1) [2,4,8] r6028 c6028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2538
  · exact u2539
  · exact u2540

def r6029 : Route 9 := (fun mask => (mask,id))

def c6029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6029 : Upper (D 5) (R 5) [6,40,80,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,258] 13 (by decide) (choices 1) [1,4,8] r6029 c6029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2541
  · exact u2542
  · exact u2543

def b6030 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 137 276 43 107 171 299), lower := (rows 7 42 84 137 276 32 64 128 256), losses := [] }

theorem u6030 : Upper (D 5) (R 5) [6,40,80,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6030
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6031 : Route 9 := (fun mask => (mask,id))

def c6031 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6031 : Upper (D 5) (R 5) [6,40,80,129,264] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,264] 13 (by decide) (choices 1) [1,2,4] r6031 c6031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2544
  · exact u2545
  · exact u2546

def r6032 : Route 9 := (fun mask => (mask,id))

def c6032 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6032 : Upper (D 5) (R 5) [6,40,80,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288] 13 (by decide) (choices 1) [1,2,4,8] r6032 c6032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2547
  · exact u2548
  · exact u2549
  · exact u2550

def b6033 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 84 138 21 297 361 425 297), lower := (rows 7 42 84 138 21 32 64 128 256), losses := [] }

theorem u6033 : Upper (D 5) (R 5) [6,40,80,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6033
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6034 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 356, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 42 84 138 25 293 357 421 293), lower := (rows 7 42 84 138 25 32 64 128 256), losses := [] }

theorem u6034 : Upper (D 5) (R 5) [6,40,80,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6034
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6035 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 138 28 289 353 417 289), lower := (rows 7 42 84 138 28 32 64 128 256), losses := [] }

theorem u6035 : Upper (D 5) (R 5) [6,40,80,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6035
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6036 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 7 42 84 138 49 301 333 397 269), lower := (rows 7 42 84 138 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 9 16 0 81 145 273), good := (rows 463 10 468 138 477 0 64 128 256) }] }

theorem u6036 : Upper (D 5) (R 5) [6,40,80,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6036
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6037 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 138 52 297 329 393 265), lower := (rows 7 42 84 138 52 32 64 128 256), losses := [] }

theorem u6037 : Upper (D 5) (R 5) [6,40,80,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6037
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6038 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 138 56 293 325 389 261), lower := (rows 7 42 84 138 56 32 64 128 256), losses := [] }

theorem u6038 : Upper (D 5) (R 5) [6,40,80,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6038
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6039 : Route 9 := (fun mask => (mask,id))

def c6039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6039 : Upper (D 5) (R 5) [6,40,80,130,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,257] 13 (by decide) (choices 1) [1,4,8] r6039 c6039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2551
  · exact u2552
  · exact u2553

def b6040 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 138 276 41 105 169 297), lower := (rows 7 42 84 138 276 32 64 128 256), losses := [] }

theorem u6040 : Upper (D 5) (R 5) [6,40,80,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6040
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6041 : Route 9 := (fun mask => (mask,id))

def c6041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6041 : Upper (D 5) (R 5) [6,40,80,130,264] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,264] 13 (by decide) (choices 1) [1,4] r6041 c6041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2554
  · exact u2555

def r6042 : Route 9 := (fun mask => (mask,id))

def c6042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6042 : Upper (D 5) (R 5) [6,40,80,130,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,288] 13 (by decide) (choices 1) [1,4,8] r6042 c6042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2556
  · exact u2557
  · exact u2558

def b6043 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 84 140 19 297 361 425 297), lower := (rows 7 42 84 140 19 32 64 128 256), losses := [] }

theorem u6043 : Upper (D 5) (R 5) [6,40,80,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6043
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6044 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 290, targets := 4 }], pairs := [(1,2),(2,3)], upper := (rows 7 42 84 140 25 291 355 419 291), lower := (rows 7 42 84 140 25 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 20 0 16 33 65 129 257), good := (rows 487 34 84 132 501 32 64 128 256) }] }

theorem u6044 : Upper (D 5) (R 5) [6,40,80,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6044
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6045 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 140 26 289 353 417 289), lower := (rows 7 42 84 140 26 32 64 128 256), losses := [] }

theorem u6045 : Upper (D 5) (R 5) [6,40,80,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6045
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6046 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 7 42 84 140 49 299 331 395 267), lower := (rows 7 42 84 140 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 25 16 0 65 129 257), good := (rows 463 10 92 140 477 0 64 128 256) }] }

theorem u6046 : Upper (D 5) (R 5) [6,40,80,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6046
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6047 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 140 50 297 329 393 265), lower := (rows 7 42 84 140 50 32 64 128 256), losses := [] }

theorem u6047 : Upper (D 5) (R 5) [6,40,80,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6047
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6048 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 140 56 291 323 387 259), lower := (rows 7 42 84 140 56 32 64 128 256), losses := [] }

theorem u6048 : Upper (D 5) (R 5) [6,40,80,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6048
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6049 : Route 9 := (fun mask => (mask,id))

def c6049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6049 : Upper (D 5) (R 5) [6,40,80,132,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,257] 13 (by decide) (choices 1) [1,2,8] r6049 c6049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2559
  · exact u2560
  · exact u2561

def r6050 : Route 9 := (fun mask => (mask,id))

def c6050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6050 : Upper (D 5) (R 5) [6,40,80,132,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,258] 13 (by decide) (choices 1) [1,8] r6050 c6050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2562
  · exact u2563

def r6051 : Route 9 := (fun mask => (mask,id))

def c6051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6051 : Upper (D 5) (R 5) [6,40,80,132,264] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,264] 13 (by decide) (choices 1) [1,2] r6051 c6051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2564
  · exact u2565

def r6052 : Route 9 := (fun mask => (mask,id))

def c6052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6052 : Upper (D 5) (R 5) [6,40,80,132,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,288] 13 (by decide) (choices 1) [1,2,8] r6052 c6052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2566
  · exact u2567
  · exact u2568

def b6053 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 84 392 19 45 109 173 301), lower := (rows 7 42 84 392 19 32 64 128 256), losses := [] }

theorem u6053 : Upper (D 5) (R 5) [6,40,80,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6053
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6054 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 84 392 21 43 107 171 299), lower := (rows 7 42 84 392 21 32 64 128 256), losses := [] }

theorem u6054 : Upper (D 5) (R 5) [6,40,80,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6054
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6055 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 392 22 41 105 169 297), lower := (rows 7 42 84 392 22 32 64 128 256), losses := [] }

theorem u6055 : Upper (D 5) (R 5) [6,40,80,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6055
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6056 : Route 9 := (fun mask => (mask,id))

def c6056 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6056 : Upper (D 5) (R 5) [6,40,80,384,9] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,9] 13 (by decide) (choices 1) [1,2,4] r6056 c6056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2569
  · exact u2570
  · exact u2571

def b6057 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 392 26 37 101 165 293), lower := (rows 7 42 84 392 26 32 64 128 256), losses := [] }

theorem u6057 : Upper (D 5) (R 5) [6,40,80,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6057
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6058 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 392 28 35 99 163 291), lower := (rows 7 42 84 392 28 32 64 128 256), losses := [] }

theorem u6058 : Upper (D 5) (R 5) [6,40,80,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6058
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6059 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 7 42 84 392 49 47 79 143 271), lower := (rows 7 42 84 392 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 25 16 0 65 129 257), good := (rows 463 10 92 392 477 0 64 128 256) }] }

theorem u6059 : Upper (D 5) (R 5) [6,40,80,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6059
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6059
end Delivery.IrregularNine14.P05
