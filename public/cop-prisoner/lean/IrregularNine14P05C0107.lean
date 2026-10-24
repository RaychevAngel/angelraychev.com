import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0048

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6420 : Route 9 := (fun mask => (mask,id))

def c6420 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6420 : Upper (D 5) (R 5) [6,65,136,288,33] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,33] 13 (by decide) (choices 1) [2,4,8,16] r6420 c6420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2898
  · exact u2899
  · exact u2900
  · exact u2901

def r6421 : Route 9 := (fun mask => (mask,id))

def c6421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6421 : Upper (D 5) (R 5) [6,65,136,288,34] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,34] 13 (by decide) (choices 1) [1,4,8,16] r6421 c6421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2902
  · exact u2903
  · exact u2904
  · exact u2905

def r6422 : Route 9 := (fun mask => (mask,id))

def c6422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6422 : Upper (D 5) (R 5) [6,65,136,288,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,36] 13 (by decide) (choices 1) [1,2,8,16] r6422 c6422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2906
  · exact u2907
  · exact u2908
  · exact u2909

def b6423 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 296 56 55 87 151 279), lower := (rows 7 67 140 296 56 32 64 128 256), losses := [] }

theorem u6423 : Upper (D 5) (R 5) [6,65,136,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6424 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 41 22 296 360 424 296), lower := (rows 7 67 148 41 22 32 64 128 256), losses := [] }

theorem u6424 : Upper (D 5) (R 5) [6,65,144,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6424
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6425 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 41 26 300 364 428 300), lower := (rows 7 67 148 41 26 32 64 128 256), losses := [] }

theorem u6425 : Upper (D 5) (R 5) [6,65,144,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6425
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6426 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 41 28 298 362 426 298), lower := (rows 7 67 148 41 28 32 64 128 256), losses := [] }

theorem u6426 : Upper (D 5) (R 5) [6,65,144,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6426
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6427 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 41 50 300 332 396 268), lower := (rows 7 67 148 41 50 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 11 16 49 81 145 273), good := (rows 493 489 500 489 508 32 64 128 256) }] }

theorem u6427 : Upper (D 5) (R 5) [6,65,144,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6427
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6428 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 41 52 298 330 394 266), lower := (rows 7 67 148 41 52 32 64 128 256), losses := [] }

theorem u6428 : Upper (D 5) (R 5) [6,65,144,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6428
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6429 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 41 56 302 334 398 270), lower := (rows 7 67 148 41 56 32 64 128 256), losses := [] }

theorem u6429 : Upper (D 5) (R 5) [6,65,144,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6429
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6430 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 41 274 44 108 172 300), lower := (rows 7 67 148 41 274 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 11 16 49 81 145 273), good := (rows 493 489 500 489 508 32 64 128 256) }] }

theorem u6430 : Upper (D 5) (R 5) [6,65,144,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6430
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6431 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 41 276 42 106 170 298), lower := (rows 7 67 148 41 276 32 64 128 256), losses := [] }

theorem u6431 : Upper (D 5) (R 5) [6,65,144,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6431
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6432 : Route 9 := (fun mask => (mask,id))

def c6432 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6432 : Upper (D 5) (R 5) [6,65,144,33,264] 13 := by
  apply FastRouting.sound _ _ [6,65,144,33,264] 13 (by decide) (choices 1) [2,4,8] r6432 c6432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2910
  · exact u2911
  · exact u2912

def r6433 : Route 9 := (fun mask => (mask,id))

def c6433 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6433 : Upper (D 5) (R 5) [6,65,144,33,288] 13 := by
  apply FastRouting.sound _ _ [6,65,144,33,288] 13 (by decide) (choices 1) [2,4,8] r6433 c6433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2913
  · exact u2914
  · exact u2915

def b6434 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 148 42 21 296 360 424 296), lower := (rows 7 67 148 42 21 32 64 128 256), losses := [] }

theorem u6434 : Upper (D 5) (R 5) [6,65,144,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6435 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 42 25 300 364 428 300), lower := (rows 7 67 148 42 25 32 64 128 256), losses := [] }

theorem u6435 : Upper (D 5) (R 5) [6,65,144,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6435
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6436 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 42 28 297 361 425 297), lower := (rows 7 67 148 42 28 32 64 128 256), losses := [] }

theorem u6436 : Upper (D 5) (R 5) [6,65,144,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6436
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6437 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 148 42 49 300 332 396 268), lower := (rows 7 67 148 42 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 11 16 49 81 145 273), good := (rows 494 490 500 42 508 32 64 128 256) }] }

theorem u6437 : Upper (D 5) (R 5) [6,65,144,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6437
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6438 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 42 52 297 329 393 265), lower := (rows 7 67 148 42 52 32 64 128 256), losses := [] }

theorem u6438 : Upper (D 5) (R 5) [6,65,144,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6438
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6439 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 42 56 301 333 397 269), lower := (rows 7 67 148 42 56 32 64 128 256), losses := [] }

theorem u6439 : Upper (D 5) (R 5) [6,65,144,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6439
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6440 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 148 42 273 44 108 172 300), lower := (rows 7 67 148 42 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 11 16 49 81 145 273), good := (rows 494 490 500 42 508 32 64 128 256) }] }

theorem u6440 : Upper (D 5) (R 5) [6,65,144,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6441 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 42 276 41 105 169 297), lower := (rows 7 67 148 42 276 32 64 128 256), losses := [] }

theorem u6441 : Upper (D 5) (R 5) [6,65,144,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6441
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6442 : Route 9 := (fun mask => (mask,id))

def c6442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6442 : Upper (D 5) (R 5) [6,65,144,34,264] 13 := by
  apply FastRouting.sound _ _ [6,65,144,34,264] 13 (by decide) (choices 1) [1,4,8] r6442 c6442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2916
  · exact u2917
  · exact u2918

def r6443 : Route 9 := (fun mask => (mask,id))

def c6443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6443 : Upper (D 5) (R 5) [6,65,144,34,288] 13 := by
  apply FastRouting.sound _ _ [6,65,144,34,288] 13 (by decide) (choices 1) [1,4,8] r6443 c6443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2919
  · exact u2920
  · exact u2921

def b6444 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 44 19 296 360 424 296), lower := (rows 7 67 148 44 19 32 64 128 256), losses := [] }

theorem u6444 : Upper (D 5) (R 5) [6,65,144,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6445 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 296, targets := 1 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 7 67 148 44 25 298 362 426 298), lower := (rows 7 67 148 44 25 32 64 128 256), losses := [] }

theorem u6445 : Upper (D 5) (R 5) [6,65,144,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6445
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6446 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 44 26 297 361 425 297), lower := (rows 7 67 148 44 26 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 67 131 259), good := (rows 493 489 156 44 508 32 64 128 256) }] }

theorem u6446 : Upper (D 5) (R 5) [6,65,144,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6446
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6447 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 148 44 49 298 330 394 266), lower := (rows 7 67 148 44 49 32 64 128 256), losses := [] }

theorem u6447 : Upper (D 5) (R 5) [6,65,144,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6447
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6448 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 148 44 50 297 329 393 265), lower := (rows 7 67 148 44 50 32 64 128 256), losses := [] }

theorem u6448 : Upper (D 5) (R 5) [6,65,144,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6448
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6449 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 44 56 299 331 395 267), lower := (rows 7 67 148 44 56 32 64 128 256), losses := [] }

theorem u6449 : Upper (D 5) (R 5) [6,65,144,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6449
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6450 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 148 44 273 42 106 170 298), lower := (rows 7 67 148 44 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 25 16 35 67 131 259), good := (rows 494 490 156 44 508 32 64 128 256) }] }

theorem u6450 : Upper (D 5) (R 5) [6,65,144,36,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6450
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6451 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 44 274 41 105 169 297), lower := (rows 7 67 148 44 274 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 67 131 259), good := (rows 493 489 156 44 508 32 64 128 256) }] }

theorem u6451 : Upper (D 5) (R 5) [6,65,144,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6451
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6452 : Route 9 := (fun mask => (mask,id))

def c6452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6452 : Upper (D 5) (R 5) [6,65,144,36,264] 13 := by
  apply FastRouting.sound _ _ [6,65,144,36,264] 13 (by decide) (choices 1) [1,2,8] r6452 c6452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2922
  · exact u2923
  · exact u2924

def b6453 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 148 44 304 43 75 139 267), lower := (rows 7 67 148 44 304 32 64 128 256), losses := [] }

theorem u6453 : Upper (D 5) (R 5) [6,65,144,36,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6453
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6454 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 265 22 40 104 168 296), lower := (rows 7 67 148 265 22 32 64 128 256), losses := [] }

theorem u6454 : Upper (D 5) (R 5) [6,65,144,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6454
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6455 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 265 26 44 108 172 300), lower := (rows 7 67 148 265 26 32 64 128 256), losses := [] }

theorem u6455 : Upper (D 5) (R 5) [6,65,144,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6455
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6456 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 265 28 42 106 170 298), lower := (rows 7 67 148 265 28 32 64 128 256), losses := [] }

theorem u6456 : Upper (D 5) (R 5) [6,65,144,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6456
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6457 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 265 50 44 108 172 300), lower := (rows 7 67 148 265 50 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 11 16 49 81 145 273), good := (rows 493 489 500 489 508 32 64 128 256) }] }

theorem u6457 : Upper (D 5) (R 5) [6,65,144,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6457
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6458 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 265 52 42 106 170 298), lower := (rows 7 67 148 265 52 32 64 128 256), losses := [] }

theorem u6458 : Upper (D 5) (R 5) [6,65,144,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6458
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6459 : Route 9 := (fun mask => (mask,id))

def c6459 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6459 : Upper (D 5) (R 5) [6,65,144,257,40] 13 := by
  apply FastRouting.sound _ _ [6,65,144,257,40] 13 (by decide) (choices 1) [2,4,8] r6459 c6459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2925
  · exact u2926
  · exact u2927

def b6460 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 148 266 21 40 104 168 296), lower := (rows 7 67 148 266 21 32 64 128 256), losses := [] }

theorem u6460 : Upper (D 5) (R 5) [6,65,144,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6460
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6461 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 266 25 44 108 172 300), lower := (rows 7 67 148 266 25 32 64 128 256), losses := [] }

theorem u6461 : Upper (D 5) (R 5) [6,65,144,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6461
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6462 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 266 28 41 105 169 297), lower := (rows 7 67 148 266 28 32 64 128 256), losses := [] }

theorem u6462 : Upper (D 5) (R 5) [6,65,144,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6462
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6463 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 148 266 49 44 108 172 300), lower := (rows 7 67 148 266 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 11 16 49 81 145 273), good := (rows 494 490 500 266 508 32 64 128 256) }] }

theorem u6463 : Upper (D 5) (R 5) [6,65,144,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6463
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6464 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 266 52 41 105 169 297), lower := (rows 7 67 148 266 52 32 64 128 256), losses := [] }

theorem u6464 : Upper (D 5) (R 5) [6,65,144,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6465 : Route 9 := (fun mask => (mask,id))

def c6465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6465 : Upper (D 5) (R 5) [6,65,144,258,40] 13 := by
  apply FastRouting.sound _ _ [6,65,144,258,40] 13 (by decide) (choices 1) [1,4,8] r6465 c6465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2928
  · exact u2929
  · exact u2930

def b6466 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 268 19 40 104 168 296), lower := (rows 7 67 148 268 19 32 64 128 256), losses := [] }

theorem u6466 : Upper (D 5) (R 5) [6,65,144,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6466
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6467 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 296, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 7 67 148 268 25 42 106 170 298), lower := (rows 7 67 148 268 25 32 64 128 256), losses := [] }

theorem u6467 : Upper (D 5) (R 5) [6,65,144,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6467
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6468 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 268 26 41 105 169 297), lower := (rows 7 67 148 268 26 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 67 131 259), good := (rows 493 489 156 268 508 32 64 128 256) }] }

theorem u6468 : Upper (D 5) (R 5) [6,65,144,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6469 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 148 268 49 42 106 170 298), lower := (rows 7 67 148 268 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 25 16 35 67 131 259), good := (rows 494 490 156 268 508 32 64 128 256) }] }

theorem u6469 : Upper (D 5) (R 5) [6,65,144,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6469
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6470 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 268 50 41 105 169 297), lower := (rows 7 67 148 268 50 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 67 131 259), good := (rows 493 489 156 268 508 32 64 128 256) }] }

theorem u6470 : Upper (D 5) (R 5) [6,65,144,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6470
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6471 : Route 9 := (fun mask => (mask,id))

def c6471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6471 : Upper (D 5) (R 5) [6,65,144,260,40] 13 := by
  apply FastRouting.sound _ _ [6,65,144,260,40] 13 (by decide) (choices 1) [1,2,8] r6471 c6471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2931
  · exact u2932
  · exact u2933

def b6472 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 296 19 44 108 172 300), lower := (rows 7 67 148 296 19 32 64 128 256), losses := [] }

theorem u6472 : Upper (D 5) (R 5) [6,65,144,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6472
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6473 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 148 296 21 42 106 170 298), lower := (rows 7 67 148 296 21 32 64 128 256), losses := [] }

theorem u6473 : Upper (D 5) (R 5) [6,65,144,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6473
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6474 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 296 22 41 105 169 297), lower := (rows 7 67 148 296 22 32 64 128 256), losses := [] }

theorem u6474 : Upper (D 5) (R 5) [6,65,144,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6475 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 148 296 25 46 110 174 302), lower := (rows 7 67 148 296 25 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 156 296 508 32 64 128 256) }] }

theorem u6475 : Upper (D 5) (R 5) [6,65,144,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6475
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6476 : Route 9 := (fun mask => (mask,id))

def c6476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6476 : Upper (D 5) (R 5) [6,65,144,288,10] 13 := by
  apply FastRouting.sound _ _ [6,65,144,288,10] 13 (by decide) (choices 1) [1,4,8] r6476 c6476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2934
  · exact u2935
  · exact u2936

def b6477 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 296 28 43 107 171 299), lower := (rows 7 67 148 296 28 32 64 128 256), losses := [] }

theorem u6477 : Upper (D 5) (R 5) [6,65,144,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6478 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 148 296 49 46 78 142 270), lower := (rows 7 67 148 296 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 156 296 508 32 64 128 256) }] }

theorem u6478 : Upper (D 5) (R 5) [6,65,144,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6479 : Route 9 := (fun mask => (mask,id))

def c6479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6479 : Upper (D 5) (R 5) [6,65,144,288,34] 13 := by
  apply FastRouting.sound _ _ [6,65,144,288,34] 13 (by decide) (choices 1) [1,4,8] r6479 c6479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2937
  · exact u2938
  · exact u2939

#print axioms u6479
end Delivery.IrregularNine14.P05
