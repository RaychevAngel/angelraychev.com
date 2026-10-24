import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0064

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7440 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 164 296 28 47 79 143 271), lower := (rows 19 67 164 296 28 32 64 128 256), losses := [] }

theorem u7440 : Upper (D 5) (R 5) [18,65,160,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7441 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 37 42 21 424 456 392 392), lower := (rows 19 70 37 42 21 32 64 128 256), losses := [] }

theorem u7441 : Upper (D 5) (R 5) [18,68,33,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7441
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7442 : PairBound 9 := { available := 396, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 37 42 25 428 460 396 396), lower := (rows 19 70 37 42 25 32 64 128 256), losses := [] }

theorem u7442 : Upper (D 5) (R 5) [18,68,33,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7442
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7443 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 451, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 37 42 28 425 457 393 393), lower := (rows 19 70 37 42 28 32 64 128 256), losses := [] }

theorem u7443 : Upper (D 5) (R 5) [18,68,33,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7443
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7444 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 330, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 42 145 300 332 396 268), lower := (rows 19 70 37 42 145 32 64 128 256), losses := [] }

theorem u7444 : Upper (D 5) (R 5) [18,68,33,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7445 : Route 9 := (fun mask => (mask,id))

def c7445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7445 : Upper (D 5) (R 5) [18,68,33,34,132] 13 := by
  apply FastRouting.sound _ _ [18,68,33,34,132] 13 (by decide) (choices 1) [1,8,256] r7445 c7445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3841
  · exact u3842
  · exact u3843

def r7446 : Route 9 := (fun mask => (mask,id))

def c7446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7446 : Upper (D 5) (R 5) [18,68,33,34,136] 13 := by
  apply FastRouting.sound _ _ [18,68,33,34,136] 13 (by decide) (choices 1) [1,4,8,256] r7446 c7446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3844
  · exact u3845
  · exact u3846
  · exact u3847

def r7447 : Route 9 := (fun mask => (mask,id))

def c7447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7447 : Upper (D 5) (R 5) [18,68,33,34,384] 13 := by
  apply FastRouting.sound _ _ [18,68,33,34,384] 13 (by decide) (choices 1) [1,4,8] r7447 c7447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3848
  · exact u3849
  · exact u3850

def b7448 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 37 137 22 296 360 424 296), lower := (rows 19 70 37 137 22 32 64 128 256), losses := [] }

theorem u7448 : Upper (D 5) (R 5) [18,68,33,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7448
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7449 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 137 26 300 364 428 300), lower := (rows 19 70 37 137 26 32 64 128 256), losses := [] }

theorem u7449 : Upper (D 5) (R 5) [18,68,33,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7449
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7450 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 70 37 137 28 298 362 426 298), lower := (rows 19 70 37 137 28 32 64 128 256), losses := [] }

theorem u7450 : Upper (D 5) (R 5) [18,68,33,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7450
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7451 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 37 137 50 300 332 396 268), lower := (rows 19 70 37 137 50 32 64 128 256), losses := [] }

theorem u7451 : Upper (D 5) (R 5) [18,68,33,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7451
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7452 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 37 137 52 298 330 394 266), lower := (rows 19 70 37 137 52 32 64 128 256), losses := [] }

theorem u7452 : Upper (D 5) (R 5) [18,68,33,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7452
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7453 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 70 37 137 56 302 334 398 270), lower := (rows 19 70 37 137 56 32 64 128 256), losses := [] }

theorem u7453 : Upper (D 5) (R 5) [18,68,33,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7453
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7454 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 137 274 44 108 172 300), lower := (rows 19 70 37 137 274 32 64 128 256), losses := [] }

theorem u7454 : Upper (D 5) (R 5) [18,68,33,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7454
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7455 : Route 9 := (fun mask => (mask,id))

def c7455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7455 : Upper (D 5) (R 5) [18,68,33,129,260] 13 := by
  apply FastRouting.sound _ _ [18,68,33,129,260] 13 (by decide) (choices 1) [2,8] r7455 c7455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3851
  · exact u3852

def r7456 : Route 9 := (fun mask => (mask,id))

def c7456 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7456 : Upper (D 5) (R 5) [18,68,33,129,264] 13 := by
  apply FastRouting.sound _ _ [18,68,33,129,264] 13 (by decide) (choices 1) [2,4,8] r7456 c7456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3853
  · exact u3854
  · exact u3855

def b7457 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 70 37 137 304 46 78 142 270), lower := (rows 19 70 37 137 304 32 64 128 256), losses := [] }

theorem u7457 : Upper (D 5) (R 5) [18,68,33,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7457
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7458 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 37 138 21 296 360 424 296), lower := (rows 19 70 37 138 21 32 64 128 256), losses := [] }

theorem u7458 : Upper (D 5) (R 5) [18,68,33,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7458
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7459 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 37 138 25 300 364 428 300), lower := (rows 19 70 37 138 25 32 64 128 256), losses := [] }

theorem u7459 : Upper (D 5) (R 5) [18,68,33,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7459
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7460 : Route 9 := (fun mask => (mask,id))

def c7460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7460 : Upper (D 5) (R 5) [18,68,33,130,12] 13 := by
  apply FastRouting.sound _ _ [18,68,33,130,12] 13 (by decide) (choices 1) [1,8,256] r7460 c7460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3856
  · exact u3857
  · exact u3858

def b7461 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 138 49 300 332 396 268), lower := (rows 19 70 37 138 49 32 64 128 256), losses := [] }

theorem u7461 : Upper (D 5) (R 5) [18,68,33,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7461
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7462 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 37 138 52 297 329 393 265), lower := (rows 19 70 37 138 52 32 64 128 256), losses := [] }

theorem u7462 : Upper (D 5) (R 5) [18,68,33,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7462
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7463 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 70 37 138 56 301 333 397 269), lower := (rows 19 70 37 138 56 32 64 128 256), losses := [] }

theorem u7463 : Upper (D 5) (R 5) [18,68,33,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7463
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7464 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 138 273 44 108 172 300), lower := (rows 19 70 37 138 273 32 64 128 256), losses := [] }

theorem u7464 : Upper (D 5) (R 5) [18,68,33,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7465 : Route 9 := (fun mask => (mask,id))

def c7465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7465 : Upper (D 5) (R 5) [18,68,33,130,260] 13 := by
  apply FastRouting.sound _ _ [18,68,33,130,260] 13 (by decide) (choices 1) [1,8] r7465 c7465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3859
  · exact u3860

def r7466 : Route 9 := (fun mask => (mask,id))

def c7466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7466 : Upper (D 5) (R 5) [18,68,33,130,264] 13 := by
  apply FastRouting.sound _ _ [18,68,33,130,264] 13 (by decide) (choices 1) [1,4,8] r7466 c7466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3861
  · exact u3862
  · exact u3863

def b7467 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 70 37 138 304 45 77 141 269), lower := (rows 19 70 37 138 304 32 64 128 256), losses := [] }

theorem u7467 : Upper (D 5) (R 5) [18,68,33,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7467
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7468 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 140 19 296 360 424 296), lower := (rows 19 70 37 140 19 32 64 128 256), losses := [] }

theorem u7468 : Upper (D 5) (R 5) [18,68,33,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7469 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 140 25 298 362 426 298), lower := (rows 19 70 37 140 25 32 64 128 256), losses := [] }

theorem u7469 : Upper (D 5) (R 5) [18,68,33,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7469
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7470 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 37 140 26 297 361 425 297), lower := (rows 19 70 37 140 26 32 64 128 256), losses := [] }

theorem u7470 : Upper (D 5) (R 5) [18,68,33,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7470
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7471 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 140 49 298 330 394 266), lower := (rows 19 70 37 140 49 32 64 128 256), losses := [] }

theorem u7471 : Upper (D 5) (R 5) [18,68,33,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7472 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 37 140 50 297 329 393 265), lower := (rows 19 70 37 140 50 32 64 128 256), losses := [] }

theorem u7472 : Upper (D 5) (R 5) [18,68,33,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7472
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7473 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 70 37 140 56 299 331 395 267), lower := (rows 19 70 37 140 56 32 64 128 256), losses := [] }

theorem u7473 : Upper (D 5) (R 5) [18,68,33,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7473
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7474 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 140 273 42 106 170 298), lower := (rows 19 70 37 140 273 32 64 128 256), losses := [] }

theorem u7474 : Upper (D 5) (R 5) [18,68,33,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7475 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 140 274 41 105 169 297), lower := (rows 19 70 37 140 274 32 64 128 256), losses := [] }

theorem u7475 : Upper (D 5) (R 5) [18,68,33,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7475
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7476 : Route 9 := (fun mask => (mask,id))

def c7476 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7476 : Upper (D 5) (R 5) [18,68,33,132,264] 13 := by
  apply FastRouting.sound _ _ [18,68,33,132,264] 13 (by decide) (choices 1) [1,2,8] r7476 c7476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3864
  · exact u3865
  · exact u3866

def b7477 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 70 37 140 304 43 75 139 267), lower := (rows 19 70 37 140 304 32 64 128 256), losses := [] }

theorem u7477 : Upper (D 5) (R 5) [18,68,33,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7478 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 168 19 300 332 396 268), lower := (rows 19 70 37 168 19 32 64 128 256), losses := [] }

theorem u7478 : Upper (D 5) (R 5) [18,68,33,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7479 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 37 168 21 298 330 394 266), lower := (rows 19 70 37 168 21 32 64 128 256), losses := [] }

theorem u7479 : Upper (D 5) (R 5) [18,68,33,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7479
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7480 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 37 168 22 297 329 393 265), lower := (rows 19 70 37 168 22 32 64 128 256), losses := [] }

theorem u7480 : Upper (D 5) (R 5) [18,68,33,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7480
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7481 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 168 25 302 334 398 270), lower := (rows 19 70 37 168 25 32 64 128 256), losses := [] }

theorem u7481 : Upper (D 5) (R 5) [18,68,33,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7481
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7482 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 168 26 301 333 397 269), lower := (rows 19 70 37 168 26 32 64 128 256), losses := [] }

theorem u7482 : Upper (D 5) (R 5) [18,68,33,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7483 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 37 168 28 299 331 395 267), lower := (rows 19 70 37 168 28 32 64 128 256), losses := [] }

theorem u7483 : Upper (D 5) (R 5) [18,68,33,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7484 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 168 273 46 78 142 270), lower := (rows 19 70 37 168 273 32 64 128 256), losses := [] }

theorem u7484 : Upper (D 5) (R 5) [18,68,33,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7485 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 168 274 45 77 141 269), lower := (rows 19 70 37 168 274 32 64 128 256), losses := [] }

theorem u7485 : Upper (D 5) (R 5) [18,68,33,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7486 : Route 9 := (fun mask => (mask,id))

def c7486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7486 : Upper (D 5) (R 5) [18,68,33,160,260] 13 := by
  apply FastRouting.sound _ _ [18,68,33,160,260] 13 (by decide) (choices 1) [1,2,8] r7486 c7486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3867
  · exact u3868
  · exact u3869

def r7487 : Route 9 := (fun mask => (mask,id))

def c7487 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7487 : Upper (D 5) (R 5) [18,68,33,160,264] 13 := by
  apply FastRouting.sound _ _ [18,68,33,160,264] 13 (by decide) (choices 1) [1,2,4,8] r7487 c7487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3870
  · exact u3871
  · exact u3872
  · exact u3873

def b7488 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 392 19 44 108 172 300), lower := (rows 19 70 37 392 19 32 64 128 256), losses := [] }

theorem u7488 : Upper (D 5) (R 5) [18,68,33,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7489 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 37 392 21 42 106 170 298), lower := (rows 19 70 37 392 21 32 64 128 256), losses := [] }

theorem u7489 : Upper (D 5) (R 5) [18,68,33,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7489
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7490 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 37 392 22 41 105 169 297), lower := (rows 19 70 37 392 22 32 64 128 256), losses := [] }

theorem u7490 : Upper (D 5) (R 5) [18,68,33,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7490
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7491 : PairBound 9 := { available := 46, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 392 25 46 110 174 302), lower := (rows 19 70 37 392 25 32 64 128 256), losses := [] }

theorem u7491 : Upper (D 5) (R 5) [18,68,33,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7491
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7492 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 37 392 26 45 109 173 301), lower := (rows 19 70 37 392 26 32 64 128 256), losses := [] }

theorem u7492 : Upper (D 5) (R 5) [18,68,33,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7493 : Route 9 := (fun mask => (mask,id))

def c7493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7493 : Upper (D 5) (R 5) [18,68,33,384,12] 13 := by
  apply FastRouting.sound _ _ [18,68,33,384,12] 13 (by decide) (choices 1) [1,2,8] r7493 c7493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3874
  · exact u3875
  · exact u3876

def b7494 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 392 49 46 78 142 270), lower := (rows 19 70 37 392 49 32 64 128 256), losses := [] }

theorem u7494 : Upper (D 5) (R 5) [18,68,33,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7495 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 37 392 50 45 77 141 269), lower := (rows 19 70 37 392 50 32 64 128 256), losses := [] }

theorem u7495 : Upper (D 5) (R 5) [18,68,33,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7496 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 37 392 52 43 75 139 267), lower := (rows 19 70 37 392 52 32 64 128 256), losses := [] }

theorem u7496 : Upper (D 5) (R 5) [18,68,33,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7497 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 70 37 392 56 47 79 143 271), lower := (rows 19 70 37 392 56 32 64 128 256), losses := [] }

theorem u7497 : Upper (D 5) (R 5) [18,68,33,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7497
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7498 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 38 41 21 424 456 392 392), lower := (rows 19 70 38 41 21 32 64 128 256), losses := [] }

theorem u7498 : Upper (D 5) (R 5) [18,68,34,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7499 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 25, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 38 41 25 428 460 396 396), lower := (rows 19 70 38 41 25 32 64 128 256), losses := [] }

theorem u7499 : Upper (D 5) (R 5) [18,68,34,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7499
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7499
end Delivery.IrregularNine14.P05
