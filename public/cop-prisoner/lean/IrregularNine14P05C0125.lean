import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0064
import IrregularNine14P05C0065

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7500 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 41 28 425 457 393 393), lower := (rows 19 70 38 41 28 32 64 128 256), losses := [] }

theorem u7500 : Upper (D 5) (R 5) [18,68,34,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7500
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7501 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 326, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 41 145 300 332 396 268), lower := (rows 19 70 38 41 145 32 64 128 256), losses := [] }

theorem u7501 : Upper (D 5) (R 5) [18,68,34,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7501
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7502 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 41 148 297 329 393 265), lower := (rows 19 70 38 41 148 32 64 128 256), losses := [] }

theorem u7502 : Upper (D 5) (R 5) [18,68,34,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7503 : Route 9 := (fun mask => (mask,id))

def c7503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7503 : Upper (D 5) (R 5) [18,68,34,33,136] 13 := by
  apply FastRouting.sound _ _ [18,68,34,33,136] 13 (by decide) (choices 1) [1,4,8,256] r7503 c7503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3877
  · exact u3878
  · exact u3879
  · exact u3880

def r7504 : Route 9 := (fun mask => (mask,id))

def c7504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7504 : Upper (D 5) (R 5) [18,68,34,33,384] 13 := by
  apply FastRouting.sound _ _ [18,68,34,33,384] 13 (by decide) (choices 1) [1,4,8] r7504 c7504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3881
  · exact u3882
  · exact u3883

def b7505 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 38 137 21 296 360 424 296), lower := (rows 19 70 38 137 21 32 64 128 256), losses := [] }

theorem u7505 : Upper (D 5) (R 5) [18,68,34,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7506 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 38 137 25 300 364 428 300), lower := (rows 19 70 38 137 25 32 64 128 256), losses := [] }

theorem u7506 : Upper (D 5) (R 5) [18,68,34,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7507 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 137 28 297 361 425 297), lower := (rows 19 70 38 137 28 32 64 128 256), losses := [] }

theorem u7507 : Upper (D 5) (R 5) [18,68,34,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7507
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7508 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 17, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 38 137 49 300 332 396 268), lower := (rows 19 70 38 137 49 32 64 128 256), losses := [] }

theorem u7508 : Upper (D 5) (R 5) [18,68,34,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7508
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7509 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 38 137 52 297 329 393 265), lower := (rows 19 70 38 137 52 32 64 128 256), losses := [] }

theorem u7509 : Upper (D 5) (R 5) [18,68,34,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7509
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7510 : Route 9 := (fun mask => (mask,id))

def c7510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7510 : Upper (D 5) (R 5) [18,68,34,129,40] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129,40] 13 (by decide) (choices 1) [1,4,8,256] r7510 c7510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3884
  · exact u3885
  · exact u3886
  · exact u3887

def b7511 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 137 273 44 108 172 300), lower := (rows 19 70 38 137 273 32 64 128 256), losses := [] }

theorem u7511 : Upper (D 5) (R 5) [18,68,34,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7511
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7512 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 137 276 41 105 169 297), lower := (rows 19 70 38 137 276 32 64 128 256), losses := [] }

theorem u7512 : Upper (D 5) (R 5) [18,68,34,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7512
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7513 : Route 9 := (fun mask => (mask,id))

def c7513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7513 : Upper (D 5) (R 5) [18,68,34,129,264] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129,264] 13 (by decide) (choices 1) [1,4,8] r7513 c7513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3888
  · exact u3889
  · exact u3890

def r7514 : Route 9 := (fun mask => (mask,id))

def c7514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7514 : Upper (D 5) (R 5) [18,68,34,129,288] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129,288] 13 (by decide) (choices 1) [1,4,8] r7514 c7514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3891
  · exact u3892
  · exact u3893

def r7515 : Route 9 := (fun mask => (mask,id))

def c7515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7515 : Upper (D 5) (R 5) [18,68,34,132,9] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,9] 13 (by decide) (choices 1) [1,8,256] r7515 c7515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3894
  · exact u3895
  · exact u3896

def b7516 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 17, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 38 140 49 297 329 393 265), lower := (rows 19 70 38 140 49 32 64 128 256), losses := [] }

theorem u7516 : Upper (D 5) (R 5) [18,68,34,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7516
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7517 : Route 9 := (fun mask => (mask,id))

def c7517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7517 : Upper (D 5) (R 5) [18,68,34,132,40] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,40] 13 (by decide) (choices 1) [1,8,256] r7517 c7517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3897
  · exact u3898
  · exact u3899

def r7518 : Route 9 := (fun mask => (mask,id))

def c7518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7518 : Upper (D 5) (R 5) [18,68,34,132,257] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,257] 13 (by decide) (choices 1) [1,8] r7518 c7518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3900
  · exact u3901

def r7519 : Route 9 := (fun mask => (mask,id))

def c7519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7519 : Upper (D 5) (R 5) [18,68,34,132,264] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,264] 13 (by decide) (choices 1) [1,8] r7519 c7519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3902
  · exact u3903

def r7520 : Route 9 := (fun mask => (mask,id))

def c7520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7520 : Upper (D 5) (R 5) [18,68,34,132,288] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,288] 13 (by decide) (choices 1) [1,8] r7520 c7520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3904
  · exact u3905

def b7521 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 38 168 21 297 329 393 265), lower := (rows 19 70 38 168 21 32 64 128 256), losses := [] }

theorem u7521 : Upper (D 5) (R 5) [18,68,34,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7522 : Route 9 := (fun mask => (mask,id))

def c7522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7522 : Upper (D 5) (R 5) [18,68,34,160,9] 13 := by
  apply FastRouting.sound _ _ [18,68,34,160,9] 13 (by decide) (choices 1) [1,4,8,256] r7522 c7522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3906
  · exact u3907
  · exact u3908
  · exact u3909

def b7523 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 168 28 297 329 393 265), lower := (rows 19 70 38 168 28 32 64 128 256), losses := [] }

theorem u7523 : Upper (D 5) (R 5) [18,68,34,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7524 : Route 9 := (fun mask => (mask,id))

def c7524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7524 : Upper (D 5) (R 5) [18,68,34,160,257] 13 := by
  apply FastRouting.sound _ _ [18,68,34,160,257] 13 (by decide) (choices 1) [1,4,8] r7524 c7524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3910
  · exact u3911
  · exact u3912

def b7525 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 168 276 41 73 137 265), lower := (rows 19 70 38 168 276 32 64 128 256), losses := [] }

theorem u7525 : Upper (D 5) (R 5) [18,68,34,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7525
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7526 : Route 9 := (fun mask => (mask,id))

def c7526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7526 : Upper (D 5) (R 5) [18,68,34,160,264] 13 := by
  apply FastRouting.sound _ _ [18,68,34,160,264] 13 (by decide) (choices 1) [1,4,8] r7526 c7526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3913
  · exact u3914
  · exact u3915

def b7527 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 38 392 21 41 105 169 297), lower := (rows 19 70 38 392 21 32 64 128 256), losses := [] }

theorem u7527 : Upper (D 5) (R 5) [18,68,34,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7527
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7528 : Route 9 := (fun mask => (mask,id))

def c7528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7528 : Upper (D 5) (R 5) [18,68,34,384,9] 13 := by
  apply FastRouting.sound _ _ [18,68,34,384,9] 13 (by decide) (choices 1) [1,4,8] r7528 c7528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3916
  · exact u3917
  · exact u3918

def b7529 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 392 28 41 105 169 297), lower := (rows 19 70 38 392 28 32 64 128 256), losses := [] }

theorem u7529 : Upper (D 5) (R 5) [18,68,34,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7530 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 17, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 38 392 49 45 77 141 269), lower := (rows 19 70 38 392 49 32 64 128 256), losses := [] }

theorem u7530 : Upper (D 5) (R 5) [18,68,34,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7530
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7531 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 38 392 52 41 73 137 265), lower := (rows 19 70 38 392 52 32 64 128 256), losses := [] }

theorem u7531 : Upper (D 5) (R 5) [18,68,34,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7531
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7532 : Route 9 := (fun mask => (mask,id))

def c7532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7532 : Upper (D 5) (R 5) [18,68,34,384,40] 13 := by
  apply FastRouting.sound _ _ [18,68,34,384,40] 13 (by decide) (choices 1) [1,4,8] r7532 c7532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3919
  · exact u3920
  · exact u3921

def b7533 : PairBound 9 := { available := 300, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 137 19 300 364 428 300), lower := (rows 19 70 44 137 19 32 64 128 256), losses := [] }

theorem u7533 : Upper (D 5) (R 5) [18,68,40,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7533
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7534 : PairBound 9 := { available := 298, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 44 137 21 298 362 426 298), lower := (rows 19 70 44 137 21 32 64 128 256), losses := [] }

theorem u7534 : Upper (D 5) (R 5) [18,68,40,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7535 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 44 137 22 297 361 425 297), lower := (rows 19 70 44 137 22 32 64 128 256), losses := [] }

theorem u7535 : Upper (D 5) (R 5) [18,68,40,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7535
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7536 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 44 137 25 294 358 422 294), lower := (rows 19 70 44 137 25 32 64 128 256), losses := [] }

theorem u7536 : Upper (D 5) (R 5) [18,68,40,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7537 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 137 26 293 357 421 293), lower := (rows 19 70 44 137 26 32 64 128 256), losses := [] }

theorem u7537 : Upper (D 5) (R 5) [18,68,40,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7537
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7538 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 137 28 291 355 419 291), lower := (rows 19 70 44 137 28 32 64 128 256), losses := [] }

theorem u7538 : Upper (D 5) (R 5) [18,68,40,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7539 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 44 137 49 302 334 398 270), lower := (rows 19 70 44 137 49 32 64 128 256), losses := [] }

theorem u7539 : Upper (D 5) (R 5) [18,68,40,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7539
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7540 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 137 50 301 333 397 269), lower := (rows 19 70 44 137 50 32 64 128 256), losses := [] }

theorem u7540 : Upper (D 5) (R 5) [18,68,40,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7541 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 137 52 299 331 395 267), lower := (rows 19 70 44 137 52 32 64 128 256), losses := [] }

theorem u7541 : Upper (D 5) (R 5) [18,68,40,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7542 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 137 56 295 327 391 263), lower := (rows 19 70 44 137 56 32 64 128 256), losses := [] }

theorem u7542 : Upper (D 5) (R 5) [18,68,40,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7542
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7543 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 44 137 273 46 110 174 302), lower := (rows 19 70 44 137 273 32 64 128 256), losses := [] }

theorem u7543 : Upper (D 5) (R 5) [18,68,40,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7543
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7544 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 137 274 45 109 173 301), lower := (rows 19 70 44 137 274 32 64 128 256), losses := [] }

theorem u7544 : Upper (D 5) (R 5) [18,68,40,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7545 : Route 9 := (fun mask => (mask,id))

def c7545 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7545 : Upper (D 5) (R 5) [18,68,40,129,260] 13 := by
  apply FastRouting.sound _ _ [18,68,40,129,260] 13 (by decide) (choices 1) [1,2,8] r7545 c7545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3922
  · exact u3923
  · exact u3924

def r7546 : Route 9 := (fun mask => (mask,id))

def c7546 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7546 : Upper (D 5) (R 5) [18,68,40,129,264] 13 := by
  apply FastRouting.sound _ _ [18,68,40,129,264] 13 (by decide) (choices 1) [1,2,4] r7546 c7546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3925
  · exact u3926
  · exact u3927

def r7547 : Route 9 := (fun mask => (mask,id))

def c7547 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7547 : Upper (D 5) (R 5) [18,68,40,129,288] 13 := by
  apply FastRouting.sound _ _ [18,68,40,129,288] 13 (by decide) (choices 1) [1,2,4,8] r7547 c7547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3928
  · exact u3929
  · exact u3930
  · exact u3931

def b7548 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 44 138 21 297 361 425 297), lower := (rows 19 70 44 138 21 32 64 128 256), losses := [] }

theorem u7548 : Upper (D 5) (R 5) [18,68,40,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7548
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7549 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 44 138 25 293 357 421 293), lower := (rows 19 70 44 138 25 32 64 128 256), losses := [] }

theorem u7549 : Upper (D 5) (R 5) [18,68,40,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7549
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7550 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 138 28 289 353 417 289), lower := (rows 19 70 44 138 28 32 64 128 256), losses := [] }

theorem u7550 : Upper (D 5) (R 5) [18,68,40,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7550
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7551 : Route 9 := (fun mask => (mask,id))

def c7551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7551 : Upper (D 5) (R 5) [18,68,40,130,33] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,33] 13 (by decide) (choices 1) [1,4,8,256] r7551 c7551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3932
  · exact u3933
  · exact u3934
  · exact u3935

def b7552 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 138 52 297 329 393 265), lower := (rows 19 70 44 138 52 32 64 128 256), losses := [] }

theorem u7552 : Upper (D 5) (R 5) [18,68,40,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7552
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7553 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 138 56 293 325 389 261), lower := (rows 19 70 44 138 56 32 64 128 256), losses := [] }

theorem u7553 : Upper (D 5) (R 5) [18,68,40,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7554 : Route 9 := (fun mask => (mask,id))

def c7554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7554 : Upper (D 5) (R 5) [18,68,40,130,257] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,257] 13 (by decide) (choices 1) [1,4,8] r7554 c7554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3936
  · exact u3937
  · exact u3938

def r7555 : Route 9 := (fun mask => (mask,id))

def c7555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7555 : Upper (D 5) (R 5) [18,68,40,130,260] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,260] 13 (by decide) (choices 1) [1,8] r7555 c7555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3939
  · exact u3940

def r7556 : Route 9 := (fun mask => (mask,id))

def c7556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7556 : Upper (D 5) (R 5) [18,68,40,130,264] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,264] 13 (by decide) (choices 1) [1,4] r7556 c7556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3941
  · exact u3942

def r7557 : Route 9 := (fun mask => (mask,id))

def c7557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7557 : Upper (D 5) (R 5) [18,68,40,130,288] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,288] 13 (by decide) (choices 1) [1,4,8] r7557 c7557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3943
  · exact u3944
  · exact u3945

def b7558 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 140 19 297 361 425 297), lower := (rows 19 70 44 140 19 32 64 128 256), losses := [] }

theorem u7558 : Upper (D 5) (R 5) [18,68,40,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7558
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7559 : Route 9 := (fun mask => (mask,id))

def c7559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7559 : Upper (D 5) (R 5) [18,68,40,132,9] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,9] 13 (by decide) (choices 1) [1,2,256] r7559 c7559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3946
  · exact u3947
  · exact u3948

#print axioms u7559
end Delivery.IrregularNine14.P05
