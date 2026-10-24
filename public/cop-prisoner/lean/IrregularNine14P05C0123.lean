import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0063
import IrregularNine14P05C0064

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7380 : Route 9 := (fun mask => (mask,id))

def c7380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7380 : Upper (D 5) (R 5) [18,65,40,132,260] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,260] 13 (by decide) (choices 1) [1,2,8] r7380 c7380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3798
  · exact u3799
  · exact u3800

def r7381 : Route 9 := (fun mask => (mask,id))

def c7381 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7381 : Upper (D 5) (R 5) [18,65,40,132,264] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,264] 13 (by decide) (choices 1) [1,2,4] r7381 c7381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3801
  · exact u3802
  · exact u3803

def r7382 : Route 9 := (fun mask => (mask,id))

def c7382 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7382 : Upper (D 5) (R 5) [18,65,40,132,288] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,288] 13 (by decide) (choices 1) [1,2,4,8] r7382 c7382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3804
  · exact u3805
  · exact u3806
  · exact u3807

def b7383 : PairBound 9 := { available := 44, camps := [{ cop := 6, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 392 19 44 108 172 300), lower := (rows 19 67 44 392 19 32 64 128 256), losses := [] }

theorem u7383 : Upper (D 5) (R 5) [18,65,40,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7383
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7384 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 392 21 46 110 174 302), lower := (rows 19 67 44 392 21 32 64 128 256), losses := [] }

theorem u7384 : Upper (D 5) (R 5) [18,65,40,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7384
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7385 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 392 22 45 109 173 301), lower := (rows 19 67 44 392 22 32 64 128 256), losses := [] }

theorem u7385 : Upper (D 5) (R 5) [18,65,40,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7386 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 392 25 38 102 166 294), lower := (rows 19 67 44 392 25 32 64 128 256), losses := [] }

theorem u7386 : Upper (D 5) (R 5) [18,65,40,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7387 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 392 26 37 101 165 293), lower := (rows 19 67 44 392 26 32 64 128 256), losses := [] }

theorem u7387 : Upper (D 5) (R 5) [18,65,40,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7388 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 392 28 39 103 167 295), lower := (rows 19 67 44 392 28 32 64 128 256), losses := [] }

theorem u7388 : Upper (D 5) (R 5) [18,65,40,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7388
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7389 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 392 49 46 78 142 270), lower := (rows 19 67 44 392 49 32 64 128 256), losses := [] }

theorem u7389 : Upper (D 5) (R 5) [18,65,40,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7390 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 392 50 45 77 141 269), lower := (rows 19 67 44 392 50 32 64 128 256), losses := [] }

theorem u7390 : Upper (D 5) (R 5) [18,65,40,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7390
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7391 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 392 52 47 79 143 271), lower := (rows 19 67 44 392 52 32 64 128 256), losses := [] }

theorem u7391 : Upper (D 5) (R 5) [18,65,40,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7391
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7392 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 392 56 39 71 135 263), lower := (rows 19 67 44 392 56 32 64 128 256), losses := [] }

theorem u7392 : Upper (D 5) (R 5) [18,65,40,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7393 : PairBound 9 := { available := 44, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 67 133 266 28 44 108 172 300), lower := (rows 19 67 133 266 28 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 52 84 148 276), good := (rows 506 74 508 266 508 32 64 128 256) }] }

theorem u7393 : Upper (D 5) (R 5) [18,65,129,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7394 : Route 9 := (fun mask => (mask,id))

def c7394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7394 : Upper (D 5) (R 5) [18,65,129,258,36] 13 := by
  apply FastRouting.sound _ _ [18,65,129,258,36] 13 (by decide) (choices 1) [4,8] r7394 c7394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3808
  · exact u3809

def r7395 : Route 9 := (fun mask => (mask,id))

def c7395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7395 : Upper (D 5) (R 5) [18,65,129,258,40] 13 := by
  apply FastRouting.sound _ _ [18,65,129,258,40] 13 (by decide) (choices 1) [4,8] r7395 c7395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3810
  · exact u3811

def b7396 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 133 268 22 40 104 168 296), lower := (rows 19 67 133 268 22 32 64 128 256), losses := [] }

theorem u7396 : Upper (D 5) (R 5) [18,65,129,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7397 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 133 268 26 44 108 172 300), lower := (rows 19 67 133 268 26 32 64 128 256), losses := [] }

theorem u7397 : Upper (D 5) (R 5) [18,65,129,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7398 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 133 268 28 42 106 170 298), lower := (rows 19 67 133 268 28 32 64 128 256), losses := [] }

theorem u7398 : Upper (D 5) (R 5) [18,65,129,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7399 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 133 268 50 44 108 172 300), lower := (rows 19 67 133 268 50 32 64 128 256), losses := [] }

theorem u7399 : Upper (D 5) (R 5) [18,65,129,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7399
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7400 : Route 9 := (fun mask => (mask,id))

def c7400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7400 : Upper (D 5) (R 5) [18,65,129,260,36] 13 := by
  apply FastRouting.sound _ _ [18,65,129,260,36] 13 (by decide) (choices 1) [2,8] r7400 c7400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3812
  · exact u3813

def r7401 : Route 9 := (fun mask => (mask,id))

def c7401 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7401 : Upper (D 5) (R 5) [18,65,129,260,40] 13 := by
  apply FastRouting.sound _ _ [18,65,129,260,40] 13 (by decide) (choices 1) [2,4,8] r7401 c7401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3814
  · exact u3815
  · exact u3816

def b7402 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 133 296 22 44 108 172 300), lower := (rows 19 67 133 296 22 32 64 128 256), losses := [] }

theorem u7402 : Upper (D 5) (R 5) [18,65,129,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7403 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 133 296 26 44 108 172 300), lower := (rows 19 67 133 296 26 32 64 128 256), losses := [] }

theorem u7403 : Upper (D 5) (R 5) [18,65,129,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7403
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7404 : Route 9 := (fun mask => (mask,id))

def c7404 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7404 : Upper (D 5) (R 5) [18,65,129,288,12] 13 := by
  apply FastRouting.sound _ _ [18,65,129,288,12] 13 (by decide) (choices 1) [2,4,8] r7404 c7404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3817
  · exact u3818
  · exact u3819

def b7405 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 133 296 50 44 76 140 268), lower := (rows 19 67 133 296 50 32 64 128 256), losses := [] }

theorem u7405 : Upper (D 5) (R 5) [18,65,129,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7406 : Route 9 := (fun mask => (mask,id))

def c7406 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7406 : Upper (D 5) (R 5) [18,65,129,288,36] 13 := by
  apply FastRouting.sound _ _ [18,65,129,288,36] 13 (by decide) (choices 1) [2,4,8] r7406 c7406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3820
  · exact u3821
  · exact u3822

def b7407 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 133 296 56 46 78 142 270), lower := (rows 19 67 133 296 56 32 64 128 256), losses := [] }

theorem u7407 : Upper (D 5) (R 5) [18,65,129,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7408 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 134 268 21 40 104 168 296), lower := (rows 19 67 134 268 21 32 64 128 256), losses := [] }

theorem u7408 : Upper (D 5) (R 5) [18,65,130,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7409 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 134 268 25 44 108 172 300), lower := (rows 19 67 134 268 25 32 64 128 256), losses := [] }

theorem u7409 : Upper (D 5) (R 5) [18,65,130,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7409
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7410 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 134 268 28 41 105 169 297), lower := (rows 19 67 134 268 28 32 64 128 256), losses := [] }

theorem u7410 : Upper (D 5) (R 5) [18,65,130,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7410
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7411 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 134 268 49 44 108 172 300), lower := (rows 19 67 134 268 49 32 64 128 256), losses := [] }

theorem u7411 : Upper (D 5) (R 5) [18,65,130,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7411
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7412 : Route 9 := (fun mask => (mask,id))

def c7412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7412 : Upper (D 5) (R 5) [18,65,130,260,36] 13 := by
  apply FastRouting.sound _ _ [18,65,130,260,36] 13 (by decide) (choices 1) [1,8] r7412 c7412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3823
  · exact u3824

def r7413 : Route 9 := (fun mask => (mask,id))

def c7413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7413 : Upper (D 5) (R 5) [18,65,130,260,40] 13 := by
  apply FastRouting.sound _ _ [18,65,130,260,40] 13 (by decide) (choices 1) [1,4,8] r7413 c7413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3825
  · exact u3826
  · exact u3827

def b7414 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 134 296 21 44 108 172 300), lower := (rows 19 67 134 296 21 32 64 128 256), losses := [] }

theorem u7414 : Upper (D 5) (R 5) [18,65,130,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7415 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 134 296 25 44 108 172 300), lower := (rows 19 67 134 296 25 32 64 128 256), losses := [] }

theorem u7415 : Upper (D 5) (R 5) [18,65,130,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7416 : Route 9 := (fun mask => (mask,id))

def c7416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7416 : Upper (D 5) (R 5) [18,65,130,288,12] 13 := by
  apply FastRouting.sound _ _ [18,65,130,288,12] 13 (by decide) (choices 1) [1,4,8] r7416 c7416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3828
  · exact u3829
  · exact u3830

def b7417 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 134 296 49 44 76 140 268), lower := (rows 19 67 134 296 49 32 64 128 256), losses := [] }

theorem u7417 : Upper (D 5) (R 5) [18,65,130,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7417
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7418 : Route 9 := (fun mask => (mask,id))

def c7418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7418 : Upper (D 5) (R 5) [18,65,130,288,36] 13 := by
  apply FastRouting.sound _ _ [18,65,130,288,36] 13 (by decide) (choices 1) [1,4,8] r7418 c7418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3831
  · exact u3832
  · exact u3833

def b7419 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 134 296 56 45 77 141 269), lower := (rows 19 67 134 296 56 32 64 128 256), losses := [] }

theorem u7419 : Upper (D 5) (R 5) [18,65,130,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7419
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7420 : PairBound 9 := { available := 44, camps := [{ cop := 6, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 268 19 44 108 172 300), lower := (rows 19 67 140 268 19 32 64 128 256), losses := [] }

theorem u7420 : Upper (D 5) (R 5) [18,65,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7420
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7421 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 140 268 21 42 106 170 298), lower := (rows 19 67 140 268 21 32 64 128 256), losses := [] }

theorem u7421 : Upper (D 5) (R 5) [18,65,136,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7421
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7422 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 268 22 41 105 169 297), lower := (rows 19 67 140 268 22 32 64 128 256), losses := [] }

theorem u7422 : Upper (D 5) (R 5) [18,65,136,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7423 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 268 28 35 99 163 291), lower := (rows 19 67 140 268 28 32 64 128 256), losses := [] }

theorem u7423 : Upper (D 5) (R 5) [18,65,136,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7424 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 140 268 49 46 110 174 302), lower := (rows 19 67 140 268 49 32 64 128 256), losses := [] }

theorem u7424 : Upper (D 5) (R 5) [18,65,136,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7424
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7425 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 268 50 45 109 173 301), lower := (rows 19 67 140 268 50 32 64 128 256), losses := [] }

theorem u7425 : Upper (D 5) (R 5) [18,65,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7425
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7426 : Route 9 := (fun mask => (mask,id))

def c7426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7426 : Upper (D 5) (R 5) [18,65,136,260,36] 13 := by
  apply FastRouting.sound _ _ [18,65,136,260,36] 13 (by decide) (choices 1) [1,2,8] r7426 c7426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3834
  · exact u3835
  · exact u3836

def b7427 : PairBound 9 := { available := 44, camps := [{ cop := 6, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 296 19 44 108 172 300), lower := (rows 19 67 140 296 19 32 64 128 256), losses := [] }

theorem u7427 : Upper (D 5) (R 5) [18,65,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7427
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7428 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 140 296 21 46 110 174 302), lower := (rows 19 67 140 296 21 32 64 128 256), losses := [] }

theorem u7428 : Upper (D 5) (R 5) [18,65,136,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7428
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7429 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 296 22 45 109 173 301), lower := (rows 19 67 140 296 22 32 64 128 256), losses := [] }

theorem u7429 : Upper (D 5) (R 5) [18,65,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7429
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7430 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 140 296 25 38 102 166 294), lower := (rows 19 67 140 296 25 32 64 128 256), losses := [] }

theorem u7430 : Upper (D 5) (R 5) [18,65,136,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7430
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7431 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 296 26 37 101 165 293), lower := (rows 19 67 140 296 26 32 64 128 256), losses := [] }

theorem u7431 : Upper (D 5) (R 5) [18,65,136,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7431
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7432 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 140 296 28 39 103 167 295), lower := (rows 19 67 140 296 28 32 64 128 256), losses := [] }

theorem u7432 : Upper (D 5) (R 5) [18,65,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7432
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7433 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 140 296 49 46 78 142 270), lower := (rows 19 67 140 296 49 32 64 128 256), losses := [] }

theorem u7433 : Upper (D 5) (R 5) [18,65,136,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7433
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7434 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 296 50 45 77 141 269), lower := (rows 19 67 140 296 50 32 64 128 256), losses := [] }

theorem u7434 : Upper (D 5) (R 5) [18,65,136,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7435 : Route 9 := (fun mask => (mask,id))

def c7435 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7435 : Upper (D 5) (R 5) [18,65,136,288,36] 13 := by
  apply FastRouting.sound _ _ [18,65,136,288,36] 13 (by decide) (choices 1) [1,2,4,8] r7435 c7435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3837
  · exact u3838
  · exact u3839
  · exact u3840

def b7436 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 140 296 56 39 71 135 263), lower := (rows 19 67 140 296 56 32 64 128 256), losses := [] }

theorem u7436 : Upper (D 5) (R 5) [18,65,136,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7436
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7437 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 164 296 19 44 76 140 268), lower := (rows 19 67 164 296 19 32 64 128 256), losses := [] }

theorem u7437 : Upper (D 5) (R 5) [18,65,160,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7437
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7438 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 164 296 21 46 78 142 270), lower := (rows 19 67 164 296 21 32 64 128 256), losses := [] }

theorem u7438 : Upper (D 5) (R 5) [18,65,160,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7438
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7439 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 164 296 22 45 77 141 269), lower := (rows 19 67 164 296 22 32 64 128 256), losses := [] }

theorem u7439 : Upper (D 5) (R 5) [18,65,160,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7439
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7439
end Delivery.IrregularNine14.P05
