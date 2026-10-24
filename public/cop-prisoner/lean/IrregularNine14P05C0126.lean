import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0065
import IrregularNine14P05C0066

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7560 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 44 140 26 289 353 417 289), lower := (rows 19 70 44 140 26 32 64 128 256), losses := [] }

theorem u7560 : Upper (D 5) (R 5) [18,68,40,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7560
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7561 : Route 9 := (fun mask => (mask,id))

def c7561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7561 : Upper (D 5) (R 5) [18,68,40,132,33] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,33] 13 (by decide) (choices 1) [1,2,8,256] r7561 c7561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3949
  · exact u3950
  · exact u3951
  · exact u3952

def b7562 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 140 50 297 329 393 265), lower := (rows 19 70 44 140 50 32 64 128 256), losses := [] }

theorem u7562 : Upper (D 5) (R 5) [18,68,40,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7562
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7563 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 140 56 291 323 387 259), lower := (rows 19 70 44 140 56 32 64 128 256), losses := [] }

theorem u7563 : Upper (D 5) (R 5) [18,68,40,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7564 : Route 9 := (fun mask => (mask,id))

def c7564 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7564 : Upper (D 5) (R 5) [18,68,40,132,257] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,257] 13 (by decide) (choices 1) [1,2,8] r7564 c7564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3953
  · exact u3954
  · exact u3955

def b7565 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 140 274 41 105 169 297), lower := (rows 19 70 44 140 274 32 64 128 256), losses := [] }

theorem u7565 : Upper (D 5) (R 5) [18,68,40,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7566 : Route 9 := (fun mask => (mask,id))

def c7566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7566 : Upper (D 5) (R 5) [18,68,40,132,264] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,264] 13 (by decide) (choices 1) [1,2] r7566 c7566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3956
  · exact u3957

def r7567 : Route 9 := (fun mask => (mask,id))

def c7567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7567 : Upper (D 5) (R 5) [18,68,40,132,288] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,288] 13 (by decide) (choices 1) [1,2,8] r7567 c7567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3958
  · exact u3959
  · exact u3960

def b7568 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 392 19 45 109 173 301), lower := (rows 19 70 44 392 19 32 64 128 256), losses := [] }

theorem u7568 : Upper (D 5) (R 5) [18,68,40,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7569 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 44 392 21 43 107 171 299), lower := (rows 19 70 44 392 21 32 64 128 256), losses := [] }

theorem u7569 : Upper (D 5) (R 5) [18,68,40,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7569
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7570 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 44 392 22 41 105 169 297), lower := (rows 19 70 44 392 22 32 64 128 256), losses := [] }

theorem u7570 : Upper (D 5) (R 5) [18,68,40,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7571 : Route 9 := (fun mask => (mask,id))

def c7571 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7571 : Upper (D 5) (R 5) [18,68,40,384,9] 13 := by
  apply FastRouting.sound _ _ [18,68,40,384,9] 13 (by decide) (choices 1) [1,2,4] r7571 c7571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3961
  · exact u3962
  · exact u3963

def b7572 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 392 26 37 101 165 293), lower := (rows 19 70 44 392 26 32 64 128 256), losses := [] }

theorem u7572 : Upper (D 5) (R 5) [18,68,40,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7572
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7573 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 392 28 35 99 163 291), lower := (rows 19 70 44 392 28 32 64 128 256), losses := [] }

theorem u7573 : Upper (D 5) (R 5) [18,68,40,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7573
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7574 : Route 9 := (fun mask => (mask,id))

def c7574 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7574 : Upper (D 5) (R 5) [18,68,40,384,33] 13 := by
  apply FastRouting.sound _ _ [18,68,40,384,33] 13 (by decide) (choices 1) [1,2,4,8] r7574 c7574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3964
  · exact u3965
  · exact u3966
  · exact u3967

def b7575 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 392 50 45 77 141 269), lower := (rows 19 70 44 392 50 32 64 128 256), losses := [] }

theorem u7575 : Upper (D 5) (R 5) [18,68,40,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7576 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 392 52 43 75 139 267), lower := (rows 19 70 44 392 52 32 64 128 256), losses := [] }

theorem u7576 : Upper (D 5) (R 5) [18,68,40,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7576
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7577 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 392 56 39 71 135 263), lower := (rows 19 70 44 392 56 32 64 128 256), losses := [] }

theorem u7577 : Upper (D 5) (R 5) [18,68,40,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7578 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 133 41 22 296 360 424 296), lower := (rows 19 70 133 41 22 32 64 128 256), losses := [] }

theorem u7578 : Upper (D 5) (R 5) [18,68,129,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7578
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7579 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 41 26 300 364 428 300), lower := (rows 19 70 133 41 26 32 64 128 256), losses := [] }

theorem u7579 : Upper (D 5) (R 5) [18,68,129,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7579
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7580 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 296, targets := 4 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 70 133 41 28 298 362 426 298), lower := (rows 19 70 133 41 28 32 64 128 256), losses := [] }

theorem u7580 : Upper (D 5) (R 5) [18,68,129,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7581 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 133 41 50 300 332 396 268), lower := (rows 19 70 133 41 50 32 64 128 256), losses := [] }

theorem u7581 : Upper (D 5) (R 5) [18,68,129,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7581
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7582 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 19 70 133 41 52 298 330 394 266), lower := (rows 19 70 133 41 52 32 64 128 256), losses := [] }

theorem u7582 : Upper (D 5) (R 5) [18,68,129,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7582
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7583 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 133 41 56 302 334 398 270), lower := (rows 19 70 133 41 56 32 64 128 256), losses := [] }

theorem u7583 : Upper (D 5) (R 5) [18,68,129,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7583
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7584 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 41 274 44 108 172 300), lower := (rows 19 70 133 41 274 32 64 128 256), losses := [] }

theorem u7584 : Upper (D 5) (R 5) [18,68,129,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7584
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7585 : Route 9 := (fun mask => (mask,id))

def c7585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7585 : Upper (D 5) (R 5) [18,68,129,33,260] 13 := by
  apply FastRouting.sound _ _ [18,68,129,33,260] 13 (by decide) (choices 1) [2,8] r7585 c7585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3968
  · exact u3969

def r7586 : Route 9 := (fun mask => (mask,id))

def c7586 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7586 : Upper (D 5) (R 5) [18,68,129,33,264] 13 := by
  apply FastRouting.sound _ _ [18,68,129,33,264] 13 (by decide) (choices 1) [2,4,8] r7586 c7586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3970
  · exact u3971
  · exact u3972

def b7587 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 19 70 133 41 304 46 78 142 270), lower := (rows 19 70 133 41 304 32 64 128 256), losses := [] }

theorem u7587 : Upper (D 5) (R 5) [18,68,129,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7588 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 133 42 21 296 360 424 296), lower := (rows 19 70 133 42 21 32 64 128 256), losses := [] }

theorem u7588 : Upper (D 5) (R 5) [18,68,129,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7588
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7589 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 133 42 25 300 364 428 300), lower := (rows 19 70 133 42 25 32 64 128 256), losses := [] }

theorem u7589 : Upper (D 5) (R 5) [18,68,129,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7590 : Route 9 := (fun mask => (mask,id))

def c7590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7590 : Upper (D 5) (R 5) [18,68,129,34,12] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,12] 13 (by decide) (choices 1) [1,8,256] r7590 c7590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3973
  · exact u3974
  · exact u3975

def b7591 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 42 49 300 332 396 268), lower := (rows 19 70 133 42 49 32 64 128 256), losses := [] }

theorem u7591 : Upper (D 5) (R 5) [18,68,129,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7592 : Route 9 := (fun mask => (mask,id))

def c7592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7592 : Upper (D 5) (R 5) [18,68,129,34,36] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,36] 13 (by decide) (choices 1) [1,8,256] r7592 c7592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3976
  · exact u3977
  · exact u3978

def b7593 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 133 42 56 301 333 397 269), lower := (rows 19 70 133 42 56 32 64 128 256), losses := [] }

theorem u7593 : Upper (D 5) (R 5) [18,68,129,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7594 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 42 273 44 108 172 300), lower := (rows 19 70 133 42 273 32 64 128 256), losses := [] }

theorem u7594 : Upper (D 5) (R 5) [18,68,129,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7595 : Route 9 := (fun mask => (mask,id))

def c7595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7595 : Upper (D 5) (R 5) [18,68,129,34,260] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,260] 13 (by decide) (choices 1) [1,8] r7595 c7595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3979
  · exact u3980

def r7596 : Route 9 := (fun mask => (mask,id))

def c7596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7596 : Upper (D 5) (R 5) [18,68,129,34,264] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,264] 13 (by decide) (choices 1) [1,4,8] r7596 c7596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3981
  · exact u3982
  · exact u3983

def r7597 : Route 9 := (fun mask => (mask,id))

def c7597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7597 : Upper (D 5) (R 5) [18,68,129,34,288] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,288] 13 (by decide) (choices 1) [1,4,8] r7597 c7597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3984
  · exact u3985
  · exact u3986

def b7598 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 44 19 296 360 424 296), lower := (rows 19 70 133 44 19 32 64 128 256), losses := [] }

theorem u7598 : Upper (D 5) (R 5) [18,68,129,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7599 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 44 25 298 362 426 298), lower := (rows 19 70 133 44 25 32 64 128 256), losses := [] }

theorem u7599 : Upper (D 5) (R 5) [18,68,129,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7599
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7600 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 133 44 26 297 361 425 297), lower := (rows 19 70 133 44 26 32 64 128 256), losses := [] }

theorem u7600 : Upper (D 5) (R 5) [18,68,129,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7600
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7601 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 44 49 298 330 394 266), lower := (rows 19 70 133 44 49 32 64 128 256), losses := [] }

theorem u7601 : Upper (D 5) (R 5) [18,68,129,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7601
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7602 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 44 50 297 329 393 265), lower := (rows 19 70 133 44 50 32 64 128 256), losses := [] }

theorem u7602 : Upper (D 5) (R 5) [18,68,129,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7602
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7603 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 133 44 56 299 331 395 267), lower := (rows 19 70 133 44 56 32 64 128 256), losses := [] }

theorem u7603 : Upper (D 5) (R 5) [18,68,129,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7603
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7604 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 44 273 42 106 170 298), lower := (rows 19 70 133 44 273 32 64 128 256), losses := [] }

theorem u7604 : Upper (D 5) (R 5) [18,68,129,36,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7605 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 44 274 41 105 169 297), lower := (rows 19 70 133 44 274 32 64 128 256), losses := [] }

theorem u7605 : Upper (D 5) (R 5) [18,68,129,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7605
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7606 : Route 9 := (fun mask => (mask,id))

def c7606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7606 : Upper (D 5) (R 5) [18,68,129,36,264] 13 := by
  apply FastRouting.sound _ _ [18,68,129,36,264] 13 (by decide) (choices 1) [1,2,8] r7606 c7606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3987
  · exact u3988
  · exact u3989

def r7607 : Route 9 := (fun mask => (mask,id))

def c7607 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7607 : Upper (D 5) (R 5) [18,68,129,36,288] 13 := by
  apply FastRouting.sound _ _ [18,68,129,36,288] 13 (by decide) (choices 1) [1,2,8] r7607 c7607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3990
  · exact u3991
  · exact u3992

def b7608 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 133 265 22 40 104 168 296), lower := (rows 19 70 133 265 22 32 64 128 256), losses := [] }

theorem u7608 : Upper (D 5) (R 5) [18,68,129,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7608
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7609 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 265 26 44 108 172 300), lower := (rows 19 70 133 265 26 32 64 128 256), losses := [] }

theorem u7609 : Upper (D 5) (R 5) [18,68,129,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7609
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7610 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 296, targets := 4 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 70 133 265 28 42 106 170 298), lower := (rows 19 70 133 265 28 32 64 128 256), losses := [] }

theorem u7610 : Upper (D 5) (R 5) [18,68,129,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7611 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 265 50 44 108 172 300), lower := (rows 19 70 133 265 50 32 64 128 256), losses := [] }

theorem u7611 : Upper (D 5) (R 5) [18,68,129,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7612 : Route 9 := (fun mask => (mask,id))

def c7612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7612 : Upper (D 5) (R 5) [18,68,129,257,36] 13 := by
  apply FastRouting.sound _ _ [18,68,129,257,36] 13 (by decide) (choices 1) [2,8] r7612 c7612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3993
  · exact u3994

def r7613 : Route 9 := (fun mask => (mask,id))

def c7613 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7613 : Upper (D 5) (R 5) [18,68,129,257,40] 13 := by
  apply FastRouting.sound _ _ [18,68,129,257,40] 13 (by decide) (choices 1) [2,4,8] r7613 c7613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3995
  · exact u3996
  · exact u3997

def b7614 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 133 266 21 40 104 168 296), lower := (rows 19 70 133 266 21 32 64 128 256), losses := [] }

theorem u7614 : Upper (D 5) (R 5) [18,68,129,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7614
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7615 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 133 266 25 44 108 172 300), lower := (rows 19 70 133 266 25 32 64 128 256), losses := [] }

theorem u7615 : Upper (D 5) (R 5) [18,68,129,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7615
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7616 : Route 9 := (fun mask => (mask,id))

def c7616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7616 : Upper (D 5) (R 5) [18,68,129,258,12] 13 := by
  apply FastRouting.sound _ _ [18,68,129,258,12] 13 (by decide) (choices 1) [1,8] r7616 c7616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3998
  · exact u3999

def b7617 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 266 49 44 108 172 300), lower := (rows 19 70 133 266 49 32 64 128 256), losses := [] }

theorem u7617 : Upper (D 5) (R 5) [18,68,129,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7618 : Route 9 := (fun mask => (mask,id))

def c7618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7618 : Upper (D 5) (R 5) [18,68,129,258,36] 13 := by
  apply FastRouting.sound _ _ [18,68,129,258,36] 13 (by decide) (choices 1) [1,8] r7618 c7618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4000
  · exact u4001

def r7619 : Route 9 := (fun mask => (mask,id))

def c7619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7619 : Upper (D 5) (R 5) [18,68,129,258,40] 13 := by
  apply FastRouting.sound _ _ [18,68,129,258,40] 13 (by decide) (choices 1) [1,4,8] r7619 c7619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4002
  · exact u4003
  · exact u4004

#print axioms u7619
end Delivery.IrregularNine14.P05
