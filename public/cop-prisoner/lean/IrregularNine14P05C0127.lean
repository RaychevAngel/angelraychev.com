import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0066
import IrregularNine14P05C0067

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7620 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 268 19 40 104 168 296), lower := (rows 19 70 133 268 19 32 64 128 256), losses := [] }

theorem u7620 : Upper (D 5) (R 5) [18,68,129,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7620
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7621 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 268 25 42 106 170 298), lower := (rows 19 70 133 268 25 32 64 128 256), losses := [] }

theorem u7621 : Upper (D 5) (R 5) [18,68,129,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7622 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 133 268 26 41 105 169 297), lower := (rows 19 70 133 268 26 32 64 128 256), losses := [] }

theorem u7622 : Upper (D 5) (R 5) [18,68,129,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7622
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7623 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 268 49 42 106 170 298), lower := (rows 19 70 133 268 49 32 64 128 256), losses := [] }

theorem u7623 : Upper (D 5) (R 5) [18,68,129,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7624 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 268 50 41 105 169 297), lower := (rows 19 70 133 268 50 32 64 128 256), losses := [] }

theorem u7624 : Upper (D 5) (R 5) [18,68,129,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7624
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7625 : Route 9 := (fun mask => (mask,id))

def c7625 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7625 : Upper (D 5) (R 5) [18,68,129,260,40] 13 := by
  apply FastRouting.sound _ _ [18,68,129,260,40] 13 (by decide) (choices 1) [1,2,8] r7625 c7625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4005
  · exact u4006
  · exact u4007

def b7626 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 296 19 44 108 172 300), lower := (rows 19 70 133 296 19 32 64 128 256), losses := [] }

theorem u7626 : Upper (D 5) (R 5) [18,68,129,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7626
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7627 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 133 296 21 42 106 170 298), lower := (rows 19 70 133 296 21 32 64 128 256), losses := [] }

theorem u7627 : Upper (D 5) (R 5) [18,68,129,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7627
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7628 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 133 296 22 41 105 169 297), lower := (rows 19 70 133 296 22 32 64 128 256), losses := [] }

theorem u7628 : Upper (D 5) (R 5) [18,68,129,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7628
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7629 : PairBound 9 := { available := 46, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 296 25 46 110 174 302), lower := (rows 19 70 133 296 25 32 64 128 256), losses := [] }

theorem u7629 : Upper (D 5) (R 5) [18,68,129,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7630 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 296 26 45 109 173 301), lower := (rows 19 70 133 296 26 32 64 128 256), losses := [] }

theorem u7630 : Upper (D 5) (R 5) [18,68,129,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7631 : Route 9 := (fun mask => (mask,id))

def c7631 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7631 : Upper (D 5) (R 5) [18,68,129,288,12] 13 := by
  apply FastRouting.sound _ _ [18,68,129,288,12] 13 (by decide) (choices 1) [1,2,8] r7631 c7631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4008
  · exact u4009
  · exact u4010

def b7632 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 296 49 46 78 142 270), lower := (rows 19 70 133 296 49 32 64 128 256), losses := [] }

theorem u7632 : Upper (D 5) (R 5) [18,68,129,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7632
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7633 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 133 296 50 45 77 141 269), lower := (rows 19 70 133 296 50 32 64 128 256), losses := [] }

theorem u7633 : Upper (D 5) (R 5) [18,68,129,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7633
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7634 : Route 9 := (fun mask => (mask,id))

def c7634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7634 : Upper (D 5) (R 5) [18,68,129,288,36] 13 := by
  apply FastRouting.sound _ _ [18,68,129,288,36] 13 (by decide) (choices 1) [1,2,8] r7634 c7634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4011
  · exact u4012
  · exact u4013

def b7635 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 133 296 56 47 79 143 271), lower := (rows 19 70 133 296 56 32 64 128 256), losses := [] }

theorem u7635 : Upper (D 5) (R 5) [18,68,129,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7636 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 134 41 21 296 360 424 296), lower := (rows 19 70 134 41 21 32 64 128 256), losses := [] }

theorem u7636 : Upper (D 5) (R 5) [18,68,130,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7636
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7637 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 134 41 25 300 364 428 300), lower := (rows 19 70 134 41 25 32 64 128 256), losses := [] }

theorem u7637 : Upper (D 5) (R 5) [18,68,130,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7637
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7638 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 134 41 28 297 361 425 297), lower := (rows 19 70 134 41 28 32 64 128 256), losses := [] }

theorem u7638 : Upper (D 5) (R 5) [18,68,130,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7639 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 41 49 300 332 396 268), lower := (rows 19 70 134 41 49 32 64 128 256), losses := [] }

theorem u7639 : Upper (D 5) (R 5) [18,68,130,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7639
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7640 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 134 41 52 297 329 393 265), lower := (rows 19 70 134 41 52 32 64 128 256), losses := [] }

theorem u7640 : Upper (D 5) (R 5) [18,68,130,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7640
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7641 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 134 41 56 301 333 397 269), lower := (rows 19 70 134 41 56 32 64 128 256), losses := [] }

theorem u7641 : Upper (D 5) (R 5) [18,68,130,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7641
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7642 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 41 273 44 108 172 300), lower := (rows 19 70 134 41 273 32 64 128 256), losses := [] }

theorem u7642 : Upper (D 5) (R 5) [18,68,130,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7642
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7643 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 134 41 276 41 105 169 297), lower := (rows 19 70 134 41 276 32 64 128 256), losses := [] }

theorem u7643 : Upper (D 5) (R 5) [18,68,130,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7643
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7644 : Route 9 := (fun mask => (mask,id))

def c7644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7644 : Upper (D 5) (R 5) [18,68,130,33,264] 13 := by
  apply FastRouting.sound _ _ [18,68,130,33,264] 13 (by decide) (choices 1) [1,4,8] r7644 c7644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4014
  · exact u4015
  · exact u4016

def b7645 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 19 70 134 41 304 45 77 141 269), lower := (rows 19 70 134 41 304 32 64 128 256), losses := [] }

theorem u7645 : Upper (D 5) (R 5) [18,68,130,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7645
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7646 : Route 9 := (fun mask => (mask,id))

def c7646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7646 : Upper (D 5) (R 5) [18,68,130,36,9] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,9] 13 (by decide) (choices 1) [1,8,256] r7646 c7646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4017
  · exact u4018
  · exact u4019

def r7647 : Route 9 := (fun mask => (mask,id))

def c7647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7647 : Upper (D 5) (R 5) [18,68,130,36,33] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,33] 13 (by decide) (choices 1) [1,8,256] r7647 c7647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4020
  · exact u4021
  · exact u4022

def b7648 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 134 44 56 297 329 393 265), lower := (rows 19 70 134 44 56 32 64 128 256), losses := [] }

theorem u7648 : Upper (D 5) (R 5) [18,68,130,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7649 : Route 9 := (fun mask => (mask,id))

def c7649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7649 : Upper (D 5) (R 5) [18,68,130,36,257] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,257] 13 (by decide) (choices 1) [1,8] r7649 c7649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4023
  · exact u4024

def r7650 : Route 9 := (fun mask => (mask,id))

def c7650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7650 : Upper (D 5) (R 5) [18,68,130,36,264] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,264] 13 (by decide) (choices 1) [1,8] r7650 c7650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4025
  · exact u4026

def r7651 : Route 9 := (fun mask => (mask,id))

def c7651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7651 : Upper (D 5) (R 5) [18,68,130,36,288] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,288] 13 (by decide) (choices 1) [1,8] r7651 c7651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4027
  · exact u4028

def b7652 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 134 265 21 40 104 168 296), lower := (rows 19 70 134 265 21 32 64 128 256), losses := [] }

theorem u7652 : Upper (D 5) (R 5) [18,68,130,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7653 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 134 265 25 44 108 172 300), lower := (rows 19 70 134 265 25 32 64 128 256), losses := [] }

theorem u7653 : Upper (D 5) (R 5) [18,68,130,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7653
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7654 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 134 265 28 41 105 169 297), lower := (rows 19 70 134 265 28 32 64 128 256), losses := [] }

theorem u7654 : Upper (D 5) (R 5) [18,68,130,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7654
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7655 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 265 49 44 108 172 300), lower := (rows 19 70 134 265 49 32 64 128 256), losses := [] }

theorem u7655 : Upper (D 5) (R 5) [18,68,130,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7656 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 134 265 52 41 105 169 297), lower := (rows 19 70 134 265 52 32 64 128 256), losses := [] }

theorem u7656 : Upper (D 5) (R 5) [18,68,130,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7657 : Route 9 := (fun mask => (mask,id))

def c7657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7657 : Upper (D 5) (R 5) [18,68,130,257,40] 13 := by
  apply FastRouting.sound _ _ [18,68,130,257,40] 13 (by decide) (choices 1) [1,4,8] r7657 c7657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4029
  · exact u4030
  · exact u4031

def r7658 : Route 9 := (fun mask => (mask,id))

def c7658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7658 : Upper (D 5) (R 5) [18,68,130,260,9] 13 := by
  apply FastRouting.sound _ _ [18,68,130,260,9] 13 (by decide) (choices 1) [1,8] r7658 c7658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4032
  · exact u4033

def r7659 : Route 9 := (fun mask => (mask,id))

def c7659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7659 : Upper (D 5) (R 5) [18,68,130,260,33] 13 := by
  apply FastRouting.sound _ _ [18,68,130,260,33] 13 (by decide) (choices 1) [1,8] r7659 c7659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4034
  · exact u4035

def r7660 : Route 9 := (fun mask => (mask,id))

def c7660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7660 : Upper (D 5) (R 5) [18,68,130,260,40] 13 := by
  apply FastRouting.sound _ _ [18,68,130,260,40] 13 (by decide) (choices 1) [1,8] r7660 c7660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4036
  · exact u4037

def b7661 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 134 296 21 41 105 169 297), lower := (rows 19 70 134 296 21 32 64 128 256), losses := [] }

theorem u7661 : Upper (D 5) (R 5) [18,68,130,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7661
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7662 : Route 9 := (fun mask => (mask,id))

def c7662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7662 : Upper (D 5) (R 5) [18,68,130,288,9] 13 := by
  apply FastRouting.sound _ _ [18,68,130,288,9] 13 (by decide) (choices 1) [1,4,8] r7662 c7662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4038
  · exact u4039
  · exact u4040

def b7663 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 134 296 28 41 105 169 297), lower := (rows 19 70 134 296 28 32 64 128 256), losses := [] }

theorem u7663 : Upper (D 5) (R 5) [18,68,130,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7663
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7664 : Route 9 := (fun mask => (mask,id))

def c7664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7664 : Upper (D 5) (R 5) [18,68,130,288,33] 13 := by
  apply FastRouting.sound _ _ [18,68,130,288,33] 13 (by decide) (choices 1) [1,4,8] r7664 c7664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4041
  · exact u4042
  · exact u4043

def b7665 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 134 296 52 41 73 137 265), lower := (rows 19 70 134 296 52 32 64 128 256), losses := [] }

theorem u7665 : Upper (D 5) (R 5) [18,68,130,288,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7665
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7666 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 134 296 56 45 77 141 269), lower := (rows 19 70 134 296 56 32 64 128 256), losses := [] }

theorem u7666 : Upper (D 5) (R 5) [18,68,130,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7666
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7667 : PairBound 9 := { available := 300, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 41 19 300 364 428 300), lower := (rows 19 70 140 41 19 32 64 128 256), losses := [] }

theorem u7667 : Upper (D 5) (R 5) [18,68,136,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7667
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7668 : PairBound 9 := { available := 298, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 41 21 298 362 426 298), lower := (rows 19 70 140 41 21 32 64 128 256), losses := [] }

theorem u7668 : Upper (D 5) (R 5) [18,68,136,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7668
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7669 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 41 22 297 361 425 297), lower := (rows 19 70 140 41 22 32 64 128 256), losses := [] }

theorem u7669 : Upper (D 5) (R 5) [18,68,136,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7669
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7670 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 140 41 25 294 358 422 294), lower := (rows 19 70 140 41 25 32 64 128 256), losses := [] }

theorem u7670 : Upper (D 5) (R 5) [18,68,136,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7670
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7671 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 41 26 293 357 421 293), lower := (rows 19 70 140 41 26 32 64 128 256), losses := [] }

theorem u7671 : Upper (D 5) (R 5) [18,68,136,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7671
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7672 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 41 28 291 355 419 291), lower := (rows 19 70 140 41 28 32 64 128 256), losses := [] }

theorem u7672 : Upper (D 5) (R 5) [18,68,136,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7673 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 41 49 302 334 398 270), lower := (rows 19 70 140 41 49 32 64 128 256), losses := [] }

theorem u7673 : Upper (D 5) (R 5) [18,68,136,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7674 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 140 41 50 301 333 397 269), lower := (rows 19 70 140 41 50 32 64 128 256), losses := [] }

theorem u7674 : Upper (D 5) (R 5) [18,68,136,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7674
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7675 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 19 70 140 41 52 299 331 395 267), lower := (rows 19 70 140 41 52 32 64 128 256), losses := [] }

theorem u7675 : Upper (D 5) (R 5) [18,68,136,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7676 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 41 56 295 327 391 263), lower := (rows 19 70 140 41 56 32 64 128 256), losses := [] }

theorem u7676 : Upper (D 5) (R 5) [18,68,136,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7676
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7677 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 41 273 46 110 174 302), lower := (rows 19 70 140 41 273 32 64 128 256), losses := [] }

theorem u7677 : Upper (D 5) (R 5) [18,68,136,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7678 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 41 274 45 109 173 301), lower := (rows 19 70 140 41 274 32 64 128 256), losses := [] }

theorem u7678 : Upper (D 5) (R 5) [18,68,136,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7678
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7679 : Route 9 := (fun mask => (mask,id))

def c7679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7679 : Upper (D 5) (R 5) [18,68,136,33,260] 13 := by
  apply FastRouting.sound _ _ [18,68,136,33,260] 13 (by decide) (choices 1) [1,2,8] r7679 c7679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4044
  · exact u4045
  · exact u4046

#print axioms u7679
end Delivery.IrregularNine14.P05
