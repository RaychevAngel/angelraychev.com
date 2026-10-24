import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0011
import IrregularNine14P09C0012

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3660 : Route 9 := (fun mask => (mask,id))

def c3660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3660 : Upper (D 9) (R 9) [34,5,192,48,72,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,72,256] 13 (by decide) (choices 1) [1,128,256] r3660 c3660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u719
  · exact u720
  · exact u721

def b3661 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 40, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,5)], upper := (rows 35 7 196 56 273 40 448 448 448), lower := (rows 35 7 196 56 273 40 64 128 256), losses := [] }

theorem u3661 : Upper (D 9) (R 9) [34,5,192,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3661 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3662 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 196 56 273 96 456 392 392), lower := (rows 35 7 196 56 273 96 64 128 256), losses := [] }

theorem u3662 : Upper (D 9) (R 9) [34,5,192,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3662 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3663 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,0)], upper := (rows 35 7 196 56 273 288 200 200 456), lower := (rows 35 7 196 56 273 288 64 128 256), losses := [] }

theorem u3663 : Upper (D 9) (R 9) [34,5,192,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3663 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3664 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 196 56 280 33 448 448 448), lower := (rows 35 7 196 56 280 33 64 128 256), losses := [] }

theorem u3664 : Upper (D 9) (R 9) [34,5,192,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3664 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3665 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 454, targets := 32 }], pairs := [(0,7),(0,8),(1,5),(1,7),(1,8)], upper := (rows 35 7 196 56 280 96 449 385 385), lower := (rows 35 7 196 56 280 96 64 128 256), losses := [] }

theorem u3665 : Upper (D 9) (R 9) [34,5,192,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3665 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3666 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0),(4,6)], upper := (rows 35 7 196 56 280 288 193 193 449), lower := (rows 35 7 196 56 280 288 64 128 256), losses := [] }

theorem u3666 : Upper (D 9) (R 9) [34,5,192,48,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3666 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3667 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 196 56 336 33 456 392 392), lower := (rows 35 7 196 56 336 33 64 128 256), losses := [] }

theorem u3667 : Upper (D 9) (R 9) [34,5,192,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3667 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3668 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 40, targets := 449 }], pairs := [(3,0),(3,6),(3,7),(3,8)], upper := (rows 35 7 196 56 336 40 449 385 385), lower := (rows 35 7 196 56 336 40 64 128 256), losses := [] }

theorem u3668 : Upper (D 9) (R 9) [34,5,192,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3668 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3669 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 35 7 196 56 336 160 329 393 265), lower := (rows 35 7 196 56 336 160 64 128 256), losses := [] }

theorem u3669 : Upper (D 9) (R 9) [34,5,192,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3669 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3670 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 35 7 196 56 336 288 201 137 393), lower := (rows 35 7 196 56 336 288 64 128 256), losses := [] }

theorem u3670 : Upper (D 9) (R 9) [34,5,192,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3670 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3671 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 7 196 73 152 48 352 416 288), lower := (rows 35 7 196 73 152 48 64 128 256), losses := [] }

theorem u3671 : Upper (D 9) (R 9) [34,5,192,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3671 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3672 : Route 9 := (fun mask => (mask,id))

def c3672 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3672 : Upper (D 9) (R 9) [34,5,192,65,136,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,136,256] 13 (by decide) (choices 1) [16,32,256] r3672 c3672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u722
  · exact u723
  · exact u724

def b3673 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 7 196 73 176 40 336 400 272), lower := (rows 35 7 196 73 176 40 64 128 256), losses := [] }

theorem u3673 : Upper (D 9) (R 9) [34,5,192,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3673 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3674 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 7 196 73 176 48 328 392 264), lower := (rows 35 7 196 73 176 48 64 128 256), losses := [] }

theorem u3674 : Upper (D 9) (R 9) [34,5,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3674 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3675 : Route 9 := (fun mask => (mask,id))

def c3675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3675 : Upper (D 9) (R 9) [34,5,192,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,160,256] 13 (by decide) (choices 1) [8,16,256] r3675 c3675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u725
  · exact u726
  · exact u727

def r3676 : Route 9 := (fun mask => (mask,id))

def c3676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3676 : Upper (D 9) (R 9) [34,5,192,65,264,16] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,264,16] 13 (by decide) (choices 1) [32,128,256] r3676 c3676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u728
  · exact u729
  · exact u730

def b3677 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,7)], upper := (rows 35 7 196 73 280 160 368 432 304), lower := (rows 35 7 196 73 280 160 64 128 256), losses := [] }

theorem u3677 : Upper (D 9) (R 9) [34,5,192,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3677 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3678 : Route 9 := (fun mask => (mask,id))

def c3678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3678 : Upper (D 9) (R 9) [34,5,192,65,264,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,264,256] 13 (by decide) (choices 1) [16,32,128] r3678 c3678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u731
  · exact u732
  · exact u733

def b3679 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 196 73 304 40 464 400 400), lower := (rows 35 7 196 73 304 40 64 128 256), losses := [] }

theorem u3679 : Upper (D 9) (R 9) [34,5,192,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3679 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3680 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 7 196 73 304 48 456 392 392), lower := (rows 35 7 196 73 304 48 64 128 256), losses := [] }

theorem u3680 : Upper (D 9) (R 9) [34,5,192,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3680 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3681 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,7)], upper := (rows 35 7 196 73 304 160 344 408 280), lower := (rows 35 7 196 73 304 160 64 128 256), losses := [] }

theorem u3681 : Upper (D 9) (R 9) [34,5,192,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3681 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3682 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 7 196 73 304 288 216 152 408), lower := (rows 35 7 196 73 304 288 64 128 256), losses := [] }

theorem u3682 : Upper (D 9) (R 9) [34,5,192,65,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3682 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3683 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 196 73 400 40 368 432 304), lower := (rows 35 7 196 73 400 40 64 128 256), losses := [] }

theorem u3683 : Upper (D 9) (R 9) [34,5,192,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3683 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3684 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 0, region := 328, targets := 128 },{ cop := 3, region := 432, targets := 64 }], pairs := [(2,0),(3,7),(4,0),(4,6)], upper := (rows 35 7 196 73 400 48 360 424 296), lower := (rows 35 7 196 73 400 48 64 128 256), losses := [] }

theorem u3684 : Upper (D 9) (R 9) [34,5,192,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3684 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3685 : Route 9 := (fun mask => (mask,id))

def c3685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3685 : Upper (D 9) (R 9) [34,5,192,65,384,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,384,256] 13 (by decide) (choices 1) [8,16,32] r3685 c3685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u734
  · exact u735
  · exact u736

def b3686 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 4, region := 332, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 35 7 196 88 176 33 328 392 264), lower := (rows 35 7 196 88 176 33 64 128 256), losses := [] }

theorem u3686 : Upper (D 9) (R 9) [34,5,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3686 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3687 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 7 196 88 176 40 321 385 257), lower := (rows 35 7 196 88 176 40 64 128 256), losses := [] }

theorem u3687 : Upper (D 9) (R 9) [34,5,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3687 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3688 : Route 9 := (fun mask => (mask,id))

def c3688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3688 : Upper (D 9) (R 9) [34,5,192,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,160,256] 13 (by decide) (choices 1) [1,8,256] r3688 c3688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u737
  · exact u738
  · exact u739

def r3689 : Route 9 := (fun mask => (mask,id))

def c3689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3689 : Upper (D 9) (R 9) [34,5,192,80,257,8] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,257,8] 13 (by decide) (choices 1) [32,128,256] r3689 c3689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u740
  · exact u741
  · exact u742

def b3690 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 35 7 196 88 273 160 360 424 296), lower := (rows 35 7 196 88 273 160 64 128 256), losses := [] }

theorem u3690 : Upper (D 9) (R 9) [34,5,192,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3690 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3691 : Route 9 := (fun mask => (mask,id))

def c3691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3691 : Upper (D 9) (R 9) [34,5,192,80,257,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,257,256] 13 (by decide) (choices 1) [8,32,128] r3691 c3691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u743
  · exact u744
  · exact u745

def b3692 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 452, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 7 196 88 280 33 480 416 416), lower := (rows 35 7 196 88 280 33 64 128 256), losses := [] }

theorem u3692 : Upper (D 9) (R 9) [34,5,192,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3692 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3693 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 },{ cop := 2, region := 35, targets := 256 }], pairs := [(0,6),(0,8),(1,6),(3,7),(4,7)], upper := (rows 35 7 196 88 280 160 353 417 289), lower := (rows 35 7 196 88 280 160 64 128 256), losses := [] }

theorem u3693 : Upper (D 9) (R 9) [34,5,192,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3693 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3694 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,8),(1,6),(1,8),(2,8)], upper := (rows 35 7 196 88 280 288 225 161 417), lower := (rows 35 7 196 88 280 288 64 128 256), losses := [] }

theorem u3694 : Upper (D 9) (R 9) [34,5,192,80,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3694 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3695 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 196 88 304 33 456 392 392), lower := (rows 35 7 196 88 304 33 64 128 256), losses := [] }

theorem u3695 : Upper (D 9) (R 9) [34,5,192,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3695 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3696 : Route 9 := (fun mask => (mask,id))

def c3696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3696 : Upper (D 9) (R 9) [34,5,192,80,288,8] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,288,8] 13 (by decide) (choices 1) [1,128,256] r3696 c3696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u746
  · exact u747
  · exact u748

def b3697 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 35 7 196 88 304 160 329 393 265), lower := (rows 35 7 196 88 304 160 64 128 256), losses := [] }

theorem u3697 : Upper (D 9) (R 9) [34,5,192,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3697 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3698 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 7 196 88 304 288 201 137 393), lower := (rows 35 7 196 88 304 288 64 128 256), losses := [] }

theorem u3698 : Upper (D 9) (R 9) [34,5,192,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3698 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3699 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 196 88 400 33 360 424 296), lower := (rows 35 7 196 88 400 33 64 128 256), losses := [] }

theorem u3699 : Upper (D 9) (R 9) [34,5,192,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3699 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3700 : Route 9 := (fun mask => (mask,id))

def c3700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3700 : Upper (D 9) (R 9) [34,5,192,80,384,8] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,384,8] 13 (by decide) (choices 1) [1,32,256] r3700 c3700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u749
  · exact u750
  · exact u751

def r3701 : Route 9 := (fun mask => (mask,id))

def c3701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3701 : Upper (D 9) (R 9) [34,5,192,80,384,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,384,256] 13 (by decide) (choices 1) [1,8,32] r3701 c3701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u752
  · exact u753
  · exact u754

def b3702 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 196 104 273 40 464 400 400), lower := (rows 35 7 196 104 273 40 64 128 256), losses := [] }

theorem u3702 : Upper (D 9) (R 9) [34,5,192,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3702 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3703 : Route 9 := (fun mask => (mask,id))

def c3703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3703 : Upper (D 9) (R 9) [34,5,192,96,257,16] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,257,16] 13 (by decide) (choices 1) [8,128,256] r3703 c3703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u755
  · exact u756
  · exact u757

def b3704 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,7)], upper := (rows 35 7 196 104 273 160 344 408 280), lower := (rows 35 7 196 104 273 160 64 128 256), losses := [] }

theorem u3704 : Upper (D 9) (R 9) [34,5,192,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3704 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3705 : Route 9 := (fun mask => (mask,id))

def c3705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3705 : Upper (D 9) (R 9) [34,5,192,96,257,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,257,256] 13 (by decide) (choices 1) [8,16,128] r3705 c3705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u758
  · exact u759
  · exact u760

def b3706 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 7 196 104 280 33 464 400 400), lower := (rows 35 7 196 104 280 33 64 128 256), losses := [] }

theorem u3706 : Upper (D 9) (R 9) [34,5,192,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3706 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3707 : Route 9 := (fun mask => (mask,id))

def c3707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3707 : Upper (D 9) (R 9) [34,5,192,96,264,16] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,264,16] 13 (by decide) (choices 1) [1,128,256] r3707 c3707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u761
  · exact u762
  · exact u763

def b3708 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,7)], upper := (rows 35 7 196 104 280 160 337 401 273), lower := (rows 35 7 196 104 280 160 64 128 256), losses := [] }

theorem u3708 : Upper (D 9) (R 9) [34,5,192,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3708 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3709 : Route 9 := (fun mask => (mask,id))

def c3709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3709 : Upper (D 9) (R 9) [34,5,192,96,264,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,264,256] 13 (by decide) (choices 1) [1,16,128] r3709 c3709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u764
  · exact u765
  · exact u766

def b3710 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 7 196 104 400 33 344 408 280), lower := (rows 35 7 196 104 400 33 64 128 256), losses := [] }

theorem u3710 : Upper (D 9) (R 9) [34,5,192,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3710 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3711 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 196 104 400 40 337 401 273), lower := (rows 35 7 196 104 400 40 64 128 256), losses := [] }

theorem u3711 : Upper (D 9) (R 9) [34,5,192,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3711 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3712 : Route 9 := (fun mask => (mask,id))

def c3712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3712 : Upper (D 9) (R 9) [34,5,192,96,384,16] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,384,16] 13 (by decide) (choices 1) [1,8,256] r3712 c3712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u767
  · exact u768
  · exact u769

def r3713 : Route 9 := (fun mask => (mask,id))

def c3713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3713 : Upper (D 9) (R 9) [34,5,192,96,384,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,384,256] 13 (by decide) (choices 1) [1,8,16] r3713 c3713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u770
  · exact u771
  · exact u772

def b3714 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 199, targets := 256 },{ cop := 0, region := 468, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 35 7 196 265 304 40 208 208 464), lower := (rows 35 7 196 265 304 40 64 128 256), losses := [] }

theorem u3714 : Upper (D 9) (R 9) [34,5,192,257,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3714 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3715 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 7 196 265 304 48 200 200 456), lower := (rows 35 7 196 265 304 48 64 128 256), losses := [] }

theorem u3715 : Upper (D 9) (R 9) [34,5,192,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3715 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3716 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 196 265 304 96 216 152 408), lower := (rows 35 7 196 265 304 96 64 128 256), losses := [] }

theorem u3716 : Upper (D 9) (R 9) [34,5,192,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3716 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3717 : Route 9 := (fun mask => (mask,id))

def c3717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3717 : Upper (D 9) (R 9) [34,5,192,257,320,8] 13 := by
  apply FastRouting.sound _ _ [34,5,192,257,320,8] 13 (by decide) (choices 1) [16,32,128] r3717 c3717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u773
  · exact u774
  · exact u775

def r3718 : Route 9 := (fun mask => (mask,id))

def c3718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3718 : Upper (D 9) (R 9) [34,5,192,257,320,16] 13 := by
  apply FastRouting.sound _ _ [34,5,192,257,320,16] 13 (by decide) (choices 1) [8,32,128] r3718 c3718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u776
  · exact u777
  · exact u778

def b3719 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 35 7 196 265 336 160 120 184 312), lower := (rows 35 7 196 265 336 160 64 128 256), losses := [] }

theorem u3719 : Upper (D 9) (R 9) [34,5,192,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3719 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3719
end Delivery.IrregularNine14.P09
