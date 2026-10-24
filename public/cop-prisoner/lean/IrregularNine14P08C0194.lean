import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0060
import IrregularNine14P08C0061

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11640 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 44 273 248 216 216 472), lower := (rows 67 162 37 44 273 32 64 128 256), losses := [] }

theorem u11640 : Upper (D 8) (R 8) [66,160,33,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11641 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 44 280 241 209 209 465), lower := (rows 67 162 37 44 280 32 64 128 256), losses := [] }

theorem u11641 : Upper (D 8) (R 8) [66,160,33,36,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11642 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 44 336 185 217 153 409), lower := (rows 67 162 37 44 336 32 64 128 256), losses := [] }

theorem u11642 : Upper (D 8) (R 8) [66,160,33,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11643 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 44 400 121 89 217 345), lower := (rows 67 162 37 44 400 32 64 128 256), losses := [] }

theorem u11643 : Upper (D 8) (R 8) [66,160,33,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11644 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 56 81 428 460 396 396), lower := (rows 67 162 37 56 81 32 64 128 256), losses := [] }

theorem u11644 : Upper (D 8) (R 8) [66,160,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11645 : Route 9 := (fun mask => (mask,id))

def c11645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u11645 : Upper (D 8) (R 8) [66,160,33,48,68] 13 := by
  apply FastRouting.sound _ _ [66,160,33,48,68] 13 (by decide) (choices 1) [1,8,128,256] r11645 c11645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3600
  · exact u3601
  · exact u3602
  · exact u3603

def b11646 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 56 88 421 453 389 389), lower := (rows 67 162 37 56 88 32 64 128 256), losses := [] }

theorem u11646 : Upper (D 8) (R 8) [66,160,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11647 : PairBound 9 := { available := 332, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 56 145 364 332 460 332), lower := (rows 67 162 37 56 145 32 64 128 256), losses := [] }

theorem u11647 : Upper (D 8) (R 8) [66,160,33,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11648 : Route 9 := (fun mask => (mask,id))

def c11648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u11648 : Upper (D 8) (R 8) [66,160,33,48,132] 13 := by
  apply FastRouting.sound _ _ [66,160,33,48,132] 13 (by decide) (choices 1) [1,8,64,256] r11648 c11648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3604
  · exact u3605
  · exact u3606
  · exact u3607

def b11649 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 56 152 357 325 453 325), lower := (rows 67 162 37 56 152 32 64 128 256), losses := [] }

theorem u11649 : Upper (D 8) (R 8) [66,160,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11650 : Route 9 := (fun mask => (mask,id))

def c11650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11650 : Upper (D 8) (R 8) [66,160,33,48,192] 13 := by
  apply FastRouting.sound _ _ [66,160,33,48,192] 13 (by decide) (choices 1) [1,4,8,256] r11650 c11650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3608
  · exact u3609
  · exact u3610
  · exact u3611

def r11651 : Route 9 := (fun mask => (mask,id))

def c11651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11651 : Upper (D 8) (R 8) [66,160,33,48,257] 13 := by
  apply FastRouting.sound _ _ [66,160,33,48,257] 13 (by decide) (choices 1) [4,8,64,128] r11651 c11651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3612
  · exact u3613
  · exact u3614
  · exact u3615

def r11652 : Route 9 := (fun mask => (mask,id))

def c11652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11652 : Upper (D 8) (R 8) [66,160,33,48,260] 13 := by
  apply FastRouting.sound _ _ [66,160,33,48,260] 13 (by decide) (choices 1) [1,8,64,128] r11652 c11652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3616
  · exact u3617
  · exact u3618
  · exact u3619

def r11653 : Route 9 := (fun mask => (mask,id))

def c11653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11653 : Upper (D 8) (R 8) [66,160,33,48,264] 13 := by
  apply FastRouting.sound _ _ [66,160,33,48,264] 13 (by decide) (choices 1) [1,4,64,128] r11653 c11653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3620
  · exact u3621
  · exact u3622
  · exact u3623

def r11654 : Route 9 := (fun mask => (mask,id))

def c11654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11654 : Upper (D 8) (R 8) [66,160,33,48,320] 13 := by
  apply FastRouting.sound _ _ [66,160,33,48,320] 13 (by decide) (choices 1) [1,4,8,128] r11654 c11654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3624
  · exact u3625
  · exact u3626
  · exact u3627

def r11655 : Route 9 := (fun mask => (mask,id))

def c11655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11655 : Upper (D 8) (R 8) [66,160,33,48,384] 13 := by
  apply FastRouting.sound _ _ [66,160,33,48,384] 13 (by decide) (choices 1) [1,4,8,64] r11655 c11655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3628
  · exact u3629
  · exact u3630
  · exact u3631

def b11656 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 73 148 312 376 440 312), lower := (rows 67 162 37 73 148 32 64 128 256), losses := [] }

theorem u11656 : Upper (D 8) (R 8) [66,160,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11657 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 73 152 308 372 436 308), lower := (rows 67 162 37 73 152 32 64 128 256), losses := [] }

theorem u11657 : Upper (D 8) (R 8) [66,160,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11658 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 73 276 184 248 184 440), lower := (rows 67 162 37 73 276 32 64 128 256), losses := [] }

theorem u11658 : Upper (D 8) (R 8) [66,160,33,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11659 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 73 280 180 244 180 436), lower := (rows 67 162 37 73 280 32 64 128 256), losses := [] }

theorem u11659 : Upper (D 8) (R 8) [66,160,33,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11660 : PairBound 9 := { available := 156, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 73 304 188 220 156 412), lower := (rows 67 162 37 73 304 32 64 128 256), losses := [] }

theorem u11660 : Upper (D 8) (R 8) [66,160,33,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11661 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 73 400 60 124 188 316), lower := (rows 67 162 37 73 400 32 64 128 256), losses := [] }

theorem u11661 : Upper (D 8) (R 8) [66,160,33,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11662 : PairBound 9 := { available := 312, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 76 145 312 376 440 312), lower := (rows 67 162 37 76 145 32 64 128 256), losses := [] }

theorem u11662 : Upper (D 8) (R 8) [66,160,33,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11663 : Route 9 := (fun mask => (mask,id))

def c11663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11663 : Upper (D 8) (R 8) [66,160,33,68,136] 13 := by
  apply FastRouting.sound _ _ [66,160,33,68,136] 13 (by decide) (choices 1) [1,16,256] r11663 c11663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3632
  · exact u3633
  · exact u3634

def b11664 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 37 76 176 313 345 409 281), lower := (rows 67 162 37 76 176 32 64 128 256), losses := [] }

theorem u11664 : Upper (D 8) (R 8) [66,160,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11665 : Route 9 := (fun mask => (mask,id))

def c11665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11665 : Upper (D 8) (R 8) [66,160,33,68,257] 13 := by
  apply FastRouting.sound _ _ [66,160,33,68,257] 13 (by decide) (choices 1) [8,16,128] r11665 c11665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3635
  · exact u3636
  · exact u3637

def r11666 : Route 9 := (fun mask => (mask,id))

def c11666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11666 : Upper (D 8) (R 8) [66,160,33,68,264] 13 := by
  apply FastRouting.sound _ _ [66,160,33,68,264] 13 (by decide) (choices 1) [1,16,128] r11666 c11666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3638
  · exact u3639
  · exact u3640

def r11667 : Route 9 := (fun mask => (mask,id))

def c11667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11667 : Upper (D 8) (R 8) [66,160,33,68,288] 13 := by
  apply FastRouting.sound _ _ [66,160,33,68,288] 13 (by decide) (choices 1) [1,8,16,128] r11667 c11667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3641
  · exact u3642
  · exact u3643
  · exact u3644

def r11668 : Route 9 := (fun mask => (mask,id))

def c11668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11668 : Upper (D 8) (R 8) [66,160,33,68,384] 13 := by
  apply FastRouting.sound _ _ [66,160,33,68,384] 13 (by decide) (choices 1) [1,8,16] r11668 c11668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3645
  · exact u3646
  · exact u3647

def b11669 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 88 145 300 364 428 300), lower := (rows 67 162 37 88 145 32 64 128 256), losses := [] }

theorem u11669 : Upper (D 8) (R 8) [66,160,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11670 : Route 9 := (fun mask => (mask,id))

def c11670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11670 : Upper (D 8) (R 8) [66,160,33,80,132] 13 := by
  apply FastRouting.sound _ _ [66,160,33,80,132] 13 (by decide) (choices 1) [1,8,256] r11670 c11670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3648
  · exact u3649
  · exact u3650

def b11671 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 88 152 293 357 421 293), lower := (rows 67 162 37 88 152 32 64 128 256), losses := [] }

theorem u11671 : Upper (D 8) (R 8) [66,160,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11672 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 37 88 176 301 333 397 269), lower := (rows 67 162 37 88 176 32 64 128 256), losses := [] }

theorem u11672 : Upper (D 8) (R 8) [66,160,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11673 : Route 9 := (fun mask => (mask,id))

def c11673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11673 : Upper (D 8) (R 8) [66,160,33,80,257] 13 := by
  apply FastRouting.sound _ _ [66,160,33,80,257] 13 (by decide) (choices 1) [4,8,128] r11673 c11673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3651
  · exact u3652
  · exact u3653

def r11674 : Route 9 := (fun mask => (mask,id))

def c11674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11674 : Upper (D 8) (R 8) [66,160,33,80,260] 13 := by
  apply FastRouting.sound _ _ [66,160,33,80,260] 13 (by decide) (choices 1) [1,8,128] r11674 c11674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3654
  · exact u3655
  · exact u3656

def b11675 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 88 280 165 229 165 421), lower := (rows 67 162 37 88 280 32 64 128 256), losses := [] }

theorem u11675 : Upper (D 8) (R 8) [66,160,33,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11676 : Route 9 := (fun mask => (mask,id))

def c11676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11676 : Upper (D 8) (R 8) [66,160,33,80,288] 13 := by
  apply FastRouting.sound _ _ [66,160,33,80,288] 13 (by decide) (choices 1) [1,4,8,128] r11676 c11676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3657
  · exact u3658
  · exact u3659
  · exact u3660

def r11677 : Route 9 := (fun mask => (mask,id))

def c11677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11677 : Upper (D 8) (R 8) [66,160,33,80,384] 13 := by
  apply FastRouting.sound _ _ [66,160,33,80,384] 13 (by decide) (choices 1) [1,4,8] r11677 c11677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3661
  · exact u3662
  · exact u3663

def b11678 : PairBound 9 := { available := 284, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 104 145 316 348 412 284), lower := (rows 67 162 37 104 145 32 64 128 256), losses := [] }

theorem u11678 : Upper (D 8) (R 8) [66,160,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11679 : Route 9 := (fun mask => (mask,id))

def c11679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11679 : Upper (D 8) (R 8) [66,160,33,96,132] 13 := by
  apply FastRouting.sound _ _ [66,160,33,96,132] 13 (by decide) (choices 1) [1,8,16,256] r11679 c11679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3664
  · exact u3665
  · exact u3666
  · exact u3667

def r11680 : Route 9 := (fun mask => (mask,id))

def c11680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11680 : Upper (D 8) (R 8) [66,160,33,96,136] 13 := by
  apply FastRouting.sound _ _ [66,160,33,96,136] 13 (by decide) (choices 1) [1,4,16,256] r11680 c11680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3668
  · exact u3669
  · exact u3670
  · exact u3671

def r11681 : Route 9 := (fun mask => (mask,id))

def c11681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11681 : Upper (D 8) (R 8) [66,160,33,96,257] 13 := by
  apply FastRouting.sound _ _ [66,160,33,96,257] 13 (by decide) (choices 1) [4,8,16,128] r11681 c11681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3672
  · exact u3673
  · exact u3674
  · exact u3675

def r11682 : Route 9 := (fun mask => (mask,id))

def c11682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11682 : Upper (D 8) (R 8) [66,160,33,96,260] 13 := by
  apply FastRouting.sound _ _ [66,160,33,96,260] 13 (by decide) (choices 1) [1,8,16,128] r11682 c11682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3676
  · exact u3677
  · exact u3678
  · exact u3679

def r11683 : Route 9 := (fun mask => (mask,id))

def c11683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11683 : Upper (D 8) (R 8) [66,160,33,96,264] 13 := by
  apply FastRouting.sound _ _ [66,160,33,96,264] 13 (by decide) (choices 1) [1,4,16,128] r11683 c11683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3680
  · exact u3681
  · exact u3682
  · exact u3683

def r11684 : Route 9 := (fun mask => (mask,id))

def c11684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11684 : Upper (D 8) (R 8) [66,160,33,96,384] 13 := by
  apply FastRouting.sound _ _ [66,160,33,96,384] 13 (by decide) (choices 1) [1,4,8,16] r11684 c11684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3684
  · exact u3685
  · exact u3686
  · exact u3687

def b11685 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 137 276 120 120 248 376), lower := (rows 67 162 37 137 276 32 64 128 256), losses := [] }

theorem u11685 : Upper (D 8) (R 8) [66,160,33,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11686 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 137 280 116 116 244 372), lower := (rows 67 162 37 137 280 32 64 128 256), losses := [] }

theorem u11686 : Upper (D 8) (R 8) [66,160,33,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11687 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 137 304 124 92 220 348), lower := (rows 67 162 37 137 304 32 64 128 256), losses := [] }

theorem u11687 : Upper (D 8) (R 8) [66,160,33,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11688 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 137 336 60 124 188 316), lower := (rows 67 162 37 137 336 32 64 128 256), losses := [] }

theorem u11688 : Upper (D 8) (R 8) [66,160,33,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11689 : Route 9 := (fun mask => (mask,id))

def c11689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11689 : Upper (D 8) (R 8) [66,160,33,132,257] 13 := by
  apply FastRouting.sound _ _ [66,160,33,132,257] 13 (by decide) (choices 1) [8,16,64] r11689 c11689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3688
  · exact u3689
  · exact u3690

def r11690 : Route 9 := (fun mask => (mask,id))

def c11690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11690 : Upper (D 8) (R 8) [66,160,33,132,264] 13 := by
  apply FastRouting.sound _ _ [66,160,33,132,264] 13 (by decide) (choices 1) [1,16,64] r11690 c11690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3691
  · exact u3692
  · exact u3693

def r11691 : Route 9 := (fun mask => (mask,id))

def c11691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11691 : Upper (D 8) (R 8) [66,160,33,132,288] 13 := by
  apply FastRouting.sound _ _ [66,160,33,132,288] 13 (by decide) (choices 1) [1,8,16,64] r11691 c11691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3694
  · exact u3695
  · exact u3696
  · exact u3697

def r11692 : Route 9 := (fun mask => (mask,id))

def c11692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11692 : Upper (D 8) (R 8) [66,160,33,132,320] 13 := by
  apply FastRouting.sound _ _ [66,160,33,132,320] 13 (by decide) (choices 1) [1,8,16] r11692 c11692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3698
  · exact u3699
  · exact u3700

def r11693 : Route 9 := (fun mask => (mask,id))

def c11693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11693 : Upper (D 8) (R 8) [66,160,33,144,257] 13 := by
  apply FastRouting.sound _ _ [66,160,33,144,257] 13 (by decide) (choices 1) [4,8,64] r11693 c11693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3701
  · exact u3702
  · exact u3703

def r11694 : Route 9 := (fun mask => (mask,id))

def c11694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11694 : Upper (D 8) (R 8) [66,160,33,144,260] 13 := by
  apply FastRouting.sound _ _ [66,160,33,144,260] 13 (by decide) (choices 1) [1,8,64] r11694 c11694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3704
  · exact u3705
  · exact u3706

def b11695 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 152 280 101 101 229 357), lower := (rows 67 162 37 152 280 32 64 128 256), losses := [] }

theorem u11695 : Upper (D 8) (R 8) [66,160,33,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11696 : Route 9 := (fun mask => (mask,id))

def c11696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11696 : Upper (D 8) (R 8) [66,160,33,144,288] 13 := by
  apply FastRouting.sound _ _ [66,160,33,144,288] 13 (by decide) (choices 1) [1,4,8,64] r11696 c11696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3707
  · exact u3708
  · exact u3709
  · exact u3710

def r11697 : Route 9 := (fun mask => (mask,id))

def c11697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11697 : Upper (D 8) (R 8) [66,160,33,144,320] 13 := by
  apply FastRouting.sound _ _ [66,160,33,144,320] 13 (by decide) (choices 1) [1,4,8] r11697 c11697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3711
  · exact u3712
  · exact u3713

def b11698 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 168 273 124 92 220 348), lower := (rows 67 162 37 168 273 32 64 128 256), losses := [] }

theorem u11698 : Upper (D 8) (R 8) [66,160,33,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11699 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 168 276 121 89 217 345), lower := (rows 67 162 37 168 276 32 64 128 256), losses := [] }

theorem u11699 : Upper (D 8) (R 8) [66,160,33,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11699
end Delivery.IrregularNine14.P08
