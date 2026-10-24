import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0327
import IrregularNine14P06C0328
import IrregularNine14P06C0329

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35700 : Route 9 := (fun mask => (mask,id))

def c35700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35700 : Upper (D 6) (R 6) [34,65,136,5,68] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5,68] 13 (by decide) (choices 1) [2,16,256] r35700 c35700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19662
  · exact u19663
  · exact u19664

def r35701 : Route 9 := (fun mask => (mask,id))

def c35701 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35701 : Upper (D 6) (R 6) [34,65,136,5,96] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5,96] 13 (by decide) (choices 1) [2,4,16,256] r35701 c35701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19665
  · exact u19666
  · exact u19667
  · exact u19668

def r35702 : Route 9 := (fun mask => (mask,id))

def c35702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35702 : Upper (D 6) (R 6) [34,65,136,5,258] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5,258] 13 (by decide) (choices 1) [4,16,64] r35702 c35702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19669
  · exact u19670
  · exact u19671

def r35703 : Route 9 := (fun mask => (mask,id))

def c35703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35703 : Upper (D 6) (R 6) [34,65,136,5,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5,260] 13 (by decide) (choices 1) [2,16,64] r35703 c35703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19672
  · exact u19673
  · exact u19674

def r35704 : Route 9 := (fun mask => (mask,id))

def c35704 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35704 : Upper (D 6) (R 6) [34,65,136,5,288] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5,288] 13 (by decide) (choices 1) [2,4,16,64] r35704 c35704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19675
  · exact u19676
  · exact u19677
  · exact u19678

def r35705 : Route 9 := (fun mask => (mask,id))

def c35705 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35705 : Upper (D 6) (R 6) [34,65,136,5,320] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5,320] 13 (by decide) (choices 1) [2,4,16] r35705 c35705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19679
  · exact u19680
  · exact u19681

def r35706 : Route 9 := (fun mask => (mask,id))

def c35706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35706 : Upper (D 6) (R 6) [34,65,136,17,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,6] 13 (by decide) (choices 1) [4,64,256] r35706 c35706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19682
  · exact u19683
  · exact u19684

def b35707 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 67 140 25 50 356 324 452 324), lower := (rows 35 67 140 25 50 32 64 128 256), losses := [] }

theorem u35707 : Upper (D 6) (R 6) [34,65,136,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35708 : Route 9 := (fun mask => (mask,id))

def c35708 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35708 : Upper (D 6) (R 6) [34,65,136,17,36] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,36] 13 (by decide) (choices 1) [2,4,64,256] r35708 c35708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19685
  · exact u19686
  · exact u19687
  · exact u19688

def b35709 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 140 25 82 292 356 420 292), lower := (rows 35 67 140 25 82 32 64 128 256), losses := [] }

theorem u35709 : Upper (D 6) (R 6) [34,65,136,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35710 : Route 9 := (fun mask => (mask,id))

def c35710 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35710 : Upper (D 6) (R 6) [34,65,136,17,68] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,68] 13 (by decide) (choices 1) [2,4,256] r35710 c35710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19689
  · exact u19690
  · exact u19691

def b35711 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 67 140 25 112 294 326 390 262), lower := (rows 35 67 140 25 112 32 64 128 256), losses := [] }

theorem u35711 : Upper (D 6) (R 6) [34,65,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35712 : Route 9 := (fun mask => (mask,id))

def c35712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35712 : Upper (D 6) (R 6) [34,65,136,17,258] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,258] 13 (by decide) (choices 1) [4,64] r35712 c35712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19692
  · exact u19693

def r35713 : Route 9 := (fun mask => (mask,id))

def c35713 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35713 : Upper (D 6) (R 6) [34,65,136,17,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,260] 13 (by decide) (choices 1) [2,4,64] r35713 c35713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19694
  · exact u19695
  · exact u19696

def r35714 : Route 9 := (fun mask => (mask,id))

def c35714 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35714 : Upper (D 6) (R 6) [34,65,136,17,288] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,288] 13 (by decide) (choices 1) [2,4,64] r35714 c35714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19697
  · exact u19698
  · exact u19699

def r35715 : Route 9 := (fun mask => (mask,id))

def c35715 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35715 : Upper (D 6) (R 6) [34,65,136,17,320] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,320] 13 (by decide) (choices 1) [2,4] r35715 c35715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19700
  · exact u19701

def b35716 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 140 28 19 356 356 484 356), lower := (rows 35 67 140 28 19 32 64 128 256), losses := [] }

theorem u35716 : Upper (D 6) (R 6) [34,65,136,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35717 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 140 28 21 354 354 482 354), lower := (rows 35 67 140 28 21 32 64 128 256), losses := [] }

theorem u35717 : Upper (D 6) (R 6) [34,65,136,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35718 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 67 140 28 49 358 326 454 326), lower := (rows 35 67 140 28 49 32 64 128 256), losses := [] }

theorem u35718 : Upper (D 6) (R 6) [34,65,136,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35719 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 67 140 28 50 357 325 453 325), lower := (rows 35 67 140 28 50 32 64 128 256), losses := [] }

theorem u35719 : Upper (D 6) (R 6) [34,65,136,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35720 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 140 28 52 355 323 451 323), lower := (rows 35 67 140 28 52 32 64 128 256), losses := [] }

theorem u35720 : Upper (D 6) (R 6) [34,65,136,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35721 : Route 9 := (fun mask => (mask,id))

def c35721 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35721 : Upper (D 6) (R 6) [34,65,136,20,96] 13 := by
  apply FastRouting.sound _ _ [34,65,136,20,96] 13 (by decide) (choices 1) [1,2,4,256] r35721 c35721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19702
  · exact u19703
  · exact u19704
  · exact u19705

def r35722 : Route 9 := (fun mask => (mask,id))

def c35722 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35722 : Upper (D 6) (R 6) [34,65,136,20,257] 13 := by
  apply FastRouting.sound _ _ [34,65,136,20,257] 13 (by decide) (choices 1) [2,4,64] r35722 c35722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19706
  · exact u19707
  · exact u19708

def b35723 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 140 28 276 99 99 227 355), lower := (rows 35 67 140 28 276 32 64 128 256), losses := [] }

theorem u35723 : Upper (D 6) (R 6) [34,65,136,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35724 : Route 9 := (fun mask => (mask,id))

def c35724 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35724 : Upper (D 6) (R 6) [34,65,136,20,288] 13 := by
  apply FastRouting.sound _ _ [34,65,136,20,288] 13 (by decide) (choices 1) [1,2,4,64] r35724 c35724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19709
  · exact u19710
  · exact u19711
  · exact u19712

def b35725 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 140 44 19 372 340 468 340), lower := (rows 35 67 140 44 19 32 64 128 256), losses := [] }

theorem u35725 : Upper (D 6) (R 6) [34,65,136,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35726 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 355, targets := 4 },{ cop := 4, region := 322, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 140 44 21 370 338 466 338), lower := (rows 35 67 140 44 21 32 64 128 256), losses := [] }

theorem u35726 : Upper (D 6) (R 6) [34,65,136,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35727 : Route 9 := (fun mask => (mask,id))

def c35727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35727 : Upper (D 6) (R 6) [34,65,136,36,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,36,6] 13 (by decide) (choices 1) [1,16,64,256] r35727 c35727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19713
  · exact u19714
  · exact u19715
  · exact u19716

def b35728 : PairBound 9 := { available := 278, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 140 44 81 310 342 406 278), lower := (rows 35 67 140 44 81 32 64 128 256), losses := [] }

theorem u35728 : Upper (D 6) (R 6) [34,65,136,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35729 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 140 44 82 309 341 405 277), lower := (rows 35 67 140 44 82 32 64 128 256), losses := [] }

theorem u35729 : Upper (D 6) (R 6) [34,65,136,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35730 : Route 9 := (fun mask => (mask,id))

def c35730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35730 : Upper (D 6) (R 6) [34,65,136,36,68] 13 := by
  apply FastRouting.sound _ _ [34,65,136,36,68] 13 (by decide) (choices 1) [1,2,16,256] r35730 c35730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19717
  · exact u19718
  · exact u19719
  · exact u19720

def r35731 : Route 9 := (fun mask => (mask,id))

def c35731 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35731 : Upper (D 6) (R 6) [34,65,136,36,257] 13 := by
  apply FastRouting.sound _ _ [34,65,136,36,257] 13 (by decide) (choices 1) [2,4,16,64] r35731 c35731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19721
  · exact u19722
  · exact u19723
  · exact u19724

def r35732 : Route 9 := (fun mask => (mask,id))

def c35732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35732 : Upper (D 6) (R 6) [34,65,136,36,258] 13 := by
  apply FastRouting.sound _ _ [34,65,136,36,258] 13 (by decide) (choices 1) [1,4,16,64] r35732 c35732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19725
  · exact u19726
  · exact u19727
  · exact u19728

def r35733 : Route 9 := (fun mask => (mask,id))

def c35733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35733 : Upper (D 6) (R 6) [34,65,136,36,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,36,260] 13 (by decide) (choices 1) [1,2,16,64] r35733 c35733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19729
  · exact u19730
  · exact u19731
  · exact u19732

def r35734 : Route 9 := (fun mask => (mask,id))

def c35734 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35734 : Upper (D 6) (R 6) [34,65,136,36,320] 13 := by
  apply FastRouting.sound _ _ [34,65,136,36,320] 13 (by decide) (choices 1) [1,2,4,16] r35734 c35734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19733
  · exact u19734
  · exact u19735
  · exact u19736

def b35735 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 67 140 56 19 356 324 452 324), lower := (rows 35 67 140 56 19 32 64 128 256), losses := [] }

theorem u35735 : Upper (D 6) (R 6) [34,65,136,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35736 : Route 9 := (fun mask => (mask,id))

def c35736 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35736 : Upper (D 6) (R 6) [34,65,136,48,5] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,5] 13 (by decide) (choices 1) [2,4,64,256] r35736 c35736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19737
  · exact u19738
  · exact u19739
  · exact u19740

def r35737 : Route 9 := (fun mask => (mask,id))

def c35737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35737 : Upper (D 6) (R 6) [34,65,136,48,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,6] 13 (by decide) (choices 1) [1,4,64,256] r35737 c35737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19741
  · exact u19742
  · exact u19743
  · exact u19744

def b35738 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 140 56 81 294 326 390 262), lower := (rows 35 67 140 56 81 32 64 128 256), losses := [] }

theorem u35738 : Upper (D 6) (R 6) [34,65,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35739 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 140 56 82 293 325 389 261), lower := (rows 35 67 140 56 82 32 64 128 256), losses := [] }

theorem u35739 : Upper (D 6) (R 6) [34,65,136,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35740 : Route 9 := (fun mask => (mask,id))

def c35740 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35740 : Upper (D 6) (R 6) [34,65,136,48,68] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,68] 13 (by decide) (choices 1) [1,2,4,256] r35740 c35740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19745
  · exact u19746
  · exact u19747
  · exact u19748

def r35741 : Route 9 := (fun mask => (mask,id))

def c35741 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35741 : Upper (D 6) (R 6) [34,65,136,48,257] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,257] 13 (by decide) (choices 1) [2,4,64] r35741 c35741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19749
  · exact u19750
  · exact u19751

def r35742 : Route 9 := (fun mask => (mask,id))

def c35742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35742 : Upper (D 6) (R 6) [34,65,136,48,258] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,258] 13 (by decide) (choices 1) [1,4,64] r35742 c35742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19752
  · exact u19753
  · exact u19754

def r35743 : Route 9 := (fun mask => (mask,id))

def c35743 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35743 : Upper (D 6) (R 6) [34,65,136,48,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,260] 13 (by decide) (choices 1) [1,2,4,64] r35743 c35743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19755
  · exact u19756
  · exact u19757
  · exact u19758

def r35744 : Route 9 := (fun mask => (mask,id))

def c35744 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35744 : Upper (D 6) (R 6) [34,65,136,48,320] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,320] 13 (by decide) (choices 1) [1,2,4] r35744 c35744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19759
  · exact u19760
  · exact u19761

def b35745 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 140 104 19 308 340 404 276), lower := (rows 35 67 140 104 19 32 64 128 256), losses := [] }

theorem u35745 : Upper (D 6) (R 6) [34,65,136,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35746 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 3, targets := 4 },{ cop := 4, region := 322, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 140 104 21 310 342 406 278), lower := (rows 35 67 140 104 21 32 64 128 256), losses := [] }

theorem u35746 : Upper (D 6) (R 6) [34,65,136,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35747 : Route 9 := (fun mask => (mask,id))

def c35747 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35747 : Upper (D 6) (R 6) [34,65,136,96,257] 13 := by
  apply FastRouting.sound _ _ [34,65,136,96,257] 13 (by decide) (choices 1) [2,4,16] r35747 c35747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19762
  · exact u19763
  · exact u19764

def r35748 : Route 9 := (fun mask => (mask,id))

def c35748 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35748 : Upper (D 6) (R 6) [34,65,136,96,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,96,260] 13 (by decide) (choices 1) [1,2,4,16] r35748 c35748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19765
  · exact u19766
  · exact u19767
  · exact u19768

def r35749 : Route 9 := (fun mask => (mask,id))

def c35749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35749 : Upper (D 6) (R 6) [34,65,136,257,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,6] 13 (by decide) (choices 1) [4,16,64] r35749 c35749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19769
  · exact u19770
  · exact u19771

def b35750 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 67 140 265 50 116 84 212 340), lower := (rows 35 67 140 265 50 32 64 128 256), losses := [] }

theorem u35750 : Upper (D 6) (R 6) [34,65,136,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35751 : Route 9 := (fun mask => (mask,id))

def c35751 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35751 : Upper (D 6) (R 6) [34,65,136,257,36] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,36] 13 (by decide) (choices 1) [2,4,16,64] r35751 c35751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19772
  · exact u19773
  · exact u19774
  · exact u19775

def b35752 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 140 265 82 52 116 180 308), lower := (rows 35 67 140 265 82 32 64 128 256), losses := [] }

theorem u35752 : Upper (D 6) (R 6) [34,65,136,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35753 : Route 9 := (fun mask => (mask,id))

def c35753 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35753 : Upper (D 6) (R 6) [34,65,136,257,68] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,68] 13 (by decide) (choices 1) [2,4,16] r35753 c35753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19776
  · exact u19777
  · exact u19778

def r35754 : Route 9 := (fun mask => (mask,id))

def c35754 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35754 : Upper (D 6) (R 6) [34,65,136,257,96] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,96] 13 (by decide) (choices 1) [2,4,16] r35754 c35754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19779
  · exact u19780
  · exact u19781

def b35755 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 140 268 19 116 116 244 372), lower := (rows 35 67 140 268 19 32 64 128 256), losses := [] }

theorem u35755 : Upper (D 6) (R 6) [34,65,136,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35756 : Route 9 := (fun mask => (mask,id))

def c35756 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35756 : Upper (D 6) (R 6) [34,65,136,260,5] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,5] 13 (by decide) (choices 1) [2,16,64] r35756 c35756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19782
  · exact u19783
  · exact u19784

def b35757 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 67 140 268 49 118 86 214 342), lower := (rows 35 67 140 268 49 32 64 128 256), losses := [] }

theorem u35757 : Upper (D 6) (R 6) [34,65,136,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35758 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 67 140 268 50 117 85 213 341), lower := (rows 35 67 140 268 50 32 64 128 256), losses := [] }

theorem u35758 : Upper (D 6) (R 6) [34,65,136,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35759 : Route 9 := (fun mask => (mask,id))

def c35759 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35759 : Upper (D 6) (R 6) [34,65,136,260,36] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,36] 13 (by decide) (choices 1) [1,2,16,64] r35759 c35759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19785
  · exact u19786
  · exact u19787
  · exact u19788

#print axioms u35759
end Delivery.IrregularNine14.P06
