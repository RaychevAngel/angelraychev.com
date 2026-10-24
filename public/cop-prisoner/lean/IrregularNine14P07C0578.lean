import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0325
import IrregularNine14P07C0326
import IrregularNine14P07C0327

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34680 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 140 88 176 291 323 387 259), lower := (rows 35 70 140 88 176 32 64 128 256), losses := [] }

theorem u34680 : Upper (D 7) (R 7) [34,68,136,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34681 : Route 9 := (fun mask => (mask,id))

def c34681 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34681 : Upper (D 7) (R 7) [34,68,136,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,257] 13 (by decide) (choices 1) [1,2,128] r34681 c34681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19529
  · exact u19530
  · exact u19531

def r34682 : Route 9 := (fun mask => (mask,id))

def c34682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34682 : Upper (D 7) (R 7) [34,68,136,80,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,258] 13 (by decide) (choices 1) [1,128] r34682 c34682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19532
  · exact u19533

def r34683 : Route 9 := (fun mask => (mask,id))

def c34683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34683 : Upper (D 7) (R 7) [34,68,136,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,288] 13 (by decide) (choices 1) [1,2,128] r34683 c34683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19534
  · exact u19535
  · exact u19536

def b34684 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 140 88 400 35 99 163 291), lower := (rows 35 70 140 88 400 32 64 128 256), losses := [] }

theorem u34684 : Upper (D 7) (R 7) [34,68,136,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34685 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 492, targets := 2 }], pairs := [(0,6),(2,1),(3,1),(4,6)], upper := (rows 35 70 140 104 19 433 465 401 401), lower := (rows 35 70 140 104 19 32 64 128 256), losses := [] }

theorem u34685 : Upper (D 7) (R 7) [34,68,136,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34686 : Route 9 := (fun mask => (mask,id))

def c34686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34686 : Upper (D 7) (R 7) [34,68,136,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,129] 13 (by decide) (choices 1) [1,2,16,256] r34686 c34686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19537
  · exact u19538
  · exact u19539
  · exact u19540

def b34687 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 104 146 305 337 401 273), lower := (rows 35 70 140 104 146 32 64 128 256), losses := [] }

theorem u34687 : Upper (D 7) (R 7) [34,68,136,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34688 : Route 9 := (fun mask => (mask,id))

def c34688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34688 : Upper (D 7) (R 7) [34,68,136,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,257] 13 (by decide) (choices 1) [1,2,16,128] r34688 c34688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19541
  · exact u19542
  · exact u19543
  · exact u19544

def r34689 : Route 9 := (fun mask => (mask,id))

def c34689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34689 : Upper (D 7) (R 7) [34,68,136,96,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,258] 13 (by decide) (choices 1) [1,16,128] r34689 c34689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19545
  · exact u19546
  · exact u19547

def r34690 : Route 9 := (fun mask => (mask,id))

def c34690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34690 : Upper (D 7) (R 7) [34,68,136,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,384] 13 (by decide) (choices 1) [1,2,16] r34690 c34690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19548
  · exact u19549
  · exact u19550

def b34691 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 70 140 265 19 240 240 240 496), lower := (rows 35 70 140 265 19 32 64 128 256), losses := [] }

theorem u34691 : Upper (D 7) (R 7) [34,68,136,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34692 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 70 140 265 49 242 210 210 466), lower := (rows 35 70 140 265 49 32 64 128 256), losses := [] }

theorem u34692 : Upper (D 7) (R 7) [34,68,136,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34693 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 70 140 265 50 241 209 209 465), lower := (rows 35 70 140 265 50 32 64 128 256), losses := [] }

theorem u34693 : Upper (D 7) (R 7) [34,68,136,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34694 : Route 9 := (fun mask => (mask,id))

def c34694 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34694 : Upper (D 7) (R 7) [34,68,136,257,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,65] 13 (by decide) (choices 1) [2,16,128] r34694 c34694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19551
  · exact u19552
  · exact u19553

def b34695 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 140 265 82 177 241 177 433), lower := (rows 35 70 140 265 82 32 64 128 256), losses := [] }

theorem u34695 : Upper (D 7) (R 7) [34,68,136,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34696 : Route 9 := (fun mask => (mask,id))

def c34696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34696 : Upper (D 7) (R 7) [34,68,136,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,96] 13 (by decide) (choices 1) [1,2,16,128] r34696 c34696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19554
  · exact u19555
  · exact u19556
  · exact u19557

def r34697 : Route 9 := (fun mask => (mask,id))

def c34697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34697 : Upper (D 7) (R 7) [34,68,136,257,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,129] 13 (by decide) (choices 1) [2,16,64] r34697 c34697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19558
  · exact u19559
  · exact u19560

def r34698 : Route 9 := (fun mask => (mask,id))

def c34698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34698 : Upper (D 7) (R 7) [34,68,136,257,130] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,130] 13 (by decide) (choices 1) [1,16,64] r34698 c34698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19561
  · exact u19562
  · exact u19563

def r34699 : Route 9 := (fun mask => (mask,id))

def c34699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34699 : Upper (D 7) (R 7) [34,68,136,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,160] 13 (by decide) (choices 1) [1,2,16,64] r34699 c34699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19564
  · exact u19565
  · exact u19566
  · exact u19567

def r34700 : Route 9 := (fun mask => (mask,id))

def c34700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34700 : Upper (D 7) (R 7) [34,68,136,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,192] 13 (by decide) (choices 1) [1,2,16] r34700 c34700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19568
  · exact u19569
  · exact u19570

def b34701 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 70 140 266 49 241 209 209 465), lower := (rows 35 70 140 266 49 32 64 128 256), losses := [] }

theorem u34701 : Upper (D 7) (R 7) [34,68,136,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34702 : Route 9 := (fun mask => (mask,id))

def c34702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34702 : Upper (D 7) (R 7) [34,68,136,258,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,65] 13 (by decide) (choices 1) [1,16,128] r34702 c34702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19571
  · exact u19572
  · exact u19573

def r34703 : Route 9 := (fun mask => (mask,id))

def c34703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34703 : Upper (D 7) (R 7) [34,68,136,258,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,96] 13 (by decide) (choices 1) [1,16,128] r34703 c34703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19574
  · exact u19575
  · exact u19576

def r34704 : Route 9 := (fun mask => (mask,id))

def c34704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34704 : Upper (D 7) (R 7) [34,68,136,258,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,129] 13 (by decide) (choices 1) [1,16,64] r34704 c34704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19577
  · exact u19578
  · exact u19579

def r34705 : Route 9 := (fun mask => (mask,id))

def c34705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34705 : Upper (D 7) (R 7) [34,68,136,258,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,160] 13 (by decide) (choices 1) [1,16,64] r34705 c34705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19580
  · exact u19581
  · exact u19582

def r34706 : Route 9 := (fun mask => (mask,id))

def c34706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34706 : Upper (D 7) (R 7) [34,68,136,258,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,192] 13 (by decide) (choices 1) [1,16] r34706 c34706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19583
  · exact u19584

def b34707 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 70 140 280 19 225 225 225 481), lower := (rows 35 70 140 280 19 32 64 128 256), losses := [] }

theorem u34707 : Upper (D 7) (R 7) [34,68,136,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34708 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 70 140 280 49 227 195 195 451), lower := (rows 35 70 140 280 49 32 64 128 256), losses := [] }

theorem u34708 : Upper (D 7) (R 7) [34,68,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34709 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 70 140 280 50 225 193 193 449), lower := (rows 35 70 140 280 50 32 64 128 256), losses := [] }

theorem u34709 : Upper (D 7) (R 7) [34,68,136,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34710 : Route 9 := (fun mask => (mask,id))

def c34710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34710 : Upper (D 7) (R 7) [34,68,136,272,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,65] 13 (by decide) (choices 1) [1,2,128] r34710 c34710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19585
  · exact u19586
  · exact u19587

def b34711 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 140 280 82 161 225 161 417), lower := (rows 35 70 140 280 82 32 64 128 256), losses := [] }

theorem u34711 : Upper (D 7) (R 7) [34,68,136,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34712 : Route 9 := (fun mask => (mask,id))

def c34712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34712 : Upper (D 7) (R 7) [34,68,136,272,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,96] 13 (by decide) (choices 1) [1,2,128] r34712 c34712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19588
  · exact u19589
  · exact u19590

def r34713 : Route 9 := (fun mask => (mask,id))

def c34713 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34713 : Upper (D 7) (R 7) [34,68,136,272,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,129] 13 (by decide) (choices 1) [1,2,64] r34713 c34713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19591
  · exact u19592
  · exact u19593

def r34714 : Route 9 := (fun mask => (mask,id))

def c34714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34714 : Upper (D 7) (R 7) [34,68,136,272,130] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,130] 13 (by decide) (choices 1) [1,64] r34714 c34714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19594
  · exact u19595

def r34715 : Route 9 := (fun mask => (mask,id))

def c34715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34715 : Upper (D 7) (R 7) [34,68,136,272,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,160] 13 (by decide) (choices 1) [1,2,64] r34715 c34715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19596
  · exact u19597
  · exact u19598

def r34716 : Route 9 := (fun mask => (mask,id))

def c34716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34716 : Upper (D 7) (R 7) [34,68,136,272,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,192] 13 (by decide) (choices 1) [1,2] r34716 c34716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19599
  · exact u19600

def b34717 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 35 70 140 296 19 241 209 209 465), lower := (rows 35 70 140 296 19 32 64 128 256), losses := [] }

theorem u34717 : Upper (D 7) (R 7) [34,68,136,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34718 : Route 9 := (fun mask => (mask,id))

def c34718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34718 : Upper (D 7) (R 7) [34,68,136,288,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,65] 13 (by decide) (choices 1) [1,2,16,128] r34718 c34718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19601
  · exact u19602
  · exact u19603
  · exact u19604

def b34719 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 140 296 82 177 209 145 401), lower := (rows 35 70 140 296 82 32 64 128 256), losses := [] }

theorem u34719 : Upper (D 7) (R 7) [34,68,136,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34720 : Route 9 := (fun mask => (mask,id))

def c34720 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34720 : Upper (D 7) (R 7) [34,68,136,288,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,129] 13 (by decide) (choices 1) [1,2,16,64] r34720 c34720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19605
  · exact u19606
  · exact u19607
  · exact u19608

def r34721 : Route 9 := (fun mask => (mask,id))

def c34721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34721 : Upper (D 7) (R 7) [34,68,136,288,130] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,130] 13 (by decide) (choices 1) [1,16,64] r34721 c34721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19609
  · exact u19610
  · exact u19611

def r34722 : Route 9 := (fun mask => (mask,id))

def c34722 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34722 : Upper (D 7) (R 7) [34,68,136,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,192] 13 (by decide) (choices 1) [1,2,16] r34722 c34722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19612
  · exact u19613
  · exact u19614

def b34723 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 140 328 19 177 241 177 433), lower := (rows 35 70 140 328 19 32 64 128 256), losses := [] }

theorem u34723 : Upper (D 7) (R 7) [34,68,136,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34724 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 140 328 49 179 211 147 403), lower := (rows 35 70 140 328 49 32 64 128 256), losses := [] }

theorem u34724 : Upper (D 7) (R 7) [34,68,136,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34725 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 140 328 50 177 209 145 401), lower := (rows 35 70 140 328 50 32 64 128 256), losses := [] }

theorem u34725 : Upper (D 7) (R 7) [34,68,136,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34726 : Route 9 := (fun mask => (mask,id))

def c34726 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34726 : Upper (D 7) (R 7) [34,68,136,320,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,129] 13 (by decide) (choices 1) [1,2,16] r34726 c34726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19615
  · exact u19616
  · exact u19617

def b34727 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 328 146 49 113 177 305), lower := (rows 35 70 140 328 146 32 64 128 256), losses := [] }

theorem u34727 : Upper (D 7) (R 7) [34,68,136,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34728 : Route 9 := (fun mask => (mask,id))

def c34728 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34728 : Upper (D 7) (R 7) [34,68,136,320,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,160] 13 (by decide) (choices 1) [1,2,16] r34728 c34728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19618
  · exact u19619
  · exact u19620

def b34729 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 164 11 25 496 464 464 464), lower := (rows 35 70 164 11 25 32 64 128 256), losses := [] }

theorem u34729 : Upper (D 7) (R 7) [34,68,160,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34730 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 81 440 472 408 408), lower := (rows 35 70 164 11 81 32 64 128 256), losses := [] }

theorem u34730 : Upper (D 7) (R 7) [34,68,160,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34731 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 88 433 465 401 401), lower := (rows 35 70 164 11 88 32 64 128 256), losses := [] }

theorem u34731 : Upper (D 7) (R 7) [34,68,160,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34732 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 145 376 344 472 344), lower := (rows 35 70 164 11 145 32 64 128 256), losses := [] }

theorem u34732 : Upper (D 7) (R 7) [34,68,160,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34733 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 152 369 337 465 337), lower := (rows 35 70 164 11 152 32 64 128 256), losses := [] }

theorem u34733 : Upper (D 7) (R 7) [34,68,160,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34734 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 208 313 345 409 281), lower := (rows 35 70 164 11 208 32 64 128 256), losses := [] }

theorem u34734 : Upper (D 7) (R 7) [34,68,160,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34735 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 273 248 216 216 472), lower := (rows 35 70 164 11 273 32 64 128 256), losses := [] }

theorem u34735 : Upper (D 7) (R 7) [34,68,160,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34736 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 280 241 209 209 465), lower := (rows 35 70 164 11 280 32 64 128 256), losses := [] }

theorem u34736 : Upper (D 7) (R 7) [34,68,160,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34737 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 336 185 217 153 409), lower := (rows 35 70 164 11 336 32 64 128 256), losses := [] }

theorem u34737 : Upper (D 7) (R 7) [34,68,160,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34738 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 164 11 400 121 89 217 345), lower := (rows 35 70 164 11 400 32 64 128 256), losses := [] }

theorem u34738 : Upper (D 7) (R 7) [34,68,160,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34739 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 164 25 25 482 450 450 450), lower := (rows 35 70 164 25 25 32 64 128 256), losses := [] }

theorem u34739 : Upper (D 7) (R 7) [34,68,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34739
end Delivery.IrregularNine14.P07
