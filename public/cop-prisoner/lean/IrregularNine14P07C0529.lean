import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0242
import IrregularNine14P07C0243

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31740 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 388 11 49 248 216 216 472), lower := (rows 7 98 388 11 49 32 64 128 256), losses := [] }

theorem u31740 : Upper (D 7) (R 7) [6,96,384,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31741 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 388 11 56 241 209 209 465), lower := (rows 7 98 388 11 56 32 64 128 256), losses := [] }

theorem u31741 : Upper (D 7) (R 7) [6,96,384,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31742 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 388 11 145 120 120 248 376), lower := (rows 7 98 388 11 145 32 64 128 256), losses := [] }

theorem u31742 : Upper (D 7) (R 7) [6,96,384,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31743 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 388 11 152 113 113 241 369), lower := (rows 7 98 388 11 152 32 64 128 256), losses := [] }

theorem u31743 : Upper (D 7) (R 7) [6,96,384,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31744 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 388 11 176 121 89 217 345), lower := (rows 7 98 388 11 176 32 64 128 256), losses := [] }

theorem u31744 : Upper (D 7) (R 7) [6,96,384,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31745 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 388 25 25 226 226 226 482), lower := (rows 7 98 388 25 25 32 64 128 256), losses := [] }

theorem u31745 : Upper (D 7) (R 7) [6,96,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31746 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 388 25 26 225 225 225 481), lower := (rows 7 98 388 25 26 32 64 128 256), losses := [] }

theorem u31746 : Upper (D 7) (R 7) [6,96,384,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31747 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 388 25 49 234 202 202 458), lower := (rows 7 98 388 25 49 32 64 128 256), losses := [] }

theorem u31747 : Upper (D 7) (R 7) [6,96,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31748 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 388 25 50 233 201 201 457), lower := (rows 7 98 388 25 50 32 64 128 256), losses := [] }

theorem u31748 : Upper (D 7) (R 7) [6,96,384,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31749 : Route 9 := (fun mask => (mask,id))

def c31749 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31749 : Upper (D 7) (R 7) [6,96,384,17,40] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,40] 13 (by decide) (choices 1) [1,2,64,128] r31749 c31749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14536
  · exact u14537
  · exact u14538
  · exact u14539

def b31750 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 388 25 112 171 203 139 395), lower := (rows 7 98 388 25 112 32 64 128 256), losses := [] }

theorem u31750 : Upper (D 7) (R 7) [6,96,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31751 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 8, targets := 98 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 388 25 145 106 106 234 362), lower := (rows 7 98 388 25 145 32 64 128 256), losses := [] }

theorem u31751 : Upper (D 7) (R 7) [6,96,384,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31752 : Route 9 := (fun mask => (mask,id))

def c31752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31752 : Upper (D 7) (R 7) [6,96,384,17,130] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,130] 13 (by decide) (choices 1) [1,8,64] r31752 c31752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14540
  · exact u14541
  · exact u14542

def r31753 : Route 9 := (fun mask => (mask,id))

def c31753 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31753 : Upper (D 7) (R 7) [6,96,384,17,136] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,136] 13 (by decide) (choices 1) [1,2,64] r31753 c31753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14543
  · exact u14544
  · exact u14545

def r31754 : Route 9 := (fun mask => (mask,id))

def c31754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31754 : Upper (D 7) (R 7) [6,96,384,17,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,160] 13 (by decide) (choices 1) [1,2,8,64] r31754 c31754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14546
  · exact u14547
  · exact u14548
  · exact u14549

def r31755 : Route 9 := (fun mask => (mask,id))

def c31755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31755 : Upper (D 7) (R 7) [6,96,384,18,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,33] 13 (by decide) (choices 1) [1,8,64,128] r31755 c31755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14550
  · exact u14551
  · exact u14552
  · exact u14553

def b31756 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 7 98 388 26 56 225 193 193 449), lower := (rows 7 98 388 26 56 32 64 128 256), losses := [] }

theorem u31756 : Upper (D 7) (R 7) [6,96,384,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31757 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 388 26 112 169 201 137 393), lower := (rows 7 98 388 26 112 32 64 128 256), losses := [] }

theorem u31757 : Upper (D 7) (R 7) [6,96,384,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31758 : Route 9 := (fun mask => (mask,id))

def c31758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31758 : Upper (D 7) (R 7) [6,96,384,18,129] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,129] 13 (by decide) (choices 1) [1,8,64] r31758 c31758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14554
  · exact u14555
  · exact u14556

def r31759 : Route 9 := (fun mask => (mask,id))

def c31759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31759 : Upper (D 7) (R 7) [6,96,384,18,136] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,136] 13 (by decide) (choices 1) [1,64] r31759 c31759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14557
  · exact u14558

def r31760 : Route 9 := (fun mask => (mask,id))

def c31760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31760 : Upper (D 7) (R 7) [6,96,384,18,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,160] 13 (by decide) (choices 1) [1,8,64] r31760 c31760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14559
  · exact u14560
  · exact u14561

def r31761 : Route 9 := (fun mask => (mask,id))

def c31761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31761 : Upper (D 7) (R 7) [6,96,384,33,65] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,65] 13 (by decide) (choices 1) [2,8,16,128] r31761 c31761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14562
  · exact u14563
  · exact u14564
  · exact u14565

def b31762 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 388 41 82 185 217 153 409), lower := (rows 7 98 388 41 82 32 64 128 256), losses := [] }

theorem u31762 : Upper (D 7) (R 7) [6,96,384,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31763 : Route 9 := (fun mask => (mask,id))

def c31763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31763 : Upper (D 7) (R 7) [6,96,384,33,72] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,72] 13 (by decide) (choices 1) [1,2,16,128] r31763 c31763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14566
  · exact u14567
  · exact u14568
  · exact u14569

def r31764 : Route 9 := (fun mask => (mask,id))

def c31764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31764 : Upper (D 7) (R 7) [6,96,384,33,129] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,129] 13 (by decide) (choices 1) [2,8,16,64] r31764 c31764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14570
  · exact u14571
  · exact u14572
  · exact u14573

def r31765 : Route 9 := (fun mask => (mask,id))

def c31765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31765 : Upper (D 7) (R 7) [6,96,384,33,130] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,130] 13 (by decide) (choices 1) [1,8,16,64] r31765 c31765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14574
  · exact u14575
  · exact u14576
  · exact u14577

def r31766 : Route 9 := (fun mask => (mask,id))

def c31766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31766 : Upper (D 7) (R 7) [6,96,384,33,136] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,136] 13 (by decide) (choices 1) [1,2,16,64] r31766 c31766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14578
  · exact u14579
  · exact u14580
  · exact u14581

def r31767 : Route 9 := (fun mask => (mask,id))

def c31767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31767 : Upper (D 7) (R 7) [6,96,384,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,192] 13 (by decide) (choices 1) [1,2,8,16] r31767 c31767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14582
  · exact u14583
  · exact u14584
  · exact u14585

def b31768 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 388 42 88 177 209 145 401), lower := (rows 7 98 388 42 88 32 64 128 256), losses := [] }

theorem u31768 : Upper (D 7) (R 7) [6,96,384,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31769 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 388 42 145 121 89 217 345), lower := (rows 7 98 388 42 145 32 64 128 256), losses := [] }

theorem u31769 : Upper (D 7) (R 7) [6,96,384,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31770 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 388 42 152 113 81 209 337), lower := (rows 7 98 388 42 152 32 64 128 256), losses := [] }

theorem u31770 : Upper (D 7) (R 7) [6,96,384,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31771 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 388 42 208 57 89 153 281), lower := (rows 7 98 388 42 208 32 64 128 256), losses := [] }

theorem u31771 : Upper (D 7) (R 7) [6,96,384,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31772 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 388 56 88 163 195 131 387), lower := (rows 7 98 388 56 88 32 64 128 256), losses := [] }

theorem u31772 : Upper (D 7) (R 7) [6,96,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31773 : Route 9 := (fun mask => (mask,id))

def c31773 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31773 : Upper (D 7) (R 7) [6,96,384,48,129] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,129] 13 (by decide) (choices 1) [1,2,8,64] r31773 c31773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14586
  · exact u14587
  · exact u14588
  · exact u14589

def r31774 : Route 9 := (fun mask => (mask,id))

def c31774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31774 : Upper (D 7) (R 7) [6,96,384,48,130] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,130] 13 (by decide) (choices 1) [1,8,64] r31774 c31774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14590
  · exact u14591
  · exact u14592

def b31775 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,5),(0,7),(1,7),(2,5)], upper := (rows 7 98 388 56 152 99 67 195 323), lower := (rows 7 98 388 56 152 32 64 128 256), losses := [] }

theorem u31775 : Upper (D 7) (R 7) [6,96,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31776 : Route 9 := (fun mask => (mask,id))

def c31776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31776 : Upper (D 7) (R 7) [6,96,384,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192] 13 (by decide) (choices 1) [1,2,8] r31776 c31776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14593
  · exact u14594
  · exact u14595

def b31777 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 388 104 145 59 91 155 283), lower := (rows 7 98 388 104 145 32 64 128 256), losses := [] }

theorem u31777 : Upper (D 7) (R 7) [6,96,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31778 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 388 104 146 57 89 153 281), lower := (rows 7 98 388 104 146 32 64 128 256), losses := [] }

theorem u31778 : Upper (D 7) (R 7) [6,96,384,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31779 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 388 104 152 51 83 147 275), lower := (rows 7 98 388 104 152 32 64 128 256), losses := [] }

theorem u31779 : Upper (D 7) (R 7) [6,96,384,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31780 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 13 56 50 224 192 192 448), lower := (rows 7 259 13 56 50 32 64 128 256), losses := [] }

theorem u31780 : Upper (D 7) (R 7) [6,257,9,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31781 : Route 9 := (fun mask => (mask,id))

def c31781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31781 : Upper (D 7) (R 7) [6,257,9,48,66] 13 := by
  apply FastRouting.sound _ _ [6,257,9,48,66] 13 (by decide) (choices 1) [64,128] r31781 c31781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14596
  · exact u14597

def b31782 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 195 }], pairs := [(3,0),(3,1),(3,6),(3,7)], upper := (rows 7 259 13 56 112 226 194 194 450), lower := (rows 7 259 13 56 112 32 64 128 256), losses := [] }

theorem u31782 : Upper (D 7) (R 7) [6,257,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31783 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31783 : Upper (D 7) (R 7) [6,257,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,257,9,48,192] 13 (by decide) (choices 1) [2,64] r31783 c31783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14598
  · exact u14599

def r31784 : Route 9 := (fun mask => (mask,id))

def c31784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31784 : Upper (D 7) (R 7) [6,257,9,96,34] 13 := by
  apply FastRouting.sound _ _ [6,257,9,96,34] 13 (by decide) (choices 1) [16,64,128] r31784 c31784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14600
  · exact u14601
  · exact u14602

def b31785 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 16, targets := 131 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,7)], upper := (rows 7 259 13 104 112 178 210 146 402), lower := (rows 7 259 13 104 112 32 64 128 256), losses := [] }

theorem u31785 : Upper (D 7) (R 7) [6,257,9,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31786 : Route 9 := (fun mask => (mask,id))

def c31786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31786 : Upper (D 7) (R 7) [6,257,9,96,130] 13 := by
  apply FastRouting.sound _ _ [6,257,9,96,130] 13 (by decide) (choices 1) [16,64,128] r31786 c31786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14603
  · exact u14604
  · exact u14605

def r31787 : Route 9 := (fun mask => (mask,id))

def c31787 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31787 : Upper (D 7) (R 7) [6,257,9,96,160] 13 := by
  apply FastRouting.sound _ _ [6,257,9,96,160] 13 (by decide) (choices 1) [2,16,64,128] r31787 c31787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14606
  · exact u14607
  · exact u14608
  · exact u14609

def b31788 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 244, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 28 11 112 224 224 224 480), lower := (rows 7 259 28 11 112 32 64 128 256), losses := [] }

theorem u31788 : Upper (D 7) (R 7) [6,257,24,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31789 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 28 41 50 224 192 192 448), lower := (rows 7 259 28 41 50 32 64 128 256), losses := [] }

theorem u31789 : Upper (D 7) (R 7) [6,257,24,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31790 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 240, targets := 1 },{ cop := 0, region := 232, targets := 2 }], pairs := [(2,0),(2,1),(3,1),(4,0)], upper := (rows 7 259 28 41 82 224 224 224 480), lower := (rows 7 259 28 41 82 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 511 511 511 511), good := (rows 502 498 508 508 498 480 480 480 480) },{ target := 1, region := (rows 1 0 20 11 16 511 511 511 511), good := (rows 493 489 508 489 508 480 480 480 480) }] }

theorem u31790 : Upper (D 7) (R 7) [6,257,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31791 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 451, targets := 32 },{ cop := 0, region := 240, targets := 1 }], pairs := [(0,5),(1,5),(2,0),(4,0)], upper := (rows 7 259 28 41 112 226 194 194 450), lower := (rows 7 259 28 41 112 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 35 67 131 259), good := (rows 502 498 28 508 112 32 64 128 256) }] }

theorem u31791 : Upper (D 7) (R 7) [6,257,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31792 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31792 : Upper (D 7) (R 7) [6,257,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,257,24,33,192] 13 (by decide) (choices 1) [2,64] r31792 c31792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14610
  · exact u14611

def b31793 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(1,5),(2,1),(4,1)], upper := (rows 7 259 28 42 112 225 193 193 449), lower := (rows 7 259 28 42 112 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 28 508 112 32 64 128 256) }] }

theorem u31793 : Upper (D 7) (R 7) [6,257,24,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31794 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31794 : Upper (D 7) (R 7) [6,257,24,34,192] 13 := by
  apply FastRouting.sound _ _ [6,257,24,34,192] 13 (by decide) (choices 1) [1,64] r31794 c31794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14612
  · exact u14613

def b31795 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 20, targets := 131 }], pairs := [(2,0),(2,1),(2,7),(4,0)], upper := (rows 7 259 28 104 112 163 195 131 387), lower := (rows 7 259 28 104 112 32 64 128 256), losses := [] }

theorem u31795 : Upper (D 7) (R 7) [6,257,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m31796_128 : Upper (D 7) (R 7) [6,257,24,96,160,128] 13 :=
  permutation_upper _ _ _ [6,257,24,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14616

def r31796 : Route 9 := (fun mask => (mask,id))

def c31796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31796 : Upper (D 7) (R 7) [6,257,24,96,160] 13 := by
  apply FastRouting.sound _ _ [6,257,24,96,160] 13 (by decide) (choices 1) [1,2,64,128] r31796 c31796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14614
  · exact u14615
  · exact u14616
  · exact m31796_128

def b31797 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5),(1,5),(3,0),(4,0)], upper := (rows 7 259 37 26 56 224 192 192 448), lower := (rows 7 259 37 26 56 32 64 128 256), losses := [] }

theorem u31797 : Upper (D 7) (R 7) [6,257,33,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31798 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 0, region := 228, targets := 2 },{ cop := 3, region := 240, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 259 37 26 88 224 224 224 480), lower := (rows 7 259 37 26 88 32 64 128 256), losses := [] }

theorem u31798 : Upper (D 7) (R 7) [6,257,33,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31799 : Route 9 := (fun mask => (mask,id))

def c31799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31799 : Upper (D 7) (R 7) [6,257,33,18,96] 13 := by
  apply FastRouting.sound _ _ [6,257,33,18,96] 13 (by decide) (choices 1) [8,64,128] r31799 c31799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14617
  · exact u14618
  · exact u14619

#print axioms u31799
end Delivery.IrregularNine14.P07
