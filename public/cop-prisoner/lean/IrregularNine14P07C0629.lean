import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0409
import IrregularNine14P07C0410
import IrregularNine14P07C0411

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37740 : Route 9 := (fun mask => (mask,id))

def c37740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37740 : Upper (D 7) (R 7) [36,96,258,18,192] 13 := by
  apply FastRouting.sound _ _ [36,96,258,18,192] 13 (by decide) (choices 1) [1,8,128] r37740 c37740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24579
  · exact u24580
  · exact u24581

def r37741 : Route 9 := (fun mask => (mask,id))

def c37741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37741 : Upper (D 7) (R 7) [36,96,258,65,129] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,129] 13 (by decide) (choices 1) [2,8,16,128] r37741 c37741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24582
  · exact u24583
  · exact u24584
  · exact u24585

def r37742 : Route 9 := (fun mask => (mask,id))

def c37742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37742 : Upper (D 7) (R 7) [36,96,258,65,130] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,130] 13 (by decide) (choices 1) [1,8,16,128] r37742 c37742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24586
  · exact u24587
  · exact u24588
  · exact u24589

def r37743 : Route 9 := (fun mask => (mask,id))

def c37743 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37743 : Upper (D 7) (R 7) [36,96,258,65,136] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,136] 13 (by decide) (choices 1) [1,2,16,128] r37743 c37743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24590
  · exact u24591
  · exact u24592
  · exact u24593

def b37744 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 262 74 145 185 217 153 409), lower := (rows 37 98 262 74 145 32 64 128 256), losses := [] }

theorem u37744 : Upper (D 7) (R 7) [36,96,258,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37745 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 262 74 152 177 209 145 401), lower := (rows 37 98 262 74 152 32 64 128 256), losses := [] }

theorem u37745 : Upper (D 7) (R 7) [36,96,258,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37746 : Route 9 := (fun mask => (mask,id))

def c37746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37746 : Upper (D 7) (R 7) [36,96,258,80,129] 13 := by
  apply FastRouting.sound _ _ [36,96,258,80,129] 13 (by decide) (choices 1) [1,2,8,128] r37746 c37746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24594
  · exact u24595
  · exact u24596
  · exact u24597

def r37747 : Route 9 := (fun mask => (mask,id))

def c37747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37747 : Upper (D 7) (R 7) [36,96,258,80,130] 13 := by
  apply FastRouting.sound _ _ [36,96,258,80,130] 13 (by decide) (choices 1) [1,8,128] r37747 c37747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24598
  · exact u24599
  · exact u24600

def r37748 : Route 9 := (fun mask => (mask,id))

def c37748 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37748 : Upper (D 7) (R 7) [36,96,258,80,136] 13 := by
  apply FastRouting.sound _ _ [36,96,258,80,136] 13 (by decide) (choices 1) [1,2,128] r37748 c37748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24601
  · exact u24602
  · exact u24603

def b37749 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 98 262 137 145 122 90 218 346), lower := (rows 37 98 262 137 145 32 64 128 256), losses := [] }

theorem u37749 : Upper (D 7) (R 7) [36,96,258,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37750 : Route 9 := (fun mask => (mask,id))

def c37750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37750 : Upper (D 7) (R 7) [36,96,258,129,130] 13 := by
  apply FastRouting.sound _ _ [36,96,258,129,130] 13 (by decide) (choices 1) [1,8,16,64] r37750 c37750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24604
  · exact u24605
  · exact u24606
  · exact u24607

def b37751 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 98 262 137 152 115 83 211 339), lower := (rows 37 98 262 137 152 32 64 128 256), losses := [] }

theorem u37751 : Upper (D 7) (R 7) [36,96,258,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37752 : Route 9 := (fun mask => (mask,id))

def c37752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37752 : Upper (D 7) (R 7) [36,96,258,129,192] 13 := by
  apply FastRouting.sound _ _ [36,96,258,129,192] 13 (by decide) (choices 1) [1,2,8,16] r37752 c37752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24608
  · exact u24609
  · exact u24610
  · exact u24611

def b37753 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 98 262 138 152 113 81 209 337), lower := (rows 37 98 262 138 152 32 64 128 256), losses := [] }

theorem u37753 : Upper (D 7) (R 7) [36,96,258,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37754 : Route 9 := (fun mask => (mask,id))

def c37754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37754 : Upper (D 7) (R 7) [36,96,258,130,192] 13 := by
  apply FastRouting.sound _ _ [36,96,258,130,192] 13 (by decide) (choices 1) [1,8,16] r37754 c37754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24612
  · exact u24613
  · exact u24614

def b37755 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 262 152 152 99 67 195 323), lower := (rows 37 98 262 152 152 32 64 128 256), losses := [] }

theorem u37755 : Upper (D 7) (R 7) [36,96,258,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37756 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 262 152 208 43 75 139 267), lower := (rows 37 98 262 152 208 32 64 128 256), losses := [] }

theorem u37756 : Upper (D 7) (R 7) [36,96,258,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37757 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 98 268 11 19 240 208 208 464), lower := (rows 37 98 268 11 19 32 64 128 256), losses := [] }

theorem u37757 : Upper (D 7) (R 7) [36,96,264,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37758 : Route 9 := (fun mask => (mask,id))

def c37758 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37758 : Upper (D 7) (R 7) [36,96,264,3,65] 13 := by
  apply FastRouting.sound _ _ [36,96,264,3,65] 13 (by decide) (choices 1) [2,16,128] r37758 c37758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24615
  · exact u24616
  · exact u24617

def b37759 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 268 11 82 177 209 145 401), lower := (rows 37 98 268 11 82 32 64 128 256), losses := [] }

theorem u37759 : Upper (D 7) (R 7) [36,96,264,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37760 : Route 9 := (fun mask => (mask,id))

def c37760 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37760 : Upper (D 7) (R 7) [36,96,264,3,129] 13 := by
  apply FastRouting.sound _ _ [36,96,264,3,129] 13 (by decide) (choices 1) [2,16,64,128] r37760 c37760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24618
  · exact u24619
  · exact u24620
  · exact u24621

def r37761 : Route 9 := (fun mask => (mask,id))

def c37761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37761 : Upper (D 7) (R 7) [36,96,264,3,130] 13 := by
  apply FastRouting.sound _ _ [36,96,264,3,130] 13 (by decide) (choices 1) [1,16,64,128] r37761 c37761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24622
  · exact u24623
  · exact u24624
  · exact u24625

def r37762 : Route 9 := (fun mask => (mask,id))

def c37762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37762 : Upper (D 7) (R 7) [36,96,264,3,192] 13 := by
  apply FastRouting.sound _ _ [36,96,264,3,192] 13 (by decide) (choices 1) [1,2,16,128] r37762 c37762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24626
  · exact u24627
  · exact u24628
  · exact u24629

def b37763 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 194 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 37 98 268 25 19 226 194 194 450), lower := (rows 37 98 268 25 19 32 64 128 256), losses := [] }

theorem u37763 : Upper (D 7) (R 7) [36,96,264,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37764 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 268 25 81 162 194 130 386), lower := (rows 37 98 268 25 81 32 64 128 256), losses := [] }

theorem u37764 : Upper (D 7) (R 7) [36,96,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37765 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 268 25 82 163 195 131 387), lower := (rows 37 98 268 25 82 32 64 128 256), losses := [] }

theorem u37765 : Upper (D 7) (R 7) [36,96,264,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37766 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 268 25 145 226 194 194 450), lower := (rows 37 98 268 25 145 32 64 128 256), losses := [] }

theorem u37766 : Upper (D 7) (R 7) [36,96,264,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37767 : Route 9 := (fun mask => (mask,id))

def c37767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37767 : Upper (D 7) (R 7) [36,96,264,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,264,17,130] 13 (by decide) (choices 1) [1,2,64,128] r37767 c37767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24630
  · exact u24631
  · exact u24632
  · exact u24633

def r37768 : Route 9 := (fun mask => (mask,id))

def c37768 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37768 : Upper (D 7) (R 7) [36,96,264,17,192] 13 := by
  apply FastRouting.sound _ _ [36,96,264,17,192] 13 (by decide) (choices 1) [1,2,128] r37768 c37768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24634
  · exact u24635
  · exact u24636

def b37769 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 193 },{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 98 268 26 19 225 193 193 449), lower := (rows 37 98 268 26 19 32 64 128 256), losses := [] }

theorem u37769 : Upper (D 7) (R 7) [36,96,264,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37770 : Route 9 := (fun mask => (mask,id))

def c37770 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37770 : Upper (D 7) (R 7) [36,96,264,18,65] 13 := by
  apply FastRouting.sound _ _ [36,96,264,18,65] 13 (by decide) (choices 1) [1,2,128] r37770 c37770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24637
  · exact u24638
  · exact u24639

def b37771 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 268 26 82 161 193 129 385), lower := (rows 37 98 268 26 82 32 64 128 256), losses := [] }

theorem u37771 : Upper (D 7) (R 7) [36,96,264,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37772 : Route 9 := (fun mask => (mask,id))

def c37772 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37772 : Upper (D 7) (R 7) [36,96,264,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,264,18,129] 13 (by decide) (choices 1) [1,2,64,128] r37772 c37772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24640
  · exact u24641
  · exact u24642
  · exact u24643

def b37773 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 268 26 146 225 193 193 449), lower := (rows 37 98 268 26 146 32 64 128 256), losses := [] }

theorem u37773 : Upper (D 7) (R 7) [36,96,264,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37774 : Route 9 := (fun mask => (mask,id))

def c37774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37774 : Upper (D 7) (R 7) [36,96,264,18,192] 13 := by
  apply FastRouting.sound _ _ [36,96,264,18,192] 13 (by decide) (choices 1) [1,2,128] r37774 c37774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24644
  · exact u24645
  · exact u24646

def r37775 : Route 9 := (fun mask => (mask,id))

def c37775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37775 : Upper (D 7) (R 7) [36,96,264,65,3] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,3] 13 (by decide) (choices 1) [2,16,128] r37775 c37775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24647
  · exact u24648
  · exact u24649

def r37776 : Route 9 := (fun mask => (mask,id))

def c37776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37776 : Upper (D 7) (R 7) [36,96,264,65,129] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,129] 13 (by decide) (choices 1) [2,16,128] r37776 c37776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24650
  · exact u24651
  · exact u24652

def r37777 : Route 9 := (fun mask => (mask,id))

def c37777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37777 : Upper (D 7) (R 7) [36,96,264,65,130] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,130] 13 (by decide) (choices 1) [1,2,16,128] r37777 c37777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24653
  · exact u24654
  · exact u24655
  · exact u24656

def b37778 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(0,6),(2,5),(2,6),(3,5)], upper := (rows 37 98 268 88 19 163 195 131 387), lower := (rows 37 98 268 88 19 32 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 48 0 144 272), good := (rows 37 34 269 445 435 32 0 128 256) }] }

theorem u37778 : Upper (D 7) (R 7) [36,96,264,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37779 : Route 9 := (fun mask => (mask,id))

def c37779 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37779 : Upper (D 7) (R 7) [36,96,264,80,129] 13 := by
  apply FastRouting.sound _ _ [36,96,264,80,129] 13 (by decide) (choices 1) [1,2,128] r37779 c37779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24657
  · exact u24658
  · exact u24659

def r37780 : Route 9 := (fun mask => (mask,id))

def c37780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37780 : Upper (D 7) (R 7) [36,96,264,80,130] 13 := by
  apply FastRouting.sound _ _ [36,96,264,80,130] 13 (by decide) (choices 1) [1,2,128] r37780 c37780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24660
  · exact u24661
  · exact u24662

def r37781 : Route 9 := (fun mask => (mask,id))

def c37781 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37781 : Upper (D 7) (R 7) [36,96,264,129,3] 13 := by
  apply FastRouting.sound _ _ [36,96,264,129,3] 13 (by decide) (choices 1) [2,16,64,128] r37781 c37781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24663
  · exact u24664
  · exact u24665
  · exact u24666

def r37782 : Route 9 := (fun mask => (mask,id))

def c37782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37782 : Upper (D 7) (R 7) [36,96,264,129,65] 13 := by
  apply FastRouting.sound _ _ [36,96,264,129,65] 13 (by decide) (choices 1) [2,16,128] r37782 c37782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24667
  · exact u24668
  · exact u24669

def b37783 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 268 137 82 179 211 147 403), lower := (rows 37 98 268 137 82 32 64 128 256), losses := [] }

theorem u37783 : Upper (D 7) (R 7) [36,96,264,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37784 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 98 268 137 145 114 82 210 338), lower := (rows 37 98 268 137 145 32 64 128 256), losses := [] }

theorem u37784 : Upper (D 7) (R 7) [36,96,264,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37785 : Route 9 := (fun mask => (mask,id))

def c37785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37785 : Upper (D 7) (R 7) [36,96,264,129,130] 13 := by
  apply FastRouting.sound _ _ [36,96,264,129,130] 13 (by decide) (choices 1) [1,2,16,64] r37785 c37785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24670
  · exact u24671
  · exact u24672
  · exact u24673

def r37786 : Route 9 := (fun mask => (mask,id))

def c37786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37786 : Upper (D 7) (R 7) [36,96,264,129,192] 13 := by
  apply FastRouting.sound _ _ [36,96,264,129,192] 13 (by decide) (choices 1) [1,2,16] r37786 c37786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24674
  · exact u24675
  · exact u24676

def r37787 : Route 9 := (fun mask => (mask,id))

def c37787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37787 : Upper (D 7) (R 7) [36,96,264,130,3] 13 := by
  apply FastRouting.sound _ _ [36,96,264,130,3] 13 (by decide) (choices 1) [1,16,64,128] r37787 c37787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24677
  · exact u24678
  · exact u24679
  · exact u24680

def r37788 : Route 9 := (fun mask => (mask,id))

def c37788 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37788 : Upper (D 7) (R 7) [36,96,264,130,65] 13 := by
  apply FastRouting.sound _ _ [36,96,264,130,65] 13 (by decide) (choices 1) [1,2,16,128] r37788 c37788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24681
  · exact u24682
  · exact u24683
  · exact u24684

def b37789 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 268 138 82 177 209 145 401), lower := (rows 37 98 268 138 82 32 64 128 256), losses := [] }

theorem u37789 : Upper (D 7) (R 7) [36,96,264,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37790 : Route 9 := (fun mask => (mask,id))

def c37790 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37790 : Upper (D 7) (R 7) [36,96,264,130,129] 13 := by
  apply FastRouting.sound _ _ [36,96,264,130,129] 13 (by decide) (choices 1) [1,2,16,64] r37790 c37790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24685
  · exact u24686
  · exact u24687
  · exact u24688

def b37791 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 98 268 138 146 113 81 209 337), lower := (rows 37 98 268 138 146 32 64 128 256), losses := [] }

theorem u37791 : Upper (D 7) (R 7) [36,96,264,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37792 : Route 9 := (fun mask => (mask,id))

def c37792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37792 : Upper (D 7) (R 7) [36,96,264,130,192] 13 := by
  apply FastRouting.sound _ _ [36,96,264,130,192] 13 (by decide) (choices 1) [1,2,16] r37792 c37792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24689
  · exact u24690
  · exact u24691

def r37793 : Route 9 := (fun mask => (mask,id))

def c37793 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37793 : Upper (D 7) (R 7) [36,96,264,144,3] 13 := by
  apply FastRouting.sound _ _ [36,96,264,144,3] 13 (by decide) (choices 1) [1,2,64,128] r37793 c37793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24692
  · exact u24693
  · exact u24694
  · exact u24695

def r37794 : Route 9 := (fun mask => (mask,id))

def c37794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37794 : Upper (D 7) (R 7) [36,96,264,144,65] 13 := by
  apply FastRouting.sound _ _ [36,96,264,144,65] 13 (by decide) (choices 1) [1,2,128] r37794 c37794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24696
  · exact u24697
  · exact u24698

def b37795 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 268 152 82 163 195 131 387), lower := (rows 37 98 268 152 82 32 64 128 256), losses := [] }

theorem u37795 : Upper (D 7) (R 7) [36,96,264,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37796 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 268 152 145 99 67 195 323), lower := (rows 37 98 268 152 145 32 64 128 256), losses := [] }

theorem u37796 : Upper (D 7) (R 7) [36,96,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37797 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 268 152 146 99 67 195 323), lower := (rows 37 98 268 152 146 32 64 128 256), losses := [] }

theorem u37797 : Upper (D 7) (R 7) [36,96,264,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37798 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 268 152 208 35 67 131 259), lower := (rows 37 98 268 152 208 32 64 128 256), losses := [] }

theorem u37798 : Upper (D 7) (R 7) [36,96,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37799 : Route 9 := (fun mask => (mask,id))

def c37799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37799 : Upper (D 7) (R 7) [36,96,264,192,3] 13 := by
  apply FastRouting.sound _ _ [36,96,264,192,3] 13 (by decide) (choices 1) [1,2,16,128] r37799 c37799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24699
  · exact u24700
  · exact u24701
  · exact u24702

#print axioms u37799
end Delivery.IrregularNine14.P07
