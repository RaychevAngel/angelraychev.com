import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0327
import IrregularNine14P07C0328

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34740 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 164 25 26 481 449 449 449), lower := (rows 35 70 164 25 26 32 64 128 256), losses := [] }

theorem u34740 : Upper (D 7) (R 7) [34,68,160,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34741 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 164 25 81 426 458 394 394), lower := (rows 35 70 164 25 81 32 64 128 256), losses := [] }

theorem u34741 : Upper (D 7) (R 7) [34,68,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34742 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 164 25 82 425 457 393 393), lower := (rows 35 70 164 25 82 32 64 128 256), losses := [] }

theorem u34742 : Upper (D 7) (R 7) [34,68,160,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34743 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 25 88 419 451 387 387), lower := (rows 35 70 164 25 88 32 64 128 256), losses := [] }

theorem u34743 : Upper (D 7) (R 7) [34,68,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34744 : PairBound 9 := { available := 330, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 164 25 145 362 330 458 330), lower := (rows 35 70 164 25 145 32 64 128 256), losses := [] }

theorem u34744 : Upper (D 7) (R 7) [34,68,160,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34745 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 164 25 146 361 329 457 329), lower := (rows 35 70 164 25 146 32 64 128 256), losses := [] }

theorem u34745 : Upper (D 7) (R 7) [34,68,160,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34746 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 164 25 152 355 323 451 323), lower := (rows 35 70 164 25 152 32 64 128 256), losses := [] }

theorem u34746 : Upper (D 7) (R 7) [34,68,160,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34747 : Route 9 := (fun mask => (mask,id))

def c34747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34747 : Upper (D 7) (R 7) [34,68,160,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,192] 13 (by decide) (choices 1) [1,2,8,256] r34747 c34747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19621
  · exact u19622
  · exact u19623
  · exact u19624

def b34748 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 164 25 273 234 202 202 458), lower := (rows 35 70 164 25 273 32 64 128 256), losses := [] }

theorem u34748 : Upper (D 7) (R 7) [34,68,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34749 : Route 9 := (fun mask => (mask,id))

def c34749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34749 : Upper (D 7) (R 7) [34,68,160,17,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,258] 13 (by decide) (choices 1) [1,8,64,128] r34749 c34749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19625
  · exact u19626
  · exact u19627
  · exact u19628

def r34750 : Route 9 := (fun mask => (mask,id))

def c34750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34750 : Upper (D 7) (R 7) [34,68,160,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,264] 13 (by decide) (choices 1) [1,2,64,128] r34750 c34750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19629
  · exact u19630
  · exact u19631
  · exact u19632

def r34751 : Route 9 := (fun mask => (mask,id))

def c34751 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34751 : Upper (D 7) (R 7) [34,68,160,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,320] 13 (by decide) (choices 1) [1,2,8,128] r34751 c34751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19633
  · exact u19634
  · exact u19635
  · exact u19636

def r34752 : Route 9 := (fun mask => (mask,id))

def c34752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34752 : Upper (D 7) (R 7) [34,68,160,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,384] 13 (by decide) (choices 1) [1,2,8,64] r34752 c34752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19637
  · exact u19638
  · exact u19639
  · exact u19640

def b34753 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 26 81 425 457 393 393), lower := (rows 35 70 164 26 81 32 64 128 256), losses := [] }

theorem u34753 : Upper (D 7) (R 7) [34,68,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34754 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 35 70 164 26 88 417 449 385 385), lower := (rows 35 70 164 26 88 32 64 128 256), losses := [] }

theorem u34754 : Upper (D 7) (R 7) [34,68,160,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34755 : Route 9 := (fun mask => (mask,id))

def c34755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34755 : Upper (D 7) (R 7) [34,68,160,18,129] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,129] 13 (by decide) (choices 1) [1,8,64,256] r34755 c34755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19641
  · exact u19642
  · exact u19643
  · exact u19644

def b34756 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 164 26 152 353 321 449 321), lower := (rows 35 70 164 26 152 32 64 128 256), losses := [] }

theorem u34756 : Upper (D 7) (R 7) [34,68,160,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34757 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 26 208 297 329 393 265), lower := (rows 35 70 164 26 208 32 64 128 256), losses := [] }

theorem u34757 : Upper (D 7) (R 7) [34,68,160,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34758 : Route 9 := (fun mask => (mask,id))

def c34758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34758 : Upper (D 7) (R 7) [34,68,160,18,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,257] 13 (by decide) (choices 1) [1,8,64,128] r34758 c34758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19645
  · exact u19646
  · exact u19647
  · exact u19648

def r34759 : Route 9 := (fun mask => (mask,id))

def c34759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34759 : Upper (D 7) (R 7) [34,68,160,18,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,264] 13 (by decide) (choices 1) [1,64,128] r34759 c34759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19649
  · exact u19650
  · exact u19651

def b34760 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 26 336 169 201 137 393), lower := (rows 35 70 164 26 336 32 64 128 256), losses := [] }

theorem u34760 : Upper (D 7) (R 7) [34,68,160,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34761 : Route 9 := (fun mask => (mask,id))

def c34761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34761 : Upper (D 7) (R 7) [34,68,160,18,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,384] 13 (by decide) (choices 1) [1,8,64] r34761 c34761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19652
  · exact u19653
  · exact u19654

def r34762 : Route 9 := (fun mask => (mask,id))

def c34762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34762 : Upper (D 7) (R 7) [34,68,160,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,129] 13 (by decide) (choices 1) [2,8,16,256] r34762 c34762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19655
  · exact u19656
  · exact u19657
  · exact u19658

def b34763 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 164 73 146 313 345 409 281), lower := (rows 35 70 164 73 146 32 64 128 256), losses := [] }

theorem u34763 : Upper (D 7) (R 7) [34,68,160,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34764 : Route 9 := (fun mask => (mask,id))

def c34764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34764 : Upper (D 7) (R 7) [34,68,160,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,136] 13 (by decide) (choices 1) [1,2,16,256] r34764 c34764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19659
  · exact u19660
  · exact u19661
  · exact u19662

def r34765 : Route 9 := (fun mask => (mask,id))

def c34765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34765 : Upper (D 7) (R 7) [34,68,160,65,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,257] 13 (by decide) (choices 1) [2,8,16,128] r34765 c34765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19663
  · exact u19664
  · exact u19665
  · exact u19666

def r34766 : Route 9 := (fun mask => (mask,id))

def c34766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34766 : Upper (D 7) (R 7) [34,68,160,65,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,258] 13 (by decide) (choices 1) [1,8,16,128] r34766 c34766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19667
  · exact u19668
  · exact u19669
  · exact u19670

def r34767 : Route 9 := (fun mask => (mask,id))

def c34767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34767 : Upper (D 7) (R 7) [34,68,160,65,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,264] 13 (by decide) (choices 1) [1,2,16,128] r34767 c34767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19671
  · exact u19672
  · exact u19673
  · exact u19674

def r34768 : Route 9 := (fun mask => (mask,id))

def c34768 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34768 : Upper (D 7) (R 7) [34,68,160,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,384] 13 (by decide) (choices 1) [1,2,8,16] r34768 c34768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19675
  · exact u19676
  · exact u19677
  · exact u19678

def b34769 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 164 74 145 313 345 409 281), lower := (rows 35 70 164 74 145 32 64 128 256), losses := [] }

theorem u34769 : Upper (D 7) (R 7) [34,68,160,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34770 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 164 74 152 305 337 401 273), lower := (rows 35 70 164 74 152 32 64 128 256), losses := [] }

theorem u34770 : Upper (D 7) (R 7) [34,68,160,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34771 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 164 74 273 185 217 153 409), lower := (rows 35 70 164 74 273 32 64 128 256), losses := [] }

theorem u34771 : Upper (D 7) (R 7) [34,68,160,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34772 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 164 74 280 177 209 145 401), lower := (rows 35 70 164 74 280 32 64 128 256), losses := [] }

theorem u34772 : Upper (D 7) (R 7) [34,68,160,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34773 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 164 74 400 57 89 153 281), lower := (rows 35 70 164 74 400 32 64 128 256), losses := [] }

theorem u34773 : Upper (D 7) (R 7) [34,68,160,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34774 : Route 9 := (fun mask => (mask,id))

def c34774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34774 : Upper (D 7) (R 7) [34,68,160,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,129] 13 (by decide) (choices 1) [1,2,8,256] r34774 c34774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19679
  · exact u19680
  · exact u19681
  · exact u19682

def b34775 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 164 88 146 297 329 393 265), lower := (rows 35 70 164 88 146 32 64 128 256), losses := [] }

theorem u34775 : Upper (D 7) (R 7) [34,68,160,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34776 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 152 291 323 387 259), lower := (rows 35 70 164 88 152 32 64 128 256), losses := [] }

theorem u34776 : Upper (D 7) (R 7) [34,68,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34777 : Route 9 := (fun mask => (mask,id))

def c34777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34777 : Upper (D 7) (R 7) [34,68,160,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,257] 13 (by decide) (choices 1) [1,2,8,128] r34777 c34777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19683
  · exact u19684
  · exact u19685
  · exact u19686

def r34778 : Route 9 := (fun mask => (mask,id))

def c34778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34778 : Upper (D 7) (R 7) [34,68,160,80,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,258] 13 (by decide) (choices 1) [1,8,128] r34778 c34778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19687
  · exact u19688
  · exact u19689

def b34779 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 280 163 195 131 387), lower := (rows 35 70 164 88 280 32 64 128 256), losses := [] }

theorem u34779 : Upper (D 7) (R 7) [34,68,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34780 : Route 9 := (fun mask => (mask,id))

def c34780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34780 : Upper (D 7) (R 7) [34,68,160,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,384] 13 (by decide) (choices 1) [1,2,8] r34780 c34780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19690
  · exact u19691
  · exact u19692

def r34781 : Route 9 := (fun mask => (mask,id))

def c34781 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34781 : Upper (D 7) (R 7) [34,68,160,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,257] 13 (by decide) (choices 1) [2,8,16,64] r34781 c34781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19693
  · exact u19694
  · exact u19695
  · exact u19696

def r34782 : Route 9 := (fun mask => (mask,id))

def c34782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34782 : Upper (D 7) (R 7) [34,68,160,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,258] 13 (by decide) (choices 1) [1,8,16,64] r34782 c34782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19697
  · exact u19698
  · exact u19699
  · exact u19700

def r34783 : Route 9 := (fun mask => (mask,id))

def c34783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34783 : Upper (D 7) (R 7) [34,68,160,129,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,264] 13 (by decide) (choices 1) [1,2,16,64] r34783 c34783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19701
  · exact u19702
  · exact u19703
  · exact u19704

def r34784 : Route 9 := (fun mask => (mask,id))

def c34784 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34784 : Upper (D 7) (R 7) [34,68,160,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,320] 13 (by decide) (choices 1) [1,2,8,16] r34784 c34784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19705
  · exact u19706
  · exact u19707
  · exact u19708

def b34785 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 35 70 164 138 273 121 89 217 345), lower := (rows 35 70 164 138 273 32 64 128 256), losses := [] }

theorem u34785 : Upper (D 7) (R 7) [34,68,160,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34786 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 35 70 164 138 280 113 81 209 337), lower := (rows 35 70 164 138 280 32 64 128 256), losses := [] }

theorem u34786 : Upper (D 7) (R 7) [34,68,160,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34787 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 35 70 164 138 336 57 89 153 281), lower := (rows 35 70 164 138 336 32 64 128 256), losses := [] }

theorem u34787 : Upper (D 7) (R 7) [34,68,160,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34788 : Route 9 := (fun mask => (mask,id))

def c34788 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34788 : Upper (D 7) (R 7) [34,68,160,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,257] 13 (by decide) (choices 1) [1,2,8,64] r34788 c34788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19709
  · exact u19710
  · exact u19711
  · exact u19712

def r34789 : Route 9 := (fun mask => (mask,id))

def c34789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34789 : Upper (D 7) (R 7) [34,68,160,144,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,258] 13 (by decide) (choices 1) [1,8,64] r34789 c34789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19713
  · exact u19714
  · exact u19715

def b34790 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 164 152 280 99 67 195 323), lower := (rows 35 70 164 152 280 32 64 128 256), losses := [] }

theorem u34790 : Upper (D 7) (R 7) [34,68,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34791 : Route 9 := (fun mask => (mask,id))

def c34791 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34791 : Upper (D 7) (R 7) [34,68,160,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,320] 13 (by decide) (choices 1) [1,2,8] r34791 c34791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19716
  · exact u19717
  · exact u19718

def r34792 : Route 9 := (fun mask => (mask,id))

def c34792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34792 : Upper (D 7) (R 7) [34,68,160,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257] 13 (by decide) (choices 1) [1,2,8,16] r34792 c34792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19719
  · exact u19720
  · exact u19721
  · exact u19722

def r34793 : Route 9 := (fun mask => (mask,id))

def c34793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34793 : Upper (D 7) (R 7) [34,68,160,192,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,258] 13 (by decide) (choices 1) [1,8,16] r34793 c34793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19723
  · exact u19724
  · exact u19725

def r34794 : Route 9 := (fun mask => (mask,id))

def c34794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34794 : Upper (D 7) (R 7) [34,68,160,192,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,264] 13 (by decide) (choices 1) [1,2,16] r34794 c34794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19726
  · exact u19727
  · exact u19728

def b34795 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 261 11 56 240 208 208 464), lower := (rows 35 70 261 11 56 32 64 128 256), losses := [] }

theorem u34795 : Upper (D 7) (R 7) [34,68,257,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34796 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 261 11 88 176 240 176 432), lower := (rows 35 70 261 11 88 32 64 128 256), losses := [] }

theorem u34796 : Upper (D 7) (R 7) [34,68,257,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34797 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 261 11 112 184 216 152 408), lower := (rows 35 70 261 11 112 32 64 128 256), losses := [] }

theorem u34797 : Upper (D 7) (R 7) [34,68,257,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34798 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 261 11 152 240 240 240 496), lower := (rows 35 70 261 11 152 32 64 128 256), losses := [] }

theorem u34798 : Upper (D 7) (R 7) [34,68,257,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34799 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 261 11 176 248 216 216 472), lower := (rows 35 70 261 11 176 32 64 128 256), losses := [] }

theorem u34799 : Upper (D 7) (R 7) [34,68,257,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34799
end Delivery.IrregularNine14.P07
