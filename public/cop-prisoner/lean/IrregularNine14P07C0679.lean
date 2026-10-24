import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0494
import IrregularNine14P07C0495

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40740 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 14 152 148 99 67 195 323), lower := (rows 97 290 14 152 148 32 64 128 256), losses := [] }

theorem u40740 : Upper (D 7) (R 7) [96,288,10,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40741 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 14 152 208 39 71 135 263), lower := (rows 97 290 14 152 208 32 64 128 256), losses := [] }

theorem u40741 : Upper (D 7) (R 7) [96,288,10,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40742 : Route 9 := (fun mask => (mask,id))

def c40742 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40742 : Upper (D 7) (R 7) [96,288,10,192,129] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,129] 13 (by decide) (choices 1) [1,2,4,16] r40742 c40742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29672
  · exact u29673
  · exact u29674
  · exact u29675

def r40743 : Route 9 := (fun mask => (mask,id))

def c40743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40743 : Upper (D 7) (R 7) [96,288,10,192,130] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,130] 13 (by decide) (choices 1) [1,4,16] r40743 c40743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29676
  · exact u29677
  · exact u29678

def r40744 : Route 9 := (fun mask => (mask,id))

def c40744 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40744 : Upper (D 7) (R 7) [96,288,10,192,132] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,132] 13 (by decide) (choices 1) [1,2,16] r40744 c40744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29679
  · exact u29680
  · exact u29681

def b40745 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 28 73 145 166 198 134 390), lower := (rows 97 290 28 73 145 32 64 128 256), losses := [] }

theorem u40745 : Upper (D 7) (R 7) [96,288,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40746 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 28 73 146 167 199 135 391), lower := (rows 97 290 28 73 146 32 64 128 256), losses := [] }

theorem u40746 : Upper (D 7) (R 7) [96,288,24,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40747 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 28 73 148 163 195 131 387), lower := (rows 97 290 28 73 148 32 64 128 256), losses := [] }

theorem u40747 : Upper (D 7) (R 7) [96,288,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40748 : Route 9 := (fun mask => (mask,id))

def c40748 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40748 : Upper (D 7) (R 7) [96,288,24,66,129] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,129] 13 (by decide) (choices 1) [1,2,4,128] r40748 c40748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29682
  · exact u29683
  · exact u29684
  · exact u29685

def r40749 : Route 9 := (fun mask => (mask,id))

def c40749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40749 : Upper (D 7) (R 7) [96,288,24,66,130] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,130] 13 (by decide) (choices 1) [1,4,128] r40749 c40749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29686
  · exact u29687
  · exact u29688

def r40750 : Route 9 := (fun mask => (mask,id))

def c40750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40750 : Upper (D 7) (R 7) [96,288,24,66,132] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,132] 13 (by decide) (choices 1) [1,2,128] r40750 c40750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29689
  · exact u29690
  · exact u29691

def r40751 : Route 9 := (fun mask => (mask,id))

def c40751 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40751 : Upper (D 7) (R 7) [96,288,24,68,129] 13 := by
  apply FastRouting.sound _ _ [96,288,24,68,129] 13 (by decide) (choices 1) [1,2,128] r40751 c40751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29692
  · exact u29693
  · exact u29694

def r40752 : Route 9 := (fun mask => (mask,id))

def c40752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40752 : Upper (D 7) (R 7) [96,288,24,68,130] 13 := by
  apply FastRouting.sound _ _ [96,288,24,68,130] 13 (by decide) (choices 1) [1,2,128] r40752 c40752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29695
  · exact u29696
  · exact u29697

def b40753 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 97 290 28 137 145 102 70 198 326), lower := (rows 97 290 28 137 145 32 64 128 256), losses := [] }

theorem u40753 : Upper (D 7) (R 7) [96,288,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40754 : Route 9 := (fun mask => (mask,id))

def c40754 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40754 : Upper (D 7) (R 7) [96,288,24,129,130] 13 := by
  apply FastRouting.sound _ _ [96,288,24,129,130] 13 (by decide) (choices 1) [1,2,4,64] r40754 c40754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29698
  · exact u29699
  · exact u29700
  · exact u29701

def b40755 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 20, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 290 28 137 148 99 67 195 323), lower := (rows 97 290 28 137 148 32 64 128 256), losses := [] }

theorem u40755 : Upper (D 7) (R 7) [96,288,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40756 : Route 9 := (fun mask => (mask,id))

def c40756 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40756 : Upper (D 7) (R 7) [96,288,24,129,192] 13 := by
  apply FastRouting.sound _ _ [96,288,24,129,192] 13 (by decide) (choices 1) [1,2,4] r40756 c40756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29702
  · exact u29703
  · exact u29704

def b40757 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 290 28 138 146 101 69 197 325), lower := (rows 97 290 28 138 146 32 64 128 256), losses := [] }

theorem u40757 : Upper (D 7) (R 7) [96,288,24,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40758 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 20, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 290 28 138 148 99 67 195 323), lower := (rows 97 290 28 138 148 32 64 128 256), losses := [] }

theorem u40758 : Upper (D 7) (R 7) [96,288,24,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40759 : Route 9 := (fun mask => (mask,id))

def c40759 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40759 : Upper (D 7) (R 7) [96,288,24,130,192] 13 := by
  apply FastRouting.sound _ _ [96,288,24,130,192] 13 (by decide) (choices 1) [1,2,4] r40759 c40759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29705
  · exact u29706
  · exact u29707

def b40760 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 12, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 290 28 140 208 35 67 131 259), lower := (rows 97 290 28 140 208 32 64 128 256), losses := [] }

theorem u40760 : Upper (D 7) (R 7) [96,288,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40761 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 290 69 137 146 62 94 158 286), lower := (rows 97 290 69 137 146 32 64 128 256), losses := [] }

theorem u40761 : Upper (D 7) (R 7) [96,288,65,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40762 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 290 69 137 148 58 90 154 282), lower := (rows 97 290 69 137 148 32 64 128 256), losses := [] }

theorem u40762 : Upper (D 7) (R 7) [96,288,65,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40763 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 290 69 138 148 59 91 155 283), lower := (rows 97 290 69 138 148 32 64 128 256), losses := [] }

theorem u40763 : Upper (D 7) (R 7) [96,288,65,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40764 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 97 290 70 137 145 62 94 158 286), lower := (rows 97 290 70 137 145 32 64 128 256), losses := [] }

theorem u40764 : Upper (D 7) (R 7) [96,288,66,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40765 : Route 9 := (fun mask => (mask,id))

def c40765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40765 : Upper (D 7) (R 7) [96,288,66,129,130] 13 := by
  apply FastRouting.sound _ _ [96,288,66,129,130] 13 (by decide) (choices 1) [1,4,8,16] r40765 c40765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29708
  · exact u29709
  · exact u29710
  · exact u29711

def r40766 : Route 9 := (fun mask => (mask,id))

def c40766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40766 : Upper (D 7) (R 7) [96,288,66,129,132] 13 := by
  apply FastRouting.sound _ _ [96,288,66,129,132] 13 (by decide) (choices 1) [1,2,8,16] r40766 c40766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29712
  · exact u29713
  · exact u29714
  · exact u29715

def b40767 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 290 70 137 152 55 87 151 279), lower := (rows 97 290 70 137 152 32 64 128 256), losses := [] }

theorem u40767 : Upper (D 7) (R 7) [96,288,66,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40768 : Route 9 := (fun mask => (mask,id))

def c40768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40768 : Upper (D 7) (R 7) [96,288,66,130,132] 13 := by
  apply FastRouting.sound _ _ [96,288,66,130,132] 13 (by decide) (choices 1) [1,8,16] r40768 c40768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29716
  · exact u29717
  · exact u29718

def b40769 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 290 70 138 152 53 85 149 277), lower := (rows 97 290 70 138 152 32 64 128 256), losses := [] }

theorem u40769 : Upper (D 7) (R 7) [96,288,66,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40770 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 290 70 140 152 51 83 147 275), lower := (rows 97 290 70 140 152 32 64 128 256), losses := [] }

theorem u40770 : Upper (D 7) (R 7) [96,288,66,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40771 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 70 152 152 39 71 135 263), lower := (rows 97 290 70 152 152 32 64 128 256), losses := [] }

theorem u40771 : Upper (D 7) (R 7) [96,288,66,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40772 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 97 290 76 137 145 54 86 150 278), lower := (rows 97 290 76 137 145 32 64 128 256), losses := [] }

theorem u40772 : Upper (D 7) (R 7) [96,288,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40773 : Route 9 := (fun mask => (mask,id))

def c40773 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40773 : Upper (D 7) (R 7) [96,288,72,129,130] 13 := by
  apply FastRouting.sound _ _ [96,288,72,129,130] 13 (by decide) (choices 1) [1,2,4,16] r40773 c40773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29719
  · exact u29720
  · exact u29721
  · exact u29722

def r40774 : Route 9 := (fun mask => (mask,id))

def c40774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40774 : Upper (D 7) (R 7) [96,288,72,129,132] 13 := by
  apply FastRouting.sound _ _ [96,288,72,129,132] 13 (by decide) (choices 1) [1,2,16] r40774 c40774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29723
  · exact u29724
  · exact u29725

def r40775 : Route 9 := (fun mask => (mask,id))

def c40775 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40775 : Upper (D 7) (R 7) [96,288,72,130,129] 13 := by
  apply FastRouting.sound _ _ [96,288,72,130,129] 13 (by decide) (choices 1) [1,2,4,16] r40775 c40775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29726
  · exact u29727
  · exact u29728
  · exact u29729

def b40776 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 97 290 76 138 146 53 85 149 277), lower := (rows 97 290 76 138 146 32 64 128 256), losses := [] }

theorem u40776 : Upper (D 7) (R 7) [96,288,72,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40777 : Route 9 := (fun mask => (mask,id))

def c40777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40777 : Upper (D 7) (R 7) [96,288,72,130,132] 13 := by
  apply FastRouting.sound _ _ [96,288,72,130,132] 13 (by decide) (choices 1) [1,2,16] r40777 c40777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29730
  · exact u29731
  · exact u29732

def b40778 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(1,7),(4,6)], upper := (rows 97 290 76 140 145 51 83 147 275), lower := (rows 97 290 76 140 145 32 64 128 256), losses := [] }

theorem u40778 : Upper (D 7) (R 7) [96,288,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40779 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(1,7),(4,6)], upper := (rows 97 290 76 140 146 51 83 147 275), lower := (rows 97 290 76 140 146 32 64 128 256), losses := [] }

theorem u40779 : Upper (D 7) (R 7) [96,288,72,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40780 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 76 152 145 39 71 135 263), lower := (rows 97 290 76 152 145 32 64 128 256), losses := [] }

theorem u40780 : Upper (D 7) (R 7) [96,288,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40781 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 76 152 146 39 71 135 263), lower := (rows 97 290 76 152 146 32 64 128 256), losses := [] }

theorem u40781 : Upper (D 7) (R 7) [96,288,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40782 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 76 152 148 35 67 131 259), lower := (rows 97 290 76 152 148 32 64 128 256), losses := [] }

theorem u40782 : Upper (D 7) (R 7) [96,288,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40783 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 386 7 11 28 240 240 240 496), lower := (rows 97 386 7 11 28 32 64 128 256), losses := [] }

theorem u40783 : Upper (D 7) (R 7) [96,384,3,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40784 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 11 52 248 216 216 472), lower := (rows 97 386 7 11 52 32 64 128 256), losses := [] }

theorem u40784 : Upper (D 7) (R 7) [96,384,3,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40785 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 11 148 120 120 248 376), lower := (rows 97 386 7 11 148 32 64 128 256), losses := [] }

theorem u40785 : Upper (D 7) (R 7) [96,384,3,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40786 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 11 176 124 92 220 348), lower := (rows 97 386 7 11 176 32 64 128 256), losses := [] }

theorem u40786 : Upper (D 7) (R 7) [96,384,3,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40787 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 386 7 13 26 240 240 240 496), lower := (rows 97 386 7 13 26 32 64 128 256), losses := [] }

theorem u40787 : Upper (D 7) (R 7) [96,384,3,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40788 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 13 50 248 216 216 472), lower := (rows 97 386 7 13 50 32 64 128 256), losses := [] }

theorem u40788 : Upper (D 7) (R 7) [96,384,3,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40789 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 13 56 242 210 210 466), lower := (rows 97 386 7 13 56 32 64 128 256), losses := [] }

theorem u40789 : Upper (D 7) (R 7) [96,384,3,5,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40790 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 13 152 114 114 242 370), lower := (rows 97 386 7 13 152 32 64 128 256), losses := [] }

theorem u40790 : Upper (D 7) (R 7) [96,384,3,5,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40791 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 13 176 122 90 218 346), lower := (rows 97 386 7 13 176 32 64 128 256), losses := [] }

theorem u40791 : Upper (D 7) (R 7) [96,384,3,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40792 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 386 7 14 25 240 240 240 496), lower := (rows 97 386 7 14 25 32 64 128 256), losses := [] }

theorem u40792 : Upper (D 7) (R 7) [96,384,3,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40793 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 14 56 241 209 209 465), lower := (rows 97 386 7 14 56 32 64 128 256), losses := [] }

theorem u40793 : Upper (D 7) (R 7) [96,384,3,6,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40794 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 14 145 120 120 248 376), lower := (rows 97 386 7 14 145 32 64 128 256), losses := [] }

theorem u40794 : Upper (D 7) (R 7) [96,384,3,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40795 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 14 152 113 113 241 369), lower := (rows 97 386 7 14 152 32 64 128 256), losses := [] }

theorem u40795 : Upper (D 7) (R 7) [96,384,3,6,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40796 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 14 176 121 89 217 345), lower := (rows 97 386 7 14 176 32 64 128 256), losses := [] }

theorem u40796 : Upper (D 7) (R 7) [96,384,3,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40797 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 386 7 25 26 228 228 228 484), lower := (rows 97 386 7 25 26 32 64 128 256), losses := [] }

theorem u40797 : Upper (D 7) (R 7) [96,384,3,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40798 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 25 28 226 226 226 482), lower := (rows 97 386 7 25 28 32 64 128 256), losses := [] }

theorem u40798 : Upper (D 7) (R 7) [96,384,3,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40799 : Route 9 := (fun mask => (mask,id))

def c40799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40799 : Upper (D 7) (R 7) [96,384,3,17,34] 13 := by
  apply FastRouting.sound _ _ [96,384,3,17,34] 13 (by decide) (choices 1) [4,8,64,128] r40799 c40799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29733
  · exact u29734
  · exact u29735
  · exact u29736

#print axioms u40799
end Delivery.IrregularNine14.P07
