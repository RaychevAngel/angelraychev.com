import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0296
import IrregularNine14P07C0297
import IrregularNine14P07C0298

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33660 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 13, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 152 208 35 99 163 291), lower := (rows 13 290 69 152 208 32 64 128 256), losses := [] }

theorem u33660 : Upper (D 7) (R 7) [12,288,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33661 : Route 9 := (fun mask => (mask,id))

def c33661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33661 : Upper (D 7) (R 7) [12,288,65,160,3] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,3] 13 (by decide) (choices 1) [2,16,64,128] r33661 c33661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17800
  · exact u17801
  · exact u17802
  · exact u17803

def b33662 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 13 290 69 168 81 178 210 146 402), lower := (rows 13 290 69 168 81 32 64 128 256), losses := [] }

theorem u33662 : Upper (D 7) (R 7) [12,288,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33663 : Route 9 := (fun mask => (mask,id))

def c33663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33663 : Upper (D 7) (R 7) [12,288,65,160,66] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,66] 13 (by decide) (choices 1) [1,2,16,128] r33663 c33663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17804
  · exact u17805
  · exact u17806
  · exact u17807

def b33664 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 290 69 168 145 114 82 210 338), lower := (rows 13 290 69 168 145 32 64 128 256), losses := [] }

theorem u33664 : Upper (D 7) (R 7) [12,288,65,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33665 : Route 9 := (fun mask => (mask,id))

def c33665 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33665 : Upper (D 7) (R 7) [12,288,65,160,130] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,130] 13 (by decide) (choices 1) [1,2,16,64] r33665 c33665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17808
  · exact u17809
  · exact u17810
  · exact u17811

def r33666 : Route 9 := (fun mask => (mask,id))

def c33666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33666 : Upper (D 7) (R 7) [12,288,65,160,192] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,192] 13 (by decide) (choices 1) [1,2,16] r33666 c33666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17812
  · exact u17813
  · exact u17814

def b33667 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 25, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 70 88 19 161 225 161 417), lower := (rows 13 290 70 88 19 32 64 128 256), losses := [] }

theorem u33667 : Upper (D 7) (R 7) [12,288,66,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33668 : Route 9 := (fun mask => (mask,id))

def c33668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33668 : Upper (D 7) (R 7) [12,288,66,80,33] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,33] 13 (by decide) (choices 1) [1,2,128] r33668 c33668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17815
  · exact u17816
  · exact u17817

def b33669 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 70 88 50 161 193 129 385), lower := (rows 13 290 70 88 50 32 64 128 256), losses := [] }

theorem u33669 : Upper (D 7) (R 7) [12,288,66,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33670 : Route 9 := (fun mask => (mask,id))

def c33670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33670 : Upper (D 7) (R 7) [12,288,66,80,129] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,129] 13 (by decide) (choices 1) [1,2,128] r33670 c33670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17818
  · exact u17819
  · exact u17820

def r33671 : Route 9 := (fun mask => (mask,id))

def c33671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33671 : Upper (D 7) (R 7) [12,288,66,80,130] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,130] 13 (by decide) (choices 1) [1,128] r33671 c33671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17821
  · exact u17822

def r33672 : Route 9 := (fun mask => (mask,id))

def c33672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33672 : Upper (D 7) (R 7) [12,288,66,80,160] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,160] 13 (by decide) (choices 1) [1,2,128] r33672 c33672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17823
  · exact u17824
  · exact u17825

def b33673 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 232, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,6),(2,5),(3,1),(4,6)], upper := (rows 13 290 70 104 19 177 209 145 401), lower := (rows 13 290 70 104 19 32 64 128 256), losses := [] }

theorem u33673 : Upper (D 7) (R 7) [12,288,66,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33674 : Route 9 := (fun mask => (mask,id))

def c33674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33674 : Upper (D 7) (R 7) [12,288,66,96,129] 13 := by
  apply FastRouting.sound _ _ [12,288,66,96,129] 13 (by decide) (choices 1) [1,2,16,128] r33674 c33674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17826
  · exact u17827
  · exact u17828
  · exact u17829

def r33675 : Route 9 := (fun mask => (mask,id))

def c33675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33675 : Upper (D 7) (R 7) [12,288,66,96,130] 13 := by
  apply FastRouting.sound _ _ [12,288,66,96,130] 13 (by decide) (choices 1) [1,16,128] r33675 c33675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17830
  · exact u17831
  · exact u17832

theorem m33676_128 : Upper (D 7) (R 7) [12,288,66,130,33,128] 13 :=
  permutation_upper _ _ _ [12,288,66,130,33,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17835

def r33676 : Route 9 := (fun mask => (mask,id))

def c33676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33676 : Upper (D 7) (R 7) [12,288,66,130,33] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,33] 13 (by decide) (choices 1) [1,16,64,128] r33676 c33676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17833
  · exact u17834
  · exact u17835
  · exact m33676_128

def r33677 : Route 9 := (fun mask => (mask,id))

def c33677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33677 : Upper (D 7) (R 7) [12,288,66,130,65] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,65] 13 (by decide) (choices 1) [1,16,128] r33677 c33677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17836
  · exact u17837
  · exact u17838

def r33678 : Route 9 := (fun mask => (mask,id))

def c33678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33678 : Upper (D 7) (R 7) [12,288,66,130,96] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,96] 13 (by decide) (choices 1) [1,16,128] r33678 c33678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17839
  · exact u17840
  · exact u17841

def r33679 : Route 9 := (fun mask => (mask,id))

def c33679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33679 : Upper (D 7) (R 7) [12,288,66,130,192] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,192] 13 (by decide) (choices 1) [1,16] r33679 c33679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17842
  · exact u17843

def r33680 : Route 9 := (fun mask => (mask,id))

def c33680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33680 : Upper (D 7) (R 7) [12,288,66,144,3] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,3] 13 (by decide) (choices 1) [1,64,128] r33680 c33680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17844
  · exact u17845
  · exact u17846

def r33681 : Route 9 := (fun mask => (mask,id))

def c33681 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33681 : Upper (D 7) (R 7) [12,288,66,144,33] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,33] 13 (by decide) (choices 1) [1,2,64,128] r33681 c33681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17847
  · exact u17848
  · exact u17849
  · exact u17850

def b33682 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 70 152 50 225 193 193 449), lower := (rows 13 290 70 152 50 32 64 128 256), losses := [] }

theorem u33682 : Upper (D 7) (R 7) [12,288,66,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33683 : Route 9 := (fun mask => (mask,id))

def c33683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33683 : Upper (D 7) (R 7) [12,288,66,144,65] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,65] 13 (by decide) (choices 1) [1,2,128] r33683 c33683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17851
  · exact u17852
  · exact u17853

def b33684 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 290 70 152 82 161 225 161 417), lower := (rows 13 290 70 152 82 32 64 128 256), losses := [] }

theorem u33684 : Upper (D 7) (R 7) [12,288,66,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33685 : Route 9 := (fun mask => (mask,id))

def c33685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33685 : Upper (D 7) (R 7) [12,288,66,144,96] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,96] 13 (by decide) (choices 1) [1,2,128] r33685 c33685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17854
  · exact u17855
  · exact u17856

def b33686 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 290 70 152 145 99 99 227 355), lower := (rows 13 290 70 152 145 32 64 128 256), losses := [] }

theorem u33686 : Upper (D 7) (R 7) [12,288,66,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33687 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 290 70 152 146 97 97 225 353), lower := (rows 13 290 70 152 146 32 64 128 256), losses := [] }

theorem u33687 : Upper (D 7) (R 7) [12,288,66,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33688 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 290 70 152 176 99 67 195 323), lower := (rows 13 290 70 152 176 32 64 128 256), losses := [] }

theorem u33688 : Upper (D 7) (R 7) [12,288,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33689 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 290 70 152 208 35 99 163 291), lower := (rows 13 290 70 152 208 32 64 128 256), losses := [] }

theorem u33689 : Upper (D 7) (R 7) [12,288,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33690 : Route 9 := (fun mask => (mask,id))

def c33690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33690 : Upper (D 7) (R 7) [12,288,66,160,3] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,3] 13 (by decide) (choices 1) [1,16,64,128] r33690 c33690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17857
  · exact u17858
  · exact u17859
  · exact u17860

def r33691 : Route 9 := (fun mask => (mask,id))

def c33691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33691 : Upper (D 7) (R 7) [12,288,66,160,65] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,65] 13 (by decide) (choices 1) [1,2,16,128] r33691 c33691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17861
  · exact u17862
  · exact u17863
  · exact u17864

def b33692 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 290 70 168 82 177 209 145 401), lower := (rows 13 290 70 168 82 32 64 128 256), losses := [] }

theorem u33692 : Upper (D 7) (R 7) [12,288,66,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33693 : Route 9 := (fun mask => (mask,id))

def c33693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33693 : Upper (D 7) (R 7) [12,288,66,160,129] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,129] 13 (by decide) (choices 1) [1,2,16,64] r33693 c33693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17865
  · exact u17866
  · exact u17867
  · exact u17868

def r33694 : Route 9 := (fun mask => (mask,id))

def c33694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33694 : Upper (D 7) (R 7) [12,288,66,160,130] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,130] 13 (by decide) (choices 1) [1,16,64] r33694 c33694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17869
  · exact u17870
  · exact u17871

def r33695 : Route 9 := (fun mask => (mask,id))

def c33695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33695 : Upper (D 7) (R 7) [12,288,66,160,192] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,192] 13 (by decide) (choices 1) [1,2,16] r33695 c33695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17872
  · exact u17873
  · exact u17874

def r33696 : Route 9 := (fun mask => (mask,id))

def c33696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33696 : Upper (D 7) (R 7) [12,288,66,192,3] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,3] 13 (by decide) (choices 1) [1,16,128] r33696 c33696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17875
  · exact u17876
  · exact u17877

def r33697 : Route 9 := (fun mask => (mask,id))

def c33697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33697 : Upper (D 7) (R 7) [12,288,66,192,33] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,33] 13 (by decide) (choices 1) [1,2,16,128] r33697 c33697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17878
  · exact u17879
  · exact u17880
  · exact u17881

def b33698 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 70 200 50 177 209 145 401), lower := (rows 13 290 70 200 50 32 64 128 256), losses := [] }

theorem u33698 : Upper (D 7) (R 7) [12,288,66,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33699 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,6),(1,7),(2,7),(4,6)], upper := (rows 13 290 70 200 145 51 115 179 307), lower := (rows 13 290 70 200 145 32 64 128 256), losses := [] }

theorem u33699 : Upper (D 7) (R 7) [12,288,66,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33700 : Route 9 := (fun mask => (mask,id))

def c33700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33700 : Upper (D 7) (R 7) [12,288,66,192,130] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,130] 13 (by decide) (choices 1) [1,16] r33700 c33700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17882
  · exact u17883

def r33701 : Route 9 := (fun mask => (mask,id))

def c33701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33701 : Upper (D 7) (R 7) [12,288,66,192,160] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,160] 13 (by decide) (choices 1) [1,2,16] r33701 c33701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17884
  · exact u17885
  · exact u17886

def r33702 : Route 9 := (fun mask => (mask,id))

def c33702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33702 : Upper (D 7) (R 7) [12,288,80,96,3] 13 := by
  apply FastRouting.sound _ _ [12,288,80,96,3] 13 (by decide) (choices 1) [1,2,128] r33702 c33702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17887
  · exact u17888
  · exact u17889

def r33703 : Route 9 := (fun mask => (mask,id))

def c33703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33703 : Upper (D 7) (R 7) [12,288,80,96,129] 13 := by
  apply FastRouting.sound _ _ [12,288,80,96,129] 13 (by decide) (choices 1) [1,2,128] r33703 c33703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17890
  · exact u17891
  · exact u17892

def r33704 : Route 9 := (fun mask => (mask,id))

def c33704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33704 : Upper (D 7) (R 7) [12,288,80,96,130] 13 := by
  apply FastRouting.sound _ _ [12,288,80,96,130] 13 (by decide) (choices 1) [1,2,128] r33704 c33704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17893
  · exact u17894
  · exact u17895

def r33705 : Route 9 := (fun mask => (mask,id))

def c33705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33705 : Upper (D 7) (R 7) [12,288,80,160,3] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160,3] 13 (by decide) (choices 1) [1,2,64,128] r33705 c33705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17896
  · exact u17897
  · exact u17898
  · exact u17899

def b33706 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 290 84 168 81 163 195 131 387), lower := (rows 13 290 84 168 81 32 64 128 256), losses := [] }

theorem u33706 : Upper (D 7) (R 7) [12,288,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33707 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 290 84 168 82 163 195 131 387), lower := (rows 13 290 84 168 82 32 64 128 256), losses := [] }

theorem u33707 : Upper (D 7) (R 7) [12,288,80,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33708 : Route 9 := (fun mask => (mask,id))

def c33708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33708 : Upper (D 7) (R 7) [12,288,80,160,129] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160,129] 13 (by decide) (choices 1) [1,2,64] r33708 c33708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17900
  · exact u17901
  · exact u17902

def r33709 : Route 9 := (fun mask => (mask,id))

def c33709 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33709 : Upper (D 7) (R 7) [12,288,80,160,130] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160,130] 13 (by decide) (choices 1) [1,2,64] r33709 c33709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17903
  · exact u17904
  · exact u17905

def b33710 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 290 84 168 208 35 67 131 259), lower := (rows 13 290 84 168 208 32 64 128 256), losses := [] }

theorem u33710 : Upper (D 7) (R 7) [12,288,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33711 : Route 9 := (fun mask => (mask,id))

def c33711 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33711 : Upper (D 7) (R 7) [12,288,80,192,3] 13 := by
  apply FastRouting.sound _ _ [12,288,80,192,3] 13 (by decide) (choices 1) [1,2,128] r33711 c33711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17906
  · exact u17907
  · exact u17908

def r33712 : Route 9 := (fun mask => (mask,id))

def c33712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33712 : Upper (D 7) (R 7) [12,288,80,192,33] 13 := by
  apply FastRouting.sound _ _ [12,288,80,192,33] 13 (by decide) (choices 1) [1,2,128] r33712 c33712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17909
  · exact u17910
  · exact u17911

def b33713 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 84 200 50 163 195 131 387), lower := (rows 13 290 84 200 50 32 64 128 256), losses := [] }

theorem u33713 : Upper (D 7) (R 7) [12,288,80,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33714 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 21, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 84 200 145 35 99 163 291), lower := (rows 13 290 84 200 145 32 64 128 256), losses := [] }

theorem u33714 : Upper (D 7) (R 7) [12,288,80,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33715 : Route 9 := (fun mask => (mask,id))

def c33715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33715 : Upper (D 7) (R 7) [12,288,80,192,130] 13 := by
  apply FastRouting.sound _ _ [12,288,80,192,130] 13 (by decide) (choices 1) [1,2] r33715 c33715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17912
  · exact u17913

def r33716 : Route 9 := (fun mask => (mask,id))

def c33716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33716 : Upper (D 7) (R 7) [12,288,80,192,160] 13 := by
  apply FastRouting.sound _ _ [12,288,80,192,160] 13 (by decide) (choices 1) [1,2] r33716 c33716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17914
  · exact u17915

def r33717 : Route 9 := (fun mask => (mask,id))

def c33717 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33717 : Upper (D 7) (R 7) [12,288,96,192,3] 13 := by
  apply FastRouting.sound _ _ [12,288,96,192,3] 13 (by decide) (choices 1) [1,2,16,128] r33717 c33717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17916
  · exact u17917
  · exact u17918
  · exact u17919

def b33718 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,6),(1,7),(2,7),(4,6)], upper := (rows 13 290 100 200 145 51 83 147 275), lower := (rows 13 290 100 200 145 32 64 128 256), losses := [] }

theorem u33718 : Upper (D 7) (R 7) [12,288,96,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33719 : Route 9 := (fun mask => (mask,id))

def c33719 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33719 : Upper (D 7) (R 7) [12,288,96,192,130] 13 := by
  apply FastRouting.sound _ _ [12,288,96,192,130] 13 (by decide) (choices 1) [1,2,16] r33719 c33719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17920
  · exact u17921
  · exact u17922

#print axioms u33719
end Delivery.IrregularNine14.P07
