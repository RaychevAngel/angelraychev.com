import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0377
import IrregularNine14P07C0378
import IrregularNine14P07C0379

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36780 : Route 9 := (fun mask => (mask,id))

def c36780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36780 : Upper (D 7) (R 7) [36,72,3,257,96] 13 := by
  apply FastRouting.sound _ _ [36,72,3,257,96] 13 (by decide) (choices 1) [2,16,128] r36780 c36780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22656
  · exact u22657
  · exact u22658

def r36781 : Route 9 := (fun mask => (mask,id))

def c36781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36781 : Upper (D 7) (R 7) [36,72,3,257,130] 13 := by
  apply FastRouting.sound _ _ [36,72,3,257,130] 13 (by decide) (choices 1) [16,64,128] r36781 c36781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22659
  · exact u22660
  · exact u22661

def r36782 : Route 9 := (fun mask => (mask,id))

def c36782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36782 : Upper (D 7) (R 7) [36,72,3,257,160] 13 := by
  apply FastRouting.sound _ _ [36,72,3,257,160] 13 (by decide) (choices 1) [2,16,64,128] r36782 c36782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22662
  · exact u22663
  · exact u22664
  · exact u22665

def r36783 : Route 9 := (fun mask => (mask,id))

def c36783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36783 : Upper (D 7) (R 7) [36,72,3,257,192] 13 := by
  apply FastRouting.sound _ _ [36,72,3,257,192] 13 (by decide) (choices 1) [2,16,128] r36783 c36783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22666
  · exact u22667
  · exact u22668

def b36784 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 74 7 266 49 240 208 208 464), lower := (rows 37 74 7 266 49 32 64 128 256), losses := [] }

theorem u36784 : Upper (D 7) (R 7) [36,72,3,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36785 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 7 266 81 176 240 176 432), lower := (rows 37 74 7 266 81 32 64 128 256), losses := [] }

theorem u36785 : Upper (D 7) (R 7) [36,72,3,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36786 : Route 9 := (fun mask => (mask,id))

def c36786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36786 : Upper (D 7) (R 7) [36,72,3,258,96] 13 := by
  apply FastRouting.sound _ _ [36,72,3,258,96] 13 (by decide) (choices 1) [1,16,128] r36786 c36786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22669
  · exact u22670
  · exact u22671

def b36787 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 7 266 145 240 240 240 496), lower := (rows 37 74 7 266 145 32 64 128 256), losses := [] }

theorem u36787 : Upper (D 7) (R 7) [36,72,3,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36788 : Route 9 := (fun mask => (mask,id))

def c36788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36788 : Upper (D 7) (R 7) [36,72,3,258,160] 13 := by
  apply FastRouting.sound _ _ [36,72,3,258,160] 13 (by decide) (choices 1) [1,16,64,128] r36788 c36788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22672
  · exact u22673
  · exact u22674
  · exact u22675

def r36789 : Route 9 := (fun mask => (mask,id))

def c36789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36789 : Upper (D 7) (R 7) [36,72,3,258,192] 13 := by
  apply FastRouting.sound _ _ [36,72,3,258,192] 13 (by decide) (choices 1) [1,16,128] r36789 c36789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22676
  · exact u22677
  · exact u22678

def b36790 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 74 7 280 19 224 224 224 480), lower := (rows 37 74 7 280 19 32 64 128 256), losses := [] }

theorem u36790 : Upper (D 7) (R 7) [36,72,3,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36791 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 7 280 49 226 194 194 450), lower := (rows 37 74 7 280 49 32 64 128 256), losses := [] }

theorem u36791 : Upper (D 7) (R 7) [36,72,3,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36792 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 280 50 225 193 193 449), lower := (rows 37 74 7 280 50 32 64 128 256), losses := [] }

theorem u36792 : Upper (D 7) (R 7) [36,72,3,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36793 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 74 7 280 81 162 226 162 418), lower := (rows 37 74 7 280 81 32 64 128 256), losses := [] }

theorem u36793 : Upper (D 7) (R 7) [36,72,3,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36794 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 7 280 82 161 225 161 417), lower := (rows 37 74 7 280 82 32 64 128 256), losses := [] }

theorem u36794 : Upper (D 7) (R 7) [36,72,3,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36795 : Route 9 := (fun mask => (mask,id))

def c36795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36795 : Upper (D 7) (R 7) [36,72,3,272,96] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,96] 13 (by decide) (choices 1) [1,2,128] r36795 c36795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22679
  · exact u22680
  · exact u22681

def r36796 : Route 9 := (fun mask => (mask,id))

def c36796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36796 : Upper (D 7) (R 7) [36,72,3,272,129] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,129] 13 (by decide) (choices 1) [2,64,128] r36796 c36796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22682
  · exact u22683
  · exact u22684

def r36797 : Route 9 := (fun mask => (mask,id))

def c36797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36797 : Upper (D 7) (R 7) [36,72,3,272,130] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,130] 13 (by decide) (choices 1) [1,64,128] r36797 c36797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22685
  · exact u22686
  · exact u22687

def r36798 : Route 9 := (fun mask => (mask,id))

def c36798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36798 : Upper (D 7) (R 7) [36,72,3,272,160] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,160] 13 (by decide) (choices 1) [1,2,64,128] r36798 c36798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22688
  · exact u22689
  · exact u22690
  · exact u22691

def r36799 : Route 9 := (fun mask => (mask,id))

def c36799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36799 : Upper (D 7) (R 7) [36,72,3,272,192] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,192] 13 (by decide) (choices 1) [1,2,128] r36799 c36799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22692
  · exact u22693
  · exact u22694

def b36800 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 37 74 7 296 19 240 208 208 464), lower := (rows 37 74 7 296 19 32 64 128 256), losses := [] }

theorem u36800 : Upper (D 7) (R 7) [36,72,3,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36801 : Route 9 := (fun mask => (mask,id))

def c36801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36801 : Upper (D 7) (R 7) [36,72,3,288,65] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,65] 13 (by decide) (choices 1) [2,16,128] r36801 c36801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22695
  · exact u22696
  · exact u22697

def b36802 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 7 296 82 177 209 145 401), lower := (rows 37 74 7 296 82 32 64 128 256), losses := [] }

theorem u36802 : Upper (D 7) (R 7) [36,72,3,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36803 : Route 9 := (fun mask => (mask,id))

def c36803 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36803 : Upper (D 7) (R 7) [36,72,3,288,129] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,129] 13 (by decide) (choices 1) [2,16,64,128] r36803 c36803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22698
  · exact u22699
  · exact u22700
  · exact u22701

def r36804 : Route 9 := (fun mask => (mask,id))

def c36804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36804 : Upper (D 7) (R 7) [36,72,3,288,130] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,130] 13 (by decide) (choices 1) [1,16,64,128] r36804 c36804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22702
  · exact u22703
  · exact u22704
  · exact u22705

def r36805 : Route 9 := (fun mask => (mask,id))

def c36805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36805 : Upper (D 7) (R 7) [36,72,3,288,192] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,192] 13 (by decide) (choices 1) [1,2,16,128] r36805 c36805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22706
  · exact u22707
  · exact u22708
  · exact u22709

def b36806 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 74 7 392 19 240 240 240 496), lower := (rows 37 74 7 392 19 32 64 128 256), losses := [] }

theorem u36806 : Upper (D 7) (R 7) [36,72,3,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36807 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 7 392 49 242 210 210 466), lower := (rows 37 74 7 392 49 32 64 128 256), losses := [] }

theorem u36807 : Upper (D 7) (R 7) [36,72,3,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36808 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 50 241 209 209 465), lower := (rows 37 74 7 392 50 32 64 128 256), losses := [] }

theorem u36808 : Upper (D 7) (R 7) [36,72,3,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36809 : Route 9 := (fun mask => (mask,id))

def c36809 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36809 : Upper (D 7) (R 7) [36,72,3,384,65] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384,65] 13 (by decide) (choices 1) [2,16,128] r36809 c36809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22710
  · exact u22711
  · exact u22712

def b36810 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 7 392 82 177 241 177 433), lower := (rows 37 74 7 392 82 32 64 128 256), losses := [] }

theorem u36810 : Upper (D 7) (R 7) [36,72,3,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36811 : Route 9 := (fun mask => (mask,id))

def c36811 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36811 : Upper (D 7) (R 7) [36,72,3,384,96] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384,96] 13 (by decide) (choices 1) [1,2,16,128] r36811 c36811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22713
  · exact u22714
  · exact u22715
  · exact u22716

def r36812 : Route 9 := (fun mask => (mask,id))

def c36812 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36812 : Upper (D 7) (R 7) [36,72,3,384,129] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384,129] 13 (by decide) (choices 1) [2,16,64] r36812 c36812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22717
  · exact u22718
  · exact u22719

def r36813 : Route 9 := (fun mask => (mask,id))

def c36813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36813 : Upper (D 7) (R 7) [36,72,3,384,130] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384,130] 13 (by decide) (choices 1) [1,16,64] r36813 c36813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22720
  · exact u22721
  · exact u22722

def r36814 : Route 9 := (fun mask => (mask,id))

def c36814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36814 : Upper (D 7) (R 7) [36,72,3,384,160] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384,160] 13 (by decide) (choices 1) [1,2,16,64] r36814 c36814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22723
  · exact u22724
  · exact u22725
  · exact u22726

def r36815 : Route 9 := (fun mask => (mask,id))

def c36815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36815 : Upper (D 7) (R 7) [36,72,3,384,192] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384,192] 13 (by decide) (choices 1) [1,2,16] r36815 c36815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22727
  · exact u22728
  · exact u22729

def b36816 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 42 19 480 448 448 448), lower := (rows 37 74 21 42 19 32 64 128 256), losses := [] }

theorem u36816 : Upper (D 7) (R 7) [36,72,17,34,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36817 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 42 81 418 450 386 386), lower := (rows 37 74 21 42 81 32 64 128 256), losses := [] }

theorem u36817 : Upper (D 7) (R 7) [36,72,17,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36818 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 42 82 417 449 385 385), lower := (rows 37 74 21 42 82 32 64 128 256), losses := [] }

theorem u36818 : Upper (D 7) (R 7) [36,72,17,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36819 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 42 145 482 450 450 450), lower := (rows 37 74 21 42 145 32 64 128 256), losses := [] }

theorem u36819 : Upper (D 7) (R 7) [36,72,17,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36820 : Route 9 := (fun mask => (mask,id))

def c36820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u36820 : Upper (D 7) (R 7) [36,72,17,34,130] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,130] 13 (by decide) (choices 1) [1,64,128,256] r36820 c36820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22730
  · exact u22731
  · exact u22732
  · exact u22733

def r36821 : Route 9 := (fun mask => (mask,id))

def c36821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36821 : Upper (D 7) (R 7) [36,72,17,34,192] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,192] 13 (by decide) (choices 1) [1,2,128,256] r36821 c36821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22734
  · exact u22735
  · exact u22736
  · exact u22737

def b36822 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 42 273 226 194 194 450), lower := (rows 37 74 21 42 273 32 64 128 256), losses := [] }

theorem u36822 : Upper (D 7) (R 7) [36,72,17,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36823 : Route 9 := (fun mask => (mask,id))

def c36823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36823 : Upper (D 7) (R 7) [36,72,17,34,258] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,258] 13 (by decide) (choices 1) [1,64,128] r36823 c36823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22738
  · exact u22739
  · exact u22740

def r36824 : Route 9 := (fun mask => (mask,id))

def c36824 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36824 : Upper (D 7) (R 7) [36,72,17,34,320] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,320] 13 (by decide) (choices 1) [1,2,128] r36824 c36824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22741
  · exact u22742
  · exact u22743

def r36825 : Route 9 := (fun mask => (mask,id))

def c36825 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36825 : Upper (D 7) (R 7) [36,72,17,34,384] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,384] 13 (by decide) (choices 1) [1,2,64,128] r36825 c36825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22744
  · exact u22745
  · exact u22746
  · exact u22747

def b36826 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 137 50 482 450 450 450), lower := (rows 37 74 21 137 50 32 64 128 256), losses := [] }

theorem u36826 : Upper (D 7) (R 7) [36,72,17,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36827 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 1, region := 16, targets := 32 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 37 74 21 137 82 418 482 418 418), lower := (rows 37 74 21 137 82 32 64 128 256), losses := [] }

theorem u36827 : Upper (D 7) (R 7) [36,72,17,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36828 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 137 112 418 450 386 386), lower := (rows 37 74 21 137 112 32 64 128 256), losses := [] }

theorem u36828 : Upper (D 7) (R 7) [36,72,17,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36829 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 21 137 146 354 354 482 354), lower := (rows 37 74 21 137 146 32 64 128 256), losses := [] }

theorem u36829 : Upper (D 7) (R 7) [36,72,17,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36830 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 137 176 354 322 450 322), lower := (rows 37 74 21 137 176 32 64 128 256), losses := [] }

theorem u36830 : Upper (D 7) (R 7) [36,72,17,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36831 : Route 9 := (fun mask => (mask,id))

def c36831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36831 : Upper (D 7) (R 7) [36,72,17,129,192] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,192] 13 (by decide) (choices 1) [2,256] r36831 c36831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22748
  · exact u22749

def r36832 : Route 9 := (fun mask => (mask,id))

def c36832 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36832 : Upper (D 7) (R 7) [36,72,17,129,258] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,258] 13 (by decide) (choices 1) [2,64,128] r36832 c36832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22750
  · exact u22751
  · exact u22752

def b36833 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 137 304 226 194 194 450), lower := (rows 37 74 21 137 304 32 64 128 256), losses := [] }

theorem u36833 : Upper (D 7) (R 7) [36,72,17,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36834 : Route 9 := (fun mask => (mask,id))

def c36834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36834 : Upper (D 7) (R 7) [36,72,17,129,320] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,320] 13 (by decide) (choices 1) [2,128] r36834 c36834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22753
  · exact u22754

def r36835 : Route 9 := (fun mask => (mask,id))

def c36835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36835 : Upper (D 7) (R 7) [36,72,17,129,384] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,384] 13 (by decide) (choices 1) [2,64] r36835 c36835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22755
  · exact u22756

def b36836 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 0, region := 458, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 138 19 480 480 480 480), lower := (rows 37 74 21 138 19 32 64 128 256), losses := [] }

theorem u36836 : Upper (D 7) (R 7) [36,72,17,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36837 : PairBound 9 := { available := 450, camps := [{ cop := 5, region := 21, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 138 49 482 450 450 450), lower := (rows 37 74 21 138 49 32 64 128 256), losses := [] }

theorem u36837 : Upper (D 7) (R 7) [36,72,17,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36838 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 138 50 481 449 449 449), lower := (rows 37 74 21 138 50 32 64 128 256), losses := [] }

theorem u36838 : Upper (D 7) (R 7) [36,72,17,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36839 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 138 81 418 482 418 418), lower := (rows 37 74 21 138 81 32 64 128 256), losses := [] }

theorem u36839 : Upper (D 7) (R 7) [36,72,17,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36839
end Delivery.IrregularNine14.P07
