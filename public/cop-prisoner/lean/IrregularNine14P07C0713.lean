import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0611
import IrregularNine14P07C0612
import IrregularNine14P07C0613
import IrregularNine14P07C0614
import IrregularNine14P07C0615
import IrregularNine14P07C0616

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42780 : Route 9 := (fun mask => (mask,id))

def c42780 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42780 : Upper (D 7) (R 7) [36,72,3,17] 13 := by
  apply FastRouting.sound _ _ [36,72,3,17] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r42780 c42780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36703
  · exact u36704
  · exact u36705
  · exact u36706
  · exact u36707
  · exact u36708
  · exact u36709
  · exact u36710
  · exact u36711
  · exact u36712

def r42781 : Route 9 := (fun mask => (mask,id))

def c42781 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42781 : Upper (D 7) (R 7) [36,72,3,18] 13 := by
  apply FastRouting.sound _ _ [36,72,3,18] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42781 c42781
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36713
  · exact u36714
  · exact u36715
  · exact u36716
  · exact u36717
  · exact u36718
  · exact u36719
  · exact u36720
  · exact u36721
  · exact u36722

def b42782 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 74 7 41 466 498 466 466 466), lower := (rows 37 74 7 41 16 32 64 128 256), losses := [] }

theorem u42782 : Upper (D 7) (R 7) [36,72,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42783 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 42 465 497 465 465 465), lower := (rows 37 74 7 42 16 32 64 128 256), losses := [] }

theorem u42783 : Upper (D 7) (R 7) [36,72,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42784 : Route 9 := (fun mask => (mask,id))

def c42784 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42784 : Upper (D 7) (R 7) [36,72,3,48] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42784 c42784
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36723
  · exact u36724
  · exact u36725
  · exact u36726
  · exact u36727
  · exact u36728
  · exact u36729
  · exact u36730
  · exact u36731
  · exact u36732

def b42785 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 6, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 7 73 434 434 498 434 434), lower := (rows 37 74 7 73 16 32 64 128 256), losses := [] }

theorem u42785 : Upper (D 7) (R 7) [36,72,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42786 : PairBound 9 := { available := 433, camps := [{ cop := 6, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 7 74 433 433 497 433 433), lower := (rows 37 74 7 74 16 32 64 128 256), losses := [] }

theorem u42786 : Upper (D 7) (R 7) [36,72,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42787 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 7 88 435 419 483 419 419), lower := (rows 37 74 7 88 16 32 64 128 256), losses := [] }

theorem u42787 : Upper (D 7) (R 7) [36,72,3,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42788 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 7, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 37 74 7 104 403 435 467 403 403), lower := (rows 37 74 7 104 16 32 64 128 256), losses := [] }

theorem u42788 : Upper (D 7) (R 7) [36,72,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42789 : Route 9 := (fun mask => (mask,id))

def c42789 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42789 : Upper (D 7) (R 7) [36,72,3,129] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r42789 c42789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36733
  · exact u36734
  · exact u36735
  · exact u36736
  · exact u36737
  · exact u36738
  · exact u36739
  · exact u36740
  · exact u36741
  · exact u36742

def r42790 : Route 9 := (fun mask => (mask,id))

def c42790 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42790 : Upper (D 7) (R 7) [36,72,3,130] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42790 c42790
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36743
  · exact u36744
  · exact u36745
  · exact u36746
  · exact u36747
  · exact u36748
  · exact u36749
  · exact u36750
  · exact u36751
  · exact u36752

def r42791 : Route 9 := (fun mask => (mask,id))

def c42791 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42791 : Upper (D 7) (R 7) [36,72,3,144] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r42791 c42791
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36753
  · exact u36754
  · exact u36755
  · exact u36756
  · exact u36757
  · exact u36758
  · exact u36759
  · exact u36760
  · exact u36761
  · exact u36762
  · exact u36763
  · exact u36764
  · exact u36765
  · exact u36766
  · exact u36767

def r42792 : Route 9 := (fun mask => (mask,id))

def c42792 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42792 : Upper (D 7) (R 7) [36,72,3,160] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42792 c42792
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36768
  · exact u36769
  · exact u36770
  · exact u36771
  · exact u36772
  · exact u36773
  · exact u36774
  · exact u36775
  · exact u36776
  · exact u36777

def b42793 : PairBound 9 := { available := 435, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 7 200 435 435 499 435 435), lower := (rows 37 74 7 200 16 32 64 128 256), losses := [] }

theorem u42793 : Upper (D 7) (R 7) [36,72,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42794 : Route 9 := (fun mask => (mask,id))

def c42794 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42794 : Upper (D 7) (R 7) [36,72,3,257] 13 := by
  apply FastRouting.sound _ _ [36,72,3,257] 13 (by decide) (choices 2) [34,66,96,130,160,192] r42794 c42794
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36778
  · exact u36779
  · exact u36780
  · exact u36781
  · exact u36782
  · exact u36783

def r42795 : Route 9 := (fun mask => (mask,id))

def c42795 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42795 : Upper (D 7) (R 7) [36,72,3,258] 13 := by
  apply FastRouting.sound _ _ [36,72,3,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42795 c42795
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36784
  · exact u36785
  · exact u36786
  · exact u36787
  · exact u36788
  · exact u36789

def r42796 : Route 9 := (fun mask => (mask,id))

def c42796 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42796 : Upper (D 7) (R 7) [36,72,3,272] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42796 c42796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36790
  · exact u36791
  · exact u36792
  · exact u36793
  · exact u36794
  · exact u36795
  · exact u36796
  · exact u36797
  · exact u36798
  · exact u36799

def r42797 : Route 9 := (fun mask => (mask,id))

def c42797 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42797 : Upper (D 7) (R 7) [36,72,3,288] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42797 c42797
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36800
  · exact u36801
  · exact u36802
  · exact u36803
  · exact u36804
  · exact u36805

def b42798 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 181, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 7 328 179 179 243 179 435), lower := (rows 37 74 7 328 16 32 64 128 256), losses := [] }

theorem u42798 : Upper (D 7) (R 7) [36,72,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42799 : Route 9 := (fun mask => (mask,id))

def c42799 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42799 : Upper (D 7) (R 7) [36,72,3,384] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42799 c42799
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36806
  · exact u36807
  · exact u36808
  · exact u36809
  · exact u36810
  · exact u36811
  · exact u36812
  · exact u36813
  · exact u36814
  · exact u36815

def b42800 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 74 21 41 466 482 450 450 450), lower := (rows 37 74 21 41 16 32 64 128 256), losses := [] }

theorem u42800 : Upper (D 7) (R 7) [36,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42801 : Route 9 := (fun mask => (mask,id))

def c42801 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42801 : Upper (D 7) (R 7) [36,72,17,34] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42801 c42801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36816
  · exact u36817
  · exact u36818
  · exact u36819
  · exact u36820
  · exact u36821
  · exact u36822
  · exact u36823
  · exact u36824
  · exact u36825

def b42802 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 21 73 434 418 482 418 418), lower := (rows 37 74 21 73 16 32 64 128 256), losses := [] }

theorem u42802 : Upper (D 7) (R 7) [36,72,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42803 : PairBound 9 := { available := 419, camps := [{ cop := 6, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 21 74 435 419 483 419 419), lower := (rows 37 74 21 74 16 32 64 128 256), losses := [] }

theorem u42803 : Upper (D 7) (R 7) [36,72,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42804 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 21 104 403 419 451 387 387), lower := (rows 37 74 21 104 16 32 64 128 256), losses := [] }

theorem u42804 : Upper (D 7) (R 7) [36,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42805 : Route 9 := (fun mask => (mask,id))

def c42805 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42805 : Upper (D 7) (R 7) [36,72,17,129] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r42805 c42805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36826
  · exact u36827
  · exact u36828
  · exact u36829
  · exact u36830
  · exact u36831
  · exact u36832
  · exact u36833
  · exact u36834
  · exact u36835

def r42806 : Route 9 := (fun mask => (mask,id))

def c42806 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42806 : Upper (D 7) (R 7) [36,72,17,130] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r42806 c42806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36836
  · exact u36837
  · exact u36838
  · exact u36839
  · exact u36840
  · exact u36841
  · exact u36842
  · exact u36843
  · exact u36844
  · exact u36845
  · exact u36846
  · exact u36847
  · exact u36848
  · exact u36849
  · exact u36850

def r42807 : Route 9 := (fun mask => (mask,id))

def c42807 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42807 : Upper (D 7) (R 7) [36,72,17,160] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42807 c42807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36851
  · exact u36852
  · exact u36853
  · exact u36854
  · exact u36855
  · exact u36856
  · exact u36857
  · exact u36858
  · exact u36859
  · exact u36860

def b42808 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 21 200 435 419 483 419 419), lower := (rows 37 74 21 200 16 32 64 128 256), losses := [] }

theorem u42808 : Upper (D 7) (R 7) [36,72,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42809 : Route 9 := (fun mask => (mask,id))

def c42809 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42809 : Upper (D 7) (R 7) [36,72,17,257] 13 := by
  apply FastRouting.sound _ _ [36,72,17,257] 13 (by decide) (choices 2) [34,66,96,130,160,192] r42809 c42809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36861
  · exact u36862
  · exact u36863
  · exact u36864
  · exact u36865
  · exact u36866

def r42810 : Route 9 := (fun mask => (mask,id))

def c42810 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42810 : Upper (D 7) (R 7) [36,72,17,258] 13 := by
  apply FastRouting.sound _ _ [36,72,17,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42810 c42810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36867
  · exact u36868
  · exact u36869
  · exact u36870
  · exact u36871
  · exact u36872
  · exact u36873
  · exact u36874
  · exact u36875
  · exact u36876

def r42811 : Route 9 := (fun mask => (mask,id))

def c42811 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42811 : Upper (D 7) (R 7) [36,72,17,288] 13 := by
  apply FastRouting.sound _ _ [36,72,17,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42811 c42811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36877
  · exact u36878
  · exact u36879
  · exact u36880
  · exact u36881
  · exact u36882

def b42812 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 181, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 21 328 179 163 227 163 419), lower := (rows 37 74 21 328 16 32 64 128 256), losses := [] }

theorem u42812 : Upper (D 7) (R 7) [36,72,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42813 : Route 9 := (fun mask => (mask,id))

def c42813 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42813 : Upper (D 7) (R 7) [36,72,17,384] 13 := by
  apply FastRouting.sound _ _ [36,72,17,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42813 c42813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36883
  · exact u36884
  · exact u36885
  · exact u36886
  · exact u36887
  · exact u36888
  · exact u36889
  · exact u36890
  · exact u36891
  · exact u36892

def b42814 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 74 22 41 467 483 451 451 451), lower := (rows 37 74 22 41 16 32 64 128 256), losses := [] }

theorem u42814 : Upper (D 7) (R 7) [36,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42815 : Route 9 := (fun mask => (mask,id))

def c42815 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42815 : Upper (D 7) (R 7) [36,72,18,34] 13 := by
  apply FastRouting.sound _ _ [36,72,18,34] 13 (by decide) (choices 2) [65,129,192,257,320,384] r42815 c42815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36893
  · exact u36894
  · exact u36895
  · exact u36896
  · exact u36897
  · exact u36898

def b42816 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 22 73 435 419 483 419 419), lower := (rows 37 74 22 73 16 32 64 128 256), losses := [] }

theorem u42816 : Upper (D 7) (R 7) [36,72,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42817 : PairBound 9 := { available := 417, camps := [{ cop := 6, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 22 74 433 417 481 417 417), lower := (rows 37 74 22 74 16 32 64 128 256), losses := [] }

theorem u42817 : Upper (D 7) (R 7) [36,72,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42818 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 22 104 403 419 451 387 387), lower := (rows 37 74 22 104 16 32 64 128 256), losses := [] }

theorem u42818 : Upper (D 7) (R 7) [36,72,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42819 : Route 9 := (fun mask => (mask,id))

def c42819 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42819 : Upper (D 7) (R 7) [36,72,18,129] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r42819 c42819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36899
  · exact u36900
  · exact u36901
  · exact u36902
  · exact u36903
  · exact u36904
  · exact u36905
  · exact u36906
  · exact u36907
  · exact u36908
  · exact u36909
  · exact u36910
  · exact u36911
  · exact u36912
  · exact u36913

def r42820 : Route 9 := (fun mask => (mask,id))

def c42820 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42820 : Upper (D 7) (R 7) [36,72,18,130] 13 := by
  apply FastRouting.sound _ _ [36,72,18,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42820 c42820
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36914
  · exact u36915
  · exact u36916
  · exact u36917
  · exact u36918
  · exact u36919
  · exact u36920
  · exact u36921
  · exact u36922
  · exact u36923

def r42821 : Route 9 := (fun mask => (mask,id))

def c42821 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42821 : Upper (D 7) (R 7) [36,72,18,160] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42821 c42821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36924
  · exact u36925
  · exact u36926
  · exact u36927
  · exact u36928
  · exact u36929
  · exact u36930
  · exact u36931
  · exact u36932
  · exact u36933

def b42822 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 22 200 435 419 483 419 419), lower := (rows 37 74 22 200 16 32 64 128 256), losses := [] }

theorem u42822 : Upper (D 7) (R 7) [36,72,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42823 : Route 9 := (fun mask => (mask,id))

def c42823 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42823 : Upper (D 7) (R 7) [36,72,18,257] 13 := by
  apply FastRouting.sound _ _ [36,72,18,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42823 c42823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36934
  · exact u36935
  · exact u36936
  · exact u36937
  · exact u36938
  · exact u36939
  · exact u36940
  · exact u36941
  · exact u36942
  · exact u36943

def r42824 : Route 9 := (fun mask => (mask,id))

def c42824 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42824 : Upper (D 7) (R 7) [36,72,18,258] 13 := by
  apply FastRouting.sound _ _ [36,72,18,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42824 c42824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36944
  · exact u36945
  · exact u36946
  · exact u36947
  · exact u36948
  · exact u36949

def r42825 : Route 9 := (fun mask => (mask,id))

def c42825 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42825 : Upper (D 7) (R 7) [36,72,18,288] 13 := by
  apply FastRouting.sound _ _ [36,72,18,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42825 c42825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36950
  · exact u36951
  · exact u36952
  · exact u36953
  · exact u36954
  · exact u36955

def b42826 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 181, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 22 328 179 163 227 163 419), lower := (rows 37 74 22 328 16 32 64 128 256), losses := [] }

theorem u42826 : Upper (D 7) (R 7) [36,72,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42827 : Route 9 := (fun mask => (mask,id))

def c42827 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42827 : Upper (D 7) (R 7) [36,72,18,384] 13 := by
  apply FastRouting.sound _ _ [36,72,18,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42827 c42827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36956
  · exact u36957
  · exact u36958
  · exact u36959
  · exact u36960
  · exact u36961
  · exact u36962
  · exact u36963
  · exact u36964
  · exact u36965

def b42828 : PairBound 9 := { available := 466, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 37 137 466 498 466 466 466), lower := (rows 37 74 37 137 16 32 64 128 256), losses := [] }

theorem u42828 : Upper (D 7) (R 7) [36,72,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42829 : PairBound 9 := { available := 467, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 37 138 467 499 467 467 467), lower := (rows 37 74 37 138 16 32 64 128 256), losses := [] }

theorem u42829 : Upper (D 7) (R 7) [36,72,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42830 : PairBound 9 := { available := 451, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 37 152 467 483 451 451 451), lower := (rows 37 74 37 152 16 32 64 128 256), losses := [] }

theorem u42830 : Upper (D 7) (R 7) [36,72,33,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42831 : PairBound 9 := { available := 210, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 37 265 210 242 210 210 466), lower := (rows 37 74 37 265 16 32 64 128 256), losses := [] }

theorem u42831 : Upper (D 7) (R 7) [36,72,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42832 : PairBound 9 := { available := 211, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 37 266 211 243 211 211 467), lower := (rows 37 74 37 266 16 32 64 128 256), losses := [] }

theorem u42832 : Upper (D 7) (R 7) [36,72,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42833 : PairBound 9 := { available := 195, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 37 280 211 227 195 195 451), lower := (rows 37 74 37 280 16 32 64 128 256), losses := [] }

theorem u42833 : Upper (D 7) (R 7) [36,72,33,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42834 : PairBound 9 := { available := 211, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 37 392 211 243 211 211 467), lower := (rows 37 74 37 392 16 32 64 128 256), losses := [] }

theorem u42834 : Upper (D 7) (R 7) [36,72,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42835 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 38 137 467 499 467 467 467), lower := (rows 37 74 38 137 16 32 64 128 256), losses := [] }

theorem u42835 : Upper (D 7) (R 7) [36,72,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42836 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 38 138 465 497 465 465 465), lower := (rows 37 74 38 138 16 32 64 128 256), losses := [] }

theorem u42836 : Upper (D 7) (R 7) [36,72,34,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42837 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 38 152 467 483 451 451 451), lower := (rows 37 74 38 152 16 32 64 128 256), losses := [] }

theorem u42837 : Upper (D 7) (R 7) [36,72,34,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42838 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 38 265 211 243 211 211 467), lower := (rows 37 74 38 265 16 32 64 128 256), losses := [] }

theorem u42838 : Upper (D 7) (R 7) [36,72,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42839 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 38 266 209 241 209 209 465), lower := (rows 37 74 38 266 16 32 64 128 256), losses := [] }

theorem u42839 : Upper (D 7) (R 7) [36,72,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u42839
end Delivery.IrregularNine14.P07
