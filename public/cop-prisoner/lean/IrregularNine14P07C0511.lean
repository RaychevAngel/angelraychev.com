import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0212
import IrregularNine14P07C0213

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30660 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 324 41 82 184 216 152 408), lower := (rows 7 35 324 41 82 32 64 128 256), losses := [] }

theorem u30660 : Upper (D 7) (R 7) [6,33,320,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30661 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 324 41 88 178 210 146 402), lower := (rows 7 35 324 41 88 32 64 128 256), losses := [] }

theorem u30661 : Upper (D 7) (R 7) [6,33,320,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30662 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 324 41 146 248 216 216 472), lower := (rows 7 35 324 41 146 32 64 128 256), losses := [] }

theorem u30662 : Upper (D 7) (R 7) [6,33,320,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30663 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 324 41 152 242 210 210 466), lower := (rows 7 35 324 41 152 32 64 128 256), losses := [] }

theorem u30663 : Upper (D 7) (R 7) [6,33,320,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30664 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 324 41 208 186 218 154 410), lower := (rows 7 35 324 41 208 32 64 128 256), losses := [] }

theorem u30664 : Upper (D 7) (R 7) [6,33,320,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30665 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 324 42 81 184 216 152 408), lower := (rows 7 35 324 42 81 32 64 128 256), losses := [] }

theorem u30665 : Upper (D 7) (R 7) [6,33,320,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30666 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 324 42 88 177 209 145 401), lower := (rows 7 35 324 42 88 32 64 128 256), losses := [] }

theorem u30666 : Upper (D 7) (R 7) [6,33,320,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30667 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 324 42 145 248 216 216 472), lower := (rows 7 35 324 42 145 32 64 128 256), losses := [] }

theorem u30667 : Upper (D 7) (R 7) [6,33,320,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30668 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 324 42 152 241 209 209 465), lower := (rows 7 35 324 42 152 32 64 128 256), losses := [] }

theorem u30668 : Upper (D 7) (R 7) [6,33,320,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30669 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 324 42 208 185 217 153 409), lower := (rows 7 35 324 42 208 32 64 128 256), losses := [] }

theorem u30669 : Upper (D 7) (R 7) [6,33,320,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30670 : Route 9 := (fun mask => (mask,id))

def c30670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30670 : Upper (D 7) (R 7) [6,33,320,48,65] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,65] 13 (by decide) (choices 1) [2,8,128] r30670 c30670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12722
  · exact u12723
  · exact u12724

def r30671 : Route 9 := (fun mask => (mask,id))

def c30671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30671 : Upper (D 7) (R 7) [6,33,320,48,66] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,66] 13 (by decide) (choices 1) [1,8,128] r30671 c30671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12725
  · exact u12726
  · exact u12727

def b30672 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,5),(0,6),(1,6),(2,5)], upper := (rows 7 35 324 56 88 163 195 131 387), lower := (rows 7 35 324 56 88 32 64 128 256), losses := [] }

theorem u30672 : Upper (D 7) (R 7) [6,33,320,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30673 : Route 9 := (fun mask => (mask,id))

def c30673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30673 : Upper (D 7) (R 7) [6,33,320,48,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,129] 13 (by decide) (choices 1) [2,8,64,128] r30673 c30673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12728
  · exact u12729
  · exact u12730
  · exact u12731

def r30674 : Route 9 := (fun mask => (mask,id))

def c30674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30674 : Upper (D 7) (R 7) [6,33,320,48,130] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,130] 13 (by decide) (choices 1) [1,8,64,128] r30674 c30674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12732
  · exact u12733
  · exact u12734
  · exact u12735

def r30675 : Route 9 := (fun mask => (mask,id))

def c30675 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30675 : Upper (D 7) (R 7) [6,33,320,48,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,136] 13 (by decide) (choices 1) [1,2,64,128] r30675 c30675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12736
  · exact u12737
  · exact u12738
  · exact u12739

def r30676 : Route 9 := (fun mask => (mask,id))

def c30676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30676 : Upper (D 7) (R 7) [6,33,320,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,192] 13 (by decide) (choices 1) [1,2,8,128] r30676 c30676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12740
  · exact u12741
  · exact u12742
  · exact u12743

def r30677 : Route 9 := (fun mask => (mask,id))

def c30677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30677 : Upper (D 7) (R 7) [6,33,320,65,130] 13 := by
  apply FastRouting.sound _ _ [6,33,320,65,130] 13 (by decide) (choices 1) [8,16,128] r30677 c30677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12744
  · exact u12745
  · exact u12746

def r30678 : Route 9 := (fun mask => (mask,id))

def c30678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30678 : Upper (D 7) (R 7) [6,33,320,65,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,65,136] 13 (by decide) (choices 1) [2,16,128] r30678 c30678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12747
  · exact u12748
  · exact u12749

def r30679 : Route 9 := (fun mask => (mask,id))

def c30679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30679 : Upper (D 7) (R 7) [6,33,320,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,65,160] 13 (by decide) (choices 1) [2,8,16,128] r30679 c30679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12750
  · exact u12751
  · exact u12752
  · exact u12753

def r30680 : Route 9 := (fun mask => (mask,id))

def c30680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30680 : Upper (D 7) (R 7) [6,33,320,66,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,66,129] 13 (by decide) (choices 1) [8,16,128] r30680 c30680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12754
  · exact u12755
  · exact u12756

def r30681 : Route 9 := (fun mask => (mask,id))

def c30681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30681 : Upper (D 7) (R 7) [6,33,320,66,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,66,136] 13 (by decide) (choices 1) [1,16,128] r30681 c30681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12757
  · exact u12758
  · exact u12759

def r30682 : Route 9 := (fun mask => (mask,id))

def c30682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30682 : Upper (D 7) (R 7) [6,33,320,66,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,66,160] 13 (by decide) (choices 1) [1,8,16,128] r30682 c30682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12760
  · exact u12761
  · exact u12762
  · exact u12763

def r30683 : Route 9 := (fun mask => (mask,id))

def c30683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30683 : Upper (D 7) (R 7) [6,33,320,80,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,129] 13 (by decide) (choices 1) [2,8,128] r30683 c30683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12764
  · exact u12765
  · exact u12766

def r30684 : Route 9 := (fun mask => (mask,id))

def c30684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30684 : Upper (D 7) (R 7) [6,33,320,80,130] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,130] 13 (by decide) (choices 1) [1,8,128] r30684 c30684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12767
  · exact u12768
  · exact u12769

def r30685 : Route 9 := (fun mask => (mask,id))

def c30685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30685 : Upper (D 7) (R 7) [6,33,320,80,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,136] 13 (by decide) (choices 1) [1,2,128] r30685 c30685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12770
  · exact u12771
  · exact u12772

def r30686 : Route 9 := (fun mask => (mask,id))

def c30686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30686 : Upper (D 7) (R 7) [6,33,320,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,160] 13 (by decide) (choices 1) [1,2,8,128] r30686 c30686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12773
  · exact u12774
  · exact u12775
  · exact u12776

def r30687 : Route 9 := (fun mask => (mask,id))

def c30687 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30687 : Upper (D 7) (R 7) [6,33,320,96,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,129] 13 (by decide) (choices 1) [2,8,16,128] r30687 c30687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12777
  · exact u12778
  · exact u12779
  · exact u12780

def r30688 : Route 9 := (fun mask => (mask,id))

def c30688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30688 : Upper (D 7) (R 7) [6,33,320,96,130] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,130] 13 (by decide) (choices 1) [1,8,16,128] r30688 c30688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12781
  · exact u12782
  · exact u12783
  · exact u12784

def r30689 : Route 9 := (fun mask => (mask,id))

def c30689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30689 : Upper (D 7) (R 7) [6,33,320,96,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,136] 13 (by decide) (choices 1) [1,2,16,128] r30689 c30689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12785
  · exact u12786
  · exact u12787
  · exact u12788

def r30690 : Route 9 := (fun mask => (mask,id))

def c30690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30690 : Upper (D 7) (R 7) [6,33,320,129,130] 13 := by
  apply FastRouting.sound _ _ [6,33,320,129,130] 13 (by decide) (choices 1) [8,16,64] r30690 c30690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12789
  · exact u12790
  · exact u12791

def b30691 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 35 324 137 152 114 114 242 370), lower := (rows 7 35 324 137 152 32 64 128 256), losses := [] }

theorem u30691 : Upper (D 7) (R 7) [6,33,320,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30692 : Route 9 := (fun mask => (mask,id))

def c30692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30692 : Upper (D 7) (R 7) [6,33,320,129,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,129,160] 13 (by decide) (choices 1) [2,8,16,64] r30692 c30692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12792
  · exact u12793
  · exact u12794
  · exact u12795

def r30693 : Route 9 := (fun mask => (mask,id))

def c30693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30693 : Upper (D 7) (R 7) [6,33,320,129,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,129,192] 13 (by decide) (choices 1) [2,8,16] r30693 c30693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12796
  · exact u12797
  · exact u12798

def b30694 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 35 324 138 152 113 113 241 369), lower := (rows 7 35 324 138 152 32 64 128 256), losses := [] }

theorem u30694 : Upper (D 7) (R 7) [6,33,320,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30695 : Route 9 := (fun mask => (mask,id))

def c30695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30695 : Upper (D 7) (R 7) [6,33,320,130,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,130,160] 13 (by decide) (choices 1) [1,8,16,64] r30695 c30695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12799
  · exact u12800
  · exact u12801
  · exact u12802

def r30696 : Route 9 := (fun mask => (mask,id))

def c30696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30696 : Upper (D 7) (R 7) [6,33,320,130,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,130,192] 13 (by decide) (choices 1) [1,8,16] r30696 c30696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12803
  · exact u12804
  · exact u12805

def b30697 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 324 152 152 99 99 227 355), lower := (rows 7 35 324 152 152 32 64 128 256), losses := [] }

theorem u30697 : Upper (D 7) (R 7) [6,33,320,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30698 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 324 152 176 107 75 203 331), lower := (rows 7 35 324 152 176 32 64 128 256), losses := [] }

theorem u30698 : Upper (D 7) (R 7) [6,33,320,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30699 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 324 152 208 43 107 171 299), lower := (rows 7 35 324 152 208 32 64 128 256), losses := [] }

theorem u30699 : Upper (D 7) (R 7) [6,33,320,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30700 : Route 9 := (fun mask => (mask,id))

def c30700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30700 : Upper (D 7) (R 7) [6,33,320,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,160,192] 13 (by decide) (choices 1) [1,2,8,16] r30700 c30700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12806
  · exact u12807
  · exact u12808
  · exact u12809

def b30701 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 21 73 50 480 448 448 448), lower := (rows 7 42 21 73 50 32 64 128 256), losses := [] }

theorem u30701 : Upper (D 7) (R 7) [6,40,17,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30702 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 21 73 82 416 480 416 416), lower := (rows 7 42 21 73 82 32 64 128 256), losses := [] }

theorem u30702 : Upper (D 7) (R 7) [6,40,17,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30703 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 73 112 418 450 386 386), lower := (rows 7 42 21 73 112 32 64 128 256), losses := [] }

theorem u30703 : Upper (D 7) (R 7) [6,40,17,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30704 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 42 21 73 146 480 480 480 480), lower := (rows 7 42 21 73 146 32 64 128 256), losses := [] }

theorem u30704 : Upper (D 7) (R 7) [6,40,17,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30705 : Route 9 := (fun mask => (mask,id))

def c30705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30705 : Upper (D 7) (R 7) [6,40,17,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,160] 13 (by decide) (choices 1) [2,64,128,256] r30705 c30705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12810
  · exact u12811
  · exact u12812
  · exact u12813

def r30706 : Route 9 := (fun mask => (mask,id))

def c30706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30706 : Upper (D 7) (R 7) [6,40,17,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,192] 13 (by decide) (choices 1) [2,128,256] r30706 c30706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12814
  · exact u12815
  · exact u12816

def b30707 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 42 21 73 274 224 224 224 480), lower := (rows 7 42 21 73 274 32 64 128 256), losses := [] }

theorem u30707 : Upper (D 7) (R 7) [6,40,17,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30708 : Route 9 := (fun mask => (mask,id))

def c30708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30708 : Upper (D 7) (R 7) [6,40,17,65,288] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,288] 13 (by decide) (choices 1) [2,64,128] r30708 c30708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12817
  · exact u12818
  · exact u12819

def r30709 : Route 9 := (fun mask => (mask,id))

def c30709 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30709 : Upper (D 7) (R 7) [6,40,17,65,320] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,320] 13 (by decide) (choices 1) [2,128] r30709 c30709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12820
  · exact u12821

def r30710 : Route 9 := (fun mask => (mask,id))

def c30710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30710 : Upper (D 7) (R 7) [6,40,17,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,384] 13 (by decide) (choices 1) [2,64,128] r30710 c30710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12822
  · exact u12823
  · exact u12824

def b30711 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 21 74 49 480 448 448 448), lower := (rows 7 42 21 74 49 32 64 128 256), losses := [] }

theorem u30711 : Upper (D 7) (R 7) [6,40,17,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30712 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 21, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 21 74 81 416 480 416 416), lower := (rows 7 42 21 74 81 32 64 128 256), losses := [] }

theorem u30712 : Upper (D 7) (R 7) [6,40,17,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30713 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 74 112 417 449 385 385), lower := (rows 7 42 21 74 112 32 64 128 256), losses := [] }

theorem u30713 : Upper (D 7) (R 7) [6,40,17,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30714 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 0, region := 490, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 7 42 21 74 145 480 480 480 480), lower := (rows 7 42 21 74 145 32 64 128 256), losses := [] }

theorem u30714 : Upper (D 7) (R 7) [6,40,17,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30715 : Route 9 := (fun mask => (mask,id))

def c30715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30715 : Upper (D 7) (R 7) [6,40,17,66,160] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,160] 13 (by decide) (choices 1) [1,64,128,256] r30715 c30715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12825
  · exact u12826
  · exact u12827
  · exact u12828

def r30716 : Route 9 := (fun mask => (mask,id))

def c30716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30716 : Upper (D 7) (R 7) [6,40,17,66,192] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,192] 13 (by decide) (choices 1) [1,128,256] r30716 c30716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12829
  · exact u12830
  · exact u12831

def b30717 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 0, region := 234, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 7 42 21 74 273 224 224 224 480), lower := (rows 7 42 21 74 273 32 64 128 256), losses := [] }

theorem u30717 : Upper (D 7) (R 7) [6,40,17,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30718 : Route 9 := (fun mask => (mask,id))

def c30718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30718 : Upper (D 7) (R 7) [6,40,17,66,288] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,288] 13 (by decide) (choices 1) [1,64,128] r30718 c30718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12832
  · exact u12833
  · exact u12834

def r30719 : Route 9 := (fun mask => (mask,id))

def c30719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30719 : Upper (D 7) (R 7) [6,40,17,66,320] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,320] 13 (by decide) (choices 1) [1,128] r30719 c30719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12835
  · exact u12836

#print axioms u30719
end Delivery.IrregularNine14.P07
