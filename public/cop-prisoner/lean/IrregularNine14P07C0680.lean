import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0495
import IrregularNine14P07C0496
import IrregularNine14P07C0497

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40800 : Route 9 := (fun mask => (mask,id))

def c40800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40800 : Upper (D 7) (R 7) [96,384,3,17,36] 13 := by
  apply FastRouting.sound _ _ [96,384,3,17,36] 13 (by decide) (choices 1) [2,8,64,128] r40800 c40800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29737
  · exact u29738
  · exact u29739
  · exact u29740

def b40801 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 386 7 25 56 230 198 198 454), lower := (rows 97 386 7 25 56 32 64 128 256), losses := [] }

theorem u40801 : Upper (D 7) (R 7) [96,384,3,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40802 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 386 7 25 112 174 206 142 398), lower := (rows 97 386 7 25 112 32 64 128 256), losses := [] }

theorem u40802 : Upper (D 7) (R 7) [96,384,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40803 : PairBound 9 := { available := 108, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 7 25 146 108 108 236 364), lower := (rows 97 386 7 25 146 32 64 128 256), losses := [] }

theorem u40803 : Upper (D 7) (R 7) [96,384,3,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40804 : Route 9 := (fun mask => (mask,id))

def c40804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40804 : Upper (D 7) (R 7) [96,384,3,17,132] 13 := by
  apply FastRouting.sound _ _ [96,384,3,17,132] 13 (by decide) (choices 1) [2,8,64] r40804 c40804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29741
  · exact u29742
  · exact u29743

def r40805 : Route 9 := (fun mask => (mask,id))

def c40805 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40805 : Upper (D 7) (R 7) [96,384,3,17,136] 13 := by
  apply FastRouting.sound _ _ [96,384,3,17,136] 13 (by decide) (choices 1) [2,4,64] r40805 c40805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29744
  · exact u29745
  · exact u29746

def r40806 : Route 9 := (fun mask => (mask,id))

def c40806 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40806 : Upper (D 7) (R 7) [96,384,3,17,160] 13 := by
  apply FastRouting.sound _ _ [96,384,3,17,160] 13 (by decide) (choices 1) [2,4,8,64] r40806 c40806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29747
  · exact u29748
  · exact u29749
  · exact u29750

def b40807 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 386 7 26 28 225 225 225 481), lower := (rows 97 386 7 26 28 32 64 128 256), losses := [] }

theorem u40807 : Upper (D 7) (R 7) [96,384,3,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40808 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 7 26 49 236 204 204 460), lower := (rows 97 386 7 26 49 32 64 128 256), losses := [] }

theorem u40808 : Upper (D 7) (R 7) [96,384,3,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40809 : Route 9 := (fun mask => (mask,id))

def c40809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40809 : Upper (D 7) (R 7) [96,384,3,18,36] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,36] 13 (by decide) (choices 1) [1,8,64,128] r40809 c40809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29751
  · exact u29752
  · exact u29753
  · exact u29754

def r40810 : Route 9 := (fun mask => (mask,id))

def c40810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40810 : Upper (D 7) (R 7) [96,384,3,18,40] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,40] 13 (by decide) (choices 1) [1,4,64,128] r40810 c40810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29755
  · exact u29756
  · exact u29757
  · exact u29758

def b40811 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 7 26 112 173 205 141 397), lower := (rows 97 386 7 26 112 32 64 128 256), losses := [] }

theorem u40811 : Upper (D 7) (R 7) [96,384,3,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40812 : Route 9 := (fun mask => (mask,id))

def c40812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40812 : Upper (D 7) (R 7) [96,384,3,18,129] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,129] 13 (by decide) (choices 1) [4,8,64] r40812 c40812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29759
  · exact u29760
  · exact u29761

def r40813 : Route 9 := (fun mask => (mask,id))

def c40813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40813 : Upper (D 7) (R 7) [96,384,3,18,132] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,132] 13 (by decide) (choices 1) [1,8,64] r40813 c40813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29762
  · exact u29763
  · exact u29764

def b40814 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 386 7 26 152 101 101 229 357), lower := (rows 97 386 7 26 152 32 64 128 256), losses := [] }

theorem u40814 : Upper (D 7) (R 7) [96,384,3,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40815 : Route 9 := (fun mask => (mask,id))

def c40815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40815 : Upper (D 7) (R 7) [96,384,3,18,160] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,160] 13 (by decide) (choices 1) [1,4,8,64] r40815 c40815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29765
  · exact u29766
  · exact u29767
  · exact u29768

def b40816 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 7 28 49 234 202 202 458), lower := (rows 97 386 7 28 49 32 64 128 256), losses := [] }

theorem u40816 : Upper (D 7) (R 7) [96,384,3,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40817 : Route 9 := (fun mask => (mask,id))

def c40817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40817 : Upper (D 7) (R 7) [96,384,3,20,34] 13 := by
  apply FastRouting.sound _ _ [96,384,3,20,34] 13 (by decide) (choices 1) [1,8,64,128] r40817 c40817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29769
  · exact u29770
  · exact u29771
  · exact u29772

def r40818 : Route 9 := (fun mask => (mask,id))

def c40818 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40818 : Upper (D 7) (R 7) [96,384,3,20,40] 13 := by
  apply FastRouting.sound _ _ [96,384,3,20,40] 13 (by decide) (choices 1) [1,2,64,128] r40818 c40818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29773
  · exact u29774
  · exact u29775
  · exact u29776

def b40819 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 7 28 112 171 203 139 395), lower := (rows 97 386 7 28 112 32 64 128 256), losses := [] }

theorem u40819 : Upper (D 7) (R 7) [96,384,3,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40820 : Route 9 := (fun mask => (mask,id))

def c40820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40820 : Upper (D 7) (R 7) [96,384,3,20,129] 13 := by
  apply FastRouting.sound _ _ [96,384,3,20,129] 13 (by decide) (choices 1) [2,8,64] r40820 c40820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29777
  · exact u29778
  · exact u29779

def b40821 : PairBound 9 := { available := 105, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 7 28 146 105 105 233 361), lower := (rows 97 386 7 28 146 32 64 128 256), losses := [] }

theorem u40821 : Upper (D 7) (R 7) [96,384,3,20,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40822 : Route 9 := (fun mask => (mask,id))

def c40822 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40822 : Upper (D 7) (R 7) [96,384,3,20,136] 13 := by
  apply FastRouting.sound _ _ [96,384,3,20,136] 13 (by decide) (choices 1) [1,2,64] r40822 c40822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29780
  · exact u29781
  · exact u29782

def r40823 : Route 9 := (fun mask => (mask,id))

def c40823 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40823 : Upper (D 7) (R 7) [96,384,3,20,160] 13 := by
  apply FastRouting.sound _ _ [96,384,3,20,160] 13 (by decide) (choices 1) [1,2,8,64] r40823 c40823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29783
  · exact u29784
  · exact u29785
  · exact u29786

def b40824 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 7 41 82 188 220 156 412), lower := (rows 97 386 7 41 82 32 64 128 256), losses := [] }

theorem u40824 : Upper (D 7) (R 7) [96,384,3,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40825 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 7 41 84 186 218 154 410), lower := (rows 97 386 7 41 84 32 64 128 256), losses := [] }

theorem u40825 : Upper (D 7) (R 7) [96,384,3,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40826 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 386 7 41 88 182 214 150 406), lower := (rows 97 386 7 41 88 32 64 128 256), losses := [] }

theorem u40826 : Upper (D 7) (R 7) [96,384,3,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40827 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 7 41 148 122 90 218 346), lower := (rows 97 386 7 41 148 32 64 128 256), losses := [] }

theorem u40827 : Upper (D 7) (R 7) [96,384,3,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40828 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 7 41 152 118 86 214 342), lower := (rows 97 386 7 41 152 32 64 128 256), losses := [] }

theorem u40828 : Upper (D 7) (R 7) [96,384,3,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40829 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 7 41 208 62 94 158 286), lower := (rows 97 386 7 41 208 32 64 128 256), losses := [] }

theorem u40829 : Upper (D 7) (R 7) [96,384,3,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40830 : Route 9 := (fun mask => (mask,id))

def c40830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40830 : Upper (D 7) (R 7) [96,384,3,34,68] 13 := by
  apply FastRouting.sound _ _ [96,384,3,34,68] 13 (by decide) (choices 1) [1,8,16,128] r40830 c40830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29787
  · exact u29788
  · exact u29789
  · exact u29790

def r40831 : Route 9 := (fun mask => (mask,id))

def c40831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40831 : Upper (D 7) (R 7) [96,384,3,34,72] 13 := by
  apply FastRouting.sound _ _ [96,384,3,34,72] 13 (by decide) (choices 1) [1,4,16,128] r40831 c40831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29791
  · exact u29792
  · exact u29793
  · exact u29794

def r40832 : Route 9 := (fun mask => (mask,id))

def c40832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40832 : Upper (D 7) (R 7) [96,384,3,34,129] 13 := by
  apply FastRouting.sound _ _ [96,384,3,34,129] 13 (by decide) (choices 1) [4,8,16,64] r40832 c40832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29795
  · exact u29796
  · exact u29797
  · exact u29798

def r40833 : Route 9 := (fun mask => (mask,id))

def c40833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40833 : Upper (D 7) (R 7) [96,384,3,34,132] 13 := by
  apply FastRouting.sound _ _ [96,384,3,34,132] 13 (by decide) (choices 1) [1,8,16,64] r40833 c40833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29799
  · exact u29800
  · exact u29801
  · exact u29802

def r40834 : Route 9 := (fun mask => (mask,id))

def c40834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40834 : Upper (D 7) (R 7) [96,384,3,34,136] 13 := by
  apply FastRouting.sound _ _ [96,384,3,34,136] 13 (by decide) (choices 1) [1,4,16,64] r40834 c40834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29803
  · exact u29804
  · exact u29805
  · exact u29806

def r40835 : Route 9 := (fun mask => (mask,id))

def c40835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40835 : Upper (D 7) (R 7) [96,384,3,34,192] 13 := by
  apply FastRouting.sound _ _ [96,384,3,34,192] 13 (by decide) (choices 1) [1,4,8,16] r40835 c40835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29807
  · exact u29808
  · exact u29809
  · exact u29810

def r40836 : Route 9 := (fun mask => (mask,id))

def c40836 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40836 : Upper (D 7) (R 7) [96,384,3,36,72] 13 := by
  apply FastRouting.sound _ _ [96,384,3,36,72] 13 (by decide) (choices 1) [1,2,16,128] r40836 c40836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29811
  · exact u29812
  · exact u29813
  · exact u29814

def r40837 : Route 9 := (fun mask => (mask,id))

def c40837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40837 : Upper (D 7) (R 7) [96,384,3,36,129] 13 := by
  apply FastRouting.sound _ _ [96,384,3,36,129] 13 (by decide) (choices 1) [2,8,16,64] r40837 c40837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29815
  · exact u29816
  · exact u29817
  · exact u29818

def b40838 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 7 44 146 121 89 217 345), lower := (rows 97 386 7 44 146 32 64 128 256), losses := [] }

theorem u40838 : Upper (D 7) (R 7) [96,384,3,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40839 : Route 9 := (fun mask => (mask,id))

def c40839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40839 : Upper (D 7) (R 7) [96,384,3,36,136] 13 := by
  apply FastRouting.sound _ _ [96,384,3,36,136] 13 (by decide) (choices 1) [1,2,16,64] r40839 c40839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29819
  · exact u29820
  · exact u29821
  · exact u29822

def r40840 : Route 9 := (fun mask => (mask,id))

def c40840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40840 : Upper (D 7) (R 7) [96,384,3,36,192] 13 := by
  apply FastRouting.sound _ _ [96,384,3,36,192] 13 (by decide) (choices 1) [1,2,8,16] r40840 c40840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29823
  · exact u29824
  · exact u29825
  · exact u29826

def b40841 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 386 7 56 88 167 199 135 391), lower := (rows 97 386 7 56 88 32 64 128 256), losses := [] }

theorem u40841 : Upper (D 7) (R 7) [96,384,3,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40842 : Route 9 := (fun mask => (mask,id))

def c40842 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40842 : Upper (D 7) (R 7) [96,384,3,48,129] 13 := by
  apply FastRouting.sound _ _ [96,384,3,48,129] 13 (by decide) (choices 1) [2,4,8,64] r40842 c40842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29827
  · exact u29828
  · exact u29829
  · exact u29830

def b40843 : PairBound 9 := { available := 77, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 7 56 146 109 77 205 333), lower := (rows 97 386 7 56 146 32 64 128 256), losses := [] }

theorem u40843 : Upper (D 7) (R 7) [96,384,3,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40844 : Route 9 := (fun mask => (mask,id))

def c40844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40844 : Upper (D 7) (R 7) [96,384,3,48,132] 13 := by
  apply FastRouting.sound _ _ [96,384,3,48,132] 13 (by decide) (choices 1) [1,2,8,64] r40844 c40844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29831
  · exact u29832
  · exact u29833
  · exact u29834

def b40845 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(2,7)], upper := (rows 97 386 7 56 152 103 71 199 327), lower := (rows 97 386 7 56 152 32 64 128 256), losses := [] }

theorem u40845 : Upper (D 7) (R 7) [96,384,3,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40846 : Route 9 := (fun mask => (mask,id))

def c40846 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40846 : Upper (D 7) (R 7) [96,384,3,48,192] 13 := by
  apply FastRouting.sound _ _ [96,384,3,48,192] 13 (by decide) (choices 1) [1,2,4,8] r40846 c40846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29835
  · exact u29836
  · exact u29837
  · exact u29838

def b40847 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 7 104 145 62 94 158 286), lower := (rows 97 386 7 104 145 32 64 128 256), losses := [] }

theorem u40847 : Upper (D 7) (R 7) [96,384,3,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40848 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 7 104 148 59 91 155 283), lower := (rows 97 386 7 104 148 32 64 128 256), losses := [] }

theorem u40848 : Upper (D 7) (R 7) [96,384,3,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40849 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 7 104 152 55 87 151 279), lower := (rows 97 386 7 104 152 32 64 128 256), losses := [] }

theorem u40849 : Upper (D 7) (R 7) [96,384,3,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40850 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 386 13 13 50 242 210 210 466), lower := (rows 97 386 13 13 50 32 64 128 256), losses := [] }

theorem u40850 : Upper (D 7) (R 7) [96,384,9,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40851 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 386 13 13 176 114 82 210 338), lower := (rows 97 386 13 13 176 32 64 128 256), losses := [] }

theorem u40851 : Upper (D 7) (R 7) [96,384,9,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40852 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 13 14 49 242 210 210 466), lower := (rows 97 386 13 14 49 32 64 128 256), losses := [] }

theorem u40852 : Upper (D 7) (R 7) [96,384,9,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40853 : Route 9 := (fun mask => (mask,id))

def c40853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40853 : Upper (D 7) (R 7) [96,384,9,6,34] 13 := by
  apply FastRouting.sound _ _ [96,384,9,6,34] 13 (by decide) (choices 1) [1,16,64,128] r40853 c40853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29839
  · exact u29840
  · exact u29841
  · exact u29842

def b40854 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 13 14 112 179 211 147 403), lower := (rows 97 386 13 14 112 32 64 128 256), losses := [] }

theorem u40854 : Upper (D 7) (R 7) [96,384,9,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40855 : Route 9 := (fun mask => (mask,id))

def c40855 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40855 : Upper (D 7) (R 7) [96,384,9,6,129] 13 := by
  apply FastRouting.sound _ _ [96,384,9,6,129] 13 (by decide) (choices 1) [2,16,64] r40855 c40855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29843
  · exact u29844
  · exact u29845

def b40856 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 13 14 146 113 113 241 369), lower := (rows 97 386 13 14 146 32 64 128 256), losses := [] }

theorem u40856 : Upper (D 7) (R 7) [96,384,9,6,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40857 : Route 9 := (fun mask => (mask,id))

def c40857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40857 : Upper (D 7) (R 7) [96,384,9,6,160] 13 := by
  apply FastRouting.sound _ _ [96,384,9,6,160] 13 (by decide) (choices 1) [1,2,16,64] r40857 c40857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29846
  · exact u29847
  · exact u29848
  · exact u29849

def b40858 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 386 13 25 22 226 226 226 482), lower := (rows 97 386 13 25 22 32 64 128 256), losses := [] }

theorem u40858 : Upper (D 7) (R 7) [96,384,9,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40859 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 4, targets := 194 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 97 386 13 25 50 230 198 198 454), lower := (rows 97 386 13 25 50 32 64 128 256), losses := [] }

theorem u40859 : Upper (D 7) (R 7) [96,384,9,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40859
end Delivery.IrregularNine14.P07
