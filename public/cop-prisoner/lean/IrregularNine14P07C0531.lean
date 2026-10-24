import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0245
import IrregularNine14P07C0246
import IrregularNine14P07C0247

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31860 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 387, targets := 32 },{ cop := 0, region := 228, targets := 1 }], pairs := [(0,5),(1,5),(2,0),(4,0)], upper := (rows 7 259 100 25 56 226 194 194 450), lower := (rows 7 259 100 25 56 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 35 67 131 259), good := (rows 486 486 100 508 60 32 64 128 256) }] }

theorem u31860 : Upper (D 7) (R 7) [6,257,96,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31861 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 259 100 25 112 170 202 138 394), lower := (rows 7 259 100 25 112 32 64 128 256), losses := [] }

theorem u31861 : Upper (D 7) (R 7) [6,257,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31862 : Route 9 := (fun mask => (mask,id))

def c31862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31862 : Upper (D 7) (R 7) [6,257,96,17,130] 13 := by
  apply FastRouting.sound _ _ [6,257,96,17,130] 13 (by decide) (choices 1) [8,64,128] r31862 c31862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14721
  · exact u14722
  · exact u14723

def r31863 : Route 9 := (fun mask => (mask,id))

def c31863 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31863 : Upper (D 7) (R 7) [6,257,96,17,136] 13 := by
  apply FastRouting.sound _ _ [6,257,96,17,136] 13 (by decide) (choices 1) [2,64,128] r31863 c31863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14724
  · exact u14725
  · exact u14726

def r31864 : Route 9 := (fun mask => (mask,id))

def c31864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31864 : Upper (D 7) (R 7) [6,257,96,17,160] 13 := by
  apply FastRouting.sound _ _ [6,257,96,17,160] 13 (by decide) (choices 1) [2,8,64,128] r31864 c31864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14727
  · exact u14728
  · exact u14729
  · exact u14730

def b31865 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,0),(2,1),(3,5)], upper := (rows 7 259 100 26 49 232 200 200 456), lower := (rows 7 259 100 26 49 32 64 128 256), losses := [] }

theorem u31865 : Upper (D 7) (R 7) [6,257,96,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31866 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 387, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,5),(1,5),(2,1),(4,1)], upper := (rows 7 259 100 26 56 225 193 193 449), lower := (rows 7 259 100 26 56 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 35 67 131 259), good := (rows 485 485 100 508 60 32 64 128 256) }] }

theorem u31866 : Upper (D 7) (R 7) [6,257,96,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31867 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 259 100 26 112 169 201 137 393), lower := (rows 7 259 100 26 112 32 64 128 256), losses := [] }

theorem u31867 : Upper (D 7) (R 7) [6,257,96,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31868 : Route 9 := (fun mask => (mask,id))

def c31868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31868 : Upper (D 7) (R 7) [6,257,96,18,129] 13 := by
  apply FastRouting.sound _ _ [6,257,96,18,129] 13 (by decide) (choices 1) [8,64,128] r31868 c31868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14731
  · exact u14732
  · exact u14733

def r31869 : Route 9 := (fun mask => (mask,id))

def c31869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31869 : Upper (D 7) (R 7) [6,257,96,18,136] 13 := by
  apply FastRouting.sound _ _ [6,257,96,18,136] 13 (by decide) (choices 1) [1,64,128] r31869 c31869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14734
  · exact u14735
  · exact u14736

def r31870 : Route 9 := (fun mask => (mask,id))

def c31870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31870 : Upper (D 7) (R 7) [6,257,96,18,160] 13 := by
  apply FastRouting.sound _ _ [6,257,96,18,160] 13 (by decide) (choices 1) [1,8,64,128] r31870 c31870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14737
  · exact u14738
  · exact u14739
  · exact u14740

def r31871 : Route 9 := (fun mask => (mask,id))

def c31871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31871 : Upper (D 7) (R 7) [6,257,96,33,66] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,66] 13 (by decide) (choices 1) [8,16,128] r31871 c31871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14741
  · exact u14742
  · exact u14743

def r31872 : Route 9 := (fun mask => (mask,id))

def c31872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31872 : Upper (D 7) (R 7) [6,257,96,33,72] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,72] 13 (by decide) (choices 1) [2,16,128] r31872 c31872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14744
  · exact u14745
  · exact u14746

def r31873 : Route 9 := (fun mask => (mask,id))

def c31873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u31873 : Upper (D 7) (R 7) [6,257,96,33,130] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,130] 13 (by decide) (choices 1) [8,16,64,128] r31873 c31873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14747
  · exact u14748
  · exact u14749
  · exact u14750

def r31874 : Route 9 := (fun mask => (mask,id))

def c31874 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31874 : Upper (D 7) (R 7) [6,257,96,33,136] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,136] 13 (by decide) (choices 1) [2,16,64,128] r31874 c31874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14751
  · exact u14752
  · exact u14753
  · exact u14754

def r31875 : Route 9 := (fun mask => (mask,id))

def c31875 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31875 : Upper (D 7) (R 7) [6,257,96,33,192] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,192] 13 (by decide) (choices 1) [2,8,16,128] r31875 c31875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14755
  · exact u14756
  · exact u14757
  · exact u14758

def r31876 : Route 9 := (fun mask => (mask,id))

def c31876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31876 : Upper (D 7) (R 7) [6,257,96,34,72] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,72] 13 (by decide) (choices 1) [1,16,128] r31876 c31876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14759
  · exact u14760
  · exact u14761

def r31877 : Route 9 := (fun mask => (mask,id))

def c31877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u31877 : Upper (D 7) (R 7) [6,257,96,34,129] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,129] 13 (by decide) (choices 1) [8,16,64,128] r31877 c31877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14762
  · exact u14763
  · exact u14764
  · exact u14765

def r31878 : Route 9 := (fun mask => (mask,id))

def c31878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31878 : Upper (D 7) (R 7) [6,257,96,34,136] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,136] 13 (by decide) (choices 1) [1,16,64,128] r31878 c31878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14766
  · exact u14767
  · exact u14768
  · exact u14769

def r31879 : Route 9 := (fun mask => (mask,id))

def c31879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31879 : Upper (D 7) (R 7) [6,257,96,34,192] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,192] 13 (by decide) (choices 1) [1,8,16,128] r31879 c31879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14770
  · exact u14771
  · exact u14772
  · exact u14773

def b31880 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 24, targets := 131 }], pairs := [(3,0),(3,1),(3,7),(4,0)], upper := (rows 7 259 100 56 88 163 195 131 387), lower := (rows 7 259 100 56 88 32 64 128 256), losses := [] }

theorem u31880 : Upper (D 7) (R 7) [6,257,96,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31881 : Route 9 := (fun mask => (mask,id))

def c31881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31881 : Upper (D 7) (R 7) [6,257,96,48,129] 13 := by
  apply FastRouting.sound _ _ [6,257,96,48,129] 13 (by decide) (choices 1) [2,8,64,128] r31881 c31881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14774
  · exact u14775
  · exact u14776
  · exact u14777

def r31882 : Route 9 := (fun mask => (mask,id))

def c31882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31882 : Upper (D 7) (R 7) [6,257,96,48,130] 13 := by
  apply FastRouting.sound _ _ [6,257,96,48,130] 13 (by decide) (choices 1) [1,8,64,128] r31882 c31882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14778
  · exact u14779
  · exact u14780
  · exact u14781

def r31883 : Route 9 := (fun mask => (mask,id))

def c31883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31883 : Upper (D 7) (R 7) [6,257,96,48,136] 13 := by
  apply FastRouting.sound _ _ [6,257,96,48,136] 13 (by decide) (choices 1) [1,2,64,128] r31883 c31883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14782
  · exact u14783
  · exact u14784
  · exact u14785

def r31884 : Route 9 := (fun mask => (mask,id))

def c31884 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31884 : Upper (D 7) (R 7) [6,257,96,48,192] 13 := by
  apply FastRouting.sound _ _ [6,257,96,48,192] 13 (by decide) (choices 1) [1,2,8,128] r31884 c31884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14786
  · exact u14787
  · exact u14788
  · exact u14789

def b31885 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 259 100 104 145 186 218 154 410), lower := (rows 7 259 100 104 145 32 64 128 256), losses := [] }

theorem u31885 : Upper (D 7) (R 7) [6,257,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31886 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 259 100 104 146 185 217 153 409), lower := (rows 7 259 100 104 146 32 64 128 256), losses := [] }

theorem u31886 : Upper (D 7) (R 7) [6,257,96,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31887 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 259 100 104 152 179 211 147 403), lower := (rows 7 259 100 104 152 32 64 128 256), losses := [] }

theorem u31887 : Upper (D 7) (R 7) [6,257,96,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31888 : Route 9 := (fun mask => (mask,id))

def c31888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31888 : Upper (D 7) (R 7) [6,257,96,129,130] 13 := by
  apply FastRouting.sound _ _ [6,257,96,129,130] 13 (by decide) (choices 1) [8,16,64] r31888 c31888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14790
  · exact u14791
  · exact u14792

def b31889 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 259 100 137 152 114 114 242 370), lower := (rows 7 259 100 137 152 32 64 128 256), losses := [] }

theorem u31889 : Upper (D 7) (R 7) [6,257,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31890 : Route 9 := (fun mask => (mask,id))

def c31890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31890 : Upper (D 7) (R 7) [6,257,96,129,160] 13 := by
  apply FastRouting.sound _ _ [6,257,96,129,160] 13 (by decide) (choices 1) [2,8,16,64] r31890 c31890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14793
  · exact u14794
  · exact u14795
  · exact u14796

def b31891 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 259 100 138 152 113 113 241 369), lower := (rows 7 259 100 138 152 32 64 128 256), losses := [] }

theorem u31891 : Upper (D 7) (R 7) [6,257,96,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31892 : Route 9 := (fun mask => (mask,id))

def c31892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31892 : Upper (D 7) (R 7) [6,257,96,130,160] 13 := by
  apply FastRouting.sound _ _ [6,257,96,130,160] 13 (by decide) (choices 1) [1,8,16,64] r31892 c31892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14797
  · exact u14798
  · exact u14799
  · exact u14800

def b31893 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 259 100 152 152 99 99 227 355), lower := (rows 7 259 100 152 152 32 64 128 256), losses := [] }

theorem u31893 : Upper (D 7) (R 7) [6,257,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31894 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 259 100 152 176 107 75 203 331), lower := (rows 7 259 100 152 176 32 64 128 256), losses := [] }

theorem u31894 : Upper (D 7) (R 7) [6,257,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31895 : Route 9 := (fun mask => (mask,id))

def c31895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31895 : Upper (D 7) (R 7) [6,257,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,257,96,160,192] 13 (by decide) (choices 1) [1,2,8,16] r31895 c31895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14801
  · exact u14802
  · exact u14803
  · exact u14804

def b31896 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 21 41 50 224 192 192 448), lower := (rows 7 266 21 41 50 32 64 128 256), losses := [] }

theorem u31896 : Upper (D 7) (R 7) [6,264,17,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31897 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 266 21 41 82 224 224 224 480), lower := (rows 7 266 21 41 82 32 64 128 256), losses := [] }

theorem u31897 : Upper (D 7) (R 7) [6,264,17,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31898 : Route 9 := (fun mask => (mask,id))

def c31898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31898 : Upper (D 7) (R 7) [6,264,17,33,96] 13 := by
  apply FastRouting.sound _ _ [6,264,17,33,96] 13 (by decide) (choices 1) [2,64,128] r31898 c31898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14805
  · exact u14806
  · exact u14807

def r31899 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31899 : Upper (D 7) (R 7) [6,264,17,33,192] 13 := by
  apply FastRouting.sound _ _ [6,264,17,33,192] 13 (by decide) (choices 1) [2,64] r31899 c31899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14808
  · exact u14809

def b31900 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 21 42 49 224 192 192 448), lower := (rows 7 266 21 42 49 32 64 128 256), losses := [] }

theorem u31900 : Upper (D 7) (R 7) [6,264,17,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31901 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 0, region := 490, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 7 266 21 42 81 224 224 224 480), lower := (rows 7 266 21 42 81 32 64 128 256), losses := [] }

theorem u31901 : Upper (D 7) (R 7) [6,264,17,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31902 : Route 9 := (fun mask => (mask,id))

def c31902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31902 : Upper (D 7) (R 7) [6,264,17,34,96] 13 := by
  apply FastRouting.sound _ _ [6,264,17,34,96] 13 (by decide) (choices 1) [1,64,128] r31902 c31902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14810
  · exact u14811
  · exact u14812

def r31903 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31903 : Upper (D 7) (R 7) [6,264,17,34,192] 13 := by
  apply FastRouting.sound _ _ [6,264,17,34,192] 13 (by decide) (choices 1) [1,64] r31903 c31903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14813
  · exact u14814

def b31904 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 21, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 266 21 104 19 224 224 224 480), lower := (rows 7 266 21 104 19 32 64 128 256), losses := [] }

theorem u31904 : Upper (D 7) (R 7) [6,264,17,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31905 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 266 21 104 49 226 194 194 450), lower := (rows 7 266 21 104 49 32 64 128 256), losses := [] }

theorem u31905 : Upper (D 7) (R 7) [6,264,17,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31906 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 21 104 50 225 193 193 449), lower := (rows 7 266 21 104 50 32 64 128 256), losses := [] }

theorem u31906 : Upper (D 7) (R 7) [6,264,17,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31907 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 16, targets := 131 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,7)], upper := (rows 7 266 21 104 112 163 195 131 387), lower := (rows 7 266 21 104 112 32 64 128 256), losses := [] }

theorem u31907 : Upper (D 7) (R 7) [6,264,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31908 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 266 21 104 145 226 226 226 482), lower := (rows 7 266 21 104 145 32 64 128 256), losses := [] }

theorem u31908 : Upper (D 7) (R 7) [6,264,17,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31909 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 266 21 104 146 225 225 225 481), lower := (rows 7 266 21 104 146 32 64 128 256), losses := [] }

theorem u31909 : Upper (D 7) (R 7) [6,264,17,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31910 : Route 9 := (fun mask => (mask,id))

def c31910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31910 : Upper (D 7) (R 7) [6,264,17,96,160] 13 := by
  apply FastRouting.sound _ _ [6,264,17,96,160] 13 (by decide) (choices 1) [1,2,64,128] r31910 c31910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14815
  · exact u14816
  · exact u14817
  · exact u14818

def b31911 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 25 50 224 192 192 448), lower := (rows 7 266 37 25 50 32 64 128 256), losses := [] }

theorem u31911 : Upper (D 7) (R 7) [6,264,33,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31912 : Route 9 := (fun mask => (mask,id))

def c31912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31912 : Upper (D 7) (R 7) [6,264,33,17,66] 13 := by
  apply FastRouting.sound _ _ [6,264,33,17,66] 13 (by decide) (choices 1) [64,128] r31912 c31912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14819
  · exact u14820

def r31913 : Route 9 := (fun mask => (mask,id))

def c31913 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31913 : Upper (D 7) (R 7) [6,264,33,17,96] 13 := by
  apply FastRouting.sound _ _ [6,264,33,17,96] 13 (by decide) (choices 1) [2,64,128] r31913 c31913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14821
  · exact u14822
  · exact u14823

def r31914 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31914 : Upper (D 7) (R 7) [6,264,33,17,192] 13 := by
  apply FastRouting.sound _ _ [6,264,33,17,192] 13 (by decide) (choices 1) [2,64] r31914 c31914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14824
  · exact u14825

def b31915 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 2, region := 16, targets := 192 }], pairs := [(2,1),(4,1),(4,6),(4,7)], upper := (rows 7 266 37 26 49 224 192 192 448), lower := (rows 7 266 37 26 49 32 64 128 256), losses := [] }

theorem u31915 : Upper (D 7) (R 7) [6,264,33,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31916 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 266 37 26 81 224 224 224 480), lower := (rows 7 266 37 26 81 32 64 128 256), losses := [] }

theorem u31916 : Upper (D 7) (R 7) [6,264,33,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31917 : Route 9 := (fun mask => (mask,id))

def c31917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31917 : Upper (D 7) (R 7) [6,264,33,18,96] 13 := by
  apply FastRouting.sound _ _ [6,264,33,18,96] 13 (by decide) (choices 1) [1,64,128] r31917 c31917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14826
  · exact u14827
  · exact u14828

def r31918 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31918 : Upper (D 7) (R 7) [6,264,33,18,192] 13 := by
  apply FastRouting.sound _ _ [6,264,33,18,192] 13 (by decide) (choices 1) [1,64] r31918 c31918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14829
  · exact u14830

def b31919 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 7 266 37 56 19 224 192 192 448), lower := (rows 7 266 37 56 19 32 64 128 256), losses := [] }

theorem u31919 : Upper (D 7) (R 7) [6,264,33,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u31919
end Delivery.IrregularNine14.P07
