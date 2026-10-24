import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0497
import IrregularNine14P07C0498

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40860 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 28, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 25 52 226 194 194 450), lower := (rows 97 386 13 25 52 32 64 128 256), losses := [] }

theorem u40860 : Upper (D 7) (R 7) [96,384,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40861 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 386 13 25 148 98 98 226 354), lower := (rows 97 386 13 25 148 32 64 128 256), losses := [] }

theorem u40861 : Upper (D 7) (R 7) [96,384,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40862 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 4, targets := 194 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 97 386 13 25 176 102 70 198 326), lower := (rows 97 386 13 25 176 32 64 128 256), losses := [] }

theorem u40862 : Upper (D 7) (R 7) [96,384,9,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40863 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 386 13 26 22 225 225 225 481), lower := (rows 97 386 13 26 22 32 64 128 256), losses := [] }

theorem u40863 : Upper (D 7) (R 7) [96,384,9,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40864 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 13 26 49 230 198 198 454), lower := (rows 97 386 13 26 49 32 64 128 256), losses := [] }

theorem u40864 : Upper (D 7) (R 7) [96,384,9,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40865 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 386 13 26 50 229 197 197 453), lower := (rows 97 386 13 26 50 32 64 128 256), losses := [] }

theorem u40865 : Upper (D 7) (R 7) [96,384,9,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40866 : Route 9 := (fun mask => (mask,id))

def c40866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40866 : Upper (D 7) (R 7) [96,384,9,18,36] 13 := by
  apply FastRouting.sound _ _ [96,384,9,18,36] 13 (by decide) (choices 1) [1,2,64,128] r40866 c40866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29850
  · exact u29851
  · exact u29852
  · exact u29853

def b40867 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 13 26 112 167 199 135 391), lower := (rows 97 386 13 26 112 32 64 128 256), losses := [] }

theorem u40867 : Upper (D 7) (R 7) [96,384,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40868 : Route 9 := (fun mask => (mask,id))

def c40868 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40868 : Upper (D 7) (R 7) [96,384,9,18,129] 13 := by
  apply FastRouting.sound _ _ [96,384,9,18,129] 13 (by decide) (choices 1) [2,4,64] r40868 c40868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29854
  · exact u29855
  · exact u29856

def b40869 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 386 13 26 146 101 101 229 357), lower := (rows 97 386 13 26 146 32 64 128 256), losses := [] }

theorem u40869 : Upper (D 7) (R 7) [96,384,9,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40870 : Route 9 := (fun mask => (mask,id))

def c40870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40870 : Upper (D 7) (R 7) [96,384,9,18,132] 13 := by
  apply FastRouting.sound _ _ [96,384,9,18,132] 13 (by decide) (choices 1) [1,2,64] r40870 c40870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29857
  · exact u29858
  · exact u29859

def r40871 : Route 9 := (fun mask => (mask,id))

def c40871 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40871 : Upper (D 7) (R 7) [96,384,9,18,160] 13 := by
  apply FastRouting.sound _ _ [96,384,9,18,160] 13 (by decide) (choices 1) [1,2,4,64] r40871 c40871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29860
  · exact u29861
  · exact u29862
  · exact u29863

def b40872 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 28, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 28 49 226 194 194 450), lower := (rows 97 386 13 28 49 32 64 128 256), losses := [] }

theorem u40872 : Upper (D 7) (R 7) [96,384,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40873 : Route 9 := (fun mask => (mask,id))

def c40873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40873 : Upper (D 7) (R 7) [96,384,9,20,34] 13 := by
  apply FastRouting.sound _ _ [96,384,9,20,34] 13 (by decide) (choices 1) [1,2,64,128] r40873 c40873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29864
  · exact u29865
  · exact u29866
  · exact u29867

def b40874 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 13 28 112 163 195 131 387), lower := (rows 97 386 13 28 112 32 64 128 256), losses := [] }

theorem u40874 : Upper (D 7) (R 7) [96,384,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40875 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 386 13 28 145 98 98 226 354), lower := (rows 97 386 13 28 145 32 64 128 256), losses := [] }

theorem u40875 : Upper (D 7) (R 7) [96,384,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40876 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 13 28 146 99 99 227 355), lower := (rows 97 386 13 28 146 32 64 128 256), losses := [] }

theorem u40876 : Upper (D 7) (R 7) [96,384,9,20,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40877 : Route 9 := (fun mask => (mask,id))

def c40877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40877 : Upper (D 7) (R 7) [96,384,9,20,160] 13 := by
  apply FastRouting.sound _ _ [96,384,9,20,160] 13 (by decide) (choices 1) [1,2,64] r40877 c40877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29868
  · exact u29869
  · exact u29870

def b40878 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 41 22 242 210 210 466), lower := (rows 97 386 13 41 22 32 64 128 256), losses := [] }

theorem u40878 : Upper (D 7) (R 7) [96,384,9,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40879 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 41 82 182 214 150 406), lower := (rows 97 386 13 41 82 32 64 128 256), losses := [] }

theorem u40879 : Upper (D 7) (R 7) [96,384,9,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40880 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 13 41 84 178 210 146 402), lower := (rows 97 386 13 41 84 32 64 128 256), losses := [] }

theorem u40880 : Upper (D 7) (R 7) [96,384,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40881 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 41 148 114 82 210 338), lower := (rows 97 386 13 41 148 32 64 128 256), losses := [] }

theorem u40881 : Upper (D 7) (R 7) [96,384,9,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40882 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 41 208 54 86 150 278), lower := (rows 97 386 13 41 208 32 64 128 256), losses := [] }

theorem u40882 : Upper (D 7) (R 7) [96,384,9,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40883 : Route 9 := (fun mask => (mask,id))

def c40883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40883 : Upper (D 7) (R 7) [96,384,9,34,6] 13 := by
  apply FastRouting.sound _ _ [96,384,9,34,6] 13 (by decide) (choices 1) [1,16,64,128] r40883 c40883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29871
  · exact u29872
  · exact u29873
  · exact u29874

def b40884 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 386 13 42 81 182 214 150 406), lower := (rows 97 386 13 42 81 32 64 128 256), losses := [] }

theorem u40884 : Upper (D 7) (R 7) [96,384,9,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40885 : Route 9 := (fun mask => (mask,id))

def c40885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40885 : Upper (D 7) (R 7) [96,384,9,34,66] 13 := by
  apply FastRouting.sound _ _ [96,384,9,34,66] 13 (by decide) (choices 1) [1,4,16,128] r40885 c40885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29875
  · exact u29876
  · exact u29877
  · exact u29878

def r40886 : Route 9 := (fun mask => (mask,id))

def c40886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40886 : Upper (D 7) (R 7) [96,384,9,34,68] 13 := by
  apply FastRouting.sound _ _ [96,384,9,34,68] 13 (by decide) (choices 1) [1,2,16,128] r40886 c40886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29879
  · exact u29880
  · exact u29881
  · exact u29882

def r40887 : Route 9 := (fun mask => (mask,id))

def c40887 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40887 : Upper (D 7) (R 7) [96,384,9,34,129] 13 := by
  apply FastRouting.sound _ _ [96,384,9,34,129] 13 (by decide) (choices 1) [2,4,16,64] r40887 c40887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29883
  · exact u29884
  · exact u29885
  · exact u29886

def b40888 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 13 42 146 117 85 213 341), lower := (rows 97 386 13 42 146 32 64 128 256), losses := [] }

theorem u40888 : Upper (D 7) (R 7) [96,384,9,34,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40889 : Route 9 := (fun mask => (mask,id))

def c40889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40889 : Upper (D 7) (R 7) [96,384,9,34,132] 13 := by
  apply FastRouting.sound _ _ [96,384,9,34,132] 13 (by decide) (choices 1) [1,2,16,64] r40889 c40889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29887
  · exact u29888
  · exact u29889
  · exact u29890

def r40890 : Route 9 := (fun mask => (mask,id))

def c40890 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40890 : Upper (D 7) (R 7) [96,384,9,34,192] 13 := by
  apply FastRouting.sound _ _ [96,384,9,34,192] 13 (by decide) (choices 1) [1,2,4,16] r40890 c40890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29891
  · exact u29892
  · exact u29893
  · exact u29894

def b40891 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 44 82 179 211 147 403), lower := (rows 97 386 13 44 82 32 64 128 256), losses := [] }

theorem u40891 : Upper (D 7) (R 7) [96,384,9,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40892 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 44 145 114 82 210 338), lower := (rows 97 386 13 44 145 32 64 128 256), losses := [] }

theorem u40892 : Upper (D 7) (R 7) [96,384,9,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40893 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 13 44 208 51 83 147 275), lower := (rows 97 386 13 44 208 32 64 128 256), losses := [] }

theorem u40893 : Upper (D 7) (R 7) [96,384,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40894 : Route 9 := (fun mask => (mask,id))

def c40894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40894 : Upper (D 7) (R 7) [96,384,9,48,6] 13 := by
  apply FastRouting.sound _ _ [96,384,9,48,6] 13 (by decide) (choices 1) [1,2,64,128] r40894 c40894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29895
  · exact u29896
  · exact u29897
  · exact u29898

def b40895 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 13 56 81 166 198 134 390), lower := (rows 97 386 13 56 81 32 64 128 256), losses := [] }

theorem u40895 : Upper (D 7) (R 7) [96,384,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40896 : Route 9 := (fun mask => (mask,id))

def c40896 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40896 : Upper (D 7) (R 7) [96,384,9,48,66] 13 := by
  apply FastRouting.sound _ _ [96,384,9,48,66] 13 (by decide) (choices 1) [1,2,4,128] r40896 c40896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29899
  · exact u29900
  · exact u29901
  · exact u29902

def b40897 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 13 56 84 163 195 131 387), lower := (rows 97 386 13 56 84 32 64 128 256), losses := [] }

theorem u40897 : Upper (D 7) (R 7) [96,384,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40898 : Route 9 := (fun mask => (mask,id))

def c40898 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40898 : Upper (D 7) (R 7) [96,384,9,48,129] 13 := by
  apply FastRouting.sound _ _ [96,384,9,48,129] 13 (by decide) (choices 1) [2,4,64] r40898 c40898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29903
  · exact u29904
  · exact u29905

def b40899 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 13 56 146 103 71 199 327), lower := (rows 97 386 13 56 146 32 64 128 256), losses := [] }

theorem u40899 : Upper (D 7) (R 7) [96,384,9,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40900 : Route 9 := (fun mask => (mask,id))

def c40900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40900 : Upper (D 7) (R 7) [96,384,9,48,132] 13 := by
  apply FastRouting.sound _ _ [96,384,9,48,132] 13 (by decide) (choices 1) [1,2,64] r40900 c40900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29906
  · exact u29907
  · exact u29908

def r40901 : Route 9 := (fun mask => (mask,id))

def c40901 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40901 : Upper (D 7) (R 7) [96,384,9,48,192] 13 := by
  apply FastRouting.sound _ _ [96,384,9,48,192] 13 (by decide) (choices 1) [1,2,4] r40901 c40901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29909
  · exact u29910
  · exact u29911

def b40902 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 13 104 22 179 211 147 403), lower := (rows 97 386 13 104 22 32 64 128 256), losses := [] }

theorem u40902 : Upper (D 7) (R 7) [96,384,9,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40903 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 13 104 145 54 86 150 278), lower := (rows 97 386 13 104 145 32 64 128 256), losses := [] }

theorem u40903 : Upper (D 7) (R 7) [96,384,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40904 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 13 104 148 51 83 147 275), lower := (rows 97 386 13 104 148 32 64 128 256), losses := [] }

theorem u40904 : Upper (D 7) (R 7) [96,384,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40905 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 386 13 137 22 114 114 242 370), lower := (rows 97 386 13 137 22 32 64 128 256), losses := [] }

theorem u40905 : Upper (D 7) (R 7) [96,384,9,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40906 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 386 13 137 50 118 86 214 342), lower := (rows 97 386 13 137 50 32 64 128 256), losses := [] }

theorem u40906 : Upper (D 7) (R 7) [96,384,9,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40907 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 386 13 137 52 114 82 210 338), lower := (rows 97 386 13 137 52 32 64 128 256), losses := [] }

theorem u40907 : Upper (D 7) (R 7) [96,384,9,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40908 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 386 13 138 22 113 113 241 369), lower := (rows 97 386 13 138 22 32 64 128 256), losses := [] }

theorem u40908 : Upper (D 7) (R 7) [96,384,9,130,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40909 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 386 13 138 50 117 85 213 341), lower := (rows 97 386 13 138 50 32 64 128 256), losses := [] }

theorem u40909 : Upper (D 7) (R 7) [96,384,9,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40910 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 386 13 138 52 115 83 211 339), lower := (rows 97 386 13 138 52 32 64 128 256), losses := [] }

theorem u40910 : Upper (D 7) (R 7) [96,384,9,130,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40911 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 13 140 49 114 82 210 338), lower := (rows 97 386 13 140 49 32 64 128 256), losses := [] }

theorem u40911 : Upper (D 7) (R 7) [96,384,9,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40912 : Route 9 := (fun mask => (mask,id))

def c40912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40912 : Upper (D 7) (R 7) [96,384,9,132,34] 13 := by
  apply FastRouting.sound _ _ [96,384,9,132,34] 13 (by decide) (choices 1) [1,2,16,64] r40912 c40912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29912
  · exact u29913
  · exact u29914
  · exact u29915

def b40913 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 13 140 112 51 83 147 275), lower := (rows 97 386 13 140 112 32 64 128 256), losses := [] }

theorem u40913 : Upper (D 7) (R 7) [96,384,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40914 : Route 9 := (fun mask => (mask,id))

def c40914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40914 : Upper (D 7) (R 7) [96,384,9,144,6] 13 := by
  apply FastRouting.sound _ _ [96,384,9,144,6] 13 (by decide) (choices 1) [1,2,64] r40914 c40914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29916
  · exact u29917
  · exact u29918

def b40915 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 13 152 49 102 70 198 326), lower := (rows 97 386 13 152 49 32 64 128 256), losses := [] }

theorem u40915 : Upper (D 7) (R 7) [96,384,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40916 : Route 9 := (fun mask => (mask,id))

def c40916 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40916 : Upper (D 7) (R 7) [96,384,9,144,34] 13 := by
  apply FastRouting.sound _ _ [96,384,9,144,34] 13 (by decide) (choices 1) [1,2,4,64] r40916 c40916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29919
  · exact u29920
  · exact u29921
  · exact u29922

def r40917 : Route 9 := (fun mask => (mask,id))

def c40917 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40917 : Upper (D 7) (R 7) [96,384,9,144,36] 13 := by
  apply FastRouting.sound _ _ [96,384,9,144,36] 13 (by decide) (choices 1) [1,2,64] r40917 c40917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29923
  · exact u29924
  · exact u29925

def b40918 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 13 152 112 39 71 135 263), lower := (rows 97 386 13 152 112 32 64 128 256), losses := [] }

theorem u40918 : Upper (D 7) (R 7) [96,384,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40919 : Route 9 := (fun mask => (mask,id))

def c40919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40919 : Upper (D 7) (R 7) [96,384,9,160,6] 13 := by
  apply FastRouting.sound _ _ [96,384,9,160,6] 13 (by decide) (choices 1) [1,2,16,64] r40919 c40919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29926
  · exact u29927
  · exact u29928
  · exact u29929

#print axioms u40919
end Delivery.IrregularNine14.P07
