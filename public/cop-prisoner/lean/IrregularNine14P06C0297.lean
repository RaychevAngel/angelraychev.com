import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0084
import IrregularNine14P06C0085

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17820 : Route 9 := (fun mask => (mask,id))

def c17820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17820 : Upper (D 6) (R 6) [10,160,258,65,36,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,36,64] 13 (by decide) (choices 1) [1,4,16] r17820 c17820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5053
  · exact u5054
  · exact u5055

def b17821 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 262 73 84 33 116 180 308), lower := (rows 11 162 262 73 84 33 64 128 256), losses := [] }

theorem u17821 : Upper (D 6) (R 6) [10,160,258,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17822 : Route 9 := (fun mask => (mask,id))

def c17822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17822 : Upper (D 6) (R 6) [10,160,258,65,68,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,68,4] 13 (by decide) (choices 1) [1,16,32] r17822 c17822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5056
  · exact u5057
  · exact u5058

def r17823 : Route 9 := (fun mask => (mask,id))

def c17823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17823 : Upper (D 6) (R 6) [10,160,258,65,68,16] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,68,16] 13 (by decide) (choices 1) [1,4,32] r17823 c17823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5059
  · exact u5060
  · exact u5061

def b17824 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 262 73 112 33 84 148 276), lower := (rows 11 162 262 73 112 33 64 128 256), losses := [] }

theorem u17824 : Upper (D 6) (R 6) [10,160,258,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17825 : Route 9 := (fun mask => (mask,id))

def c17825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17825 : Upper (D 6) (R 6) [10,160,258,65,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,96,4] 13 (by decide) (choices 1) [1,4,16] r17825 c17825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5062
  · exact u5063
  · exact u5064

def b17826 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 262 73 112 48 69 133 261), lower := (rows 11 162 262 73 112 48 64 128 256), losses := [] }

theorem u17826 : Upper (D 6) (R 6) [10,160,258,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17826 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17827 : Route 9 := (fun mask => (mask,id))

def c17827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17827 : Upper (D 6) (R 6) [10,160,258,68,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,5,1] 13 (by decide) (choices 1) [16,32] r17827 c17827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5065
  · exact u5066

def b17828 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 104, targets := 2 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,1)], upper := (rows 11 162 262 76 21 48 97 225 353), lower := (rows 11 162 262 76 21 48 64 128 256), losses := [] }

theorem u17828 : Upper (D 6) (R 6) [10,160,258,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17828 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17829 : Route 9 := (fun mask => (mask,id))

def c17829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17829 : Upper (D 6) (R 6) [10,160,258,68,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,5,64] 13 (by decide) (choices 1) [1,16,32] r17829 c17829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5067
  · exact u5068
  · exact u5069

def b17830 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 262 76 49 33 84 212 340), lower := (rows 11 162 262 76 49 33 64 128 256), losses := [] }

theorem u17830 : Upper (D 6) (R 6) [10,160,258,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17831 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 11 162 262 76 49 36 81 209 337), lower := (rows 11 162 262 76 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 81 145 273), good := (rows 505 160 292 108 497 36 64 128 256) },{ target := 6, region := (rows 1 2 4 8 17 44 0 128 256), good := (rows 59 162 294 44 49 36 0 128 256) }] }

theorem u17831 : Upper (D 6) (R 6) [10,160,258,68,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17832 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 262 76 49 48 69 197 325), lower := (rows 11 162 262 76 49 48 64 128 256), losses := [] }

theorem u17832 : Upper (D 6) (R 6) [10,160,258,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17832 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17833 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 162 262 76 49 96 85 149 277), lower := (rows 11 162 262 76 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 104 64 128 256), good := (rows 57 160 260 108 49 96 96 128 256) }] }

theorem u17833 : Upper (D 6) (R 6) [10,160,258,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17834 : Route 9 := (fun mask => (mask,id))

def c17834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17834 : Upper (D 6) (R 6) [10,160,258,68,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,36,1] 13 (by decide) (choices 1) [1,16] r17834 c17834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5070
  · exact u5071

def b17835 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 262 76 52 48 65 193 321), lower := (rows 11 162 262 76 52 48 64 128 256), losses := [] }

theorem u17835 : Upper (D 6) (R 6) [10,160,258,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17835 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17836 : Route 9 := (fun mask => (mask,id))

def c17836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17836 : Upper (D 6) (R 6) [10,160,258,68,36,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,36,64] 13 (by decide) (choices 1) [1,16] r17836 c17836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5072
  · exact u5073

def r17837 : Route 9 := (fun mask => (mask,id))

def c17837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17837 : Upper (D 6) (R 6) [10,160,258,68,65,1] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,65,1] 13 (by decide) (choices 1) [4,16,32] r17837 c17837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5074
  · exact u5075
  · exact u5076

def b17838 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 162 262 76 81 36 113 177 305), lower := (rows 11 162 262 76 81 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 160 292 108 465 36 64 128 256) }] }

theorem u17838 : Upper (D 6) (R 6) [10,160,258,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17839 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 162 262 76 81 48 101 165 293), lower := (rows 11 162 262 76 81 48 64 128 256), losses := [] }

theorem u17839 : Upper (D 6) (R 6) [10,160,258,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17839 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17840 : Route 9 := (fun mask => (mask,id))

def c17840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17840 : Upper (D 6) (R 6) [10,160,258,68,96,1] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,96,1] 13 (by decide) (choices 1) [1,4,16] r17840 c17840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5077
  · exact u5078
  · exact u5079

def r17841 : Route 9 := (fun mask => (mask,id))

def c17841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17841 : Upper (D 6) (R 6) [10,160,258,68,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,96,4] 13 (by decide) (choices 1) [1,16] r17841 c17841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5080
  · exact u5081

def b17842 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 262 76 112 48 69 133 261), lower := (rows 11 162 262 76 112 48 64 128 256), losses := [] }

theorem u17842 : Upper (D 6) (R 6) [10,160,258,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17842 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17843 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 162 262 88 21 33 100 228 356), lower := (rows 11 162 262 88 21 33 64 128 256), losses := [] }

theorem u17843 : Upper (D 6) (R 6) [10,160,258,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17844 : Route 9 := (fun mask => (mask,id))

def c17844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17844 : Upper (D 6) (R 6) [10,160,258,80,5,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,5,4] 13 (by decide) (choices 1) [1,32] r17844 c17844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5082
  · exact u5083

def r17845 : Route 9 := (fun mask => (mask,id))

def c17845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17845 : Upper (D 6) (R 6) [10,160,258,80,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,5,64] 13 (by decide) (choices 1) [1,4,32] r17845 c17845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5084
  · exact u5085
  · exact u5086

def b17846 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 262 88 49 33 68 196 324), lower := (rows 11 162 262 88 49 33 64 128 256), losses := [] }

theorem u17846 : Upper (D 6) (R 6) [10,160,258,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17847 : Route 9 := (fun mask => (mask,id))

def c17847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17847 : Upper (D 6) (R 6) [10,160,258,80,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,33,4] 13 (by decide) (choices 1) [1,4] r17847 c17847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5087
  · exact u5088

def b17848 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 390, targets := 64 },{ cop := 0, region := 260, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 11 162 262 88 49 96 69 133 261), lower := (rows 11 162 262 88 49 96 64 128 256), losses := [] }

theorem u17848 : Upper (D 6) (R 6) [10,160,258,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17849 : Route 9 := (fun mask => (mask,id))

def c17849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17849 : Upper (D 6) (R 6) [10,160,258,80,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,36,1] 13 (by decide) (choices 1) [1,4] r17849 c17849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5089
  · exact u5090

def b17850 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 262 88 52 36 65 193 321), lower := (rows 11 162 262 88 52 36 64 128 256), losses := [] }

theorem u17850 : Upper (D 6) (R 6) [10,160,258,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17851 : Route 9 := (fun mask => (mask,id))

def c17851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17851 : Upper (D 6) (R 6) [10,160,258,80,36,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,36,64] 13 (by decide) (choices 1) [1,4] r17851 c17851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5091
  · exact u5092

def r17852 : Route 9 := (fun mask => (mask,id))

def c17852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17852 : Upper (D 6) (R 6) [10,160,258,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,160,258,96,68,1] 13 (by decide) (choices 1) [1,4,16] r17852 c17852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5093
  · exact u5094
  · exact u5095

def b17853 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 262 104 84 36 81 145 273), lower := (rows 11 162 262 104 84 36 64 128 256), losses := [] }

theorem u17853 : Upper (D 6) (R 6) [10,160,258,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17854 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 262 104 84 48 69 133 261), lower := (rows 11 162 262 104 84 48 64 128 256), losses := [] }

theorem u17854 : Upper (D 6) (R 6) [10,160,258,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17854 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17855 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 276 13 49 34 68 196 324), lower := (rows 11 162 276 13 49 34 64 128 256), losses := [] }

theorem u17855 : Upper (D 6) (R 6) [10,160,272,5,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17856 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 276 13 49 36 66 194 322), lower := (rows 11 162 276 13 49 36 64 128 256), losses := [] }

theorem u17856 : Upper (D 6) (R 6) [10,160,272,5,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17857 : Route 9 := (fun mask => (mask,id))

def c17857 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17857 : Upper (D 6) (R 6) [10,160,272,5,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,33,64] 13 (by decide) (choices 1) [2,4] r17857 c17857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5096
  · exact u5097

def b17858 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 52 33 66 194 322), lower := (rows 11 162 276 13 52 33 64 128 256), losses := [] }

theorem u17858 : Upper (D 6) (R 6) [10,160,272,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17859 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 13 52 34 65 193 321), lower := (rows 11 162 276 13 52 34 64 128 256), losses := [] }

theorem u17859 : Upper (D 6) (R 6) [10,160,272,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17860 : Route 9 := (fun mask => (mask,id))

def c17860 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17860 : Upper (D 6) (R 6) [10,160,272,5,36,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,36,64] 13 (by decide) (choices 1) [1,2] r17860 c17860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5098
  · exact u5099

def b17861 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 13 81 34 100 228 356), lower := (rows 11 162 276 13 81 34 64 128 256), losses := [] }

theorem u17861 : Upper (D 6) (R 6) [10,160,272,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17862 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 5, region := 194, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 162 276 13 81 36 98 226 354), lower := (rows 11 162 276 13 81 36 64 128 256), losses := [] }

theorem u17862 : Upper (D 6) (R 6) [10,160,272,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17863 : Route 9 := (fun mask => (mask,id))

def c17863 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17863 : Upper (D 6) (R 6) [10,160,272,5,65,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,65,64] 13 (by decide) (choices 1) [2,4,32] r17863 c17863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5100
  · exact u5101
  · exact u5102

def b17864 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 82 33 100 228 356), lower := (rows 11 162 276 13 82 33 64 128 256), losses := [] }

theorem u17864 : Upper (D 6) (R 6) [10,160,272,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17865 : Route 9 := (fun mask => (mask,id))

def c17865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17865 : Upper (D 6) (R 6) [10,160,272,5,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,66,4] 13 (by decide) (choices 1) [1,32] r17865 c17865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5103
  · exact u5104

def r17866 : Route 9 := (fun mask => (mask,id))

def c17866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17866 : Upper (D 6) (R 6) [10,160,272,5,66,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,66,64] 13 (by decide) (choices 1) [1,4,32] r17866 c17866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5105
  · exact u5106
  · exact u5107

def b17867 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 84 33 98 226 354), lower := (rows 11 162 276 13 84 33 64 128 256), losses := [] }

theorem u17867 : Upper (D 6) (R 6) [10,160,272,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17868 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 13 84 34 97 225 353), lower := (rows 11 162 276 13 84 34 64 128 256), losses := [] }

theorem u17868 : Upper (D 6) (R 6) [10,160,272,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17869 : Route 9 := (fun mask => (mask,id))

def c17869 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17869 : Upper (D 6) (R 6) [10,160,272,5,68,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,68,64] 13 (by decide) (choices 1) [1,2,32] r17869 c17869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5108
  · exact u5109
  · exact u5110

def b17870 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 112 33 70 198 326), lower := (rows 11 162 276 13 112 33 64 128 256), losses := [] }

theorem u17870 : Upper (D 6) (R 6) [10,160,272,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17871 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 13 112 34 69 197 325), lower := (rows 11 162 276 13 112 34 64 128 256), losses := [] }

theorem u17871 : Upper (D 6) (R 6) [10,160,272,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17872 : Route 9 := (fun mask => (mask,id))

def c17872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17872 : Upper (D 6) (R 6) [10,160,272,5,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,96,4] 13 (by decide) (choices 1) [1,2] r17872 c17872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5111
  · exact u5112

def b17873 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 276 13 112 96 71 135 263), lower := (rows 11 162 276 13 112 96 64 128 256), losses := [] }

theorem u17873 : Upper (D 6) (R 6) [10,160,272,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17874 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 276 44 81 33 70 198 326), lower := (rows 11 162 276 44 81 33 64 128 256), losses := [] }

theorem u17874 : Upper (D 6) (R 6) [10,160,272,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17875 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 276 44 81 34 69 197 325), lower := (rows 11 162 276 44 81 34 64 128 256), losses := [] }

theorem u17875 : Upper (D 6) (R 6) [10,160,272,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17876 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 276 44 81 36 67 195 323), lower := (rows 11 162 276 44 81 36 64 128 256), losses := [] }

theorem u17876 : Upper (D 6) (R 6) [10,160,272,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17877 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 276 44 81 96 71 135 263), lower := (rows 11 162 276 44 81 96 64 128 256), losses := [] }

theorem u17877 : Upper (D 6) (R 6) [10,160,272,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17878 : Route 9 := (fun mask => (mask,id))

def c17878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17878 : Upper (D 6) (R 6) [10,160,272,36,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,272,36,66,1] 13 (by decide) (choices 1) [1,4] r17878 c17878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5113
  · exact u5114

def b17879 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 276 44 82 36 65 193 321), lower := (rows 11 162 276 44 82 36 64 128 256), losses := [] }

theorem u17879 : Upper (D 6) (R 6) [10,160,272,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17879
end Delivery.IrregularNine14.P06
