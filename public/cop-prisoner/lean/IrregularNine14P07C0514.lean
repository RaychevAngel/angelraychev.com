import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0216
import IrregularNine14P07C0217
import IrregularNine14P07C0218

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30840 : Route 9 := (fun mask => (mask,id))

def c30840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30840 : Upper (D 7) (R 7) [6,40,65,144,320] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,320] 13 (by decide) (choices 1) [1,2,128] r30840 c30840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13010
  · exact u13011
  · exact u13012

def b30841 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 69 152 400 99 99 227 355), lower := (rows 7 42 69 152 400 32 64 128 256), losses := [] }

theorem u30841 : Upper (D 7) (R 7) [6,40,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30842 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,5),(4,7)], upper := (rows 7 42 69 200 19 432 496 432 432), lower := (rows 7 42 69 200 19 32 64 128 256), losses := [] }

theorem u30842 : Upper (D 7) (R 7) [6,40,65,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30843 : Route 9 := (fun mask => (mask,id))

def c30843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30843 : Upper (D 7) (R 7) [6,40,65,192,33] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,33] 13 (by decide) (choices 1) [2,16,128,256] r30843 c30843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13013
  · exact u13014
  · exact u13015
  · exact u13016

def b30844 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 69 200 50 433 465 401 401), lower := (rows 7 42 69 200 50 32 64 128 256), losses := [] }

theorem u30844 : Upper (D 7) (R 7) [6,40,65,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30845 : Route 9 := (fun mask => (mask,id))

def c30845 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30845 : Upper (D 7) (R 7) [6,40,65,192,129] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,129] 13 (by decide) (choices 1) [2,16,256] r30845 c30845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13017
  · exact u13018
  · exact u13019

def r30846 : Route 9 := (fun mask => (mask,id))

def c30846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30846 : Upper (D 7) (R 7) [6,40,65,192,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,130] 13 (by decide) (choices 1) [1,16,256] r30846 c30846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13020
  · exact u13021
  · exact u13022

def r30847 : Route 9 := (fun mask => (mask,id))

def c30847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30847 : Upper (D 7) (R 7) [6,40,65,192,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,160] 13 (by decide) (choices 1) [1,2,16,256] r30847 c30847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13023
  · exact u13024
  · exact u13025
  · exact u13026

def r30848 : Route 9 := (fun mask => (mask,id))

def c30848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30848 : Upper (D 7) (R 7) [6,40,65,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,257] 13 (by decide) (choices 1) [2,16,128] r30848 c30848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13027
  · exact u13028
  · exact u13029

def r30849 : Route 9 := (fun mask => (mask,id))

def c30849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30849 : Upper (D 7) (R 7) [6,40,65,192,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,258] 13 (by decide) (choices 1) [1,16,128] r30849 c30849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13030
  · exact u13031
  · exact u13032

def r30850 : Route 9 := (fun mask => (mask,id))

def c30850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30850 : Upper (D 7) (R 7) [6,40,65,192,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,288] 13 (by decide) (choices 1) [1,2,16,128] r30850 c30850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13033
  · exact u13034
  · exact u13035
  · exact u13036

def r30851 : Route 9 := (fun mask => (mask,id))

def c30851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30851 : Upper (D 7) (R 7) [6,40,65,192,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,384] 13 (by decide) (choices 1) [1,2,16] r30851 c30851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13037
  · exact u13038
  · exact u13039

def b30852 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 16, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 42 69 265 50 240 208 208 464), lower := (rows 7 42 69 265 50 32 64 128 256), losses := [] }

theorem u30852 : Upper (D 7) (R 7) [6,40,65,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30853 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 265 82 176 240 176 432), lower := (rows 7 42 69 265 82 32 64 128 256), losses := [] }

theorem u30853 : Upper (D 7) (R 7) [6,40,65,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30854 : Route 9 := (fun mask => (mask,id))

def c30854 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30854 : Upper (D 7) (R 7) [6,40,65,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,257,96] 13 (by decide) (choices 1) [2,16,128] r30854 c30854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13040
  · exact u13041
  · exact u13042

def r30855 : Route 9 := (fun mask => (mask,id))

def c30855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30855 : Upper (D 7) (R 7) [6,40,65,257,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,257,130] 13 (by decide) (choices 1) [16,64,128] r30855 c30855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13043
  · exact u13044
  · exact u13045

def r30856 : Route 9 := (fun mask => (mask,id))

def c30856 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30856 : Upper (D 7) (R 7) [6,40,65,257,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,257,160] 13 (by decide) (choices 1) [2,16,64,128] r30856 c30856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13046
  · exact u13047
  · exact u13048
  · exact u13049

def r30857 : Route 9 := (fun mask => (mask,id))

def c30857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30857 : Upper (D 7) (R 7) [6,40,65,257,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,257,192] 13 (by decide) (choices 1) [2,16,128] r30857 c30857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13050
  · exact u13051
  · exact u13052

def b30858 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 266 49 240 208 208 464), lower := (rows 7 42 69 266 49 32 64 128 256), losses := [] }

theorem u30858 : Upper (D 7) (R 7) [6,40,65,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30859 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 2, region := 16, targets := 160 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 69 266 81 176 240 176 432), lower := (rows 7 42 69 266 81 32 64 128 256), losses := [] }

theorem u30859 : Upper (D 7) (R 7) [6,40,65,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30860 : Route 9 := (fun mask => (mask,id))

def c30860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30860 : Upper (D 7) (R 7) [6,40,65,258,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258,96] 13 (by decide) (choices 1) [1,16,128] r30860 c30860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13053
  · exact u13054
  · exact u13055

def b30861 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 266 145 240 240 240 496), lower := (rows 7 42 69 266 145 32 64 128 256), losses := [] }

theorem u30861 : Upper (D 7) (R 7) [6,40,65,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30862 : Route 9 := (fun mask => (mask,id))

def c30862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30862 : Upper (D 7) (R 7) [6,40,65,258,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258,160] 13 (by decide) (choices 1) [1,16,64,128] r30862 c30862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13056
  · exact u13057
  · exact u13058
  · exact u13059

def r30863 : Route 9 := (fun mask => (mask,id))

def c30863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30863 : Upper (D 7) (R 7) [6,40,65,258,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258,192] 13 (by decide) (choices 1) [1,16,128] r30863 c30863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13060
  · exact u13061
  · exact u13062

def b30864 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 42 69 280 19 224 224 224 480), lower := (rows 7 42 69 280 19 32 64 128 256), losses := [] }

theorem u30864 : Upper (D 7) (R 7) [6,40,65,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30865 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 4, region := 458, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,0)], upper := (rows 7 42 69 280 49 226 194 194 450), lower := (rows 7 42 69 280 49 32 64 128 256), losses := [] }

theorem u30865 : Upper (D 7) (R 7) [6,40,65,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30866 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 69 280 50 225 193 193 449), lower := (rows 7 42 69 280 50 32 64 128 256), losses := [] }

theorem u30866 : Upper (D 7) (R 7) [6,40,65,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30867 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 69 280 81 162 226 162 418), lower := (rows 7 42 69 280 81 32 64 128 256), losses := [] }

theorem u30867 : Upper (D 7) (R 7) [6,40,65,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30868 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 280 82 161 225 161 417), lower := (rows 7 42 69 280 82 32 64 128 256), losses := [] }

theorem u30868 : Upper (D 7) (R 7) [6,40,65,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30869 : Route 9 := (fun mask => (mask,id))

def c30869 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30869 : Upper (D 7) (R 7) [6,40,65,272,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,96] 13 (by decide) (choices 1) [1,2,128] r30869 c30869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13063
  · exact u13064
  · exact u13065

def r30870 : Route 9 := (fun mask => (mask,id))

def c30870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30870 : Upper (D 7) (R 7) [6,40,65,272,129] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,129] 13 (by decide) (choices 1) [2,64,128] r30870 c30870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13066
  · exact u13067
  · exact u13068

def r30871 : Route 9 := (fun mask => (mask,id))

def c30871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30871 : Upper (D 7) (R 7) [6,40,65,272,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,130] 13 (by decide) (choices 1) [1,64,128] r30871 c30871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13069
  · exact u13070
  · exact u13071

def r30872 : Route 9 := (fun mask => (mask,id))

def c30872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30872 : Upper (D 7) (R 7) [6,40,65,272,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,160] 13 (by decide) (choices 1) [1,2,64,128] r30872 c30872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13072
  · exact u13073
  · exact u13074
  · exact u13075

def r30873 : Route 9 := (fun mask => (mask,id))

def c30873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30873 : Upper (D 7) (R 7) [6,40,65,272,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,192] 13 (by decide) (choices 1) [1,2,128] r30873 c30873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13076
  · exact u13077
  · exact u13078

def b30874 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,5),(4,7)], upper := (rows 7 42 69 328 19 176 240 176 432), lower := (rows 7 42 69 328 19 32 64 128 256), losses := [] }

theorem u30874 : Upper (D 7) (R 7) [6,40,65,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30875 : Route 9 := (fun mask => (mask,id))

def c30875 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30875 : Upper (D 7) (R 7) [6,40,65,320,33] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320,33] 13 (by decide) (choices 1) [2,16,128] r30875 c30875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13079
  · exact u13080
  · exact u13081

def b30876 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 69 328 50 177 209 145 401), lower := (rows 7 42 69 328 50 32 64 128 256), losses := [] }

theorem u30876 : Upper (D 7) (R 7) [6,40,65,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30877 : Route 9 := (fun mask => (mask,id))

def c30877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30877 : Upper (D 7) (R 7) [6,40,65,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320,129] 13 (by decide) (choices 1) [2,16,128] r30877 c30877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13082
  · exact u13083
  · exact u13084

def r30878 : Route 9 := (fun mask => (mask,id))

def c30878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30878 : Upper (D 7) (R 7) [6,40,65,320,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320,130] 13 (by decide) (choices 1) [1,16,128] r30878 c30878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13085
  · exact u13086
  · exact u13087

def r30879 : Route 9 := (fun mask => (mask,id))

def c30879 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30879 : Upper (D 7) (R 7) [6,40,65,320,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320,160] 13 (by decide) (choices 1) [1,2,16,128] r30879 c30879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13088
  · exact u13089
  · exact u13090
  · exact u13091

def b30880 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 42 69 392 19 240 240 240 496), lower := (rows 7 42 69 392 19 32 64 128 256), losses := [] }

theorem u30880 : Upper (D 7) (R 7) [6,40,65,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30881 : Route 9 := (fun mask => (mask,id))

def c30881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30881 : Upper (D 7) (R 7) [6,40,65,384,33] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,33] 13 (by decide) (choices 1) [2,16,64,128] r30881 c30881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13092
  · exact u13093
  · exact u13094
  · exact u13095

def b30882 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 69 392 50 241 209 209 465), lower := (rows 7 42 69 392 50 32 64 128 256), losses := [] }

theorem u30882 : Upper (D 7) (R 7) [6,40,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30883 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 69 392 81 178 242 178 434), lower := (rows 7 42 69 392 81 32 64 128 256), losses := [] }

theorem u30883 : Upper (D 7) (R 7) [6,40,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30884 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 392 82 177 241 177 433), lower := (rows 7 42 69 392 82 32 64 128 256), losses := [] }

theorem u30884 : Upper (D 7) (R 7) [6,40,65,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30885 : Route 9 := (fun mask => (mask,id))

def c30885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30885 : Upper (D 7) (R 7) [6,40,65,384,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,96] 13 (by decide) (choices 1) [1,2,16,128] r30885 c30885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13096
  · exact u13097
  · exact u13098
  · exact u13099

def r30886 : Route 9 := (fun mask => (mask,id))

def c30886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30886 : Upper (D 7) (R 7) [6,40,65,384,129] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,129] 13 (by decide) (choices 1) [2,16,64] r30886 c30886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13100
  · exact u13101
  · exact u13102

def r30887 : Route 9 := (fun mask => (mask,id))

def c30887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30887 : Upper (D 7) (R 7) [6,40,65,384,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,130] 13 (by decide) (choices 1) [1,16,64] r30887 c30887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13103
  · exact u13104
  · exact u13105

def r30888 : Route 9 := (fun mask => (mask,id))

def c30888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30888 : Upper (D 7) (R 7) [6,40,65,384,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,160] 13 (by decide) (choices 1) [1,2,16,64] r30888 c30888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13106
  · exact u13107
  · exact u13108
  · exact u13109

def r30889 : Route 9 := (fun mask => (mask,id))

def c30889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30889 : Upper (D 7) (R 7) [6,40,65,384,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,192] 13 (by decide) (choices 1) [1,2,16] r30889 c30889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13110
  · exact u13111
  · exact u13112

def b30890 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,5),(4,6),(4,7)], upper := (rows 7 42 84 73 19 416 480 416 416), lower := (rows 7 42 84 73 19 32 64 128 256), losses := [] }

theorem u30890 : Upper (D 7) (R 7) [6,40,80,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30891 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(1,6),(3,5),(4,6)], upper := (rows 7 42 84 73 49 418 450 386 386), lower := (rows 7 42 84 73 49 32 64 128 256), losses := [] }

theorem u30891 : Upper (D 7) (R 7) [6,40,80,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30892 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 84 73 50 417 449 385 385), lower := (rows 7 42 84 73 50 32 64 128 256), losses := [] }

theorem u30892 : Upper (D 7) (R 7) [6,40,80,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30893 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(1,6),(2,0),(4,6)], upper := (rows 7 42 84 73 145 418 482 418 418), lower := (rows 7 42 84 73 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 84 490 500 32 64 128 256) }] }

theorem u30893 : Upper (D 7) (R 7) [6,40,80,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30894 : Route 9 := (fun mask => (mask,id))

def c30894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30894 : Upper (D 7) (R 7) [6,40,80,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,130] 13 (by decide) (choices 1) [1,128,256] r30894 c30894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13113
  · exact u13114
  · exact u13115

def r30895 : Route 9 := (fun mask => (mask,id))

def c30895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30895 : Upper (D 7) (R 7) [6,40,80,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,160] 13 (by decide) (choices 1) [1,2,128,256] r30895 c30895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13116
  · exact u13117
  · exact u13118
  · exact u13119

def b30896 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(1,6),(2,0),(4,6)], upper := (rows 7 42 84 73 273 162 226 162 418), lower := (rows 7 42 84 73 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 84 490 500 32 64 128 256) }] }

theorem u30896 : Upper (D 7) (R 7) [6,40,80,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30897 : Route 9 := (fun mask => (mask,id))

def c30897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30897 : Upper (D 7) (R 7) [6,40,80,65,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,258] 13 (by decide) (choices 1) [1,128] r30897 c30897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13120
  · exact u13121

def r30898 : Route 9 := (fun mask => (mask,id))

def c30898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30898 : Upper (D 7) (R 7) [6,40,80,65,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,288] 13 (by decide) (choices 1) [1,2,128] r30898 c30898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13122
  · exact u13123
  · exact u13124

def r30899 : Route 9 := (fun mask => (mask,id))

def c30899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30899 : Upper (D 7) (R 7) [6,40,80,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,384] 13 (by decide) (choices 1) [1,2,128] r30899 c30899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13125
  · exact u13126
  · exact u13127

#print axioms u30899
end Delivery.IrregularNine14.P07
