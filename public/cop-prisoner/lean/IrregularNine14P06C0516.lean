import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0214
import IrregularNine14P06C0215

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30960 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 11 35 196 88 21 294 358 422 294), lower := (rows 11 35 196 88 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 494 486 196 92 508 32 64 128 256) }] }

theorem u30960 : Upper (D 6) (R 6) [10,33,192,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30961 : Route 9 := (fun mask => (mask,id))

def c30961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30961 : Upper (D 6) (R 6) [10,33,192,80,6] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,6] 13 (by decide) (choices 1) [1,4,256] r30961 c30961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12872
  · exact u12873
  · exact u12874

def b30962 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 196 88 49 294 326 390 262), lower := (rows 11 35 196 88 49 32 64 128 256), losses := [] }

theorem u30962 : Upper (D 6) (R 6) [10,33,192,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30963 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 196 88 50 293 325 389 261), lower := (rows 11 35 196 88 50 32 64 128 256), losses := [] }

theorem u30963 : Upper (D 6) (R 6) [10,33,192,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30964 : Route 9 := (fun mask => (mask,id))

def c30964 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30964 : Upper (D 6) (R 6) [10,33,192,80,36] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,36] 13 (by decide) (choices 1) [1,2,4,256] r30964 c30964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12875
  · exact u12876
  · exact u12877
  · exact u12878

def r30965 : Route 9 := (fun mask => (mask,id))

def c30965 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30965 : Upper (D 6) (R 6) [10,33,192,80,257] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,257] 13 (by decide) (choices 1) [2,4] r30965 c30965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12879
  · exact u12880

def r30966 : Route 9 := (fun mask => (mask,id))

def c30966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30966 : Upper (D 6) (R 6) [10,33,192,80,258] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,258] 13 (by decide) (choices 1) [1,4] r30966 c30966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12881
  · exact u12882

def r30967 : Route 9 := (fun mask => (mask,id))

def c30967 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30967 : Upper (D 6) (R 6) [10,33,192,80,260] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,260] 13 (by decide) (choices 1) [1,2,4] r30967 c30967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12883
  · exact u12884
  · exact u12885

def r30968 : Route 9 := (fun mask => (mask,id))

def c30968 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30968 : Upper (D 6) (R 6) [10,33,192,80,288] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,288] 13 (by decide) (choices 1) [1,2,4] r30968 c30968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12886
  · exact u12887
  · exact u12888

def b30969 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 265 22 116 116 244 372), lower := (rows 11 35 196 265 22 32 64 128 256), losses := [] }

theorem u30969 : Upper (D 6) (R 6) [10,33,192,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30970 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 196 265 50 116 84 212 340), lower := (rows 11 35 196 265 50 32 64 128 256), losses := [] }

theorem u30970 : Upper (D 6) (R 6) [10,33,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30971 : Route 9 := (fun mask => (mask,id))

def c30971 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30971 : Upper (D 6) (R 6) [10,33,192,257,36] 13 := by
  apply FastRouting.sound _ _ [10,33,192,257,36] 13 (by decide) (choices 1) [2,4,16,64] r30971 c30971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12889
  · exact u12890
  · exact u12891
  · exact u12892

def b30972 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 265 82 52 116 180 308), lower := (rows 11 35 196 265 82 32 64 128 256), losses := [] }

theorem u30972 : Upper (D 6) (R 6) [10,33,192,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30973 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 196 265 84 54 118 182 310), lower := (rows 11 35 196 265 84 32 64 128 256), losses := [] }

theorem u30973 : Upper (D 6) (R 6) [10,33,192,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30974 : Route 9 := (fun mask => (mask,id))

def c30974 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30974 : Upper (D 6) (R 6) [10,33,192,257,96] 13 := by
  apply FastRouting.sound _ _ [10,33,192,257,96] 13 (by decide) (choices 1) [2,4,16] r30974 c30974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12893
  · exact u12894
  · exact u12895

def b30975 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 268 19 116 116 244 372), lower := (rows 11 35 196 268 19 32 64 128 256), losses := [] }

theorem u30975 : Upper (D 6) (R 6) [10,33,192,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30976 : Route 9 := (fun mask => (mask,id))

def c30976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30976 : Upper (D 6) (R 6) [10,33,192,260,5] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260,5] 13 (by decide) (choices 1) [2,16,64] r30976 c30976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12896
  · exact u12897
  · exact u12898

def r30977 : Route 9 := (fun mask => (mask,id))

def c30977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30977 : Upper (D 6) (R 6) [10,33,192,260,6] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260,6] 13 (by decide) (choices 1) [1,16,64] r30977 c30977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12899
  · exact u12900
  · exact u12901

def b30978 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 196 268 49 118 86 214 342), lower := (rows 11 35 196 268 49 32 64 128 256), losses := [] }

theorem u30978 : Upper (D 6) (R 6) [10,33,192,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30979 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 196 268 50 117 85 213 341), lower := (rows 11 35 196 268 50 32 64 128 256), losses := [] }

theorem u30979 : Upper (D 6) (R 6) [10,33,192,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30980 : Route 9 := (fun mask => (mask,id))

def c30980 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30980 : Upper (D 6) (R 6) [10,33,192,260,36] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260,36] 13 (by decide) (choices 1) [1,2,16,64] r30980 c30980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12902
  · exact u12903
  · exact u12904
  · exact u12905

def r30981 : Route 9 := (fun mask => (mask,id))

def c30981 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30981 : Upper (D 6) (R 6) [10,33,192,260,65] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260,65] 13 (by decide) (choices 1) [2,4,16] r30981 c30981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12906
  · exact u12907
  · exact u12908

def r30982 : Route 9 := (fun mask => (mask,id))

def c30982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30982 : Upper (D 6) (R 6) [10,33,192,260,66] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260,66] 13 (by decide) (choices 1) [1,4,16] r30982 c30982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12909
  · exact u12910
  · exact u12911

def b30983 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 196 268 84 51 115 179 307), lower := (rows 11 35 196 268 84 32 64 128 256), losses := [] }

theorem u30983 : Upper (D 6) (R 6) [10,33,192,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30984 : Route 9 := (fun mask => (mask,id))

def c30984 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30984 : Upper (D 6) (R 6) [10,33,192,260,96] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260,96] 13 (by decide) (choices 1) [1,2,4,16] r30984 c30984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12912
  · exact u12913
  · exact u12914
  · exact u12915

def b30985 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 280 19 100 100 228 356), lower := (rows 11 35 196 280 19 32 64 128 256), losses := [] }

theorem u30985 : Upper (D 6) (R 6) [10,33,192,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30986 : Route 9 := (fun mask => (mask,id))

def c30986 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30986 : Upper (D 6) (R 6) [10,33,192,272,5] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,5] 13 (by decide) (choices 1) [2,4,64] r30986 c30986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12916
  · exact u12917
  · exact u12918

def r30987 : Route 9 := (fun mask => (mask,id))

def c30987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30987 : Upper (D 6) (R 6) [10,33,192,272,6] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,6] 13 (by decide) (choices 1) [1,4,64] r30987 c30987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12919
  · exact u12920
  · exact u12921

def b30988 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 196 280 49 102 70 198 326), lower := (rows 11 35 196 280 49 32 64 128 256), losses := [] }

theorem u30988 : Upper (D 6) (R 6) [10,33,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30989 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 196 280 50 101 69 197 325), lower := (rows 11 35 196 280 50 32 64 128 256), losses := [] }

theorem u30989 : Upper (D 6) (R 6) [10,33,192,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30990 : Route 9 := (fun mask => (mask,id))

def c30990 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30990 : Upper (D 6) (R 6) [10,33,192,272,36] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,36] 13 (by decide) (choices 1) [1,2,4,64] r30990 c30990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12922
  · exact u12923
  · exact u12924
  · exact u12925

def r30991 : Route 9 := (fun mask => (mask,id))

def c30991 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30991 : Upper (D 6) (R 6) [10,33,192,272,65] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,65] 13 (by decide) (choices 1) [2,4] r30991 c30991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12926
  · exact u12927

def r30992 : Route 9 := (fun mask => (mask,id))

def c30992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30992 : Upper (D 6) (R 6) [10,33,192,272,66] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,66] 13 (by decide) (choices 1) [1,4] r30992 c30992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12928
  · exact u12929

def b30993 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 196 280 84 39 103 167 295), lower := (rows 11 35 196 280 84 32 64 128 256), losses := [] }

theorem u30993 : Upper (D 6) (R 6) [10,33,192,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30994 : Route 9 := (fun mask => (mask,id))

def c30994 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30994 : Upper (D 6) (R 6) [10,33,192,272,96] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,96] 13 (by decide) (choices 1) [1,2,4] r30994 c30994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12930
  · exact u12931
  · exact u12932

def b30995 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 328 19 52 116 180 308), lower := (rows 11 35 196 328 19 32 64 128 256), losses := [] }

theorem u30995 : Upper (D 6) (R 6) [10,33,192,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30996 : Route 9 := (fun mask => (mask,id))

def c30996 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30996 : Upper (D 6) (R 6) [10,33,192,320,5] 13 := by
  apply FastRouting.sound _ _ [10,33,192,320,5] 13 (by decide) (choices 1) [2,4,16] r30996 c30996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12933
  · exact u12934
  · exact u12935

def r30997 : Route 9 := (fun mask => (mask,id))

def c30997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30997 : Upper (D 6) (R 6) [10,33,192,320,6] 13 := by
  apply FastRouting.sound _ _ [10,33,192,320,6] 13 (by decide) (choices 1) [1,4,16] r30997 c30997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12936
  · exact u12937
  · exact u12938

def b30998 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 196 328 49 54 86 150 278), lower := (rows 11 35 196 328 49 32 64 128 256), losses := [] }

theorem u30998 : Upper (D 6) (R 6) [10,33,192,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30999 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 196 328 50 53 85 149 277), lower := (rows 11 35 196 328 50 32 64 128 256), losses := [] }

theorem u30999 : Upper (D 6) (R 6) [10,33,192,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31000 : Route 9 := (fun mask => (mask,id))

def c31000 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31000 : Upper (D 6) (R 6) [10,33,192,320,36] 13 := by
  apply FastRouting.sound _ _ [10,33,192,320,36] 13 (by decide) (choices 1) [1,2,4,16] r31000 c31000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12939
  · exact u12940
  · exact u12941
  · exact u12942

def b31001 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 388 13 22 112 112 240 368), lower := (rows 11 35 388 13 22 32 64 128 256), losses := [] }

theorem u31001 : Upper (D 6) (R 6) [10,33,384,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31002 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 388 13 50 116 84 212 340), lower := (rows 11 35 388 13 50 32 64 128 256), losses := [] }

theorem u31002 : Upper (D 6) (R 6) [10,33,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31003 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 388 13 52 114 82 210 338), lower := (rows 11 35 388 13 52 32 64 128 256), losses := [] }

theorem u31003 : Upper (D 6) (R 6) [10,33,384,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31004 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 420, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 388 13 82 116 116 244 372), lower := (rows 11 35 388 13 82 32 64 128 256), losses := [] }

theorem u31004 : Upper (D 6) (R 6) [10,33,384,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31005 : Route 9 := (fun mask => (mask,id))

def c31005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31005 : Upper (D 6) (R 6) [10,33,384,5,68] 13 := by
  apply FastRouting.sound _ _ [10,33,384,5,68] 13 (by decide) (choices 1) [2,16,64] r31005 c31005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12943
  · exact u12944
  · exact u12945

def r31006 : Route 9 := (fun mask => (mask,id))

def c31006 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31006 : Upper (D 6) (R 6) [10,33,384,5,96] 13 := by
  apply FastRouting.sound _ _ [10,33,384,5,96] 13 (by decide) (choices 1) [2,4,16,64] r31006 c31006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12946
  · exact u12947
  · exact u12948
  · exact u12949

def b31007 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 388 25 22 100 100 228 356), lower := (rows 11 35 388 25 22 32 64 128 256), losses := [] }

theorem u31007 : Upper (D 6) (R 6) [10,33,384,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31008 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 27, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 25 50 100 68 196 324), lower := (rows 11 35 388 25 50 32 64 128 256), losses := [] }

theorem u31008 : Upper (D 6) (R 6) [10,33,384,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31009 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 25 52 102 70 198 326), lower := (rows 11 35 388 25 52 32 64 128 256), losses := [] }

theorem u31009 : Upper (D 6) (R 6) [10,33,384,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31010 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 388 25 82 100 100 228 356), lower := (rows 11 35 388 25 82 32 64 128 256), losses := [] }

theorem u31010 : Upper (D 6) (R 6) [10,33,384,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31011 : Route 9 := (fun mask => (mask,id))

def c31011 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31011 : Upper (D 6) (R 6) [10,33,384,17,68] 13 := by
  apply FastRouting.sound _ _ [10,33,384,17,68] 13 (by decide) (choices 1) [2,4,64] r31011 c31011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12950
  · exact u12951
  · exact u12952

def b31012 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 25 112 102 70 198 326), lower := (rows 11 35 388 25 112 32 64 128 256), losses := [] }

theorem u31012 : Upper (D 6) (R 6) [10,33,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31013 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 388 28 19 100 100 228 356), lower := (rows 11 35 388 28 19 32 64 128 256), losses := [] }

theorem u31013 : Upper (D 6) (R 6) [10,33,384,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31014 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 388 28 21 98 98 226 354), lower := (rows 11 35 388 28 21 32 64 128 256), losses := [] }

theorem u31014 : Upper (D 6) (R 6) [10,33,384,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31015 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 388 28 22 97 97 225 353), lower := (rows 11 35 388 28 22 32 64 128 256), losses := [] }

theorem u31015 : Upper (D 6) (R 6) [10,33,384,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31016 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 388 28 49 102 70 198 326), lower := (rows 11 35 388 28 49 32 64 128 256), losses := [] }

theorem u31016 : Upper (D 6) (R 6) [10,33,384,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31017 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 388 28 50 101 69 197 325), lower := (rows 11 35 388 28 50 32 64 128 256), losses := [] }

theorem u31017 : Upper (D 6) (R 6) [10,33,384,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31018 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 388 28 52 99 67 195 323), lower := (rows 11 35 388 28 52 32 64 128 256), losses := [] }

theorem u31018 : Upper (D 6) (R 6) [10,33,384,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31019 : Route 9 := (fun mask => (mask,id))

def c31019 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31019 : Upper (D 6) (R 6) [10,33,384,20,65] 13 := by
  apply FastRouting.sound _ _ [10,33,384,20,65] 13 (by decide) (choices 1) [2,4,64] r31019 c31019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12953
  · exact u12954
  · exact u12955

#print axioms u31019
end Delivery.IrregularNine14.P06
