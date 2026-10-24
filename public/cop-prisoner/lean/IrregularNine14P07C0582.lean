import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0331
import IrregularNine14P07C0332
import IrregularNine14P07C0333

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34920 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 268 73 50 177 209 145 401), lower := (rows 35 70 268 73 50 32 64 128 256), losses := [] }

theorem u34920 : Upper (D 7) (R 7) [34,68,264,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34921 : Route 9 := (fun mask => (mask,id))

def c34921 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34921 : Upper (D 7) (R 7) [34,68,264,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,65,129] 13 (by decide) (choices 1) [2,16,128] r34921 c34921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19917
  · exact u19918
  · exact u19919

def r34922 : Route 9 := (fun mask => (mask,id))

def c34922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34922 : Upper (D 7) (R 7) [34,68,264,65,130] 13 := by
  apply FastRouting.sound _ _ [34,68,264,65,130] 13 (by decide) (choices 1) [1,16,128] r34922 c34922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19920
  · exact u19921
  · exact u19922

def r34923 : Route 9 := (fun mask => (mask,id))

def c34923 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34923 : Upper (D 7) (R 7) [34,68,264,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,65,160] 13 (by decide) (choices 1) [1,2,16,128] r34923 c34923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19923
  · exact u19924
  · exact u19925
  · exact u19926

def b34924 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 268 88 19 161 225 161 417), lower := (rows 35 70 268 88 19 32 64 128 256), losses := [] }

theorem u34924 : Upper (D 7) (R 7) [34,68,264,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34925 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 268 88 49 163 195 131 387), lower := (rows 35 70 268 88 49 32 64 128 256), losses := [] }

theorem u34925 : Upper (D 7) (R 7) [34,68,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34926 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 268 88 50 161 193 129 385), lower := (rows 35 70 268 88 50 32 64 128 256), losses := [] }

theorem u34926 : Upper (D 7) (R 7) [34,68,264,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34927 : Route 9 := (fun mask => (mask,id))

def c34927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34927 : Upper (D 7) (R 7) [34,68,264,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,80,129] 13 (by decide) (choices 1) [1,2,128] r34927 c34927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19927
  · exact u19928
  · exact u19929

def r34928 : Route 9 := (fun mask => (mask,id))

def c34928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34928 : Upper (D 7) (R 7) [34,68,264,80,130] 13 := by
  apply FastRouting.sound _ _ [34,68,264,80,130] 13 (by decide) (choices 1) [1,128] r34928 c34928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19930
  · exact u19931

def r34929 : Route 9 := (fun mask => (mask,id))

def c34929 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34929 : Upper (D 7) (R 7) [34,68,264,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,80,160] 13 (by decide) (choices 1) [1,2,128] r34929 c34929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19932
  · exact u19933
  · exact u19934

def b34930 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 492, targets := 2 }], pairs := [(0,6),(2,1),(3,1),(4,6)], upper := (rows 35 70 268 104 19 177 209 145 401), lower := (rows 35 70 268 104 19 32 64 128 256), losses := [] }

theorem u34930 : Upper (D 7) (R 7) [34,68,264,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34931 : Route 9 := (fun mask => (mask,id))

def c34931 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34931 : Upper (D 7) (R 7) [34,68,264,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,96,129] 13 (by decide) (choices 1) [1,2,16,128] r34931 c34931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19935
  · exact u19936
  · exact u19937
  · exact u19938

def r34932 : Route 9 := (fun mask => (mask,id))

def c34932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34932 : Upper (D 7) (R 7) [34,68,264,96,130] 13 := by
  apply FastRouting.sound _ _ [34,68,264,96,130] 13 (by decide) (choices 1) [1,16,128] r34932 c34932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19939
  · exact u19940
  · exact u19941

def b34933 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 70 268 137 19 240 240 240 496), lower := (rows 35 70 268 137 19 32 64 128 256), losses := [] }

theorem u34933 : Upper (D 7) (R 7) [34,68,264,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34934 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 70 268 137 49 242 210 210 466), lower := (rows 35 70 268 137 49 32 64 128 256), losses := [] }

theorem u34934 : Upper (D 7) (R 7) [34,68,264,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34935 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 70 268 137 50 241 209 209 465), lower := (rows 35 70 268 137 50 32 64 128 256), losses := [] }

theorem u34935 : Upper (D 7) (R 7) [34,68,264,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34936 : Route 9 := (fun mask => (mask,id))

def c34936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34936 : Upper (D 7) (R 7) [34,68,264,129,65] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,65] 13 (by decide) (choices 1) [2,16,128] r34936 c34936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19942
  · exact u19943
  · exact u19944

def b34937 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 268 137 82 177 241 177 433), lower := (rows 35 70 268 137 82 32 64 128 256), losses := [] }

theorem u34937 : Upper (D 7) (R 7) [34,68,264,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34938 : Route 9 := (fun mask => (mask,id))

def c34938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34938 : Upper (D 7) (R 7) [34,68,264,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,96] 13 (by decide) (choices 1) [1,2,16,128] r34938 c34938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19945
  · exact u19946
  · exact u19947
  · exact u19948

def b34939 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 268 137 145 114 114 242 370), lower := (rows 35 70 268 137 145 32 64 128 256), losses := [] }

theorem u34939 : Upper (D 7) (R 7) [34,68,264,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34940 : Route 9 := (fun mask => (mask,id))

def c34940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34940 : Upper (D 7) (R 7) [34,68,264,129,130] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,130] 13 (by decide) (choices 1) [1,16,64] r34940 c34940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19949
  · exact u19950
  · exact u19951

def r34941 : Route 9 := (fun mask => (mask,id))

def c34941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34941 : Upper (D 7) (R 7) [34,68,264,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,160] 13 (by decide) (choices 1) [1,2,16,64] r34941 c34941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19952
  · exact u19953
  · exact u19954
  · exact u19955

def r34942 : Route 9 := (fun mask => (mask,id))

def c34942 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34942 : Upper (D 7) (R 7) [34,68,264,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,192] 13 (by decide) (choices 1) [1,2,16] r34942 c34942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19956
  · exact u19957
  · exact u19958

def b34943 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 70 268 138 49 241 209 209 465), lower := (rows 35 70 268 138 49 32 64 128 256), losses := [] }

theorem u34943 : Upper (D 7) (R 7) [34,68,264,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34944 : Route 9 := (fun mask => (mask,id))

def c34944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34944 : Upper (D 7) (R 7) [34,68,264,130,65] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,65] 13 (by decide) (choices 1) [1,16,128] r34944 c34944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19959
  · exact u19960
  · exact u19961

def r34945 : Route 9 := (fun mask => (mask,id))

def c34945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34945 : Upper (D 7) (R 7) [34,68,264,130,96] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,96] 13 (by decide) (choices 1) [1,16,128] r34945 c34945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19962
  · exact u19963
  · exact u19964

def r34946 : Route 9 := (fun mask => (mask,id))

def c34946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34946 : Upper (D 7) (R 7) [34,68,264,130,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,129] 13 (by decide) (choices 1) [1,16,64] r34946 c34946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19965
  · exact u19966
  · exact u19967

def r34947 : Route 9 := (fun mask => (mask,id))

def c34947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34947 : Upper (D 7) (R 7) [34,68,264,130,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,160] 13 (by decide) (choices 1) [1,16,64] r34947 c34947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19968
  · exact u19969
  · exact u19970

def r34948 : Route 9 := (fun mask => (mask,id))

def c34948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34948 : Upper (D 7) (R 7) [34,68,264,130,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,192] 13 (by decide) (choices 1) [1,16] r34948 c34948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19971
  · exact u19972

def b34949 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 70 268 152 19 225 225 225 481), lower := (rows 35 70 268 152 19 32 64 128 256), losses := [] }

theorem u34949 : Upper (D 7) (R 7) [34,68,264,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34950 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 70 268 152 49 227 195 195 451), lower := (rows 35 70 268 152 49 32 64 128 256), losses := [] }

theorem u34950 : Upper (D 7) (R 7) [34,68,264,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34951 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 70 268 152 50 225 193 193 449), lower := (rows 35 70 268 152 50 32 64 128 256), losses := [] }

theorem u34951 : Upper (D 7) (R 7) [34,68,264,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34952 : Route 9 := (fun mask => (mask,id))

def c34952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34952 : Upper (D 7) (R 7) [34,68,264,144,65] 13 := by
  apply FastRouting.sound _ _ [34,68,264,144,65] 13 (by decide) (choices 1) [1,2,128] r34952 c34952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19973
  · exact u19974
  · exact u19975

def b34953 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 268 152 82 161 225 161 417), lower := (rows 35 70 268 152 82 32 64 128 256), losses := [] }

theorem u34953 : Upper (D 7) (R 7) [34,68,264,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34954 : Route 9 := (fun mask => (mask,id))

def c34954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34954 : Upper (D 7) (R 7) [34,68,264,144,96] 13 := by
  apply FastRouting.sound _ _ [34,68,264,144,96] 13 (by decide) (choices 1) [1,2,128] r34954 c34954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19976
  · exact u19977
  · exact u19978

def b34955 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 268 152 145 99 99 227 355), lower := (rows 35 70 268 152 145 32 64 128 256), losses := [] }

theorem u34955 : Upper (D 7) (R 7) [34,68,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34956 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 268 152 146 97 97 225 353), lower := (rows 35 70 268 152 146 32 64 128 256), losses := [] }

theorem u34956 : Upper (D 7) (R 7) [34,68,264,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34957 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 268 152 176 99 67 195 323), lower := (rows 35 70 268 152 176 32 64 128 256), losses := [] }

theorem u34957 : Upper (D 7) (R 7) [34,68,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34958 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 268 152 208 35 99 163 291), lower := (rows 35 70 268 152 208 32 64 128 256), losses := [] }

theorem u34958 : Upper (D 7) (R 7) [34,68,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34959 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 35 70 268 168 19 241 209 209 465), lower := (rows 35 70 268 168 19 32 64 128 256), losses := [] }

theorem u34959 : Upper (D 7) (R 7) [34,68,264,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34960 : Route 9 := (fun mask => (mask,id))

def c34960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34960 : Upper (D 7) (R 7) [34,68,264,160,65] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160,65] 13 (by decide) (choices 1) [1,2,16,128] r34960 c34960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19979
  · exact u19980
  · exact u19981
  · exact u19982

def b34961 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 268 168 82 177 209 145 401), lower := (rows 35 70 268 168 82 32 64 128 256), losses := [] }

theorem u34961 : Upper (D 7) (R 7) [34,68,264,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34962 : Route 9 := (fun mask => (mask,id))

def c34962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34962 : Upper (D 7) (R 7) [34,68,264,160,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160,129] 13 (by decide) (choices 1) [1,2,16,64] r34962 c34962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19983
  · exact u19984
  · exact u19985
  · exact u19986

def r34963 : Route 9 := (fun mask => (mask,id))

def c34963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34963 : Upper (D 7) (R 7) [34,68,264,160,130] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160,130] 13 (by decide) (choices 1) [1,16,64] r34963 c34963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19987
  · exact u19988
  · exact u19989

def r34964 : Route 9 := (fun mask => (mask,id))

def c34964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34964 : Upper (D 7) (R 7) [34,68,264,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160,192] 13 (by decide) (choices 1) [1,2,16] r34964 c34964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19990
  · exact u19991
  · exact u19992

def b34965 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 268 200 19 177 241 177 433), lower := (rows 35 70 268 200 19 32 64 128 256), losses := [] }

theorem u34965 : Upper (D 7) (R 7) [34,68,264,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34966 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 268 200 49 179 211 147 403), lower := (rows 35 70 268 200 49 32 64 128 256), losses := [] }

theorem u34966 : Upper (D 7) (R 7) [34,68,264,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34967 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 268 200 50 177 209 145 401), lower := (rows 35 70 268 200 50 32 64 128 256), losses := [] }

theorem u34967 : Upper (D 7) (R 7) [34,68,264,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34968 : Route 9 := (fun mask => (mask,id))

def c34968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34968 : Upper (D 7) (R 7) [34,68,264,192,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,192,129] 13 (by decide) (choices 1) [1,2,16] r34968 c34968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19993
  · exact u19994
  · exact u19995

def r34969 : Route 9 := (fun mask => (mask,id))

def c34969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34969 : Upper (D 7) (R 7) [34,68,264,192,130] 13 := by
  apply FastRouting.sound _ _ [34,68,264,192,130] 13 (by decide) (choices 1) [1,16] r34969 c34969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19996
  · exact u19997

def r34970 : Route 9 := (fun mask => (mask,id))

def c34970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34970 : Upper (D 7) (R 7) [34,68,264,192,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,192,160] 13 (by decide) (choices 1) [1,2,16] r34970 c34970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19998
  · exact u19999
  · exact u20000

def b34971 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 292 11 25 240 208 208 464), lower := (rows 35 70 292 11 25 32 64 128 256), losses := [] }

theorem u34971 : Upper (D 7) (R 7) [34,68,288,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34972 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 292 11 81 184 216 152 408), lower := (rows 35 70 292 11 81 32 64 128 256), losses := [] }

theorem u34972 : Upper (D 7) (R 7) [34,68,288,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34973 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 292 11 88 177 209 145 401), lower := (rows 35 70 292 11 88 32 64 128 256), losses := [] }

theorem u34973 : Upper (D 7) (R 7) [34,68,288,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34974 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 292 11 145 248 216 216 472), lower := (rows 35 70 292 11 145 32 64 128 256), losses := [] }

theorem u34974 : Upper (D 7) (R 7) [34,68,288,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34975 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 292 11 152 241 209 209 465), lower := (rows 35 70 292 11 152 32 64 128 256), losses := [] }

theorem u34975 : Upper (D 7) (R 7) [34,68,288,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34976 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 292 11 208 185 217 153 409), lower := (rows 35 70 292 11 208 32 64 128 256), losses := [] }

theorem u34976 : Upper (D 7) (R 7) [34,68,288,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34977 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 292 25 25 226 194 194 450), lower := (rows 35 70 292 25 25 32 64 128 256), losses := [] }

theorem u34977 : Upper (D 7) (R 7) [34,68,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34978 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 292 25 26 225 193 193 449), lower := (rows 35 70 292 25 26 32 64 128 256), losses := [] }

theorem u34978 : Upper (D 7) (R 7) [34,68,288,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34979 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 292 25 81 170 202 138 394), lower := (rows 35 70 292 25 81 32 64 128 256), losses := [] }

theorem u34979 : Upper (D 7) (R 7) [34,68,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34979
end Delivery.IrregularNine14.P07
