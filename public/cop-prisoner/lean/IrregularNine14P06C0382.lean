import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0116
import IrregularNine14P06C0117

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22920 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 74 336 36 81 145 273), lower := (rows 35 134 44 74 336 36 64 128 256), losses := [] }

theorem u22920 : Upper (D 6) (R 6) [34,132,40,66,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22921 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 74 336 48 69 133 261), lower := (rows 35 134 44 74 336 48 64 128 256), losses := [] }

theorem u22921 : Upper (D 6) (R 6) [34,132,40,66,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22921 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22922 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 44 88 273 33 70 198 326), lower := (rows 35 134 44 88 273 33 64 128 256), losses := [] }

theorem u22922 : Upper (D 6) (R 6) [34,132,40,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22923 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 88 273 34 69 197 325), lower := (rows 35 134 44 88 273 34 64 128 256), losses := [] }

theorem u22923 : Upper (D 6) (R 6) [34,132,40,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22924 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 88 273 36 67 195 323), lower := (rows 35 134 44 88 273 36 64 128 256), losses := [] }

theorem u22924 : Upper (D 6) (R 6) [34,132,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22925 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 88 273 96 71 135 263), lower := (rows 35 134 44 88 273 96 64 128 256), losses := [] }

theorem u22925 : Upper (D 6) (R 6) [34,132,40,80,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22926 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 88 274 33 69 197 325), lower := (rows 35 134 44 88 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 128 256), good := (rows 35 167 44 61 307 33 0 128 256) }] }

theorem u22926 : Upper (D 6) (R 6) [34,132,40,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22927 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 88 274 36 65 193 321), lower := (rows 35 134 44 88 274 36 64 128 256), losses := [] }

theorem u22927 : Upper (D 6) (R 6) [34,132,40,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22928 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 88 274 96 69 133 261), lower := (rows 35 134 44 88 274 96 64 128 256), losses := [] }

theorem u22928 : Upper (D 6) (R 6) [34,132,40,80,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22929 : Route 9 := (fun mask => (mask,id))

def c22929 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22929 : Upper (D 6) (R 6) [34,132,40,80,260,1] 13 := by
  apply FastRouting.sound _ _ [34,132,40,80,260,1] 13 (by decide) (choices 1) [1,2] r22929 c22929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7018
  · exact u7019

def b22930 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 88 276 34 65 193 321), lower := (rows 35 134 44 88 276 34 64 128 256), losses := [] }

theorem u22930 : Upper (D 6) (R 6) [34,132,40,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22931 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 88 276 96 67 131 259), lower := (rows 35 134 44 88 276 96 64 128 256), losses := [] }

theorem u22931 : Upper (D 6) (R 6) [34,132,40,80,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22932 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 265 81 34 84 212 340), lower := (rows 35 134 44 265 81 34 64 128 256), losses := [] }

theorem u22932 : Upper (D 6) (R 6) [34,132,40,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22933 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 265 81 36 82 210 338), lower := (rows 35 134 44 265 81 36 64 128 256), losses := [] }

theorem u22933 : Upper (D 6) (R 6) [34,132,40,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22934 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 194, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 44 265 81 48 70 198 326), lower := (rows 35 134 44 265 81 48 64 128 256), losses := [] }

theorem u22934 : Upper (D 6) (R 6) [34,132,40,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22934 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22935 : Route 9 := (fun mask => (mask,id))

def c22935 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22935 : Upper (D 6) (R 6) [34,132,40,257,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,257,65,64] 13 (by decide) (choices 1) [2,4,16] r22935 c22935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7020
  · exact u7021
  · exact u7022

def b22936 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 265 82 33 84 212 340), lower := (rows 35 134 44 265 82 33 64 128 256), losses := [] }

theorem u22936 : Upper (D 6) (R 6) [34,132,40,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22937 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 265 82 36 81 209 337), lower := (rows 35 134 44 265 82 36 64 128 256), losses := [] }

theorem u22937 : Upper (D 6) (R 6) [34,132,40,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22938 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 44 265 82 48 69 197 325), lower := (rows 35 134 44 265 82 48 64 128 256), losses := [] }

theorem u22938 : Upper (D 6) (R 6) [34,132,40,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22938 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22939 : Route 9 := (fun mask => (mask,id))

def c22939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22939 : Upper (D 6) (R 6) [34,132,40,257,66,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,257,66,64] 13 (by decide) (choices 1) [1,4,16] r22939 c22939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7023
  · exact u7024
  · exact u7025

def b22940 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 265 84 33 82 210 338), lower := (rows 35 134 44 265 84 33 64 128 256), losses := [] }

theorem u22940 : Upper (D 6) (R 6) [34,132,40,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22941 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 265 84 34 81 209 337), lower := (rows 35 134 44 265 84 34 64 128 256), losses := [] }

theorem u22941 : Upper (D 6) (R 6) [34,132,40,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22942 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 265 84 48 67 195 323), lower := (rows 35 134 44 265 84 48 64 128 256), losses := [] }

theorem u22942 : Upper (D 6) (R 6) [34,132,40,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22942 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22943 : Route 9 := (fun mask => (mask,id))

def c22943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22943 : Upper (D 6) (R 6) [34,132,40,257,68,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,257,68,64] 13 (by decide) (choices 1) [1,2,16] r22943 c22943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7026
  · exact u7027
  · exact u7028

def b22944 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 44 266 21 33 80 208 336), lower := (rows 35 134 44 266 21 33 64 128 256), losses := [] }

theorem u22944 : Upper (D 6) (R 6) [34,132,40,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22945 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 134 44 266 21 48 65 193 321), lower := (rows 35 134 44 266 21 48 64 128 256), losses := [] }

theorem u22945 : Upper (D 6) (R 6) [34,132,40,258,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22945 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22946 : Route 9 := (fun mask => (mask,id))

def c22946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22946 : Upper (D 6) (R 6) [34,132,40,258,5,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258,5,64] 13 (by decide) (choices 1) [1,16] r22946 c22946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7029
  · exact u7030

def b22947 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 266 81 33 84 212 340), lower := (rows 35 134 44 266 81 33 64 128 256), losses := [] }

theorem u22947 : Upper (D 6) (R 6) [34,132,40,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22948 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 266 81 36 81 209 337), lower := (rows 35 134 44 266 81 36 64 128 256), losses := [] }

theorem u22948 : Upper (D 6) (R 6) [34,132,40,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22949 : Route 9 := (fun mask => (mask,id))

def c22949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22949 : Upper (D 6) (R 6) [34,132,40,258,65,16] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258,65,16] 13 (by decide) (choices 1) [1,4] r22949 c22949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7031
  · exact u7032

def r22950 : Route 9 := (fun mask => (mask,id))

def c22950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22950 : Upper (D 6) (R 6) [34,132,40,258,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258,65,64] 13 (by decide) (choices 1) [1,4,16] r22950 c22950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7033
  · exact u7034
  · exact u7035

def b22951 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 266 84 33 81 209 337), lower := (rows 35 134 44 266 84 33 64 128 256), losses := [] }

theorem u22951 : Upper (D 6) (R 6) [34,132,40,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22952 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 266 84 48 65 193 321), lower := (rows 35 134 44 266 84 48 64 128 256), losses := [] }

theorem u22952 : Upper (D 6) (R 6) [34,132,40,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22952 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22953 : Route 9 := (fun mask => (mask,id))

def c22953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22953 : Upper (D 6) (R 6) [34,132,40,258,68,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258,68,64] 13 (by decide) (choices 1) [1,16] r22953 c22953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7036
  · exact u7037

def b22954 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 44 280 81 33 70 198 326), lower := (rows 35 134 44 280 81 33 64 128 256), losses := [] }

theorem u22954 : Upper (D 6) (R 6) [34,132,40,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22955 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 280 81 34 69 197 325), lower := (rows 35 134 44 280 81 34 64 128 256), losses := [] }

theorem u22955 : Upper (D 6) (R 6) [34,132,40,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22956 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 280 81 36 67 195 323), lower := (rows 35 134 44 280 81 36 64 128 256), losses := [] }

theorem u22956 : Upper (D 6) (R 6) [34,132,40,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22957 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 134 44 280 81 96 71 135 263), lower := (rows 35 134 44 280 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 134 44 316 112 96 96 128 256) }] }

theorem u22957 : Upper (D 6) (R 6) [34,132,40,272,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22958 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 280 82 33 69 197 325), lower := (rows 35 134 44 280 82 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 128 256), good := (rows 35 167 44 317 51 33 0 128 256) }] }

theorem u22958 : Upper (D 6) (R 6) [34,132,40,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22959 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 280 82 36 65 193 321), lower := (rows 35 134 44 280 82 36 64 128 256), losses := [] }

theorem u22959 : Upper (D 6) (R 6) [34,132,40,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22960 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 44 280 82 96 69 133 261), lower := (rows 35 134 44 280 82 96 64 128 256), losses := [] }

theorem u22960 : Upper (D 6) (R 6) [34,132,40,272,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22961 : Route 9 := (fun mask => (mask,id))

def c22961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22961 : Upper (D 6) (R 6) [34,132,40,272,68,1] 13 := by
  apply FastRouting.sound _ _ [34,132,40,272,68,1] 13 (by decide) (choices 1) [1,2] r22961 c22961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7038
  · exact u7039

def b22962 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 280 84 34 65 193 321), lower := (rows 35 134 44 280 84 34 64 128 256), losses := [] }

theorem u22962 : Upper (D 6) (R 6) [34,132,40,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22963 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 44 280 84 96 67 131 259), lower := (rows 35 134 44 280 84 96 64 128 256), losses := [] }

theorem u22963 : Upper (D 6) (R 6) [34,132,40,272,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22964 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 44 328 21 33 82 210 338), lower := (rows 35 134 44 328 21 33 64 128 256), losses := [] }

theorem u22964 : Upper (D 6) (R 6) [34,132,40,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22965 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 328 21 34 81 209 337), lower := (rows 35 134 44 328 21 34 64 128 256), losses := [] }

theorem u22965 : Upper (D 6) (R 6) [34,132,40,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22966 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 328 21 48 67 195 323), lower := (rows 35 134 44 328 21 48 64 128 256), losses := [] }

theorem u22966 : Upper (D 6) (R 6) [34,132,40,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22966 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22967 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 147, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 328 21 96 83 147 275), lower := (rows 35 134 44 328 21 96 64 128 256), losses := [] }

theorem u22967 : Upper (D 6) (R 6) [34,132,40,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22968 : Route 9 := (fun mask => (mask,id))

def c22968 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22968 : Upper (D 6) (R 6) [34,132,40,320,65,1] 13 := by
  apply FastRouting.sound _ _ [34,132,40,320,65,1] 13 (by decide) (choices 1) [2,4,16] r22968 c22968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7040
  · exact u7041
  · exact u7042

def b22969 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 328 81 34 85 149 277), lower := (rows 35 134 44 328 81 34 64 128 256), losses := [] }

theorem u22969 : Upper (D 6) (R 6) [34,132,40,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22970 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 328 81 36 83 147 275), lower := (rows 35 134 44 328 81 36 64 128 256), losses := [] }

theorem u22970 : Upper (D 6) (R 6) [34,132,40,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22971 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 328 81 48 71 135 263), lower := (rows 35 134 44 328 81 48 64 128 256), losses := [] }

theorem u22971 : Upper (D 6) (R 6) [34,132,40,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22971 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22972 : Route 9 := (fun mask => (mask,id))

def c22972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22972 : Upper (D 6) (R 6) [34,132,40,320,66,1] 13 := by
  apply FastRouting.sound _ _ [34,132,40,320,66,1] 13 (by decide) (choices 1) [1,4,16] r22972 c22972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7043
  · exact u7044
  · exact u7045

def b22973 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 328 82 36 81 145 273), lower := (rows 35 134 44 328 82 36 64 128 256), losses := [] }

theorem u22973 : Upper (D 6) (R 6) [34,132,40,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22974 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 44 328 82 48 69 133 261), lower := (rows 35 134 44 328 82 48 64 128 256), losses := [] }

theorem u22974 : Upper (D 6) (R 6) [34,132,40,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22974 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22975 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 44 328 84 33 83 147 275), lower := (rows 35 134 44 328 84 33 64 128 256), losses := [] }

theorem u22975 : Upper (D 6) (R 6) [34,132,40,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22976 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 328 84 34 81 145 273), lower := (rows 35 134 44 328 84 34 64 128 256), losses := [] }

theorem u22976 : Upper (D 6) (R 6) [34,132,40,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22977 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 44 328 84 48 67 131 259), lower := (rows 35 134 44 328 84 48 64 128 256), losses := [] }

theorem u22977 : Upper (D 6) (R 6) [34,132,40,320,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22977 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22978 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 13 112 33 338 402 274), lower := (rows 35 134 76 13 112 33 64 128 256), losses := [] }

theorem u22978 : Upper (D 6) (R 6) [34,132,72,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22979 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 13 112 34 337 401 273), lower := (rows 35 134 76 13 112 34 64 128 256), losses := [] }

theorem u22979 : Upper (D 6) (R 6) [34,132,72,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22979
end Delivery.IrregularNine14.P06
