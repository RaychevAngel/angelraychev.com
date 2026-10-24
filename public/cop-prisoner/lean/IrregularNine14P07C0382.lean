import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0118

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22920 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 74 69 137 274 48 226 162 418), lower := (rows 37 74 69 137 274 48 64 128 256), losses := [] }

theorem u22920 : Upper (D 7) (R 7) [36,72,65,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22920 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22921 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 432, targets := 64 }], pairs := [(0,1),(1,0),(4,0),(4,6)], upper := (rows 37 74 69 137 274 160 114 178 306), lower := (rows 37 74 69 137 274 160 64 128 256), losses := [{ target := 1, region := (rows 3 0 6 8 16 168 64 128 256), good := (rows 37 109 69 169 277 160 64 160 256) }] }

theorem u22921 : Upper (D 7) (R 7) [36,72,65,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22922 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 69 137 304 34 210 146 402), lower := (rows 37 74 69 137 304 34 64 128 256), losses := [] }

theorem u22922 : Upper (D 7) (R 7) [36,72,65,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22923 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 74 69 137 304 48 194 130 386), lower := (rows 37 74 69 137 304 48 64 128 256), losses := [] }

theorem u22923 : Upper (D 7) (R 7) [36,72,65,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22923 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22924 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 432, targets := 64 }], pairs := [(0,1),(1,0),(4,0),(4,6)], upper := (rows 37 74 69 137 304 160 82 146 274), lower := (rows 37 74 69 137 304 160 64 128 256), losses := [{ target := 1, region := (rows 3 0 6 8 16 168 64 128 256), good := (rows 37 109 69 169 304 160 64 160 256) }] }

theorem u22924 : Upper (D 7) (R 7) [36,72,65,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22925 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 69 137 400 34 114 178 306), lower := (rows 37 74 69 137 400 34 64 128 256), losses := [] }

theorem u22925 : Upper (D 7) (R 7) [36,72,65,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22926 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 74 69 137 400 48 98 162 290), lower := (rows 37 74 69 137 400 48 64 128 256), losses := [] }

theorem u22926 : Upper (D 7) (R 7) [36,72,65,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22926 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22927 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 138 50 33 464 400 400), lower := (rows 37 74 69 138 50 33 64 128 256), losses := [] }

theorem u22927 : Upper (D 7) (R 7) [36,72,65,130,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22928 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 138 50 48 449 385 385), lower := (rows 37 74 69 138 50 48 64 128 256), losses := [] }

theorem u22928 : Upper (D 7) (R 7) [36,72,65,130,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22928 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22929 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 4, region := 325, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,6)], upper := (rows 37 74 69 138 50 160 337 401 273), lower := (rows 37 74 69 138 50 160 64 128 256), losses := [] }

theorem u22929 : Upper (D 7) (R 7) [36,72,65,130,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22930 : Route 9 := (fun mask => (mask,id))

def c22930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22930 : Upper (D 7) (R 7) [36,72,65,130,34,256] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,34,256] 13 (by decide) (choices 1) [1,16,128] r22930 c22930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7091
  · exact u7092
  · exact u7093

def b22931 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 74 69 138 145 34 368 432 304), lower := (rows 37 74 69 138 145 34 64 128 256), losses := [] }

theorem u22931 : Upper (D 7) (R 7) [36,72,65,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22932 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(1,0),(3,0)], upper := (rows 37 74 69 138 145 48 354 418 290), lower := (rows 37 74 69 138 145 48 64 128 256), losses := [{ target := 1, region := (rows 11 0 6 8 24 58 64 128 256), good := (rows 37 125 69 189 177 48 64 128 256) }] }

theorem u22932 : Upper (D 7) (R 7) [36,72,65,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22932 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22933 : Route 9 := (fun mask => (mask,id))

def c22933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22933 : Upper (D 7) (R 7) [36,72,65,130,129,256] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,129,256] 13 (by decide) (choices 1) [2,16,32] r22933 c22933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7094
  · exact u7095
  · exact u7096

def b22934 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 138 176 33 338 402 274), lower := (rows 37 74 69 138 176 33 64 128 256), losses := [] }

theorem u22934 : Upper (D 7) (R 7) [36,72,65,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22935 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 74 69 138 176 34 337 401 273), lower := (rows 37 74 69 138 176 34 64 128 256), losses := [] }

theorem u22935 : Upper (D 7) (R 7) [36,72,65,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22936 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 138 176 48 323 387 259), lower := (rows 37 74 69 138 176 48 64 128 256), losses := [] }

theorem u22936 : Upper (D 7) (R 7) [36,72,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22936 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22937 : Route 9 := (fun mask => (mask,id))

def c22937 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22937 : Upper (D 7) (R 7) [36,72,65,130,160,256] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,160,256] 13 (by decide) (choices 1) [1,2,16] r22937 c22937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7097
  · exact u7098
  · exact u7099

def b22938 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 74 69 138 273 34 240 176 432), lower := (rows 37 74 69 138 273 34 64 128 256), losses := [] }

theorem u22938 : Upper (D 7) (R 7) [36,72,65,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22939 : Route 9 := (fun mask => (mask,id))

def c22939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22939 : Upper (D 7) (R 7) [36,72,65,130,257,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,257,16] 13 (by decide) (choices 1) [2,32,128] r22939 c22939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7100
  · exact u7101
  · exact u7102

def b22940 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 69 138 273 160 114 178 306), lower := (rows 37 74 69 138 273 160 64 128 256), losses := [{ target := 1, region := (rows 11 0 6 8 16 168 64 128 256), good := (rows 37 109 69 173 273 160 64 160 256) }] }

theorem u22940 : Upper (D 7) (R 7) [36,72,65,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22941 : PairBound 9 := { available := 176, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 138 274 33 240 176 432), lower := (rows 37 74 69 138 274 33 64 128 256), losses := [] }

theorem u22941 : Upper (D 7) (R 7) [36,72,65,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22942 : Route 9 := (fun mask => (mask,id))

def c22942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22942 : Upper (D 7) (R 7) [36,72,65,130,258,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,258,16] 13 (by decide) (choices 1) [1,32,128] r22942 c22942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7103
  · exact u7104
  · exact u7105

def r22943 : Route 9 := (fun mask => (mask,id))

def c22943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22943 : Upper (D 7) (R 7) [36,72,65,130,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,258,128] 13 (by decide) (choices 1) [1,16,32] r22943 c22943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7106
  · exact u7107
  · exact u7108

def b22944 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 138 304 33 210 146 402), lower := (rows 37 74 69 138 304 33 64 128 256), losses := [] }

theorem u22944 : Upper (D 7) (R 7) [36,72,65,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22945 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 74 69 138 304 34 209 145 401), lower := (rows 37 74 69 138 304 34 64 128 256), losses := [] }

theorem u22945 : Upper (D 7) (R 7) [36,72,65,130,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22946 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 74 69 138 304 48 195 131 387), lower := (rows 37 74 69 138 304 48 64 128 256), losses := [] }

theorem u22946 : Upper (D 7) (R 7) [36,72,65,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22946 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22947 : Route 9 := (fun mask => (mask,id))

def c22947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22947 : Upper (D 7) (R 7) [36,72,65,130,288,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,288,128] 13 (by decide) (choices 1) [1,2,16] r22947 c22947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7109
  · exact u7110
  · exact u7111

def b22948 : PairBound 9 := { available := 50, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 138 400 33 114 178 306), lower := (rows 37 74 69 138 400 33 64 128 256), losses := [] }

theorem u22948 : Upper (D 7) (R 7) [36,72,65,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22949 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 74 69 138 400 34 113 177 305), lower := (rows 37 74 69 138 400 34 64 128 256), losses := [] }

theorem u22949 : Upper (D 7) (R 7) [36,72,65,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22950 : Route 9 := (fun mask => (mask,id))

def c22950 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22950 : Upper (D 7) (R 7) [36,72,65,130,384,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,384,16] 13 (by decide) (choices 1) [1,2,32] r22950 c22950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7112
  · exact u7113
  · exact u7114

def b22951 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 69 152 19 34 480 416 416), lower := (rows 37 74 69 152 19 34 64 128 256), losses := [] }

theorem u22951 : Upper (D 7) (R 7) [36,72,65,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22952 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(1,0),(3,0),(3,6)], upper := (rows 37 74 69 152 19 160 354 418 290), lower := (rows 37 74 69 152 19 160 64 128 256), losses := [{ target := 1, region := (rows 3 0 6 8 16 168 64 128 256), good := (rows 37 109 69 184 21 160 64 160 256) }] }

theorem u22952 : Upper (D 7) (R 7) [36,72,65,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22953 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 37 74 69 152 19 288 226 162 418), lower := (rows 37 74 69 152 19 288 64 128 256), losses := [] }

theorem u22953 : Upper (D 7) (R 7) [36,72,65,144,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22953 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22954 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 152 50 33 450 386 386), lower := (rows 37 74 69 152 50 33 64 128 256), losses := [] }

theorem u22954 : Upper (D 7) (R 7) [36,72,65,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22955 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 69 152 50 34 449 385 385), lower := (rows 37 74 69 152 50 34 64 128 256), losses := [] }

theorem u22955 : Upper (D 7) (R 7) [36,72,65,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22956 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 325, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,0)], upper := (rows 37 74 69 152 50 160 323 387 259), lower := (rows 37 74 69 152 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 36 122 68 184 50 160 64 160 256) },{ target := 1, region := (rows 19 0 6 8 16 168 64 128 256), good := (rows 37 109 69 185 53 160 64 160 256) }] }

theorem u22956 : Upper (D 7) (R 7) [36,72,65,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22957 : Route 9 := (fun mask => (mask,id))

def c22957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22957 : Upper (D 7) (R 7) [36,72,65,144,34,256] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,34,256] 13 (by decide) (choices 1) [1,2,128] r22957 c22957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7115
  · exact u7116
  · exact u7117

def b22958 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 152 273 34 226 162 418), lower := (rows 37 74 69 152 273 34 64 128 256), losses := [] }

theorem u22958 : Upper (D 7) (R 7) [36,72,65,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22959 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 69 152 273 160 98 162 290), lower := (rows 37 74 69 152 273 160 64 128 256), losses := [{ target := 1, region := (rows 3 0 6 8 16 168 64 128 256), good := (rows 37 109 69 184 273 160 64 160 256) }] }

theorem u22959 : Upper (D 7) (R 7) [36,72,65,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22960 : PairBound 9 := { available := 162, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 152 274 33 226 162 418), lower := (rows 37 74 69 152 274 33 64 128 256), losses := [] }

theorem u22960 : Upper (D 7) (R 7) [36,72,65,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22961 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 152 274 34 225 161 417), lower := (rows 37 74 69 152 274 34 64 128 256), losses := [] }

theorem u22961 : Upper (D 7) (R 7) [36,72,65,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22962 : Route 9 := (fun mask => (mask,id))

def c22962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22962 : Upper (D 7) (R 7) [36,72,65,144,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,258,128] 13 (by decide) (choices 1) [1,2,32] r22962 c22962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7118
  · exact u7119
  · exact u7120

def b22963 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 152 304 33 194 130 386), lower := (rows 37 74 69 152 304 33 64 128 256), losses := [] }

theorem u22963 : Upper (D 7) (R 7) [36,72,65,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22964 : Route 9 := (fun mask => (mask,id))

def c22964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22964 : Upper (D 7) (R 7) [36,72,65,144,288,2] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,288,2] 13 (by decide) (choices 1) [1,2,128] r22964 c22964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7121
  · exact u7122
  · exact u7123

def r22965 : Route 9 := (fun mask => (mask,id))

def c22965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22965 : Upper (D 7) (R 7) [36,72,65,144,288,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,288,128] 13 (by decide) (choices 1) [1,2] r22965 c22965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7124
  · exact u7125

def b22966 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 168 145 34 338 402 274), lower := (rows 37 74 69 168 145 34 64 128 256), losses := [] }

theorem u22966 : Upper (D 7) (R 7) [36,72,65,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22967 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 69 168 145 48 322 386 258), lower := (rows 37 74 69 168 145 48 64 128 256), losses := [] }

theorem u22967 : Upper (D 7) (R 7) [36,72,65,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22967 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22968 : Route 9 := (fun mask => (mask,id))

def c22968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22968 : Upper (D 7) (R 7) [36,72,65,160,129,256] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,129,256] 13 (by decide) (choices 1) [2,16] r22968 c22968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7126
  · exact u7127

def b22969 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 69 168 146 33 338 402 274), lower := (rows 37 74 69 168 146 33 64 128 256), losses := [] }

theorem u22969 : Upper (D 7) (R 7) [36,72,65,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22970 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,7),(2,7),(3,0),(3,6)], upper := (rows 37 74 69 168 146 34 337 401 273), lower := (rows 37 74 69 168 146 34 64 128 256), losses := [] }

theorem u22970 : Upper (D 7) (R 7) [36,72,65,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22971 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 69 168 146 48 323 387 259), lower := (rows 37 74 69 168 146 48 64 128 256), losses := [] }

theorem u22971 : Upper (D 7) (R 7) [36,72,65,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22971 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22972 : Route 9 := (fun mask => (mask,id))

def c22972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22972 : Upper (D 7) (R 7) [36,72,65,160,130,256] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,130,256] 13 (by decide) (choices 1) [1,2,16] r22972 c22972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7128
  · exact u7129
  · exact u7130

def b22973 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 168 273 34 210 146 402), lower := (rows 37 74 69 168 273 34 64 128 256), losses := [] }

theorem u22973 : Upper (D 7) (R 7) [36,72,65,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22974 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 69 168 273 48 194 130 386), lower := (rows 37 74 69 168 273 48 64 128 256), losses := [] }

theorem u22974 : Upper (D 7) (R 7) [36,72,65,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22974 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22975 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 69 168 273 160 82 146 274), lower := (rows 37 74 69 168 273 160 64 128 256), losses := [] }

theorem u22975 : Upper (D 7) (R 7) [36,72,65,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22976 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 69 168 274 33 210 146 402), lower := (rows 37 74 69 168 274 33 64 128 256), losses := [] }

theorem u22976 : Upper (D 7) (R 7) [36,72,65,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22977 : Route 9 := (fun mask => (mask,id))

def c22977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22977 : Upper (D 7) (R 7) [36,72,65,160,258,2] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,258,2] 13 (by decide) (choices 1) [1,16,128] r22977 c22977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7131
  · exact u7132
  · exact u7133

def r22978 : Route 9 := (fun mask => (mask,id))

def c22978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22978 : Upper (D 7) (R 7) [36,72,65,160,258,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,258,16] 13 (by decide) (choices 1) [1,2,128] r22978 c22978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7134
  · exact u7135
  · exact u7136

def b22979 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 69 168 274 160 83 147 275), lower := (rows 37 74 69 168 274 160 64 128 256), losses := [] }

theorem u22979 : Upper (D 7) (R 7) [36,72,65,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22979
end Delivery.IrregularNine14.P07
