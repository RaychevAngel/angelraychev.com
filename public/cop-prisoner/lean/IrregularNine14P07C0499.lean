import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0193

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29940 : PairBound 9 := { available := 67, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(2,5)], upper := (rows 97 386 14 28 176 33 67 195 323), lower := (rows 97 386 14 28 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 51 28 24 16 0 97 161 289), good := (rows 451 386 14 30 478 451 64 128 256) }] }

theorem u29940 : Upper (D 7) (R 7) [96,384,10,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29941 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 60, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 386 14 28 176 34 65 193 321), lower := (rows 97 386 14 28 176 34 64 128 256), losses := [] }

theorem u29941 : Upper (D 7) (R 7) [96,384,10,20,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29942 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 28 176 96 67 131 259), lower := (rows 97 386 14 28 176 96 64 128 256), losses := [] }

theorem u29942 : Upper (D 7) (R 7) [96,384,10,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29943 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 402, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 97 386 14 44 82 33 209 145 401), lower := (rows 97 386 14 44 82 33 64 128 256), losses := [] }

theorem u29943 : Upper (D 7) (R 7) [96,384,10,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29944 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 386 14 44 82 48 193 129 385), lower := (rows 97 386 14 44 82 48 64 128 256), losses := [] }

theorem u29944 : Upper (D 7) (R 7) [96,384,10,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29944 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29945 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 386 14 44 82 160 81 145 273), lower := (rows 97 386 14 44 82 160 64 128 256), losses := [] }

theorem u29945 : Upper (D 7) (R 7) [96,384,10,36,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29946 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 97 386 14 44 145 33 82 210 338), lower := (rows 97 386 14 44 145 33 64 128 256), losses := [] }

theorem u29946 : Upper (D 7) (R 7) [96,384,10,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29947 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0)], upper := (rows 97 386 14 44 145 34 81 209 337), lower := (rows 97 386 14 44 145 34 64 128 256), losses := [] }

theorem u29947 : Upper (D 7) (R 7) [96,384,10,36,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29948 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 386 14 44 145 48 67 195 323), lower := (rows 97 386 14 44 145 48 64 128 256), losses := [{ target := 5, region := (rows 1 51 12 8 17 0 81 145 273), good := (rows 467 386 14 14 467 466 64 128 256) }] }

theorem u29948 : Upper (D 7) (R 7) [96,384,10,36,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29948 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29949 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 44 145 96 83 147 275), lower := (rows 97 386 14 44 145 96 64 128 256), losses := [] }

theorem u29949 : Upper (D 7) (R 7) [96,384,10,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29950 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 97 386 14 44 208 33 83 147 275), lower := (rows 97 386 14 44 208 33 64 128 256), losses := [] }

theorem u29950 : Upper (D 7) (R 7) [96,384,10,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29951 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0)], upper := (rows 97 386 14 44 208 34 81 145 273), lower := (rows 97 386 14 44 208 34 64 128 256), losses := [] }

theorem u29951 : Upper (D 7) (R 7) [96,384,10,36,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29952 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 14 44 208 48 67 131 259), lower := (rows 97 386 14 44 208 48 64 128 256), losses := [] }

theorem u29952 : Upper (D 7) (R 7) [96,384,10,36,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29952 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29953 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 386 14 56 82 33 197 133 389), lower := (rows 97 386 14 56 82 33 64 128 256), losses := [] }

theorem u29953 : Upper (D 7) (R 7) [96,384,10,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29954 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 386 14 56 82 36 193 129 385), lower := (rows 97 386 14 56 82 36 64 128 256), losses := [] }

theorem u29954 : Upper (D 7) (R 7) [96,384,10,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29954 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29955 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(2,0),(3,0),(3,1)], upper := (rows 97 386 14 56 82 160 69 133 261), lower := (rows 97 386 14 56 82 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 162 64 128 256), good := (rows 96 418 46 60 126 160 64 160 256) },{ target := 1, region := (rows 21 0 4 24 16 166 68 132 260), good := (rows 97 416 493 57 121 160 64 160 256) }] }

theorem u29955 : Upper (D 7) (R 7) [96,384,10,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29956 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 14 56 84 33 195 131 387), lower := (rows 97 386 14 56 84 33 64 128 256), losses := [] }

theorem u29956 : Upper (D 7) (R 7) [96,384,10,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29957 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 0, region := 386, targets := 64 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(1,5),(1,6),(3,0)], upper := (rows 97 386 14 56 84 34 193 129 385), lower := (rows 97 386 14 56 84 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 38 64 128 256), good := (rows 96 418 46 56 124 34 64 128 256) }] }

theorem u29957 : Upper (D 7) (R 7) [96,384,10,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29958 : Route 9 := (fun mask => (mask,id))

def c29958 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29958 : Upper (D 7) (R 7) [96,384,10,48,68,128] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,68,128] 13 (by decide) (choices 1) [1,2] r29958 c29958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11608
  · exact u11609

def b29959 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 386 14 56 145 33 70 198 326), lower := (rows 97 386 14 56 145 33 64 128 256), losses := [] }

theorem u29959 : Upper (D 7) (R 7) [96,384,10,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29960 : Route 9 := (fun mask => (mask,id))

def c29960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29960 : Upper (D 7) (R 7) [96,384,10,48,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,129,2] 13 (by decide) (choices 1) [1,4] r29960 c29960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11610
  · exact u11611

def b29961 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 97 386 14 56 145 36 67 195 323), lower := (rows 97 386 14 56 145 36 64 128 256), losses := [] }

theorem u29961 : Upper (D 7) (R 7) [96,384,10,48,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29961 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29962 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 56 145 96 71 135 263), lower := (rows 97 386 14 56 145 96 64 128 256), losses := [] }

theorem u29962 : Upper (D 7) (R 7) [96,384,10,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29963 : PairBound 9 := { available := 67, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(2,5)], upper := (rows 97 386 14 56 148 33 67 195 323), lower := (rows 97 386 14 56 148 33 64 128 256), losses := [{ target := 5, region := (rows 1 43 12 8 24 0 97 161 289), good := (rows 451 386 30 478 148 451 64 128 256) }] }

theorem u29963 : Upper (D 7) (R 7) [96,384,10,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29964 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 60, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 386 14 56 148 34 65 193 321), lower := (rows 97 386 14 56 148 34 64 128 256), losses := [] }

theorem u29964 : Upper (D 7) (R 7) [96,384,10,48,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29965 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 56 148 96 67 131 259), lower := (rows 97 386 14 56 148 96 64 128 256), losses := [] }

theorem u29965 : Upper (D 7) (R 7) [96,384,10,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29966 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 14 56 208 33 71 135 263), lower := (rows 97 386 14 56 208 33 64 128 256), losses := [] }

theorem u29966 : Upper (D 7) (R 7) [96,384,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29967 : Route 9 := (fun mask => (mask,id))

def c29967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29967 : Upper (D 7) (R 7) [96,384,10,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,192,2] 13 (by decide) (choices 1) [1,4] r29967 c29967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11612
  · exact u11613

def b29968 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 97 386 14 56 208 36 67 131 259), lower := (rows 97 386 14 56 208 36 64 128 256), losses := [] }

theorem u29968 : Upper (D 7) (R 7) [96,384,10,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29968 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29969 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(4,6),(4,7)], upper := (rows 97 386 14 137 50 33 84 212 340), lower := (rows 97 386 14 137 50 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 41 0 128 256), good := (rows 33 386 62 169 50 33 0 128 256) }] }

theorem u29969 : Upper (D 7) (R 7) [96,384,10,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29970 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(4,0),(4,6)], upper := (rows 97 386 14 137 50 36 81 209 337), lower := (rows 97 386 14 137 50 36 64 128 256), losses := [] }

theorem u29970 : Upper (D 7) (R 7) [96,384,10,129,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29970 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29971 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 14 137 50 48 69 197 325), lower := (rows 97 386 14 137 50 48 64 128 256), losses := [] }

theorem u29971 : Upper (D 7) (R 7) [96,384,10,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29971 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29972 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 137 50 96 85 149 277), lower := (rows 97 386 14 137 50 96 64 128 256), losses := [] }

theorem u29972 : Upper (D 7) (R 7) [96,384,10,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29973 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 4, region := 450, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(4,7)], upper := (rows 97 386 14 137 52 33 82 210 338), lower := (rows 97 386 14 137 52 33 64 128 256), losses := [] }

theorem u29973 : Upper (D 7) (R 7) [96,384,10,129,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29974 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(4,0),(4,6),(4,7)], upper := (rows 97 386 14 137 52 34 81 209 337), lower := (rows 97 386 14 137 52 34 64 128 256), losses := [] }

theorem u29974 : Upper (D 7) (R 7) [96,384,10,129,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29975 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 14 137 52 48 67 195 323), lower := (rows 97 386 14 137 52 48 64 128 256), losses := [] }

theorem u29975 : Upper (D 7) (R 7) [96,384,10,129,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29975 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29976 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 137 52 96 83 147 275), lower := (rows 97 386 14 137 52 96 64 128 256), losses := [] }

theorem u29976 : Upper (D 7) (R 7) [96,384,10,129,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29977 : Route 9 := (fun mask => (mask,id))

def c29977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29977 : Upper (D 7) (R 7) [96,384,10,144,34,1] 13 := by
  apply FastRouting.sound _ _ [96,384,10,144,34,1] 13 (by decide) (choices 1) [1,4] r29977 c29977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11614
  · exact u11615

def b29978 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 60, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 386 14 152 50 36 65 193 321), lower := (rows 97 386 14 152 50 36 64 128 256), losses := [] }

theorem u29978 : Upper (D 7) (R 7) [96,384,10,144,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29978 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29979 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 152 50 96 69 133 261), lower := (rows 97 386 14 152 50 96 64 128 256), losses := [] }

theorem u29979 : Upper (D 7) (R 7) [96,384,10,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29980 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 0, region := 386, targets := 32 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,5),(4,7)], upper := (rows 97 386 14 152 52 33 67 195 323), lower := (rows 97 386 14 152 52 33 64 128 256), losses := [] }

theorem u29980 : Upper (D 7) (R 7) [96,384,10,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29981 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 60, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 386 14 152 52 34 65 193 321), lower := (rows 97 386 14 152 52 34 64 128 256), losses := [] }

theorem u29981 : Upper (D 7) (R 7) [96,384,10,144,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29982 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 152 52 96 67 131 259), lower := (rows 97 386 14 152 52 96 64 128 256), losses := [] }

theorem u29982 : Upper (D 7) (R 7) [96,384,10,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29983 : Route 9 := (fun mask => (mask,id))

def c29983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29983 : Upper (D 7) (R 7) [96,384,10,160,66,1] 13 := by
  apply FastRouting.sound _ _ [96,384,10,160,66,1] 13 (by decide) (choices 1) [1,4,16] r29983 c29983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11616
  · exact u11617
  · exact u11618

def b29984 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 386 14 168 82 36 81 145 273), lower := (rows 97 386 14 168 82 36 64 128 256), losses := [] }

theorem u29984 : Upper (D 7) (R 7) [96,384,10,160,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29984 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29985 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 14 168 82 48 69 133 261), lower := (rows 97 386 14 168 82 48 64 128 256), losses := [] }

theorem u29985 : Upper (D 7) (R 7) [96,384,10,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29985 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29986 : Route 9 := (fun mask => (mask,id))

def c29986 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29986 : Upper (D 7) (R 7) [96,384,10,160,68,1] 13 := by
  apply FastRouting.sound _ _ [96,384,10,160,68,1] 13 (by decide) (choices 1) [1,2,16] r29986 c29986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11619
  · exact u11620
  · exact u11621

def b29987 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 386 14 168 84 34 81 145 273), lower := (rows 97 386 14 168 84 34 64 128 256), losses := [] }

theorem u29987 : Upper (D 7) (R 7) [96,384,10,160,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29988 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 14 168 84 48 67 131 259), lower := (rows 97 386 14 168 84 48 64 128 256), losses := [] }

theorem u29988 : Upper (D 7) (R 7) [96,384,10,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29988 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29989 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 386 28 42 82 33 197 133 389), lower := (rows 97 386 28 42 82 33 64 128 256), losses := [] }

theorem u29989 : Upper (D 7) (R 7) [96,384,24,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29990 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 386 28 42 82 36 193 129 385), lower := (rows 97 386 28 42 82 36 64 128 256), losses := [] }

theorem u29990 : Upper (D 7) (R 7) [96,384,24,34,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29990 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29991 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 386 28 42 82 160 69 133 261), lower := (rows 97 386 28 42 82 160 64 128 256), losses := [] }

theorem u29991 : Upper (D 7) (R 7) [96,384,24,34,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29992 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(3,6)], upper := (rows 97 386 28 42 84 33 195 131 387), lower := (rows 97 386 28 42 84 33 64 128 256), losses := [] }

theorem u29992 : Upper (D 7) (R 7) [96,384,24,34,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29993 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 28 42 84 34 193 129 385), lower := (rows 97 386 28 42 84 34 64 128 256), losses := [] }

theorem u29993 : Upper (D 7) (R 7) [96,384,24,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29994 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(4,7)], upper := (rows 97 386 28 42 84 160 67 131 259), lower := (rows 97 386 28 42 84 160 64 128 256), losses := [] }

theorem u29994 : Upper (D 7) (R 7) [96,384,24,34,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29995 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 386 28 42 145 33 70 198 326), lower := (rows 97 386 28 42 145 33 64 128 256), losses := [] }

theorem u29995 : Upper (D 7) (R 7) [96,384,24,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29996 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 28 42 145 34 69 197 325), lower := (rows 97 386 28 42 145 34 64 128 256), losses := [] }

theorem u29996 : Upper (D 7) (R 7) [96,384,24,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29997 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 97 386 28 42 145 36 67 195 323), lower := (rows 97 386 28 42 145 36 64 128 256), losses := [] }

theorem u29997 : Upper (D 7) (R 7) [96,384,24,34,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29997 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29998 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 28 42 145 96 71 135 263), lower := (rows 97 386 28 42 145 96 64 128 256), losses := [] }

theorem u29998 : Upper (D 7) (R 7) [96,384,24,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29999 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 0, region := 386, targets := 32 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,5),(3,7)], upper := (rows 97 386 28 42 148 33 67 195 323), lower := (rows 97 386 28 42 148 33 64 128 256), losses := [] }

theorem u29999 : Upper (D 7) (R 7) [96,384,24,34,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29999
end Delivery.IrregularNine14.P07
