import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0049
import IrregularNine14P06C0050

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r13920 : Route 9 := (fun mask => (mask,id))

def c13920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13920 : Upper (D 6) (R 6) [10,36,384,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,36,384,17,68,64] 13 (by decide) (choices 1) [1,2,32] r13920 c13920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2989
  · exact u2990
  · exact u2991

def b13921 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 388 25 112 33 70 198 326), lower := (rows 11 38 388 25 112 33 64 128 256), losses := [] }

theorem u13921 : Upper (D 6) (R 6) [10,36,384,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13922 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 388 25 112 34 69 197 325), lower := (rows 11 38 388 25 112 34 64 128 256), losses := [] }

theorem u13922 : Upper (D 6) (R 6) [10,36,384,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13923 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 388 25 112 36 67 195 323), lower := (rows 11 38 388 25 112 36 64 128 256), losses := [] }

theorem u13923 : Upper (D 6) (R 6) [10,36,384,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13924 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 388 25 112 96 71 135 263), lower := (rows 11 38 388 25 112 96 64 128 256), losses := [] }

theorem u13924 : Upper (D 6) (R 6) [10,36,384,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13925 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 5, region := 454, targets := 1 }], pairs := [(0,6),(1,0),(1,6)], upper := (rows 11 38 388 28 81 33 98 226 354), lower := (rows 11 38 388 28 81 33 64 128 256), losses := [] }

theorem u13925 : Upper (D 6) (R 6) [10,36,384,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13926 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 388 28 81 34 97 225 353), lower := (rows 11 38 388 28 81 34 64 128 256), losses := [] }

theorem u13926 : Upper (D 6) (R 6) [10,36,384,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13927 : Route 9 := (fun mask => (mask,id))

def c13927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13927 : Upper (D 6) (R 6) [10,36,384,20,65,64] 13 := by
  apply FastRouting.sound _ _ [10,36,384,20,65,64] 13 (by decide) (choices 1) [1,2,32] r13927 c13927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2992
  · exact u2993
  · exact u2994

def b13928 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 38 388 28 82 33 97 225 353), lower := (rows 11 38 388 28 82 33 64 128 256), losses := [] }

theorem u13928 : Upper (D 6) (R 6) [10,36,384,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13929 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(2,1),(4,2)], upper := (rows 11 38 388 28 82 96 97 161 289), lower := (rows 11 38 388 28 82 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 112 64 128 256), good := (rows 10 38 388 62 114 96 96 128 256) }] }

theorem u13929 : Upper (D 6) (R 6) [10,36,384,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13930 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 388 28 112 33 67 195 323), lower := (rows 11 38 388 28 112 33 64 128 256), losses := [] }

theorem u13930 : Upper (D 6) (R 6) [10,36,384,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13931 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 388 28 112 34 65 193 321), lower := (rows 11 38 388 28 112 34 64 128 256), losses := [] }

theorem u13931 : Upper (D 6) (R 6) [10,36,384,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13932 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 388 28 112 96 67 131 259), lower := (rows 11 38 388 28 112 96 64 128 256), losses := [] }

theorem u13932 : Upper (D 6) (R 6) [10,36,384,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13933 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 38 388 56 81 33 70 198 326), lower := (rows 11 38 388 56 81 33 64 128 256), losses := [] }

theorem u13933 : Upper (D 6) (R 6) [10,36,384,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13934 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 388 56 81 34 69 197 325), lower := (rows 11 38 388 56 81 34 64 128 256), losses := [] }

theorem u13934 : Upper (D 6) (R 6) [10,36,384,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13935 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 388 56 81 36 67 195 323), lower := (rows 11 38 388 56 81 36 64 128 256), losses := [] }

theorem u13935 : Upper (D 6) (R 6) [10,36,384,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13936 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 388 56 81 96 71 135 263), lower := (rows 11 38 388 56 81 96 64 128 256), losses := [] }

theorem u13936 : Upper (D 6) (R 6) [10,36,384,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13937 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 388 56 84 33 67 195 323), lower := (rows 11 38 388 56 84 33 64 128 256), losses := [] }

theorem u13937 : Upper (D 6) (R 6) [10,36,384,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13938 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 388 56 84 34 65 193 321), lower := (rows 11 38 388 56 84 34 64 128 256), losses := [] }

theorem u13938 : Upper (D 6) (R 6) [10,36,384,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13939 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 388 56 84 96 67 131 259), lower := (rows 11 38 388 56 84 96 64 128 256), losses := [] }

theorem u13939 : Upper (D 6) (R 6) [10,36,384,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13940 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 388 73 21 34 112 240 368), lower := (rows 11 38 388 73 21 34 64 128 256), losses := [] }

theorem u13940 : Upper (D 6) (R 6) [10,36,384,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13941 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 388 73 21 48 98 226 354), lower := (rows 11 38 388 73 21 48 64 128 256), losses := [] }

theorem u13941 : Upper (D 6) (R 6) [10,36,384,65,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13941 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13942 : Route 9 := (fun mask => (mask,id))

def c13942 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13942 : Upper (D 6) (R 6) [10,36,384,65,5,64] 13 := by
  apply FastRouting.sound _ _ [10,36,384,65,5,64] 13 (by decide) (choices 1) [2,16,32] r13942 c13942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2995
  · exact u2996
  · exact u2997

def b13943 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 388 73 49 34 84 212 340), lower := (rows 11 38 388 73 49 34 64 128 256), losses := [] }

theorem u13943 : Upper (D 6) (R 6) [10,36,384,65,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13944 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 388 73 49 36 82 210 338), lower := (rows 11 38 388 73 49 36 64 128 256), losses := [] }

theorem u13944 : Upper (D 6) (R 6) [10,36,384,65,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13945 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 388 73 49 48 70 198 326), lower := (rows 11 38 388 73 49 48 64 128 256), losses := [] }

theorem u13945 : Upper (D 6) (R 6) [10,36,384,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13945 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13946 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 6 },{ cop := 4, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 388 73 49 96 86 150 278), lower := (rows 11 38 388 73 49 96 64 128 256), losses := [] }

theorem u13946 : Upper (D 6) (R 6) [10,36,384,65,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13947 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 388 73 84 33 114 178 306), lower := (rows 11 38 388 73 84 33 64 128 256), losses := [] }

theorem u13947 : Upper (D 6) (R 6) [10,36,384,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13948 : Route 9 := (fun mask => (mask,id))

def c13948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13948 : Upper (D 6) (R 6) [10,36,384,65,68,2] 13 := by
  apply FastRouting.sound _ _ [10,36,384,65,68,2] 13 (by decide) (choices 1) [1,16,32] r13948 c13948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2998
  · exact u2999
  · exact u3000

def b13949 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 388 73 84 48 99 163 291), lower := (rows 11 38 388 73 84 48 64 128 256), losses := [] }

theorem u13949 : Upper (D 6) (R 6) [10,36,384,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13949 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13950 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 388 73 112 33 86 150 278), lower := (rows 11 38 388 73 112 33 64 128 256), losses := [] }

theorem u13950 : Upper (D 6) (R 6) [10,36,384,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13951 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 38 388 73 112 34 85 149 277), lower := (rows 11 38 388 73 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 39 64 128 256), good := (rows 58 38 422 120 112 34 64 128 256) }] }

theorem u13951 : Upper (D 6) (R 6) [10,36,384,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13952 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 388 73 112 36 83 147 275), lower := (rows 11 38 388 73 112 36 64 128 256), losses := [] }

theorem u13952 : Upper (D 6) (R 6) [10,36,384,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13953 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 388 73 112 48 71 135 263), lower := (rows 11 38 388 73 112 48 64 128 256), losses := [] }

theorem u13953 : Upper (D 6) (R 6) [10,36,384,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13953 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13954 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 38 388 76 49 33 82 210 338), lower := (rows 11 38 388 76 49 33 64 128 256), losses := [] }

theorem u13954 : Upper (D 6) (R 6) [10,36,384,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13955 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 388 76 49 34 81 209 337), lower := (rows 11 38 388 76 49 34 64 128 256), losses := [] }

theorem u13955 : Upper (D 6) (R 6) [10,36,384,68,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13956 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 388 76 49 48 67 195 323), lower := (rows 11 38 388 76 49 48 64 128 256), losses := [] }

theorem u13956 : Upper (D 6) (R 6) [10,36,384,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13956 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13957 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 390, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 11 38 388 76 49 96 83 147 275), lower := (rows 11 38 388 76 49 96 64 128 256), losses := [] }

theorem u13957 : Upper (D 6) (R 6) [10,36,384,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13958 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 388 76 82 33 113 177 305), lower := (rows 11 38 388 76 82 33 64 128 256), losses := [] }

theorem u13958 : Upper (D 6) (R 6) [10,36,384,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13959 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 388 76 82 48 97 161 289), lower := (rows 11 38 388 76 82 48 64 128 256), losses := [] }

theorem u13959 : Upper (D 6) (R 6) [10,36,384,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13959 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13960 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 388 76 112 33 83 147 275), lower := (rows 11 38 388 76 112 33 64 128 256), losses := [] }

theorem u13960 : Upper (D 6) (R 6) [10,36,384,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13961 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 388 76 112 34 81 145 273), lower := (rows 11 38 388 76 112 34 64 128 256), losses := [] }

theorem u13961 : Upper (D 6) (R 6) [10,36,384,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13962 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 388 76 112 48 67 131 259), lower := (rows 11 38 388 76 112 48 64 128 256), losses := [] }

theorem u13962 : Upper (D 6) (R 6) [10,36,384,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13962 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13963 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 388 88 21 33 98 226 354), lower := (rows 11 38 388 88 21 33 64 128 256), losses := [] }

theorem u13963 : Upper (D 6) (R 6) [10,36,384,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13964 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,2)], upper := (rows 11 38 388 88 21 34 97 225 353), lower := (rows 11 38 388 88 21 34 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 35 81 145 273), good := (rows 491 34 384 472 505 34 64 128 256) }] }

theorem u13964 : Upper (D 6) (R 6) [10,36,384,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13965 : Route 9 := (fun mask => (mask,id))

def c13965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13965 : Upper (D 6) (R 6) [10,36,384,80,5,64] 13 := by
  apply FastRouting.sound _ _ [10,36,384,80,5,64] 13 (by decide) (choices 1) [1,2,32] r13965 c13965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3001
  · exact u3002
  · exact u3003

def b13966 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 388 88 49 33 70 198 326), lower := (rows 11 38 388 88 49 33 64 128 256), losses := [] }

theorem u13966 : Upper (D 6) (R 6) [10,36,384,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13967 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 388 88 49 34 69 197 325), lower := (rows 11 38 388 88 49 34 64 128 256), losses := [] }

theorem u13967 : Upper (D 6) (R 6) [10,36,384,80,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13968 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 388 88 49 36 67 195 323), lower := (rows 11 38 388 88 49 36 64 128 256), losses := [] }

theorem u13968 : Upper (D 6) (R 6) [10,36,384,80,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13969 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 390, targets := 64 },{ cop := 0, region := 388, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 11 38 388 88 49 96 71 135 263), lower := (rows 11 38 388 88 49 96 64 128 256), losses := [] }

theorem u13969 : Upper (D 6) (R 6) [10,36,384,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13970 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 388 104 21 33 82 210 338), lower := (rows 11 38 388 104 21 33 64 128 256), losses := [] }

theorem u13970 : Upper (D 6) (R 6) [10,36,384,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13971 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 388 104 21 34 81 209 337), lower := (rows 11 38 388 104 21 34 64 128 256), losses := [] }

theorem u13971 : Upper (D 6) (R 6) [10,36,384,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13972 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 388 104 21 48 67 195 323), lower := (rows 11 38 388 104 21 48 64 128 256), losses := [] }

theorem u13972 : Upper (D 6) (R 6) [10,36,384,96,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13972 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13973 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 388 104 21 96 83 147 275), lower := (rows 11 38 388 104 21 96 64 128 256), losses := [] }

theorem u13973 : Upper (D 6) (R 6) [10,36,384,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13974 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 388 104 82 33 85 149 277), lower := (rows 11 38 388 104 82 33 64 128 256), losses := [] }

theorem u13974 : Upper (D 6) (R 6) [10,36,384,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13975 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 388 104 82 36 81 145 273), lower := (rows 11 38 388 104 82 36 64 128 256), losses := [] }

theorem u13975 : Upper (D 6) (R 6) [10,36,384,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13976 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 388 104 82 48 69 133 261), lower := (rows 11 38 388 104 82 48 64 128 256), losses := [] }

theorem u13976 : Upper (D 6) (R 6) [10,36,384,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13976 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13977 : Route 9 := (fun mask => (mask,id))

def c13977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13977 : Upper (D 6) (R 6) [10,36,384,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,36,384,96,68,1] 13 (by decide) (choices 1) [1,2,16] r13977 c13977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3004
  · exact u3005
  · exact u3006

def b13978 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 388 104 84 34 81 145 273), lower := (rows 11 38 388 104 84 34 64 128 256), losses := [] }

theorem u13978 : Upper (D 6) (R 6) [10,36,384,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13979 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 388 104 84 48 67 131 259), lower := (rows 11 38 388 104 84 48 64 128 256), losses := [] }

theorem u13979 : Upper (D 6) (R 6) [10,36,384,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13979 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13979
end Delivery.IrregularNine14.P06
