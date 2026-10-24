import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7920 : PairBound 9 := { available := 36, camps := [{ cop := 8, region := 82, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 133 73 274 36 66 164 292), lower := (rows 41 82 133 73 274 36 66 128 256), losses := [] }

theorem u7920 : Upper (D 6) (R 6) [40,80,129,65,258,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7921 : PairBound 9 := { available := 34, camps := [{ cop := 7, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 73 274 36 68 162 290), lower := (rows 41 82 133 73 274 36 68 128 256), losses := [] }

theorem u7921 : Upper (D 6) (R 6) [40,80,129,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7922 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 82 133 73 274 36 96 134 262), lower := (rows 41 82 133 73 274 36 96 128 256), losses := [] }

theorem u7922 : Upper (D 6) (R 6) [40,80,129,65,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7923 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 82 133 73 304 36 66 134 262), lower := (rows 41 82 133 73 304 36 66 128 256), losses := [] }

theorem u7923 : Upper (D 6) (R 6) [40,80,129,65,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7924 : PairBound 9 := { available := 2, camps := [{ cop := 7, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 73 304 36 68 130 258), lower := (rows 41 82 133 73 304 36 68 128 256), losses := [] }

theorem u7924 : Upper (D 6) (R 6) [40,80,129,65,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7925 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 82, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 41 82 133 76 19 288 66 164 292), lower := (rows 41 82 133 76 19 288 66 128 256), losses := [] }

theorem u7925 : Upper (D 6) (R 6) [40,80,129,68,3,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7925 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7926 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 90, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 41 82 133 76 19 288 68 162 290), lower := (rows 41 82 133 76 19 288 68 128 256), losses := [] }

theorem u7926 : Upper (D 6) (R 6) [40,80,129,68,3,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7926 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7927 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 41 82 133 76 19 288 96 134 262), lower := (rows 41 82 133 76 19 288 96 128 256), losses := [] }

theorem u7927 : Upper (D 6) (R 6) [40,80,129,68,3,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7927 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7928 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 41 82 133 76 50 288 65 134 262), lower := (rows 41 82 133 76 50 288 65 128 256), losses := [] }

theorem u7928 : Upper (D 6) (R 6) [40,80,129,68,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7928 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7929 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 289, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 82 133 76 50 288 66 133 261), lower := (rows 41 82 133 76 50 288 66 128 256), losses := [] }

theorem u7929 : Upper (D 6) (R 6) [40,80,129,68,34,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7929 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7930 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 41 82 133 76 50 288 68 131 259), lower := (rows 41 82 133 76 50 288 68 128 256), losses := [] }

theorem u7930 : Upper (D 6) (R 6) [40,80,129,68,34,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7930 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7931 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 72, targets := 34 },{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 41 82 133 76 52 34 65 386 258), lower := (rows 41 82 133 76 52 34 65 128 256), losses := [] }

theorem u7931 : Upper (D 6) (R 6) [40,80,129,68,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7932 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 76 52 34 66 385 257), lower := (rows 41 82 133 76 52 34 66 128 256), losses := [] }

theorem u7932 : Upper (D 6) (R 6) [40,80,129,68,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7933 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 82 133 76 52 34 320 131 259), lower := (rows 41 82 133 76 52 34 320 128 256), losses := [] }

theorem u7933 : Upper (D 6) (R 6) [40,80,129,68,36,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7933 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7934 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 41 82 133 76 52 288 65 130 258), lower := (rows 41 82 133 76 52 288 65 128 256), losses := [] }

theorem u7934 : Upper (D 6) (R 6) [40,80,129,68,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7934 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7935 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 41 82 133 76 52 288 66 131 259), lower := (rows 41 82 133 76 52 288 66 128 256), losses := [] }

theorem u7935 : Upper (D 6) (R 6) [40,80,129,68,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7935 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7936 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 76 273 34 66 164 292), lower := (rows 41 82 133 76 273 34 66 128 256), losses := [] }

theorem u7936 : Upper (D 6) (R 6) [40,80,129,68,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7937 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 82 133 76 273 34 68 162 290), lower := (rows 41 82 133 76 273 34 68 128 256), losses := [] }

theorem u7937 : Upper (D 6) (R 6) [40,80,129,68,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7938 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 41 82 133 76 273 34 96 134 262), lower := (rows 41 82 133 76 273 34 96 128 256), losses := [{ target := 0, region := (rows 0 18 4 12 16 50 115 128 256), good := (rows 104 114 204 76 370 98 96 128 256) }] }

theorem u7938 : Upper (D 6) (R 6) [40,80,129,68,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7939 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 72, targets := 34 },{ cop := 3, region := 306, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 41 82 133 76 276 34 65 162 290), lower := (rows 41 82 133 76 276 34 65 128 256), losses := [] }

theorem u7939 : Upper (D 6) (R 6) [40,80,129,68,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7940 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 76 276 34 66 161 289), lower := (rows 41 82 133 76 276 34 66 128 256), losses := [] }

theorem u7940 : Upper (D 6) (R 6) [40,80,129,68,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7941 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 41 82 133 76 276 34 96 131 259), lower := (rows 41 82 133 76 276 34 96 128 256), losses := [] }

theorem u7941 : Upper (D 6) (R 6) [40,80,129,68,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7942 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 72, targets := 34 },{ cop := 3, region := 306, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 41 82 133 76 304 34 65 134 262), lower := (rows 41 82 133 76 304 34 65 128 256), losses := [] }

theorem u7942 : Upper (D 6) (R 6) [40,80,129,68,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7943 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 76 304 34 66 133 261), lower := (rows 41 82 133 76 304 34 66 128 256), losses := [] }

theorem u7943 : Upper (D 6) (R 6) [40,80,129,68,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7944 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 82 133 76 304 34 68 131 259), lower := (rows 41 82 133 76 304 34 68 128 256), losses := [] }

theorem u7944 : Upper (D 6) (R 6) [40,80,129,68,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7945 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 429, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 265 22 36 66 224 352), lower := (rows 41 82 133 265 22 36 66 128 256), losses := [] }

theorem u7945 : Upper (D 6) (R 6) [40,80,129,257,6,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7946 : Route 9 := (fun mask => (mask,id))

def c7946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7946 : Upper (D 6) (R 6) [40,80,129,257,6,4,32] 13 := by
  apply FastRouting.sound _ _ [40,80,129,257,6,4,32] 13 (by decide) (choices 1) [2,64] r7946 c7946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u615
  · exact u616

def b7947 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 397, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 133 265 22 96 66 164 292), lower := (rows 41 82 133 265 22 96 66 128 256), losses := [] }

theorem u7947 : Upper (D 6) (R 6) [40,80,129,257,6,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7948 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 297, targets := 4 },{ cop := 2, region := 82, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 133 265 22 96 68 162 290), lower := (rows 41 82 133 265 22 96 68 128 256), losses := [] }

theorem u7948 : Upper (D 6) (R 6) [40,80,129,257,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7949 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 82 133 265 22 96 96 134 262), lower := (rows 41 82 133 265 22 96 96 128 256), losses := [] }

theorem u7949 : Upper (D 6) (R 6) [40,80,129,257,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7950 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 429, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 265 50 36 66 196 324), lower := (rows 41 82 133 265 50 36 66 128 256), losses := [] }

theorem u7950 : Upper (D 6) (R 6) [40,80,129,257,34,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7951 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 41 82 133 265 50 36 68 194 322), lower := (rows 41 82 133 265 50 36 68 128 256), losses := [{ target := 2, region := (rows 17 2 0 26 16 32 64 130 258), good := (rows 41 475 129 265 443 32 64 128 256) }] }

theorem u7951 : Upper (D 6) (R 6) [40,80,129,257,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7952 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(1,5),(4,5)], upper := (rows 41 82 133 266 19 36 68 224 352), lower := (rows 41 82 133 266 19 36 68 128 256), losses := [] }

theorem u7952 : Upper (D 6) (R 6) [40,80,129,258,3,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7953 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 266 19 36 96 196 324), lower := (rows 41 82 133 266 19 36 96 128 256), losses := [] }

theorem u7953 : Upper (D 6) (R 6) [40,80,129,258,3,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7954 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(1,5),(4,5)], upper := (rows 41 82 133 266 22 36 65 224 352), lower := (rows 41 82 133 266 22 36 65 128 256), losses := [] }

theorem u7954 : Upper (D 6) (R 6) [40,80,129,258,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7955 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 133 266 22 36 96 193 321), lower := (rows 41 82 133 266 22 36 96 128 256), losses := [] }

theorem u7955 : Upper (D 6) (R 6) [40,80,129,258,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7956 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 2, region := 112, targets := 2 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 82 133 266 52 96 65 134 262), lower := (rows 41 82 133 266 52 96 65 128 256), losses := [] }

theorem u7956 : Upper (D 6) (R 6) [40,80,129,258,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7957 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 148, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 266 52 96 66 133 261), lower := (rows 41 82 133 266 52 96 66 128 256), losses := [] }

theorem u7957 : Upper (D 6) (R 6) [40,80,129,258,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7958 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 297, targets := 4 },{ cop := 2, region := 114, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 133 266 52 96 68 131 259), lower := (rows 41 82 133 266 52 96 68 128 256), losses := [] }

theorem u7958 : Upper (D 6) (R 6) [40,80,129,258,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7959 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 397, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 133 268 19 96 66 164 292), lower := (rows 41 82 133 268 19 96 66 128 256), losses := [] }

theorem u7959 : Upper (D 6) (R 6) [40,80,129,260,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7960 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(4,5)], upper := (rows 41 82 133 268 19 96 68 162 290), lower := (rows 41 82 133 268 19 96 68 128 256), losses := [] }

theorem u7960 : Upper (D 6) (R 6) [40,80,129,260,3,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7961 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 41 82 133 268 19 96 96 134 262), lower := (rows 41 82 133 268 19 96 96 128 256), losses := [] }

theorem u7961 : Upper (D 6) (R 6) [40,80,129,260,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7962 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(4,5)], upper := (rows 41 82 133 268 22 96 65 162 290), lower := (rows 41 82 133 268 22 96 65 128 256), losses := [] }

theorem u7962 : Upper (D 6) (R 6) [40,80,129,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7963 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 397, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 133 268 22 96 66 161 289), lower := (rows 41 82 133 268 22 96 66 128 256), losses := [] }

theorem u7963 : Upper (D 6) (R 6) [40,80,129,260,6,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7964 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 133 268 22 96 96 131 259), lower := (rows 41 82 133 268 22 96 96 128 256), losses := [] }

theorem u7964 : Upper (D 6) (R 6) [40,80,129,260,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7965 : PairBound 9 := { available := 66, camps := [], pairs := [(1,2),(1,5),(3,5)], upper := (rows 41 82 133 268 52 34 65 194 322), lower := (rows 41 82 133 268 52 34 65 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 50 69 146 274), good := (rows 105 498 193 328 498 418 65 128 256) },{ target := 5, region := (rows 1 18 4 24 16 0 69 146 274), good := (rows 73 474 197 332 478 386 65 128 256) }] }

theorem u7965 : Upper (D 6) (R 6) [40,80,129,260,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7966 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 82 133 268 52 34 66 193 321), lower := (rows 41 82 133 268 52 34 66 128 256), losses := [] }

theorem u7966 : Upper (D 6) (R 6) [40,80,129,260,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7967 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 113, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 82 133 268 52 96 65 130 258), lower := (rows 41 82 133 268 52 96 65 128 256), losses := [] }

theorem u7967 : Upper (D 6) (R 6) [40,80,129,260,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7968 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 82 133 268 52 96 66 131 259), lower := (rows 41 82 133 268 52 96 66 128 256), losses := [] }

theorem u7968 : Upper (D 6) (R 6) [40,80,129,260,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7969 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 82, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 133 328 19 36 66 164 292), lower := (rows 41 82 133 328 19 36 66 128 256), losses := [] }

theorem u7969 : Upper (D 6) (R 6) [40,80,129,320,3,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7970 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 4, region := 164, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 41 82 133 328 19 36 68 162 290), lower := (rows 41 82 133 328 19 36 68 128 256), losses := [] }

theorem u7970 : Upper (D 6) (R 6) [40,80,129,320,3,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7971 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 4, region := 132, targets := 32 }], pairs := [(1,2),(2,5),(4,2)], upper := (rows 41 82 133 328 19 36 96 134 262), lower := (rows 41 82 133 328 19 36 96 128 256), losses := [] }

theorem u7971 : Upper (D 6) (R 6) [40,80,129,320,3,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7972 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 82, targets := 32 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 41 82 133 328 22 36 65 162 290), lower := (rows 41 82 133 328 22 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 52 64 146 274), good := (rows 40 506 164 328 446 36 64 128 256) }] }

theorem u7972 : Upper (D 6) (R 6) [40,80,129,320,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7973 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 133 328 22 36 66 161 289), lower := (rows 41 82 133 328 22 36 66 128 256), losses := [] }

theorem u7973 : Upper (D 6) (R 6) [40,80,129,320,6,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7974 : Route 9 := (fun mask => (mask,id))

def c7974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7974 : Upper (D 6) (R 6) [40,80,129,320,6,4,32] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,6,4,32] 13 (by decide) (choices 1) [1,2] r7974 c7974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u617
  · exact u618

def r7975 : Route 9 := (fun mask => (mask,id))

def c7975 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7975 : Upper (D 6) (R 6) [40,80,129,320,34,4,1] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,34,4,1] 13 (by decide) (choices 1) [2,4] r7975 c7975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u619
  · exact u620

def b7976 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 133 328 50 36 66 133 261), lower := (rows 41 82 133 328 50 36 66 128 256), losses := [] }

theorem u7976 : Upper (D 6) (R 6) [40,80,129,320,34,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7977 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 133 328 50 36 68 131 259), lower := (rows 41 82 133 328 50 36 68 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 100 100 128 256), good := (rows 105 112 229 361 112 100 100 128 256) }] }

theorem u7977 : Upper (D 6) (R 6) [40,80,129,320,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7978 : PairBound 9 := { available := 6, camps := [], pairs := [(1,2),(1,5),(3,5)], upper := (rows 41 82 133 328 52 34 65 134 262), lower := (rows 41 82 133 328 52 34 65 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 50 69 128 256), good := (rows 105 114 193 328 114 34 65 128 256) },{ target := 5, region := (rows 1 18 4 26 16 0 69 144 272), good := (rows 73 474 197 328 478 10 65 128 256) }] }

theorem u7978 : Upper (D 6) (R 6) [40,80,129,320,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7979 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 148, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 328 52 34 66 133 261), lower := (rows 41 82 133 328 52 34 66 128 256), losses := [] }

theorem u7979 : Upper (D 6) (R 6) [40,80,129,320,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7979
end Delivery.IrregularNine14.P06
