import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0013

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3060 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 50 33 76 140 268), lower := (rows 7 67 164 280 50 33 64 128 256), losses := [] }

theorem u3060 : Upper (D 5) (R 5) [6,65,160,272,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3060
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3061 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 50 36 73 137 265), lower := (rows 7 67 164 280 50 36 64 128 256), losses := [] }

theorem u3061 : Upper (D 5) (R 5) [6,65,160,272,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3061
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3062 : Route 9 := (fun mask => (mask,id))

def c3062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3062 : Upper (D 5) (R 5) [6,65,160,272,34,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,34,8] 13 (by decide) (choices 1) [1,4,8] r3062 c3062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u823
  · exact u824
  · exact u825

def b3063 : PairBound 9 := { available := 14, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 280 56 33 78 142 270), lower := (rows 7 67 164 280 56 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 52 32 65 129 257), good := (rows 478 458 188 280 60 508 64 128 256) }] }

theorem u3063 : Upper (D 5) (R 5) [6,65,160,272,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3064 : Route 9 := (fun mask => (mask,id))

def c3064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3064 : Upper (D 5) (R 5) [6,65,160,272,40,2] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,40,2] 13 (by decide) (choices 1) [1,4,8] r3064 c3064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u826
  · exact u827
  · exact u828

def b3065 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 56 36 75 139 267), lower := (rows 7 67 164 280 56 36 64 128 256), losses := [] }

theorem u3065 : Upper (D 5) (R 5) [6,65,160,272,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3065
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3066 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 280 56 40 71 135 263), lower := (rows 7 67 164 280 56 40 64 128 256), losses := [] }

theorem u3066 : Upper (D 5) (R 5) [6,65,160,272,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3066
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3067 : PairBound 9 := { available := 28, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 296 25 34 92 156 284), lower := (rows 7 67 164 296 25 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 98 164 296 508 34 64 128 256) }] }

theorem u3067 : Upper (D 5) (R 5) [6,65,160,288,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3067
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3068 : PairBound 9 := { available := 26, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 296 25 36 90 154 282), lower := (rows 7 67 164 296 25 36 64 128 256), losses := [] }

theorem u3068 : Upper (D 5) (R 5) [6,65,160,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3068
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3069 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 296 25 40 86 150 278), lower := (rows 7 67 164 296 25 40 64 128 256), losses := [] }

theorem u3069 : Upper (D 5) (R 5) [6,65,160,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3069
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3070 : Route 9 := (fun mask => (mask,id))

def c3070 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3070 : Upper (D 5) (R 5) [6,65,160,288,9,16] 13 := by
  apply FastRouting.sound _ _ [6,65,160,288,9,16] 13 (by decide) (choices 1) [2,4,8] r3070 c3070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u829
  · exact u830
  · exact u831

def b3071 : PairBound 9 := { available := 28, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 296 26 33 92 156 284), lower := (rows 7 67 164 296 26 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 17 32 113 177 305), good := (rows 478 466 492 492 478 508 64 128 256) }] }

theorem u3071 : Upper (D 5) (R 5) [6,65,160,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3071
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3072 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 296 26 36 89 153 281), lower := (rows 7 67 164 296 26 36 64 128 256), losses := [] }

theorem u3072 : Upper (D 5) (R 5) [6,65,160,288,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3072
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3073 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 296 26 40 85 149 277), lower := (rows 7 67 164 296 26 40 64 128 256), losses := [] }

theorem u3073 : Upper (D 5) (R 5) [6,65,160,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3073
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3074 : Route 9 := (fun mask => (mask,id))

def c3074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3074 : Upper (D 5) (R 5) [6,65,160,288,10,16] 13 := by
  apply FastRouting.sound _ _ [6,65,160,288,10,16] 13 (by decide) (choices 1) [1,4,8] r3074 c3074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u832
  · exact u833
  · exact u834

def b3075 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 67 388 25 52 34 104 168 296), lower := (rows 7 67 388 25 52 34 64 128 256), losses := [] }

theorem u3075 : Upper (D 5) (R 5) [6,65,384,17,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3075
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3076 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 25 52 40 106 170 298), lower := (rows 7 67 388 25 52 40 64 128 256), losses := [] }

theorem u3076 : Upper (D 5) (R 5) [6,65,384,17,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3076
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3077 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 388 25 56 34 108 172 300), lower := (rows 7 67 388 25 56 34 64 128 256), losses := [] }

theorem u3077 : Upper (D 5) (R 5) [6,65,384,17,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3077
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3078 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 25 56 36 106 170 298), lower := (rows 7 67 388 25 56 36 64 128 256), losses := [] }

theorem u3078 : Upper (D 5) (R 5) [6,65,384,17,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3078
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3079 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 56, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 388 25 56 40 102 166 294), lower := (rows 7 67 388 25 56 40 64 128 256), losses := [] }

theorem u3079 : Upper (D 5) (R 5) [6,65,384,17,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3079
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3080 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 388 26 52 33 104 168 296), lower := (rows 7 67 388 26 52 33 64 128 256), losses := [] }

theorem u3080 : Upper (D 5) (R 5) [6,65,384,18,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3080
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3081 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 26 52 40 105 169 297), lower := (rows 7 67 388 26 52 40 64 128 256), losses := [] }

theorem u3081 : Upper (D 5) (R 5) [6,65,384,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3081
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3082 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 388 26 56 33 108 172 300), lower := (rows 7 67 388 26 56 33 64 128 256), losses := [] }

theorem u3082 : Upper (D 5) (R 5) [6,65,384,18,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3082
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3083 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 26 56 36 105 169 297), lower := (rows 7 67 388 26 56 36 64 128 256), losses := [] }

theorem u3083 : Upper (D 5) (R 5) [6,65,384,18,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3083
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3084 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 56, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 388 26 56 40 101 165 293), lower := (rows 7 67 388 26 56 40 64 128 256), losses := [] }

theorem u3084 : Upper (D 5) (R 5) [6,65,384,18,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3084
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3085 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 28 49 34 104 168 296), lower := (rows 7 67 388 28 49 34 64 128 256), losses := [] }

theorem u3085 : Upper (D 5) (R 5) [6,65,384,20,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3085
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3086 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 28 49 40 106 170 298), lower := (rows 7 67 388 28 49 40 64 128 256), losses := [] }

theorem u3086 : Upper (D 5) (R 5) [6,65,384,20,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3086
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3087 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 28 50 33 104 168 296), lower := (rows 7 67 388 28 50 33 64 128 256), losses := [] }

theorem u3087 : Upper (D 5) (R 5) [6,65,384,20,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3087
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3088 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 28 50 40 105 169 297), lower := (rows 7 67 388 28 50 40 64 128 256), losses := [] }

theorem u3088 : Upper (D 5) (R 5) [6,65,384,20,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3088
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3089 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 28 56 33 106 170 298), lower := (rows 7 67 388 28 56 33 64 128 256), losses := [] }

theorem u3089 : Upper (D 5) (R 5) [6,65,384,20,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3089
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3090 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 28 56 34 105 169 297), lower := (rows 7 67 388 28 56 34 64 128 256), losses := [] }

theorem u3090 : Upper (D 5) (R 5) [6,65,384,20,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3090
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3091 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 388 28 56 40 99 163 291), lower := (rows 7 67 388 28 56 40 64 128 256), losses := [] }

theorem u3091 : Upper (D 5) (R 5) [6,65,384,20,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3091
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3092 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 41 28 34 120 184 312), lower := (rows 7 67 388 41 28 34 64 128 256), losses := [] }

theorem u3092 : Upper (D 5) (R 5) [6,65,384,33,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3092
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3093 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 41 28 40 114 178 306), lower := (rows 7 67 388 41 28 40 64 128 256), losses := [] }

theorem u3093 : Upper (D 5) (R 5) [6,65,384,33,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3093
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3094 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1)], upper := (rows 7 67 388 41 28 48 106 170 298), lower := (rows 7 67 388 41 28 48 64 128 256), losses := [] }

theorem u3094 : Upper (D 5) (R 5) [6,65,384,33,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3094
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3095 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 67 388 41 50 36 88 152 280), lower := (rows 7 67 388 41 50 36 64 128 256), losses := [] }

theorem u3095 : Upper (D 5) (R 5) [6,65,384,33,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3095
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3096 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 388 41 50 40 92 156 284), lower := (rows 7 67 388 41 50 40 64 128 256), losses := [] }

theorem u3096 : Upper (D 5) (R 5) [6,65,384,33,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3096
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3097 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 388 41 50 48 76 140 268), lower := (rows 7 67 388 41 50 48 64 128 256), losses := [] }

theorem u3097 : Upper (D 5) (R 5) [6,65,384,33,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3097
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3098 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 41 52 34 88 152 280), lower := (rows 7 67 388 41 52 34 64 128 256), losses := [] }

theorem u3098 : Upper (D 5) (R 5) [6,65,384,33,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3098
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3099 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 41 52 40 90 154 282), lower := (rows 7 67 388 41 52 40 64 128 256), losses := [] }

theorem u3099 : Upper (D 5) (R 5) [6,65,384,33,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3099
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3100 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 388 41 52 48 74 138 266), lower := (rows 7 67 388 41 52 48 64 128 256), losses := [] }

theorem u3100 : Upper (D 5) (R 5) [6,65,384,33,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3100
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3101 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 42 28 33 120 184 312), lower := (rows 7 67 388 42 28 33 64 128 256), losses := [] }

theorem u3101 : Upper (D 5) (R 5) [6,65,384,34,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3101
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3102 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 42 28 40 113 177 305), lower := (rows 7 67 388 42 28 40 64 128 256), losses := [] }

theorem u3102 : Upper (D 5) (R 5) [6,65,384,34,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3102
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3103 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 388 42 28 48 105 169 297), lower := (rows 7 67 388 42 28 48 64 128 256), losses := [] }

theorem u3103 : Upper (D 5) (R 5) [6,65,384,34,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3103
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3104 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 388 42 49 36 88 152 280), lower := (rows 7 67 388 42 49 36 64 128 256), losses := [] }

theorem u3104 : Upper (D 5) (R 5) [6,65,384,34,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3104
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3105 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 388 42 49 40 92 156 284), lower := (rows 7 67 388 42 49 40 64 128 256), losses := [] }

theorem u3105 : Upper (D 5) (R 5) [6,65,384,34,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3105
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3106 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 389, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 388 42 49 48 76 140 268), lower := (rows 7 67 388 42 49 48 64 128 256), losses := [] }

theorem u3106 : Upper (D 5) (R 5) [6,65,384,34,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3106
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3107 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 42 52 33 88 152 280), lower := (rows 7 67 388 42 52 33 64 128 256), losses := [] }

theorem u3107 : Upper (D 5) (R 5) [6,65,384,34,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3107
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3108 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 42 52 40 89 153 281), lower := (rows 7 67 388 42 52 40 64 128 256), losses := [] }

theorem u3108 : Upper (D 5) (R 5) [6,65,384,34,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3109 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 388 42 52 48 73 137 265), lower := (rows 7 67 388 42 52 48 64 128 256), losses := [] }

theorem u3109 : Upper (D 5) (R 5) [6,65,384,34,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3109
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3110 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 40, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 7 67 388 44 25 34 120 184 312), lower := (rows 7 67 388 44 25 34 64 128 256), losses := [] }

theorem u3110 : Upper (D 5) (R 5) [6,65,384,36,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3110
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3111 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 44 25 40 114 178 306), lower := (rows 7 67 388 44 25 40 64 128 256), losses := [] }

theorem u3111 : Upper (D 5) (R 5) [6,65,384,36,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3111
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3112 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1)], upper := (rows 7 67 388 44 25 48 106 170 298), lower := (rows 7 67 388 44 25 48 64 128 256), losses := [] }

theorem u3112 : Upper (D 5) (R 5) [6,65,384,36,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3112
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3113 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 388 44 26 33 120 184 312), lower := (rows 7 67 388 44 26 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 80 144 272), good := (rows 45 105 388 44 508 41 64 128 256) }] }

theorem u3113 : Upper (D 5) (R 5) [6,65,384,36,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3114 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 44 26 40 113 177 305), lower := (rows 7 67 388 44 26 40 64 128 256), losses := [] }

theorem u3114 : Upper (D 5) (R 5) [6,65,384,36,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3114
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3115 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 388 44 26 48 105 169 297), lower := (rows 7 67 388 44 26 48 64 128 256), losses := [] }

theorem u3115 : Upper (D 5) (R 5) [6,65,384,36,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3115
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3116 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 44 49 34 88 152 280), lower := (rows 7 67 388 44 49 34 64 128 256), losses := [] }

theorem u3116 : Upper (D 5) (R 5) [6,65,384,36,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3116
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3117 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 44 49 40 90 154 282), lower := (rows 7 67 388 44 49 40 64 128 256), losses := [] }

theorem u3117 : Upper (D 5) (R 5) [6,65,384,36,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3117
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3118 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 388 44 49 48 74 138 266), lower := (rows 7 67 388 44 49 48 64 128 256), losses := [] }

theorem u3118 : Upper (D 5) (R 5) [6,65,384,36,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3118
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3119 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 44 50 33 88 152 280), lower := (rows 7 67 388 44 50 33 64 128 256), losses := [] }

theorem u3119 : Upper (D 5) (R 5) [6,65,384,36,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3119
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3119
end Delivery.IrregularNine14.P05
