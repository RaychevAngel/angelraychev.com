import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0031
import IrregularNine14P00C0032

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3060 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 263 19 100 104 153 185 217 153 409), lower := (rows 263 19 100 104 16 32 64 128 256), losses := [] }

theorem u3060 : Upper (D 0) (R 0) [262,17,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3060
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3061 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 100 137 248 248 248 248 504), lower := (rows 263 19 100 137 16 32 64 128 256), losses := [] }

theorem u3061 : Upper (D 0) (R 0) [262,17,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3061
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3062 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u3062 : Upper (D 0) (R 0) [262,17,96,144] 13 := by
  apply FastRouting.sound _ _ [262,17,96,144] 13 (by decide) (choices 1) [1,8,32,128] r3062 c3062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1877
  · exact u1878
  · exact u1879
  · exact u1880

def r3063 : Route 9 := (fun mask => (mask,id))

def c3063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3063 : Upper (D 0) (R 0) [262,17,96,160] 13 := by
  apply FastRouting.sound _ _ [262,17,96,160] 13 (by decide) (choices 1) [1,8,64,128] r3063 c3063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1881
  · exact u1882
  · exact u1883
  · exact u1884

def b3064 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 263 26 100 25 241 225 225 225 481), lower := (rows 263 26 100 25 16 32 64 128 256), losses := [] }

theorem u3064 : Upper (D 0) (R 0) [262,24,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3064
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3065 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 41 209 241 209 209 465), lower := (rows 263 26 100 41 16 32 64 128 256), losses := [] }

theorem u3065 : Upper (D 0) (R 0) [262,24,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3065
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3066 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 263 26 100 56 209 225 193 193 449), lower := (rows 263 26 100 56 16 32 64 128 256), losses := [] }

theorem u3066 : Upper (D 0) (R 0) [262,24,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3066
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3067 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 263 26 100 104 145 177 209 145 401), lower := (rows 263 26 100 104 16 32 64 128 256), losses := [] }

theorem u3067 : Upper (D 0) (R 0) [262,24,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3067
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3068 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3068 : Upper (D 0) (R 0) [262,24,96,129] 13 := by
  apply FastRouting.sound _ _ [262,24,96,129] 13 (by decide) (choices 1) [1,32,128] r3068 c3068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1885
  · exact u1886
  · exact u1887

def b3069 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 263 26 100 152 241 225 225 225 481), lower := (rows 263 26 100 152 16 32 64 128 256), losses := [] }

theorem u3069 : Upper (D 0) (R 0) [262,24,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3069
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3070 : Route 9 := (fun mask => (mask,id))

def c3070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3070 : Upper (D 0) (R 0) [262,24,96,160] 13 := by
  apply FastRouting.sound _ _ [262,24,96,160] 13 (by decide) (choices 1) [1,64,128] r3070 c3070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1888
  · exact u1889
  · exact u1890

def b3071 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 263 50 196 25 249 233 233 233 489), lower := (rows 263 50 196 25 16 32 64 128 256), losses := [] }

theorem u3071 : Upper (D 0) (R 0) [262,48,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3071
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3072 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 263 50 196 56 217 233 201 201 457), lower := (rows 263 50 196 56 16 32 64 128 256), losses := [] }

theorem u3072 : Upper (D 0) (R 0) [262,48,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3072
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3073 : Route 9 := (fun mask => (mask,id))

def c3073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3073 : Upper (D 0) (R 0) [262,48,192,80] 13 := by
  apply FastRouting.sound _ _ [262,48,192,80] 13 (by decide) (choices 1) [1,8,32,128] r3073 c3073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1891
  · exact u1892
  · exact u1893
  · exact u1894

def b3074 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 44 25 240 224 224 224 480), lower := (rows 275 7 44 25 16 32 64 128 256), losses := [] }

theorem u3074 : Upper (D 0) (R 0) [274,5,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3074
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3075 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 275 7 44 41 208 240 208 208 464), lower := (rows 275 7 44 41 16 32 64 128 256), losses := [] }

theorem u3075 : Upper (D 0) (R 0) [274,5,40,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3075
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3076 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 56 209 225 193 193 449), lower := (rows 275 7 44 56 16 32 64 128 256), losses := [] }

theorem u3076 : Upper (D 0) (R 0) [274,5,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3076
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3077 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 73 240 240 240 240 496), lower := (rows 275 7 44 73 16 32 64 128 256), losses := [] }

theorem u3077 : Upper (D 0) (R 0) [274,5,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3077
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3078 : Route 9 := (fun mask => (mask,id))

def c3078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3078 : Upper (D 0) (R 0) [274,5,40,80] 13 := by
  apply FastRouting.sound _ _ [274,5,40,80] 13 (by decide) (choices 1) [1,32,64,128] r3078 c3078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1895
  · exact u1896
  · exact u1897
  · exact u1898

def b3079 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 104 209 241 209 209 465), lower := (rows 275 7 44 104 16 32 64 128 256), losses := [] }

theorem u3079 : Upper (D 0) (R 0) [274,5,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3079
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3080 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3080 : Upper (D 0) (R 0) [274,5,40,192] 13 := by
  apply FastRouting.sound _ _ [274,5,40,192] 13 (by decide) (choices 1) [1,32,64] r3080 c3080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1899
  · exact u1900
  · exact u1901

def b3081 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 100 25 248 232 232 232 488), lower := (rows 275 7 100 25 16 32 64 128 256), losses := [] }

theorem u3081 : Upper (D 0) (R 0) [274,5,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3081
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3082 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 100 41 216 248 216 216 472), lower := (rows 275 7 100 41 16 32 64 128 256), losses := [] }

theorem u3082 : Upper (D 0) (R 0) [274,5,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3082
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3083 : Route 9 := (fun mask => (mask,id))

def c3083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3083 : Upper (D 0) (R 0) [274,5,96,48] 13 := by
  apply FastRouting.sound _ _ [274,5,96,48] 13 (by decide) (choices 1) [1,8,64,128] r3083 c3083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1902
  · exact u1903
  · exact u1904
  · exact u1905

def b3084 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 275 7 100 104 153 185 217 153 409), lower := (rows 275 7 100 104 16 32 64 128 256), losses := [] }

theorem u3084 : Upper (D 0) (R 0) [274,5,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3084
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3085 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 100 137 248 248 248 248 504), lower := (rows 275 7 100 137 16 32 64 128 256), losses := [] }

theorem u3085 : Upper (D 0) (R 0) [274,5,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3085
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3086 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u3086 : Upper (D 0) (R 0) [274,5,96,144] 13 := by
  apply FastRouting.sound _ _ [274,5,96,144] 13 (by decide) (choices 1) [1,8,32,128] r3086 c3086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1906
  · exact u1907
  · exact u1908
  · exact u1909

def r3087 : Route 9 := (fun mask => (mask,id))

def c3087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3087 : Upper (D 0) (R 0) [274,5,96,160] 13 := by
  apply FastRouting.sound _ _ [274,5,96,160] 13 (by decide) (choices 1) [1,8,64,128] r3087 c3087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1910
  · exact u1911
  · exact u1912
  · exact u1913

def b3088 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 14 21 41 240 224 224 224 480), lower := (rows 275 14 21 41 16 32 64 128 256), losses := [] }

theorem u3088 : Upper (D 0) (R 0) [274,12,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3088
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3089 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 14 21 104 241 225 225 225 481), lower := (rows 275 14 21 104 16 32 64 128 256), losses := [] }

theorem u3089 : Upper (D 0) (R 0) [274,12,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3089
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3090 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 275 14 37 41 208 240 208 208 464), lower := (rows 275 14 37 41 16 32 64 128 256), losses := [] }

theorem u3090 : Upper (D 0) (R 0) [274,12,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3090
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3091 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 275 14 37 56 209 225 193 193 449), lower := (rows 275 14 37 56 16 32 64 128 256), losses := [] }

theorem u3091 : Upper (D 0) (R 0) [274,12,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3091
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3092_64 : Upper (D 0) (R 0) [274,12,33,65,64] 13 :=
  permutation_upper _ _ _ [274,12,33,65,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1914

def r3092 : Route 9 := (fun mask => (mask,id))

def c3092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3092 : Upper (D 0) (R 0) [274,12,33,65] 13 := by
  apply FastRouting.sound _ _ [274,12,33,65] 13 (by decide) (choices 1) [32,64,128] r3092 c3092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1914
  · exact m3092_64
  · exact u1915

def b3093 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 275 14 37 88 241 225 225 225 481), lower := (rows 275 14 37 88 16 32 64 128 256), losses := [] }

theorem u3093 : Upper (D 0) (R 0) [274,12,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3093
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3094 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 14 37 104 209 241 209 209 465), lower := (rows 275 14 37 104 16 32 64 128 256), losses := [] }

theorem u3094 : Upper (D 0) (R 0) [274,12,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3094
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3095 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3095 : Upper (D 0) (R 0) [274,12,33,192] 13 := by
  apply FastRouting.sound _ _ [274,12,33,192] 13 (by decide) (choices 1) [1,32,64] r3095 c3095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1916
  · exact u1917
  · exact u1918

def b3096 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 14 52 104 209 225 193 193 449), lower := (rows 275 14 52 104 16 32 64 128 256), losses := [] }

theorem u3096 : Upper (D 0) (R 0) [274,12,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3096
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3097 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 14 52 200 241 225 225 225 481), lower := (rows 275 14 52 200 16 32 64 128 256), losses := [] }

theorem u3097 : Upper (D 0) (R 0) [274,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3097
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3098 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 275 14 100 104 145 177 209 145 401), lower := (rows 275 14 100 104 16 32 64 128 256), losses := [] }

theorem u3098 : Upper (D 0) (R 0) [274,12,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3098
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3099 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 14 100 168 209 241 209 209 465), lower := (rows 275 14 100 168 16 32 64 128 256), losses := [] }

theorem u3099 : Upper (D 0) (R 0) [274,12,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3099
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3100 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 13 28 240 224 224 224 480), lower := (rows 275 35 13 28 16 32 64 128 256), losses := [] }

theorem u3100 : Upper (D 0) (R 0) [274,33,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3100
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3101 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 13 44 208 240 208 208 464), lower := (rows 275 35 13 44 16 32 64 128 256), losses := [] }

theorem u3101 : Upper (D 0) (R 0) [274,33,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3101
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3102 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 13 56 212 228 196 196 452), lower := (rows 275 35 13 56 16 32 64 128 256), losses := [] }

theorem u3102 : Upper (D 0) (R 0) [274,33,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3102
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3103 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 13 76 240 240 240 240 496), lower := (rows 275 35 13 76 16 32 64 128 256), losses := [] }

theorem u3103 : Upper (D 0) (R 0) [274,33,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3103
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3104 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 13 88 244 228 228 228 484), lower := (rows 275 35 13 88 16 32 64 128 256), losses := [] }

theorem u3104 : Upper (D 0) (R 0) [274,33,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3104
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3105 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 13 104 212 244 212 212 468), lower := (rows 275 35 13 104 16 32 64 128 256), losses := [] }

theorem u3105 : Upper (D 0) (R 0) [274,33,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3105
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3106 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 13 200 244 244 244 244 500), lower := (rows 275 35 13 200 16 32 64 128 256), losses := [] }

theorem u3106 : Upper (D 0) (R 0) [274,33,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3106
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3107 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 21 44 216 232 200 200 456), lower := (rows 275 35 21 44 16 32 64 128 256), losses := [] }

theorem u3107 : Upper (D 0) (R 0) [274,33,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3107
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3108 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 21 76 248 232 232 232 488), lower := (rows 275 35 21 76 16 32 64 128 256), losses := [] }

theorem u3108 : Upper (D 0) (R 0) [274,33,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3108
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3109 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 21 104 220 236 204 204 460), lower := (rows 275 35 21 104 16 32 64 128 256), losses := [] }

theorem u3109 : Upper (D 0) (R 0) [274,33,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3109
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3110 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 21 200 252 236 236 236 492), lower := (rows 275 35 21 200 16 32 64 128 256), losses := [] }

theorem u3110 : Upper (D 0) (R 0) [274,33,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3110
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3111 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 35 28 41 212 228 196 196 452), lower := (rows 275 35 28 41 16 32 64 128 256), losses := [] }

theorem u3111 : Upper (D 0) (R 0) [274,33,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3111
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3112 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 28 44 209 225 193 193 449), lower := (rows 275 35 28 44 16 32 64 128 256), losses := [] }

theorem u3112 : Upper (D 0) (R 0) [274,33,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3112
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3113 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 28 73 244 228 228 228 484), lower := (rows 275 35 28 73 16 32 64 128 256), losses := [] }

theorem u3113 : Upper (D 0) (R 0) [274,33,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3113
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3114 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 28 76 241 225 225 225 481), lower := (rows 275 35 28 76 16 32 64 128 256), losses := [] }

theorem u3114 : Upper (D 0) (R 0) [274,33,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3114
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3115 : Route 9 := (fun mask => (mask,id))

def c3115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3115 : Upper (D 0) (R 0) [274,33,24,96] 13 := by
  apply FastRouting.sound _ _ [274,33,24,96] 13 (by decide) (choices 1) [1,4,64,128] r3115 c3115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1919
  · exact u1920
  · exact u1921
  · exact u1922

def r3116 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3116 : Upper (D 0) (R 0) [274,33,24,192] 13 := by
  apply FastRouting.sound _ _ [274,33,24,192] 13 (by decide) (choices 1) [1,4,32,64] r3116 c3116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1923
  · exact u1924
  · exact u1925
  · exact u1926

def b3117 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 37 76 216 248 216 216 472), lower := (rows 275 35 37 76 16 32 64 128 256), losses := [] }

theorem u3117 : Upper (D 0) (R 0) [274,33,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3117
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3118 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 37 88 220 236 204 204 460), lower := (rows 275 35 37 88 16 32 64 128 256), losses := [] }

theorem u3118 : Upper (D 0) (R 0) [274,33,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3118
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3119 : PairBound 9 := { available := 220, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 37 200 220 252 220 220 476), lower := (rows 275 35 37 200 16 32 64 128 256), losses := [] }

theorem u3119 : Upper (D 0) (R 0) [274,33,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3119
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u3119
end Delivery.IrregularNine14.P00
