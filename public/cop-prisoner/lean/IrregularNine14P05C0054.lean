import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0015
import IrregularNine14P05C0016

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3240 : Route 9 := (fun mask => (mask,id))

def c3240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3240 : Upper (D 5) (R 5) [6,72,160,17,260,8] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,260,8] 13 (by decide) (choices 1) [1,2,32] r3240 c3240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u905
  · exact u906
  · exact u907

def r3241 : Route 9 := (fun mask => (mask,id))

def c3241 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3241 : Upper (D 5) (R 5) [6,72,160,17,288,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,288,1] 13 (by decide) (choices 1) [2,4,8] r3241 c3241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u908
  · exact u909
  · exact u910

def r3242 : Route 9 := (fun mask => (mask,id))

def c3242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3242 : Upper (D 5) (R 5) [6,72,160,17,288,2] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,288,2] 13 (by decide) (choices 1) [1,4,8] r3242 c3242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u911
  · exact u912
  · exact u913

def b3243 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 25 304 36 75 139 267), lower := (rows 7 74 164 25 304 36 64 128 256), losses := [] }

theorem u3243 : Upper (D 5) (R 5) [6,72,160,17,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3243
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3244 : Route 9 := (fun mask => (mask,id))

def c3244 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3244 : Upper (D 5) (R 5) [6,72,160,17,288,8] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,288,8] 13 (by decide) (choices 1) [1,2,4] r3244 c3244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u914
  · exact u915
  · exact u916

def b3245 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 164 26 49 33 332 396 268), lower := (rows 7 74 164 26 49 33 64 128 256), losses := [] }

theorem u3245 : Upper (D 5) (R 5) [6,72,160,18,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3245
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3246 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 164 26 49 36 329 393 265), lower := (rows 7 74 164 26 49 36 64 128 256), losses := [] }

theorem u3246 : Upper (D 5) (R 5) [6,72,160,18,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3246
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3247 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 26 49 40 325 389 261), lower := (rows 7 74 164 26 49 40 64 128 256), losses := [] }

theorem u3247 : Upper (D 5) (R 5) [6,72,160,18,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3247
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3248 : Route 9 := (fun mask => (mask,id))

def c3248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3248 : Upper (D 5) (R 5) [6,72,160,18,33,256] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18,33,256] 13 (by decide) (choices 1) [1,4,8] r3248 c3248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u917
  · exact u918
  · exact u919

def r3249 : Route 9 := (fun mask => (mask,id))

def c3249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3249 : Upper (D 5) (R 5) [6,72,160,18,257,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18,257,1] 13 (by decide) (choices 1) [4,8,32] r3249 c3249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u920
  · exact u921
  · exact u922

def b3250 : PairBound 9 := { available := 41, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 26 273 36 105 169 297), lower := (rows 7 74 164 26 273 36 64 128 256), losses := [] }

theorem u3250 : Upper (D 5) (R 5) [6,72,160,18,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3250
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3251 : PairBound 9 := { available := 37, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 74 164 26 273 40 101 165 293), lower := (rows 7 74 164 26 273 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 42 65 129 257), good := (rows 501 104 164 56 469 40 64 128 256) }] }

theorem u3251 : Upper (D 5) (R 5) [6,72,160,18,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3251
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3252 : Route 9 := (fun mask => (mask,id))

def c3252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3252 : Upper (D 5) (R 5) [6,72,160,18,260,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18,260,1] 13 (by decide) (choices 1) [1,8,32] r3252 c3252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u923
  · exact u924
  · exact u925

def b3253 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 74 164 26 276 40 97 161 289), lower := (rows 7 74 164 26 276 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 42 65 129 257), good := (rows 501 104 164 56 276 40 64 128 256) }] }

theorem u3253 : Upper (D 5) (R 5) [6,72,160,18,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3253
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3254 : Route 9 := (fun mask => (mask,id))

def c3254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3254 : Upper (D 5) (R 5) [6,72,160,18,288,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18,288,1] 13 (by decide) (choices 1) [1,4,8] r3254 c3254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u926
  · exact u927
  · exact u928

def b3255 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 26 304 36 73 137 265), lower := (rows 7 74 164 26 304 36 64 128 256), losses := [] }

theorem u3255 : Upper (D 5) (R 5) [6,72,160,18,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3255
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3256 : PairBound 9 := { available := 5, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 74 164 26 304 40 69 133 261), lower := (rows 7 74 164 26 304 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 42 65 129 257), good := (rows 501 104 164 56 304 40 64 128 256) }] }

theorem u3256 : Upper (D 5) (R 5) [6,72,160,18,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3256
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3257 : Route 9 := (fun mask => (mask,id))

def c3257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3257 : Upper (D 5) (R 5) [6,72,160,20,257,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,20,257,1] 13 (by decide) (choices 1) [2,8,32] r3257 c3257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u929
  · exact u930
  · exact u931

def r3258 : Route 9 := (fun mask => (mask,id))

def c3258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3258 : Upper (D 5) (R 5) [6,72,160,20,257,2] 13 := by
  apply FastRouting.sound _ _ [6,72,160,20,257,2] 13 (by decide) (choices 1) [1,8,32] r3258 c3258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u932
  · exact u933
  · exact u934

def r3259 : Route 9 := (fun mask => (mask,id))

def c3259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3259 : Upper (D 5) (R 5) [6,72,160,20,257,8] 13 := by
  apply FastRouting.sound _ _ [6,72,160,20,257,8] 13 (by decide) (choices 1) [1,2,32] r3259 c3259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u935
  · exact u936
  · exact u937

def r3260 : Route 9 := (fun mask => (mask,id))

def c3260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3260 : Upper (D 5) (R 5) [6,72,160,20,258,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,20,258,1] 13 (by decide) (choices 1) [1,8,32] r3260 c3260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u938
  · exact u939
  · exact u940

def b3261 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(4,2)], upper := (rows 7 74 164 28 274 40 97 161 289), lower := (rows 7 74 164 28 274 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 42 65 129 257), good := (rows 485 104 164 60 304 40 64 128 256) },{ target := 2, region := (rows 1 2 0 8 17 42 65 129 257), good := (rows 499 106 160 56 306 40 64 128 256) }] }

theorem u3261 : Upper (D 5) (R 5) [6,72,160,20,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3262 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 164 41 273 34 92 156 284), lower := (rows 7 74 164 41 273 34 64 128 256), losses := [] }

theorem u3262 : Upper (D 5) (R 5) [6,72,160,33,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3262
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3263 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 164 41 273 36 90 154 282), lower := (rows 7 74 164 41 273 36 64 128 256), losses := [] }

theorem u3263 : Upper (D 5) (R 5) [6,72,160,33,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3263
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3264 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 164 41 273 40 86 150 278), lower := (rows 7 74 164 41 273 40 64 128 256), losses := [] }

theorem u3264 : Upper (D 5) (R 5) [6,72,160,33,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3265 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 41 273 48 78 142 270), lower := (rows 7 74 164 41 273 48 64 128 256), losses := [] }

theorem u3265 : Upper (D 5) (R 5) [6,72,160,33,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3265
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3266 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 164 41 274 33 92 156 284), lower := (rows 7 74 164 41 274 33 64 128 256), losses := [] }

theorem u3266 : Upper (D 5) (R 5) [6,72,160,33,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3266
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3267 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 164 41 274 36 89 153 281), lower := (rows 7 74 164 41 274 36 64 128 256), losses := [] }

theorem u3267 : Upper (D 5) (R 5) [6,72,160,33,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3268 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 164 41 274 40 85 149 277), lower := (rows 7 74 164 41 274 40 64 128 256), losses := [] }

theorem u3268 : Upper (D 5) (R 5) [6,72,160,33,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3269 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 7 74 164 41 274 48 77 141 269), lower := (rows 7 74 164 41 274 48 64 128 256), losses := [] }

theorem u3269 : Upper (D 5) (R 5) [6,72,160,33,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3270 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 164 41 276 33 90 154 282), lower := (rows 7 74 164 41 276 33 64 128 256), losses := [] }

theorem u3270 : Upper (D 5) (R 5) [6,72,160,33,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3271 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 164 41 276 34 89 153 281), lower := (rows 7 74 164 41 276 34 64 128 256), losses := [] }

theorem u3271 : Upper (D 5) (R 5) [6,72,160,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3272 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 164 41 276 40 83 147 275), lower := (rows 7 74 164 41 276 40 64 128 256), losses := [] }

theorem u3272 : Upper (D 5) (R 5) [6,72,160,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3272
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3273 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 7 74 164 41 276 48 75 139 267), lower := (rows 7 74 164 41 276 48 64 128 256), losses := [] }

theorem u3273 : Upper (D 5) (R 5) [6,72,160,33,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3273
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3274 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 164 41 280 33 86 150 278), lower := (rows 7 74 164 41 280 33 64 128 256), losses := [] }

theorem u3274 : Upper (D 5) (R 5) [6,72,160,33,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3275 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 164 41 280 34 85 149 277), lower := (rows 7 74 164 41 280 34 64 128 256), losses := [] }

theorem u3275 : Upper (D 5) (R 5) [6,72,160,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3275
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3276 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 164 41 280 36 83 147 275), lower := (rows 7 74 164 41 280 36 64 128 256), losses := [] }

theorem u3276 : Upper (D 5) (R 5) [6,72,160,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3276
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3277 : PairBound 9 := { available := 7, camps := [], pairs := [(0,3)], upper := (rows 7 74 164 41 280 48 71 135 263), lower := (rows 7 74 164 41 280 48 64 128 256), losses := [{ target := 3, region := (rows 3 2 12 0 16 48 67 131 259), good := (rows 455 455 164 485 308 48 64 128 256) }] }

theorem u3277 : Upper (D 5) (R 5) [6,72,160,33,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3277
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3278 : Route 9 := (fun mask => (mask,id))

def c3278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3278 : Upper (D 5) (R 5) [6,72,160,34,257,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,257,1] 13 (by decide) (choices 1) [4,8,16] r3278 c3278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u941
  · exact u942
  · exact u943

def b3279 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 42 273 36 89 153 281), lower := (rows 7 74 164 42 273 36 64 128 256), losses := [] }

theorem u3279 : Upper (D 5) (R 5) [6,72,160,34,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3279
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3280 : PairBound 9 := { available := 21, camps := [{ cop := 6, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 164 42 273 40 85 149 277), lower := (rows 7 74 164 42 273 40 64 128 256), losses := [] }

theorem u3280 : Upper (D 5) (R 5) [6,72,160,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3281 : Route 9 := (fun mask => (mask,id))

def c3281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3281 : Upper (D 5) (R 5) [6,72,160,34,257,16] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,257,16] 13 (by decide) (choices 1) [1,4,8] r3281 c3281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u944
  · exact u945
  · exact u946

def r3282 : Route 9 := (fun mask => (mask,id))

def c3282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3282 : Upper (D 5) (R 5) [6,72,160,34,260,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,260,1] 13 (by decide) (choices 1) [1,8,16] r3282 c3282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u947
  · exact u948
  · exact u949

def b3283 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 164 42 276 40 81 145 273), lower := (rows 7 74 164 42 276 40 64 128 256), losses := [] }

theorem u3283 : Upper (D 5) (R 5) [6,72,160,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3283
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3284 : Route 9 := (fun mask => (mask,id))

def c3284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3284 : Upper (D 5) (R 5) [6,72,160,34,260,16] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,260,16] 13 (by decide) (choices 1) [1,8] r3284 c3284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u950
  · exact u951

def r3285 : Route 9 := (fun mask => (mask,id))

def c3285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3285 : Upper (D 5) (R 5) [6,72,160,34,264,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,264,1] 13 (by decide) (choices 1) [1,4,16] r3285 c3285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u952
  · exact u953
  · exact u954

def b3286 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 42 280 36 81 145 273), lower := (rows 7 74 164 42 280 36 64 128 256), losses := [] }

theorem u3286 : Upper (D 5) (R 5) [6,72,160,34,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3286
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3287 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 133, targets := 8 }], pairs := [(0,3)], upper := (rows 7 74 164 42 280 48 69 133 261), lower := (rows 7 74 164 42 280 48 64 128 256), losses := [] }

theorem u3287 : Upper (D 5) (R 5) [6,72,160,34,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3287
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3288 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 164 56 273 33 78 142 270), lower := (rows 7 74 164 56 273 33 64 128 256), losses := [] }

theorem u3288 : Upper (D 5) (R 5) [6,72,160,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3288
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3289 : PairBound 9 := { available := 13, camps := [], pairs := [(3,0),(3,2)], upper := (rows 7 74 164 56 273 34 77 141 269), lower := (rows 7 74 164 56 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 38 106 164 56 312 34 64 128 256) },{ target := 2, region := (rows 1 2 0 24 16 35 64 128 256), good := (rows 35 106 160 56 313 34 64 128 256) }] }

theorem u3289 : Upper (D 5) (R 5) [6,72,160,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3289
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3290 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 56 273 36 75 139 267), lower := (rows 7 74 164 56 273 36 64 128 256), losses := [] }

theorem u3290 : Upper (D 5) (R 5) [6,72,160,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3290
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3291 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 164 56 273 40 71 135 263), lower := (rows 7 74 164 56 273 40 64 128 256), losses := [] }

theorem u3291 : Upper (D 5) (R 5) [6,72,160,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3291
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3292 : Route 9 := (fun mask => (mask,id))

def c3292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3292 : Upper (D 5) (R 5) [6,72,160,48,258,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,258,1] 13 (by decide) (choices 1) [1,4,8] r3292 c3292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u955
  · exact u956
  · exact u957

def b3293 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 56 274 36 73 137 265), lower := (rows 7 74 164 56 274 36 64 128 256), losses := [] }

theorem u3293 : Upper (D 5) (R 5) [6,72,160,48,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3294 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 164 56 274 40 69 133 261), lower := (rows 7 74 164 56 274 40 64 128 256), losses := [] }

theorem u3294 : Upper (D 5) (R 5) [6,72,160,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3294
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3295 : Route 9 := (fun mask => (mask,id))

def c3295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3295 : Upper (D 5) (R 5) [6,72,160,48,260,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,260,1] 13 (by decide) (choices 1) [1,2,8] r3295 c3295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u958
  · exact u959
  · exact u960

def r3296 : Route 9 := (fun mask => (mask,id))

def c3296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3296 : Upper (D 5) (R 5) [6,72,160,48,260,2] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,260,2] 13 (by decide) (choices 1) [1,8] r3296 c3296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u961
  · exact u962

def b3297 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 164 56 276 40 67 131 259), lower := (rows 7 74 164 56 276 40 64 128 256), losses := [] }

theorem u3297 : Upper (D 5) (R 5) [6,72,160,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3298 : Route 9 := (fun mask => (mask,id))

def c3298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3298 : Upper (D 5) (R 5) [6,72,160,257,12,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,12,1] 13 (by decide) (choices 1) [2,16,32] r3298 c3298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u963
  · exact u964
  · exact u965

def r3299 : Route 9 := (fun mask => (mask,id))

def c3299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3299 : Upper (D 5) (R 5) [6,72,160,257,12,2] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,12,2] 13 (by decide) (choices 1) [1,16,32] r3299 c3299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u966
  · exact u967
  · exact u968

#print axioms u3299
end Delivery.IrregularNine14.P05
