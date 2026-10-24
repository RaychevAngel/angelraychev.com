import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0014
import IrregularNine14P05C0015

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3180 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 148 41 304 40 71 135 263), lower := (rows 7 74 148 41 304 40 64 128 256), losses := [] }

theorem u3180 : Upper (D 5) (R 5) [6,72,144,33,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3180
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3181 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 148 42 49 33 332 396 268), lower := (rows 7 74 148 42 49 33 64 128 256), losses := [] }

theorem u3181 : Upper (D 5) (R 5) [6,72,144,34,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3181
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3182 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 42 49 36 329 393 265), lower := (rows 7 74 148 42 49 36 64 128 256), losses := [] }

theorem u3182 : Upper (D 5) (R 5) [6,72,144,34,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3182
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3183 : PairBound 9 := { available := 261, camps := [{ cop := 6, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 42 49 40 325 389 261), lower := (rows 7 74 148 42 49 40 64 128 256), losses := [] }

theorem u3183 : Upper (D 5) (R 5) [6,72,144,34,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3183
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3184 : Route 9 := (fun mask => (mask,id))

def c3184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3184 : Upper (D 5) (R 5) [6,72,144,34,33,256] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,33,256] 13 (by decide) (choices 1) [1,4,8] r3184 c3184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u846
  · exact u847
  · exact u848

def r3185 : Route 9 := (fun mask => (mask,id))

def c3185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3185 : Upper (D 5) (R 5) [6,72,144,34,257,1] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,257,1] 13 (by decide) (choices 1) [4,8,32] r3185 c3185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u849
  · exact u850
  · exact u851

def r3186 : Route 9 := (fun mask => (mask,id))

def c3186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3186 : Upper (D 5) (R 5) [6,72,144,34,257,4] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,257,4] 13 (by decide) (choices 1) [1,8,32] r3186 c3186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u852
  · exact u853
  · exact u854

def b3187 : PairBound 9 := { available := 37, camps := [{ cop := 6, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 42 273 40 101 165 293), lower := (rows 7 74 148 42 273 40 64 128 256), losses := [] }

theorem u3187 : Upper (D 5) (R 5) [6,72,144,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3187
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3188 : Route 9 := (fun mask => (mask,id))

def c3188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3188 : Upper (D 5) (R 5) [6,72,144,34,264,1] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,264,1] 13 (by decide) (choices 1) [1,4,32] r3188 c3188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u855
  · exact u856
  · exact u857

def r3189 : Route 9 := (fun mask => (mask,id))

def c3189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3189 : Upper (D 5) (R 5) [6,72,144,34,264,4] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,264,4] 13 (by decide) (choices 1) [1,32] r3189 c3189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u858
  · exact u859

def r3190 : Route 9 := (fun mask => (mask,id))

def c3190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3190 : Upper (D 5) (R 5) [6,72,144,34,288,1] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,288,1] 13 (by decide) (choices 1) [1,4,8] r3190 c3190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u860
  · exact u861
  · exact u862

def r3191 : Route 9 := (fun mask => (mask,id))

def c3191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3191 : Upper (D 5) (R 5) [6,72,144,34,288,4] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,288,4] 13 (by decide) (choices 1) [1,8] r3191 c3191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u863
  · exact u864

def b3192 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 42 304 40 69 133 261), lower := (rows 7 74 148 42 304 40 64 128 256), losses := [] }

theorem u3192 : Upper (D 5) (R 5) [6,72,144,34,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3192
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3193 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 44 273 33 106 170 298), lower := (rows 7 74 148 44 273 33 64 128 256), losses := [] }

theorem u3193 : Upper (D 5) (R 5) [6,72,144,36,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3193
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3194 : Route 9 := (fun mask => (mask,id))

def c3194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3194 : Upper (D 5) (R 5) [6,72,144,36,257,2] 13 := by
  apply FastRouting.sound _ _ [6,72,144,36,257,2] 13 (by decide) (choices 1) [1,8,32] r3194 c3194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u865
  · exact u866
  · exact u867

def b3195 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 148 44 273 40 99 163 291), lower := (rows 7 74 148 44 273 40 64 128 256), losses := [] }

theorem u3195 : Upper (D 5) (R 5) [6,72,144,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3195
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3196 : Route 9 := (fun mask => (mask,id))

def c3196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3196 : Upper (D 5) (R 5) [6,72,144,36,258,1] 13 := by
  apply FastRouting.sound _ _ [6,72,144,36,258,1] 13 (by decide) (choices 1) [1,8,32] r3196 c3196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u868
  · exact u869
  · exact u870

def b3197 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 148 44 274 40 97 161 289), lower := (rows 7 74 148 44 274 40 64 128 256), losses := [] }

theorem u3197 : Upper (D 5) (R 5) [6,72,144,36,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3198 : Route 9 := (fun mask => (mask,id))

def c3198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3198 : Upper (D 5) (R 5) [6,72,144,36,264,1] 13 := by
  apply FastRouting.sound _ _ [6,72,144,36,264,1] 13 (by decide) (choices 1) [1,2,32] r3198 c3198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u871
  · exact u872
  · exact u873

def r3199 : Route 9 := (fun mask => (mask,id))

def c3199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3199 : Upper (D 5) (R 5) [6,72,144,36,264,2] 13 := by
  apply FastRouting.sound _ _ [6,72,144,36,264,2] 13 (by decide) (choices 1) [1,32] r3199 c3199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u874
  · exact u875

def b3200 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 265 49 34 108 172 300), lower := (rows 7 74 148 265 49 34 64 128 256), losses := [] }

theorem u3200 : Upper (D 5) (R 5) [6,72,144,257,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3200
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3201 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 265 49 36 106 170 298), lower := (rows 7 74 148 265 49 36 64 128 256), losses := [] }

theorem u3201 : Upper (D 5) (R 5) [6,72,144,257,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3202 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 265 49 40 102 166 294), lower := (rows 7 74 148 265 49 40 64 128 256), losses := [] }

theorem u3202 : Upper (D 5) (R 5) [6,72,144,257,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3203 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 265 50 33 108 172 300), lower := (rows 7 74 148 265 50 33 64 128 256), losses := [] }

theorem u3203 : Upper (D 5) (R 5) [6,72,144,257,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3204 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1),(4,0)], upper := (rows 7 74 148 265 50 36 105 169 297), lower := (rows 7 74 148 265 50 36 64 128 256), losses := [] }

theorem u3204 : Upper (D 5) (R 5) [6,72,144,257,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3205 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 265 50 40 101 165 293), lower := (rows 7 74 148 265 50 40 64 128 256), losses := [] }

theorem u3205 : Upper (D 5) (R 5) [6,72,144,257,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3205
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3206 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 265 56 33 102 166 294), lower := (rows 7 74 148 265 56 33 64 128 256), losses := [] }

theorem u3206 : Upper (D 5) (R 5) [6,72,144,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3206
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3207 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 265 56 34 101 165 293), lower := (rows 7 74 148 265 56 34 64 128 256), losses := [] }

theorem u3207 : Upper (D 5) (R 5) [6,72,144,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3207
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3208 : PairBound 9 := { available := 35, camps := [], pairs := [(4,0),(4,1)], upper := (rows 7 74 148 265 56 36 99 163 291), lower := (rows 7 74 148 265 56 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 37 64 128 256), good := (rows 38 90 180 312 56 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 24 37 64 128 256), good := (rows 37 88 180 313 56 36 64 128 256) }] }

theorem u3208 : Upper (D 5) (R 5) [6,72,144,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3208
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3209 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 266 49 33 108 172 300), lower := (rows 7 74 148 266 49 33 64 128 256), losses := [] }

theorem u3209 : Upper (D 5) (R 5) [6,72,144,258,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3209
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3210 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 266 49 36 105 169 297), lower := (rows 7 74 148 266 49 36 64 128 256), losses := [] }

theorem u3210 : Upper (D 5) (R 5) [6,72,144,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3211 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 132, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 148 266 49 40 101 165 293), lower := (rows 7 74 148 266 49 40 64 128 256), losses := [] }

theorem u3211 : Upper (D 5) (R 5) [6,72,144,258,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3211
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3212 : Route 9 := (fun mask => (mask,id))

def c3212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3212 : Upper (D 5) (R 5) [6,72,144,258,40,1] 13 := by
  apply FastRouting.sound _ _ [6,72,144,258,40,1] 13 (by decide) (choices 1) [1,4,32] r3212 c3212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u876
  · exact u877
  · exact u878

def r3213 : Route 9 := (fun mask => (mask,id))

def c3213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3213 : Upper (D 5) (R 5) [6,72,144,258,40,4] 13 := by
  apply FastRouting.sound _ _ [6,72,144,258,40,4] 13 (by decide) (choices 1) [1,32] r3213 c3213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u879
  · exact u880

def b3214 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 268 49 33 106 170 298), lower := (rows 7 74 148 268 49 33 64 128 256), losses := [] }

theorem u3214 : Upper (D 5) (R 5) [6,72,144,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3215 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 268 49 34 105 169 297), lower := (rows 7 74 148 268 49 34 64 128 256), losses := [] }

theorem u3215 : Upper (D 5) (R 5) [6,72,144,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3216 : PairBound 9 := { available := 35, camps := [], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 268 49 40 99 163 291), lower := (rows 7 74 148 268 49 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 42 64 128 256), good := (rows 53 104 148 300 49 40 64 128 256) },{ target := 2, region := (rows 1 2 0 8 17 42 65 129 257), good := (rows 499 106 144 296 497 40 64 128 256) }] }

theorem u3216 : Upper (D 5) (R 5) [6,72,144,260,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3216
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3217 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 268 50 33 105 169 297), lower := (rows 7 74 148 268 50 33 64 128 256), losses := [] }

theorem u3217 : Upper (D 5) (R 5) [6,72,144,260,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3217
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3218 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 268 50 40 97 161 289), lower := (rows 7 74 148 268 50 40 64 128 256), losses := [] }

theorem u3218 : Upper (D 5) (R 5) [6,72,144,260,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3219 : Route 9 := (fun mask => (mask,id))

def c3219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3219 : Upper (D 5) (R 5) [6,72,144,260,40,1] 13 := by
  apply FastRouting.sound _ _ [6,72,144,260,40,1] 13 (by decide) (choices 1) [1,2,32] r3219 c3219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u881
  · exact u882
  · exact u883

def b3220 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 268 56 34 97 161 289), lower := (rows 7 74 148 268 56 34 64 128 256), losses := [] }

theorem u3220 : Upper (D 5) (R 5) [6,72,144,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3220
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3221 : Route 9 := (fun mask => (mask,id))

def c3221 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3221 : Upper (D 5) (R 5) [6,72,144,288,9,1] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288,9,1] 13 (by decide) (choices 1) [2,4,32] r3221 c3221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u884
  · exact u885
  · exact u886

def r3222 : Route 9 := (fun mask => (mask,id))

def c3222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3222 : Upper (D 5) (R 5) [6,72,144,288,9,2] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288,9,2] 13 (by decide) (choices 1) [1,4,32] r3222 c3222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u887
  · exact u888
  · exact u889

def r3223 : Route 9 := (fun mask => (mask,id))

def c3223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3223 : Upper (D 5) (R 5) [6,72,144,288,9,4] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288,9,4] 13 (by decide) (choices 1) [1,2,32] r3223 c3223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u890
  · exact u891
  · exact u892

def b3224 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 296 49 33 78 142 270), lower := (rows 7 74 148 296 49 33 64 128 256), losses := [] }

theorem u3224 : Upper (D 5) (R 5) [6,72,144,288,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3224
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3225 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 296 49 34 77 141 269), lower := (rows 7 74 148 296 49 34 64 128 256), losses := [] }

theorem u3225 : Upper (D 5) (R 5) [6,72,144,288,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3225
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3226 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 296 49 36 75 139 267), lower := (rows 7 74 148 296 49 36 64 128 256), losses := [] }

theorem u3226 : Upper (D 5) (R 5) [6,72,144,288,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3226
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3227 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 148 296 49 40 71 135 263), lower := (rows 7 74 148 296 49 40 64 128 256), losses := [] }

theorem u3227 : Upper (D 5) (R 5) [6,72,144,288,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3228 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 296 50 33 77 141 269), lower := (rows 7 74 148 296 50 33 64 128 256), losses := [] }

theorem u3228 : Upper (D 5) (R 5) [6,72,144,288,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3228
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3229 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1),(4,0)], upper := (rows 7 74 148 296 50 36 73 137 265), lower := (rows 7 74 148 296 50 36 64 128 256), losses := [] }

theorem u3229 : Upper (D 5) (R 5) [6,72,144,288,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3229
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3230 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 133, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 74 148 296 50 40 69 133 261), lower := (rows 7 74 148 296 50 40 64 128 256), losses := [] }

theorem u3230 : Upper (D 5) (R 5) [6,72,144,288,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3231 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 25 50 33 332 396 268), lower := (rows 7 74 164 25 50 33 64 128 256), losses := [] }

theorem u3231 : Upper (D 5) (R 5) [6,72,160,17,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3231
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3232 : PairBound 9 := { available := 265, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 25 50 36 329 393 265), lower := (rows 7 74 164 25 50 36 64 128 256), losses := [] }

theorem u3232 : Upper (D 5) (R 5) [6,72,160,17,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3232
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3233 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 25 50 40 325 389 261), lower := (rows 7 74 164 25 50 40 64 128 256), losses := [] }

theorem u3233 : Upper (D 5) (R 5) [6,72,160,17,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3233
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3234 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 420, targets := 2 }], pairs := [(2,1)], upper := (rows 7 74 164 25 50 288 77 141 269), lower := (rows 7 74 164 25 50 288 64 128 256), losses := [] }

theorem u3234 : Upper (D 5) (R 5) [6,72,160,17,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3234
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3235 : Route 9 := (fun mask => (mask,id))

def c3235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3235 : Upper (D 5) (R 5) [6,72,160,17,258,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,258,1] 13 (by decide) (choices 1) [4,8,32] r3235 c3235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u893
  · exact u894
  · exact u895

def b3236 : PairBound 9 := { available := 41, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 25 274 36 105 169 297), lower := (rows 7 74 164 25 274 36 64 128 256), losses := [] }

theorem u3236 : Upper (D 5) (R 5) [6,72,160,17,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3236
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3237 : Route 9 := (fun mask => (mask,id))

def c3237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3237 : Upper (D 5) (R 5) [6,72,160,17,258,8] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,258,8] 13 (by decide) (choices 1) [1,4,32] r3237 c3237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u896
  · exact u897
  · exact u898

def r3238 : Route 9 := (fun mask => (mask,id))

def c3238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3238 : Upper (D 5) (R 5) [6,72,160,17,260,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,260,1] 13 (by decide) (choices 1) [2,8,32] r3238 c3238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u899
  · exact u900
  · exact u901

def r3239 : Route 9 := (fun mask => (mask,id))

def c3239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3239 : Upper (D 5) (R 5) [6,72,160,17,260,2] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,260,2] 13 (by decide) (choices 1) [1,8,32] r3239 c3239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u902
  · exact u903
  · exact u904

#print axioms u3239
end Delivery.IrregularNine14.P05
