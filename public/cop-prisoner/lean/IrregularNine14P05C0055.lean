import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0016

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3300 : Route 9 := (fun mask => (mask,id))

def c3300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3300 : Upper (D 5) (R 5) [6,72,160,257,12,16] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,12,16] 13 (by decide) (choices 1) [1,2,32] r3300 c3300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u969
  · exact u970
  · exact u971

def b3301 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 265 49 34 92 156 284), lower := (rows 7 74 164 265 49 34 64 128 256), losses := [] }

theorem u3301 : Upper (D 5) (R 5) [6,72,160,257,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3302 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 164 265 49 36 90 154 282), lower := (rows 7 74 164 265 49 36 64 128 256), losses := [] }

theorem u3302 : Upper (D 5) (R 5) [6,72,160,257,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3302
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3303 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 265 49 40 86 150 278), lower := (rows 7 74 164 265 49 40 64 128 256), losses := [] }

theorem u3303 : Upper (D 5) (R 5) [6,72,160,257,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3304 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 74 164 265 49 48 78 142 270), lower := (rows 7 74 164 265 49 48 64 128 256), losses := [] }

theorem u3304 : Upper (D 5) (R 5) [6,72,160,257,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3304
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3305 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 265 50 33 92 156 284), lower := (rows 7 74 164 265 50 33 64 128 256), losses := [] }

theorem u3305 : Upper (D 5) (R 5) [6,72,160,257,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3305
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3306 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 265 50 36 89 153 281), lower := (rows 7 74 164 265 50 36 64 128 256), losses := [] }

theorem u3306 : Upper (D 5) (R 5) [6,72,160,257,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3306
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3307 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 265 50 40 85 149 277), lower := (rows 7 74 164 265 50 40 64 128 256), losses := [] }

theorem u3307 : Upper (D 5) (R 5) [6,72,160,257,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3308 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 164 265 50 48 77 141 269), lower := (rows 7 74 164 265 50 48 64 128 256), losses := [] }

theorem u3308 : Upper (D 5) (R 5) [6,72,160,257,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3308
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3309 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 265 56 33 86 150 278), lower := (rows 7 74 164 265 56 33 64 128 256), losses := [] }

theorem u3309 : Upper (D 5) (R 5) [6,72,160,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3310 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 265 56 34 85 149 277), lower := (rows 7 74 164 265 56 34 64 128 256), losses := [] }

theorem u3310 : Upper (D 5) (R 5) [6,72,160,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3310
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3311 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 265 56 36 83 147 275), lower := (rows 7 74 164 265 56 36 64 128 256), losses := [] }

theorem u3311 : Upper (D 5) (R 5) [6,72,160,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3312 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5)], upper := (rows 7 74 164 265 56 48 71 135 263), lower := (rows 7 74 164 265 56 48 64 128 256), losses := [] }

theorem u3312 : Upper (D 5) (R 5) [6,72,160,257,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3312
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3313 : Route 9 := (fun mask => (mask,id))

def c3313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3313 : Upper (D 5) (R 5) [6,72,160,258,12,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,258,12,1] 13 (by decide) (choices 1) [1,16,32] r3313 c3313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u972
  · exact u973
  · exact u974

def r3314 : Route 9 := (fun mask => (mask,id))

def c3314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3314 : Upper (D 5) (R 5) [6,72,160,258,12,16] 13 := by
  apply FastRouting.sound _ _ [6,72,160,258,12,16] 13 (by decide) (choices 1) [1,32] r3314 c3314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u975
  · exact u976

def b3315 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 266 49 33 92 156 284), lower := (rows 7 74 164 266 49 33 64 128 256), losses := [] }

theorem u3315 : Upper (D 5) (R 5) [6,72,160,258,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 164 266 49 36 89 153 281), lower := (rows 7 74 164 266 49 36 64 128 256), losses := [] }

theorem u3316 : Upper (D 5) (R 5) [6,72,160,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3316
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3317 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 132, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 266 49 40 85 149 277), lower := (rows 7 74 164 266 49 40 64 128 256), losses := [] }

theorem u3317 : Upper (D 5) (R 5) [6,72,160,258,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3318 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 74 164 266 49 48 77 141 269), lower := (rows 7 74 164 266 49 48 64 128 256), losses := [] }

theorem u3318 : Upper (D 5) (R 5) [6,72,160,258,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3318
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3319 : Route 9 := (fun mask => (mask,id))

def c3319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3319 : Upper (D 5) (R 5) [6,72,160,258,40,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,258,40,1] 13 (by decide) (choices 1) [1,4,16] r3319 c3319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u977
  · exact u978
  · exact u979

def b3320 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 266 56 36 81 145 273), lower := (rows 7 74 164 266 56 36 64 128 256), losses := [] }

theorem u3320 : Upper (D 5) (R 5) [6,72,160,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3320
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3321 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5)], upper := (rows 7 74 164 266 56 48 69 133 261), lower := (rows 7 74 164 266 56 48 64 128 256), losses := [] }

theorem u3321 : Upper (D 5) (R 5) [6,72,160,258,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3322 : Route 9 := (fun mask => (mask,id))

def c3322 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3322 : Upper (D 5) (R 5) [6,72,160,260,9,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,260,9,1] 13 (by decide) (choices 1) [2,16,32] r3322 c3322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u980
  · exact u981
  · exact u982

def b3323 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,3)], upper := (rows 7 74 164 268 25 34 113 177 305), lower := (rows 7 74 164 268 25 34 64 128 256), losses := [{ target := 3, region := (rows 1 2 20 0 16 35 80 144 272), good := (rows 39 98 164 260 501 34 64 128 256) }] }

theorem u3323 : Upper (D 5) (R 5) [6,72,160,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3323
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3324 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2)], upper := (rows 7 74 164 268 25 48 99 163 291), lower := (rows 7 74 164 268 25 48 64 128 256), losses := [] }

theorem u3324 : Upper (D 5) (R 5) [6,72,160,260,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3324
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3325 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 268 49 33 90 154 282), lower := (rows 7 74 164 268 49 33 64 128 256), losses := [] }

theorem u3325 : Upper (D 5) (R 5) [6,72,160,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3325
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3326 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 268 49 34 89 153 281), lower := (rows 7 74 164 268 49 34 64 128 256), losses := [] }

theorem u3326 : Upper (D 5) (R 5) [6,72,160,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3326
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3327 : PairBound 9 := { available := 19, camps := [], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 268 49 40 83 147 275), lower := (rows 7 74 164 268 49 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 42 64 128 256), good := (rows 53 104 164 300 49 40 64 128 256) },{ target := 2, region := (rows 1 2 0 8 17 42 65 129 257), good := (rows 499 106 160 296 497 40 64 128 256) }] }

theorem u3327 : Upper (D 5) (R 5) [6,72,160,260,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3328 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 74 164 268 49 48 75 139 267), lower := (rows 7 74 164 268 49 48 64 128 256), losses := [] }

theorem u3328 : Upper (D 5) (R 5) [6,72,160,260,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3328
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3329 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 268 50 33 89 153 281), lower := (rows 7 74 164 268 50 33 64 128 256), losses := [] }

theorem u3329 : Upper (D 5) (R 5) [6,72,160,260,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3330 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 268 50 40 81 145 273), lower := (rows 7 74 164 268 50 40 64 128 256), losses := [] }

theorem u3330 : Upper (D 5) (R 5) [6,72,160,260,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3330
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3331 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 164 268 50 48 73 137 265), lower := (rows 7 74 164 268 50 48 64 128 256), losses := [] }

theorem u3331 : Upper (D 5) (R 5) [6,72,160,260,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3331
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3332 : Route 9 := (fun mask => (mask,id))

def c3332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3332 : Upper (D 5) (R 5) [6,72,160,260,40,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,260,40,1] 13 (by decide) (choices 1) [1,2,16] r3332 c3332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u983
  · exact u984
  · exact u985

def b3333 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 268 56 34 81 145 273), lower := (rows 7 74 164 268 56 34 64 128 256), losses := [] }

theorem u3333 : Upper (D 5) (R 5) [6,72,160,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3333
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3334 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5)], upper := (rows 7 74 164 268 56 48 67 131 259), lower := (rows 7 74 164 268 56 48 64 128 256), losses := [] }

theorem u3334 : Upper (D 5) (R 5) [6,72,160,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3334
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3335 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 280 49 33 78 142 270), lower := (rows 7 74 164 280 49 33 64 128 256), losses := [] }

theorem u3335 : Upper (D 5) (R 5) [6,72,160,272,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3335
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3336 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 280 49 34 77 141 269), lower := (rows 7 74 164 280 49 34 64 128 256), losses := [] }

theorem u3336 : Upper (D 5) (R 5) [6,72,160,272,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3336
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3337 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 164 280 49 36 75 139 267), lower := (rows 7 74 164 280 49 36 64 128 256), losses := [] }

theorem u3337 : Upper (D 5) (R 5) [6,72,160,272,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3337
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3338 : PairBound 9 := { available := 7, camps := [], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 280 49 40 71 135 263), lower := (rows 7 74 164 280 49 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 42 64 128 256), good := (rows 53 104 164 312 49 40 64 128 256) },{ target := 2, region := (rows 1 2 0 8 17 42 64 128 256), good := (rows 51 106 160 312 49 40 64 128 256) }] }

theorem u3338 : Upper (D 5) (R 5) [6,72,160,272,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3338
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3339 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 280 50 33 77 141 269), lower := (rows 7 74 164 280 50 33 64 128 256), losses := [] }

theorem u3339 : Upper (D 5) (R 5) [6,72,160,272,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3339
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3340 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 280 50 36 73 137 265), lower := (rows 7 74 164 280 50 36 64 128 256), losses := [] }

theorem u3340 : Upper (D 5) (R 5) [6,72,160,272,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3340
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3341 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 280 50 40 69 133 261), lower := (rows 7 74 164 280 50 40 64 128 256), losses := [] }

theorem u3341 : Upper (D 5) (R 5) [6,72,160,272,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3341
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3342 : Route 9 := (fun mask => (mask,id))

def c3342 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3342 : Upper (D 5) (R 5) [6,72,160,288,9,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,9,1] 13 (by decide) (choices 1) [2,4,16] r3342 c3342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u986
  · exact u987
  · exact u988

def r3343 : Route 9 := (fun mask => (mask,id))

def c3343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3343 : Upper (D 5) (R 5) [6,72,160,288,9,2] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,9,2] 13 (by decide) (choices 1) [1,4,16] r3343 c3343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u989
  · exact u990
  · exact u991

def b3344 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 296 25 36 83 147 275), lower := (rows 7 74 164 296 25 36 64 128 256), losses := [] }

theorem u3344 : Upper (D 5) (R 5) [6,72,160,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3344
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3345 : PairBound 9 := { available := 7, camps := [], pairs := [(2,3)], upper := (rows 7 74 164 296 25 48 71 135 263), lower := (rows 7 74 164 296 25 48 64 128 256), losses := [{ target := 3, region := (rows 1 2 20 0 16 48 65 129 257), good := (rows 455 66 164 288 501 52 64 128 256) }] }

theorem u3345 : Upper (D 5) (R 5) [6,72,160,288,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3345
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3346 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 388 25 50 33 108 172 300), lower := (rows 7 74 388 25 50 33 64 128 256), losses := [] }

theorem u3346 : Upper (D 5) (R 5) [6,72,384,17,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3346
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3347 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 388 25 50 36 105 169 297), lower := (rows 7 74 388 25 50 36 64 128 256), losses := [] }

theorem u3347 : Upper (D 5) (R 5) [6,72,384,17,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3347
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3348 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 388 25 50 40 101 165 293), lower := (rows 7 74 388 25 50 40 64 128 256), losses := [] }

theorem u3348 : Upper (D 5) (R 5) [6,72,384,17,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3348
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3349 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 74 388 25 52 33 106 170 298), lower := (rows 7 74 388 25 52 33 64 128 256), losses := [] }

theorem u3349 : Upper (D 5) (R 5) [6,72,384,17,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3349
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3350 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 388 25 52 34 105 169 297), lower := (rows 7 74 388 25 52 34 64 128 256), losses := [] }

theorem u3350 : Upper (D 5) (R 5) [6,72,384,17,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3350
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3351 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 74 388 25 52 40 99 163 291), lower := (rows 7 74 388 25 52 40 64 128 256), losses := [] }

theorem u3351 : Upper (D 5) (R 5) [6,72,384,17,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3352 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 388 26 49 33 108 172 300), lower := (rows 7 74 388 26 49 33 64 128 256), losses := [] }

theorem u3352 : Upper (D 5) (R 5) [6,72,384,18,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3352
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3353 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 388 26 49 36 105 169 297), lower := (rows 7 74 388 26 49 36 64 128 256), losses := [] }

theorem u3353 : Upper (D 5) (R 5) [6,72,384,18,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3353
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3354 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 388 26 49 40 101 165 293), lower := (rows 7 74 388 26 49 40 64 128 256), losses := [] }

theorem u3354 : Upper (D 5) (R 5) [6,72,384,18,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3354
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3355 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 388 26 52 33 105 169 297), lower := (rows 7 74 388 26 52 33 64 128 256), losses := [] }

theorem u3355 : Upper (D 5) (R 5) [6,72,384,18,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3355
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3356 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 74 388 26 52 40 97 161 289), lower := (rows 7 74 388 26 52 40 64 128 256), losses := [] }

theorem u3356 : Upper (D 5) (R 5) [6,72,384,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3357 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 388 28 49 33 106 170 298), lower := (rows 7 74 388 28 49 33 64 128 256), losses := [] }

theorem u3357 : Upper (D 5) (R 5) [6,72,384,20,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3357
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3358 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 388 28 49 34 105 169 297), lower := (rows 7 74 388 28 49 34 64 128 256), losses := [] }

theorem u3358 : Upper (D 5) (R 5) [6,72,384,20,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3358
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3359 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 74 388 28 49 40 99 163 291), lower := (rows 7 74 388 28 49 40 64 128 256), losses := [] }

theorem u3359 : Upper (D 5) (R 5) [6,72,384,20,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3359
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3359
end Delivery.IrregularNine14.P05
