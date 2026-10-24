import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0061
import IrregularNine14P05C0062

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7260 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 265 19 44 108 172 300), lower := (rows 19 38 196 265 19 32 64 128 256), losses := [] }

theorem u7260 : Upper (D 5) (R 5) [18,36,192,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7260
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7261 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 196 265 21 42 106 170 298), lower := (rows 19 38 196 265 21 32 64 128 256), losses := [] }

theorem u7261 : Upper (D 5) (R 5) [18,36,192,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7262 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 196 265 22 41 105 169 297), lower := (rows 19 38 196 265 22 32 64 128 256), losses := [] }

theorem u7262 : Upper (D 5) (R 5) [18,36,192,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7262
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7263 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 38 196 265 25 46 110 174 302), lower := (rows 19 38 196 265 25 32 64 128 256), losses := [] }

theorem u7263 : Upper (D 5) (R 5) [18,36,192,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7263
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7264 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 265 26 45 109 173 301), lower := (rows 19 38 196 265 26 32 64 128 256), losses := [] }

theorem u7264 : Upper (D 5) (R 5) [18,36,192,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7265 : Route 9 := (fun mask => (mask,id))

def c7265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7265 : Upper (D 5) (R 5) [18,36,192,257,12] 13 := by
  apply FastRouting.sound _ _ [18,36,192,257,12] 13 (by decide) (choices 1) [1,2,8] r7265 c7265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3708
  · exact u3709
  · exact u3710

def b7266 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 265 49 46 78 142 270), lower := (rows 19 38 196 265 49 32 64 128 256), losses := [] }

theorem u7266 : Upper (D 5) (R 5) [18,36,192,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7266
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7267 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 265 50 45 77 141 269), lower := (rows 19 38 196 265 50 32 64 128 256), losses := [] }

theorem u7267 : Upper (D 5) (R 5) [18,36,192,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7268 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 196 265 52 43 75 139 267), lower := (rows 19 38 196 265 52 32 64 128 256), losses := [] }

theorem u7268 : Upper (D 5) (R 5) [18,36,192,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7269 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 196 265 56 47 79 143 271), lower := (rows 19 38 196 265 56 32 64 128 256), losses := [] }

theorem u7269 : Upper (D 5) (R 5) [18,36,192,257,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7270 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 196 266 21 41 105 169 297), lower := (rows 19 38 196 266 21 32 64 128 256), losses := [] }

theorem u7270 : Upper (D 5) (R 5) [18,36,192,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7271 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 38 196 266 25 45 109 173 301), lower := (rows 19 38 196 266 25 32 64 128 256), losses := [] }

theorem u7271 : Upper (D 5) (R 5) [18,36,192,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7272 : Route 9 := (fun mask => (mask,id))

def c7272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7272 : Upper (D 5) (R 5) [18,36,192,258,12] 13 := by
  apply FastRouting.sound _ _ [18,36,192,258,12] 13 (by decide) (choices 1) [1,8] r7272 c7272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3711
  · exact u3712

def b7273 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 266 49 45 77 141 269), lower := (rows 19 38 196 266 49 32 64 128 256), losses := [] }

theorem u7273 : Upper (D 5) (R 5) [18,36,192,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7273
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7274 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 196 266 52 41 73 137 265), lower := (rows 19 38 196 266 52 32 64 128 256), losses := [] }

theorem u7274 : Upper (D 5) (R 5) [18,36,192,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7275 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 196 266 56 45 77 141 269), lower := (rows 19 38 196 266 56 32 64 128 256), losses := [] }

theorem u7275 : Upper (D 5) (R 5) [18,36,192,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7275
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7276 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 268 19 41 105 169 297), lower := (rows 19 38 196 268 19 32 64 128 256), losses := [] }

theorem u7276 : Upper (D 5) (R 5) [18,36,192,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7276
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7277 : Route 9 := (fun mask => (mask,id))

def c7277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7277 : Upper (D 5) (R 5) [18,36,192,260,9] 13 := by
  apply FastRouting.sound _ _ [18,36,192,260,9] 13 (by decide) (choices 1) [1,2,8] r7277 c7277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3713
  · exact u3714
  · exact u3715

def b7278 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 38 196 268 26 41 105 169 297), lower := (rows 19 38 196 268 26 32 64 128 256), losses := [] }

theorem u7278 : Upper (D 5) (R 5) [18,36,192,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7278
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7279 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 268 49 43 75 139 267), lower := (rows 19 38 196 268 49 32 64 128 256), losses := [] }

theorem u7279 : Upper (D 5) (R 5) [18,36,192,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7279
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7280 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 268 50 41 73 137 265), lower := (rows 19 38 196 268 50 32 64 128 256), losses := [] }

theorem u7280 : Upper (D 5) (R 5) [18,36,192,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7281 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 196 268 56 43 75 139 267), lower := (rows 19 38 196 268 56 32 64 128 256), losses := [] }

theorem u7281 : Upper (D 5) (R 5) [18,36,192,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7281
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7282 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 296 19 45 77 141 269), lower := (rows 19 38 196 296 19 32 64 128 256), losses := [] }

theorem u7282 : Upper (D 5) (R 5) [18,36,192,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7282
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7283 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 196 296 21 43 75 139 267), lower := (rows 19 38 196 296 21 32 64 128 256), losses := [] }

theorem u7283 : Upper (D 5) (R 5) [18,36,192,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7283
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7284 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 196 296 22 41 73 137 265), lower := (rows 19 38 196 296 22 32 64 128 256), losses := [] }

theorem u7284 : Upper (D 5) (R 5) [18,36,192,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7284
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7285 : Route 9 := (fun mask => (mask,id))

def c7285 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7285 : Upper (D 5) (R 5) [18,36,192,288,9] 13 := by
  apply FastRouting.sound _ _ [18,36,192,288,9] 13 (by decide) (choices 1) [1,2,4,8] r7285 c7285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3716
  · exact u3717
  · exact u3718
  · exact u3719

def b7286 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 38 196 296 26 45 77 141 269), lower := (rows 19 38 196 296 26 32 64 128 256), losses := [] }

theorem u7286 : Upper (D 5) (R 5) [18,36,192,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7286
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7287 : Route 9 := (fun mask => (mask,id))

def c7287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7287 : Upper (D 5) (R 5) [18,36,192,288,12] 13 := by
  apply FastRouting.sound _ _ [18,36,192,288,12] 13 (by decide) (choices 1) [1,2,8] r7287 c7287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3720
  · exact u3721
  · exact u3722

def b7288 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 451, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 37 42 28 428 460 396 396), lower := (rows 19 67 37 42 28 32 64 128 256), losses := [] }

theorem u7288 : Upper (D 5) (R 5) [18,65,33,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7288
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7289 : Route 9 := (fun mask => (mask,id))

def c7289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7289 : Upper (D 5) (R 5) [18,65,33,34,132] 13 := by
  apply FastRouting.sound _ _ [18,65,33,34,132] 13 (by decide) (choices 1) [4,8,256] r7289 c7289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3723
  · exact u3724
  · exact u3725

def r7290 : Route 9 := (fun mask => (mask,id))

def c7290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7290 : Upper (D 5) (R 5) [18,65,33,34,136] 13 := by
  apply FastRouting.sound _ _ [18,65,33,34,136] 13 (by decide) (choices 1) [4,8,256] r7290 c7290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3726
  · exact u3727
  · exact u3728

def r7291 : Route 9 := (fun mask => (mask,id))

def c7291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7291 : Upper (D 5) (R 5) [18,65,33,34,384] 13 := by
  apply FastRouting.sound _ _ [18,65,33,34,384] 13 (by decide) (choices 1) [4,8] r7291 c7291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3729
  · exact u3730

def b7292 : PairBound 9 := { available := 300, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 67 37 138 28 300 364 428 300), lower := (rows 19 67 37 138 28 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 52 84 148 276), good := (rows 506 74 508 138 508 32 64 128 256) }] }

theorem u7292 : Upper (D 5) (R 5) [18,65,33,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7292
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7293 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 37 138 52 300 332 396 268), lower := (rows 19 67 37 138 52 32 64 128 256), losses := [] }

theorem u7293 : Upper (D 5) (R 5) [18,65,33,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7294 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 67 37 138 56 300 332 396 268), lower := (rows 19 67 37 138 56 32 64 128 256), losses := [] }

theorem u7294 : Upper (D 5) (R 5) [18,65,33,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7294
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7295 : Route 9 := (fun mask => (mask,id))

def c7295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7295 : Upper (D 5) (R 5) [18,65,33,130,260] 13 := by
  apply FastRouting.sound _ _ [18,65,33,130,260] 13 (by decide) (choices 1) [4,8] r7295 c7295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3731
  · exact u3732

def r7296 : Route 9 := (fun mask => (mask,id))

def c7296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7296 : Upper (D 5) (R 5) [18,65,33,130,264] 13 := by
  apply FastRouting.sound _ _ [18,65,33,130,264] 13 (by decide) (choices 1) [4,8] r7296 c7296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3733
  · exact u3734

def b7297 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 67 37 138 304 44 76 140 268), lower := (rows 19 67 37 138 304 32 64 128 256), losses := [] }

theorem u7297 : Upper (D 5) (R 5) [18,65,33,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7298 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 140 22 296 360 424 296), lower := (rows 19 67 37 140 22 32 64 128 256), losses := [] }

theorem u7298 : Upper (D 5) (R 5) [18,65,33,132,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7298
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7299 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 140 26 300 364 428 300), lower := (rows 19 67 37 140 26 32 64 128 256), losses := [] }

theorem u7299 : Upper (D 5) (R 5) [18,65,33,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7299
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7300 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 37 140 28 298 362 426 298), lower := (rows 19 67 37 140 28 32 64 128 256), losses := [] }

theorem u7300 : Upper (D 5) (R 5) [18,65,33,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7300
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7301 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 67 37 140 50 300 332 396 268), lower := (rows 19 67 37 140 50 32 64 128 256), losses := [] }

theorem u7301 : Upper (D 5) (R 5) [18,65,33,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7302 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 37 140 52 298 330 394 266), lower := (rows 19 67 37 140 52 32 64 128 256), losses := [] }

theorem u7302 : Upper (D 5) (R 5) [18,65,33,132,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7302
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7303 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 67 37 140 56 302 334 398 270), lower := (rows 19 67 37 140 56 32 64 128 256), losses := [] }

theorem u7303 : Upper (D 5) (R 5) [18,65,33,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7304 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 140 274 44 108 172 300), lower := (rows 19 67 37 140 274 32 64 128 256), losses := [] }

theorem u7304 : Upper (D 5) (R 5) [18,65,33,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7304
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7305 : Route 9 := (fun mask => (mask,id))

def c7305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7305 : Upper (D 5) (R 5) [18,65,33,132,260] 13 := by
  apply FastRouting.sound _ _ [18,65,33,132,260] 13 (by decide) (choices 1) [2,8] r7305 c7305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3735
  · exact u3736

def r7306 : Route 9 := (fun mask => (mask,id))

def c7306 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7306 : Upper (D 5) (R 5) [18,65,33,132,264] 13 := by
  apply FastRouting.sound _ _ [18,65,33,132,264] 13 (by decide) (choices 1) [2,4,8] r7306 c7306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3737
  · exact u3738
  · exact u3739

def b7307 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 67 37 140 304 46 78 142 270), lower := (rows 19 67 37 140 304 32 64 128 256), losses := [] }

theorem u7307 : Upper (D 5) (R 5) [18,65,33,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7308 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 168 22 300 332 396 268), lower := (rows 19 67 37 168 22 32 64 128 256), losses := [] }

theorem u7308 : Upper (D 5) (R 5) [18,65,33,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7308
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7309 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 168 26 300 332 396 268), lower := (rows 19 67 37 168 26 32 64 128 256), losses := [] }

theorem u7309 : Upper (D 5) (R 5) [18,65,33,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7310 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 37 168 28 302 334 398 270), lower := (rows 19 67 37 168 28 32 64 128 256), losses := [] }

theorem u7310 : Upper (D 5) (R 5) [18,65,33,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7310
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7311 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 168 274 44 76 140 268), lower := (rows 19 67 37 168 274 32 64 128 256), losses := [] }

theorem u7311 : Upper (D 5) (R 5) [18,65,33,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7312 : Route 9 := (fun mask => (mask,id))

def c7312 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7312 : Upper (D 5) (R 5) [18,65,33,160,260] 13 := by
  apply FastRouting.sound _ _ [18,65,33,160,260] 13 (by decide) (choices 1) [2,4,8] r7312 c7312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3740
  · exact u3741
  · exact u3742

def r7313 : Route 9 := (fun mask => (mask,id))

def c7313 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7313 : Upper (D 5) (R 5) [18,65,33,160,264] 13 := by
  apply FastRouting.sound _ _ [18,65,33,160,264] 13 (by decide) (choices 1) [2,4,8] r7313 c7313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3743
  · exact u3744
  · exact u3745

def b7314 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 392 22 44 108 172 300), lower := (rows 19 67 37 392 22 32 64 128 256), losses := [] }

theorem u7314 : Upper (D 5) (R 5) [18,65,33,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7315 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 392 26 44 108 172 300), lower := (rows 19 67 37 392 26 32 64 128 256), losses := [] }

theorem u7315 : Upper (D 5) (R 5) [18,65,33,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7316 : Route 9 := (fun mask => (mask,id))

def c7316 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7316 : Upper (D 5) (R 5) [18,65,33,384,12] 13 := by
  apply FastRouting.sound _ _ [18,65,33,384,12] 13 (by decide) (choices 1) [2,4,8] r7316 c7316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3746
  · exact u3747
  · exact u3748

def b7317 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 67 37 392 50 44 76 140 268), lower := (rows 19 67 37 392 50 32 64 128 256), losses := [] }

theorem u7317 : Upper (D 5) (R 5) [18,65,33,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7318 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 37 392 52 46 78 142 270), lower := (rows 19 67 37 392 52 32 64 128 256), losses := [] }

theorem u7318 : Upper (D 5) (R 5) [18,65,33,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7318
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7319 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 67 37 392 56 46 78 142 270), lower := (rows 19 67 37 392 56 32 64 128 256), losses := [] }

theorem u7319 : Upper (D 5) (R 5) [18,65,33,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7319
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7319
end Delivery.IrregularNine14.P05
