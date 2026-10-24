import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0062
import IrregularNine14P01C0063

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7260 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 322 134 74 185 185 249 185 441), lower := (rows 53 322 134 74 16 32 64 128 256), losses := [] }

theorem u7260 : Upper (D 1) (R 1) [52,320,130,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7260
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7261 : Route 9 := (fun mask => (mask,id))

def c7261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7261 : Upper (D 1) (R 1) [52,320,130,80] 13 := by
  apply FastRouting.sound _ _ [52,320,130,80] 13 (by decide) (choices 1) [1,2,8,32,128] r7261 c7261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3750
  · exact u3751
  · exact u3752
  · exact u3753
  · exact u3754

def b7262 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 134 137 122 122 122 250 378), lower := (rows 53 322 134 137 16 32 64 128 256), losses := [] }

theorem u7262 : Upper (D 1) (R 1) [52,320,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7262
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7263 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 322 134 138 121 121 121 249 377), lower := (rows 53 322 134 138 16 32 64 128 256), losses := [] }

theorem u7263 : Upper (D 1) (R 1) [52,320,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7264 : Route 9 := (fun mask => (mask,id))

def c7264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7264 : Upper (D 1) (R 1) [52,320,130,144] 13 := by
  apply FastRouting.sound _ _ [52,320,130,144] 13 (by decide) (choices 1) [1,2,8,32,64] r7264 c7264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3755
  · exact u3756
  · exact u3757
  · exact u3758
  · exact u3759

def r7265 : Route 9 := (fun mask => (mask,id))

def c7265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7265 : Upper (D 1) (R 1) [52,320,130,192] 13 := by
  apply FastRouting.sound _ _ [52,320,130,192] 13 (by decide) (choices 1) [1,2,8,32] r7265 c7265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3760
  · exact u3761
  · exact u3762
  · exact u3763

def r7266 : Route 9 := (fun mask => (mask,id))

def c7266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7266 : Upper (D 1) (R 1) [52,320,136,3] 13 := by
  apply FastRouting.sound _ _ [52,320,136,3] 13 (by decide) (choices 1) [2,32,64,128] r7266 c7266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3764
  · exact u3765
  · exact u3766
  · exact u3767

def b7267 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 140 25 242 226 226 226 482), lower := (rows 53 322 140 25 16 32 64 128 256), losses := [] }

theorem u7267 : Upper (D 1) (R 1) [52,320,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7267
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7268 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 140 26 243 227 227 227 483), lower := (rows 53 322 140 26 16 32 64 128 256), losses := [] }

theorem u7268 : Upper (D 1) (R 1) [52,320,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7268
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7269 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 140 56 211 227 195 195 451), lower := (rows 53 322 140 56 16 32 64 128 256), losses := [] }

theorem u7269 : Upper (D 1) (R 1) [52,320,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7269
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7270 : Route 9 := (fun mask => (mask,id))

def c7270 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7270 : Upper (D 1) (R 1) [52,320,136,65] 13 := by
  apply FastRouting.sound _ _ [52,320,136,65] 13 (by decide) (choices 1) [2,32,128] r7270 c7270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3768
  · exact u3769
  · exact u3770

def b7271 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 322 140 74 179 179 243 179 435), lower := (rows 53 322 140 74 16 32 64 128 256), losses := [] }

theorem u7271 : Upper (D 1) (R 1) [52,320,136,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7271
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7272 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 140 88 179 163 227 163 419), lower := (rows 53 322 140 88 16 32 64 128 256), losses := [] }

theorem u7272 : Upper (D 1) (R 1) [52,320,136,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7272
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7273 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 140 137 114 114 114 242 370), lower := (rows 53 322 140 137 16 32 64 128 256), losses := [] }

theorem u7273 : Upper (D 1) (R 1) [52,320,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7273
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7274 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 140 138 115 115 115 243 371), lower := (rows 53 322 140 138 16 32 64 128 256), losses := [] }

theorem u7274 : Upper (D 1) (R 1) [52,320,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7275 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 140 152 115 99 99 227 355), lower := (rows 53 322 140 152 16 32 64 128 256), losses := [] }

theorem u7275 : Upper (D 1) (R 1) [52,320,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7275
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7276 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 140 200 51 51 115 179 307), lower := (rows 53 322 140 200 16 32 64 128 256), losses := [] }

theorem u7276 : Upper (D 1) (R 1) [52,320,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7276
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7277 : Route 9 := (fun mask => (mask,id))

def c7277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7277 : Upper (D 1) (R 1) [52,320,192,3] 13 := by
  apply FastRouting.sound _ _ [52,320,192,3] 13 (by decide) (choices 1) [2,8,32,128] r7277 c7277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3771
  · exact u3772
  · exact u3773
  · exact u3774

def b7278 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 196 25 186 170 234 170 426), lower := (rows 53 322 196 25 16 32 64 128 256), losses := [] }

theorem u7278 : Upper (D 1) (R 1) [52,320,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7278
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7279 : Route 9 := (fun mask => (mask,id))

def c7279 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7279 : Upper (D 1) (R 1) [52,320,192,18] 13 := by
  apply FastRouting.sound _ _ [52,320,192,18] 13 (by decide) (choices 1) [1,2,8,32,128] r7279 c7279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3775
  · exact u3776
  · exact u3777
  · exact u3778
  · exact u3779

def b7280 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 196 56 155 171 203 139 395), lower := (rows 53 322 196 56 16 32 64 128 256), losses := [] }

theorem u7280 : Upper (D 1) (R 1) [52,320,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7280
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7281 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 196 137 58 58 122 186 314), lower := (rows 53 322 196 137 16 32 64 128 256), losses := [] }

theorem u7281 : Upper (D 1) (R 1) [52,320,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7281
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7282 : Route 9 := (fun mask => (mask,id))

def c7282 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7282 : Upper (D 1) (R 1) [52,320,192,130] 13 := by
  apply FastRouting.sound _ _ [52,320,192,130] 13 (by decide) (choices 1) [1,2,8,32] r7282 c7282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3780
  · exact u3781
  · exact u3782
  · exact u3783

def r7283 : Route 9 := (fun mask => (mask,id))

def c7283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7283 : Upper (D 1) (R 1) [52,320,192,144] 13 := by
  apply FastRouting.sound _ _ [52,320,192,144] 13 (by decide) (choices 1) [1,2,8,32] r7283 c7283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3784
  · exact u3785
  · exact u3786
  · exact u3787

def b7284 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 26 496 480 480 480 480), lower := (rows 113 7 14 26 16 32 64 128 256), losses := [] }

theorem u7284 : Upper (D 1) (R 1) [112,5,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7284
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7285 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 14 56 466 482 450 450 450), lower := (rows 113 7 14 56 16 32 64 128 256), losses := [] }

theorem u7285 : Upper (D 1) (R 1) [112,5,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7286 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 7 14 138 496 496 496 496 496), lower := (rows 113 7 14 138 16 32 64 128 256), losses := [] }

theorem u7286 : Upper (D 1) (R 1) [112,5,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7286
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7287 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u7287 : Upper (D 1) (R 1) [112,5,10,144] 13 := by
  apply FastRouting.sound _ _ [112,5,10,144] 13 (by decide) (choices 1) [2,32,128,256] r7287 c7287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3788
  · exact u3789
  · exact u3790
  · exact u3791

def b7288 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 7 14 266 240 240 240 240 496), lower := (rows 113 7 14 266 16 32 64 128 256), losses := [] }

theorem u7288 : Upper (D 1) (R 1) [112,5,10,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7288
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7289 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7289 : Upper (D 1) (R 1) [112,5,10,272] 13 := by
  apply FastRouting.sound _ _ [112,5,10,272] 13 (by decide) (choices 1) [2,32,128] r7289 c7289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3792
  · exact u3793
  · exact u3794

def r7290 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7290 : Upper (D 1) (R 1) [112,5,10,384] 13 := by
  apply FastRouting.sound _ _ [112,5,10,384] 13 (by decide) (choices 1) [2,32,128] r7290 c7290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3795
  · exact u3796
  · exact u3797

def b7291 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 134 26 504 488 488 488 488), lower := (rows 113 7 134 26 16 32 64 128 256), losses := [] }

theorem u7291 : Upper (D 1) (R 1) [112,5,130,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7291
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7292 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 7 134 56 474 490 458 458 458), lower := (rows 113 7 134 56 16 32 64 128 256), losses := [] }

theorem u7292 : Upper (D 1) (R 1) [112,5,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7293 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 134 138 376 376 376 504 376), lower := (rows 113 7 134 138 16 32 64 128 256), losses := [] }

theorem u7293 : Upper (D 1) (R 1) [112,5,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7293
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7294 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u7294 : Upper (D 1) (R 1) [112,5,130,144] 13 := by
  apply FastRouting.sound _ _ [112,5,130,144] 13 (by decide) (choices 1) [2,8,32,256] r7294 c7294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3798
  · exact u3799
  · exact u3800
  · exact u3801

def b7295 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 134 266 248 248 248 248 504), lower := (rows 113 7 134 266 16 32 64 128 256), losses := [] }

theorem u7295 : Upper (D 1) (R 1) [112,5,130,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7296 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7296 : Upper (D 1) (R 1) [112,5,130,272] 13 := by
  apply FastRouting.sound _ _ [112,5,130,272] 13 (by decide) (choices 1) [2,8,32,128] r7296 c7296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3802
  · exact u3803
  · exact u3804
  · exact u3805

def r7297 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7297 : Upper (D 1) (R 1) [112,5,130,384] 13 := by
  apply FastRouting.sound _ _ [112,5,130,384] 13 (by decide) (choices 1) [2,8,32] r7297 c7297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3806
  · exact u3807
  · exact u3808

def b7298 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 7 140 26 498 482 482 482 482), lower := (rows 113 7 140 26 16 32 64 128 256), losses := [] }

theorem u7298 : Upper (D 1) (R 1) [112,5,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7298
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7299 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 7 140 56 466 482 450 450 450), lower := (rows 113 7 140 56 16 32 64 128 256), losses := [] }

theorem u7299 : Upper (D 1) (R 1) [112,5,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7299
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7300 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 7 140 138 370 370 370 498 370), lower := (rows 113 7 140 138 16 32 64 128 256), losses := [] }

theorem u7300 : Upper (D 1) (R 1) [112,5,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7300
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7301 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 7 140 152 370 354 354 482 354), lower := (rows 113 7 140 152 16 32 64 128 256), losses := [] }

theorem u7301 : Upper (D 1) (R 1) [112,5,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7302 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7302 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7302 : Upper (D 1) (R 1) [112,5,136,258] 13 := by
  apply FastRouting.sound _ _ [112,5,136,258] 13 (by decide) (choices 1) [2,32,128] r7302 c7302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3809
  · exact u3810
  · exact u3811

def r7303 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7303 : Upper (D 1) (R 1) [112,5,136,272] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272] 13 (by decide) (choices 1) [2,32,128] r7303 c7303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3812
  · exact u3813
  · exact u3814

def b7304 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 7 140 392 114 114 114 242 370), lower := (rows 113 7 140 392 16 32 64 128 256), losses := [] }

theorem u7304 : Upper (D 1) (R 1) [112,5,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7305 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 262 26 248 232 232 232 488), lower := (rows 113 7 262 26 16 32 64 128 256), losses := [] }

theorem u7305 : Upper (D 1) (R 1) [112,5,258,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7305
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7306 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 7 262 56 218 234 202 202 458), lower := (rows 113 7 262 56 16 32 64 128 256), losses := [] }

theorem u7306 : Upper (D 1) (R 1) [112,5,258,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7307 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 113, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 262 138 248 248 248 248 504), lower := (rows 113 7 262 138 16 32 64 128 256), losses := [] }

theorem u7307 : Upper (D 1) (R 1) [112,5,258,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7307
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7308 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7308 : Upper (D 1) (R 1) [112,5,258,144] 13 := by
  apply FastRouting.sound _ _ [112,5,258,144] 13 (by decide) (choices 1) [2,8,32,128] r7308 c7308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3815
  · exact u3816
  · exact u3817
  · exact u3818

def b7309 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 7 268 26 242 226 226 226 482), lower := (rows 113 7 268 26 16 32 64 128 256), losses := [] }

theorem u7309 : Upper (D 1) (R 1) [112,5,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7310 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 7 268 56 210 226 194 194 450), lower := (rows 113 7 268 56 16 32 64 128 256), losses := [] }

theorem u7310 : Upper (D 1) (R 1) [112,5,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7310
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7311 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7311 : Upper (D 1) (R 1) [112,5,264,130] 13 := by
  apply FastRouting.sound _ _ [112,5,264,130] 13 (by decide) (choices 1) [2,32,128] r7311 c7311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3819
  · exact u3820
  · exact u3821

def r7312 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7312 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7312 : Upper (D 1) (R 1) [112,5,264,144] 13 := by
  apply FastRouting.sound _ _ [112,5,264,144] 13 (by decide) (choices 1) [2,32,128] r7312 c7312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3822
  · exact u3823
  · exact u3824

def b7313 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 7 388 26 250 234 234 234 490), lower := (rows 113 7 388 26 16 32 64 128 256), losses := [] }

theorem u7313 : Upper (D 1) (R 1) [112,5,384,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7313
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7314 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 7 388 56 218 234 202 202 458), lower := (rows 113 7 388 56 16 32 64 128 256), losses := [] }

theorem u7314 : Upper (D 1) (R 1) [112,5,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7314
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7315 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 388 138 122 122 122 250 378), lower := (rows 113 7 388 138 16 32 64 128 256), losses := [] }

theorem u7315 : Upper (D 1) (R 1) [112,5,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7316 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7316 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7316 : Upper (D 1) (R 1) [112,5,384,144] 13 := by
  apply FastRouting.sound _ _ [112,5,384,144] 13 (by decide) (choices 1) [2,8,32] r7316 c7316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3825
  · exact u3826
  · exact u3827

def b7317 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 7 26 496 480 480 480 480), lower := (rows 113 14 7 26 16 32 64 128 256), losses := [] }

theorem u7317 : Upper (D 1) (R 1) [112,12,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7317
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7318 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 7 56 466 482 450 450 450), lower := (rows 113 14 7 56 16 32 64 128 256), losses := [] }

theorem u7318 : Upper (D 1) (R 1) [112,12,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7318
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7319 : PairBound 9 := { available := 496, camps := [{ cop := 1, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 7 138 496 496 496 496 496), lower := (rows 113 14 7 138 16 32 64 128 256), losses := [] }

theorem u7319 : Upper (D 1) (R 1) [112,12,3,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7319
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7319
end Delivery.IrregularNine14.P01
