import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0013

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3240 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 196 11 144 306 370 434 306), lower := (rows 53 74 196 11 144 32 64 128 256), losses := [] }

theorem u3240 : Upper (D 1) (R 1) [52,72,192,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3241 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 74 196 11 272 178 242 178 434), lower := (rows 53 74 196 11 272 32 64 128 256), losses := [] }

theorem u3241 : Upper (D 1) (R 1) [52,72,192,3,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3241
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3242 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 53 74 196 26 17 418 482 418 418), lower := (rows 53 74 196 26 17 32 64 128 256), losses := [] }

theorem u3242 : Upper (D 1) (R 1) [52,72,192,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3242
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3243 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 26 18 417 481 417 417), lower := (rows 53 74 196 26 18 32 64 128 256), losses := [] }

theorem u3243 : Upper (D 1) (R 1) [52,72,192,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3244 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 26 48 419 451 387 387), lower := (rows 53 74 196 26 48 32 64 128 256), losses := [] }

theorem u3244 : Upper (D 1) (R 1) [52,72,192,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3245 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 196 26 144 291 355 419 291), lower := (rows 53 74 196 26 144 32 64 128 256), losses := [] }

theorem u3245 : Upper (D 1) (R 1) [52,72,192,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3245
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3246 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 74 196 26 272 163 227 163 419), lower := (rows 53 74 196 26 272 32 64 128 256), losses := [] }

theorem u3246 : Upper (D 1) (R 1) [52,72,192,18,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3246
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3247 : PairBound 9 := { available := 290, camps := [], pairs := [], upper := (rows 53 74 196 152 17 290 354 418 290), lower := (rows 53 74 196 152 17 32 64 128 256), losses := [] }

theorem u3247 : Upper (D 1) (R 1) [52,72,192,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3247
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3248 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 152 18 291 355 419 291), lower := (rows 53 74 196 152 18 32 64 128 256), losses := [] }

theorem u3248 : Upper (D 1) (R 1) [52,72,192,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3248
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3249 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 152 48 291 323 387 259), lower := (rows 53 74 196 152 48 32 64 128 256), losses := [] }

theorem u3249 : Upper (D 1) (R 1) [52,72,192,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3249
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3250 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 53 74 196 152 272 35 99 163 291), lower := (rows 53 74 196 152 272 32 64 128 256), losses := [] }

theorem u3250 : Upper (D 1) (R 1) [52,72,192,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3250
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3251 : PairBound 9 := { available := 178, camps := [], pairs := [(3,6)], upper := (rows 53 74 196 265 18 178 242 178 434), lower := (rows 53 74 196 265 18 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 18 50 0 146 274), good := (rows 445 442 132 265 434 32 0 128 256) }] }

theorem u3251 : Upper (D 1) (R 1) [52,72,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3251
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3252 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 265 48 178 210 146 402), lower := (rows 53 74 196 265 48 32 64 128 256), losses := [] }

theorem u3252 : Upper (D 1) (R 1) [52,72,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3253 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 196 265 144 50 114 178 306), lower := (rows 53 74 196 265 144 32 64 128 256), losses := [] }

theorem u3253 : Upper (D 1) (R 1) [52,72,192,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3254 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 74 196 266 17 178 242 178 434), lower := (rows 53 74 196 266 17 32 64 128 256), losses := [] }

theorem u3254 : Upper (D 1) (R 1) [52,72,192,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3255 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 196 266 18 177 241 177 433), lower := (rows 53 74 196 266 18 32 64 128 256), losses := [] }

theorem u3255 : Upper (D 1) (R 1) [52,72,192,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3255
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3256 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 266 48 179 211 147 403), lower := (rows 53 74 196 266 48 32 64 128 256), losses := [] }

theorem u3256 : Upper (D 1) (R 1) [52,72,192,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3256
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3257 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 196 266 144 51 115 179 307), lower := (rows 53 74 196 266 144 32 64 128 256), losses := [] }

theorem u3257 : Upper (D 1) (R 1) [52,72,192,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3257
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3258 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 74 196 280 17 162 226 162 418), lower := (rows 53 74 196 280 17 32 64 128 256), losses := [] }

theorem u3258 : Upper (D 1) (R 1) [52,72,192,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3258
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3259 : Route 9 := (fun mask => (mask,id))

def c3259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3259 : Upper (D 1) (R 1) [52,72,192,272,2] 13 := by
  apply FastRouting.sound _ _ [52,72,192,272,2] 13 (by decide) (choices 1) [1,2,128] r3259 c3259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u785
  · exact u786
  · exact u787

def b3260 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 280 48 163 195 131 387), lower := (rows 53 74 196 280 48 32 64 128 256), losses := [] }

theorem u3260 : Upper (D 1) (R 1) [52,72,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3260
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3261 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 196 280 144 35 99 163 291), lower := (rows 53 74 196 280 144 32 64 128 256), losses := [] }

theorem u3261 : Upper (D 1) (R 1) [52,72,192,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3261
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3262 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 74 196 392 17 50 114 178 306), lower := (rows 53 74 196 392 17 32 64 128 256), losses := [] }

theorem u3262 : Upper (D 1) (R 1) [52,72,192,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3262
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3263_1 : Upper (D 1) (R 1) [52,72,192,384,2,1] 13 :=
  permutation_upper _ _ _ [52,72,192,384,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u788

def r3263 : Route 9 := (fun mask => (mask,id))

def c3263 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3263 : Upper (D 1) (R 1) [52,72,192,384,2] 13 := by
  apply FastRouting.sound _ _ [52,72,192,384,2] 13 (by decide) (choices 1) [1,2,16] r3263 c3263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3263_1
  · exact u789
  · exact u790

def b3264 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 196 392 48 51 83 147 275), lower := (rows 53 74 196 392 48 32 64 128 256), losses := [] }

theorem u3264 : Upper (D 1) (R 1) [52,72,192,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3265 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 261 138 18 240 240 240 496), lower := (rows 53 74 261 138 18 32 64 128 256), losses := [] }

theorem u3265 : Upper (D 1) (R 1) [52,72,257,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3265
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3266 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 261 138 48 242 210 210 466), lower := (rows 53 74 261 138 48 32 64 128 256), losses := [] }

theorem u3266 : Upper (D 1) (R 1) [52,72,257,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3266
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3267_2 : Upper (D 1) (R 1) [52,72,257,130,64,2] 13 :=
  permutation_upper _ _ _ [52,72,257,130,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u791

theorem m3267_16 : Upper (D 1) (R 1) [52,72,257,130,64,16] 13 :=
  permutation_upper _ _ _ [52,72,257,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u793

def r3267 : Route 9 := (fun mask => (mask,id))

def c3267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3267 : Upper (D 1) (R 1) [52,72,257,130,64] 13 := by
  apply FastRouting.sound _ _ [52,72,257,130,64] 13 (by decide) (choices 1) [2,16,128] r3267 c3267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3267_2
  · exact m3267_16
  · exact u795

theorem m3268_2 : Upper (D 1) (R 1) [52,72,257,130,128,2] 13 :=
  permutation_upper _ _ _ [52,72,257,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u792

theorem m3268_16 : Upper (D 1) (R 1) [52,72,257,130,128,16] 13 :=
  permutation_upper _ _ _ [52,72,257,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u794

theorem m3268_64 : Upper (D 1) (R 1) [52,72,257,130,128,64] 13 :=
  permutation_upper _ _ _ [52,72,257,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u795

def r3268 : Route 9 := (fun mask => (mask,id))

def c3268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3268 : Upper (D 1) (R 1) [52,72,257,130,128] 13 := by
  apply FastRouting.sound _ _ [52,72,257,130,128] 13 (by decide) (choices 1) [2,16,64] r3268 c3268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3268_2
  · exact m3268_16
  · exact m3268_64

def b3269 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 137 18 240 240 240 496), lower := (rows 53 74 262 137 18 32 64 128 256), losses := [] }

theorem u3269 : Upper (D 1) (R 1) [52,72,258,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3269
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3270 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 262 137 48 242 210 210 466), lower := (rows 53 74 262 137 48 32 64 128 256), losses := [] }

theorem u3270 : Upper (D 1) (R 1) [52,72,258,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3270
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3271_2 : Upper (D 1) (R 1) [52,72,258,129,64,2] 13 :=
  permutation_upper _ _ _ [52,72,258,129,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u796

theorem m3271_16 : Upper (D 1) (R 1) [52,72,258,129,64,16] 13 :=
  permutation_upper _ _ _ [52,72,258,129,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u798

def r3271 : Route 9 := (fun mask => (mask,id))

def c3271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3271 : Upper (D 1) (R 1) [52,72,258,129,64] 13 := by
  apply FastRouting.sound _ _ [52,72,258,129,64] 13 (by decide) (choices 1) [2,16,128] r3271 c3271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3271_2
  · exact m3271_16
  · exact u800

theorem m3272_2 : Upper (D 1) (R 1) [52,72,258,129,128,2] 13 :=
  permutation_upper _ _ _ [52,72,258,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u797

theorem m3272_16 : Upper (D 1) (R 1) [52,72,258,129,128,16] 13 :=
  permutation_upper _ _ _ [52,72,258,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u799

theorem m3272_64 : Upper (D 1) (R 1) [52,72,258,129,128,64] 13 :=
  permutation_upper _ _ _ [52,72,258,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u800

def r3272 : Route 9 := (fun mask => (mask,id))

def c3272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3272 : Upper (D 1) (R 1) [52,72,258,129,128] 13 := by
  apply FastRouting.sound _ _ [52,72,258,129,128] 13 (by decide) (choices 1) [2,16,64] r3272 c3272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3272_2
  · exact m3272_16
  · exact m3272_64

def b3273 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 74 262 152 17 226 226 226 482), lower := (rows 53 74 262 152 17 32 64 128 256), losses := [] }

theorem u3273 : Upper (D 1) (R 1) [52,72,258,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3273
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3274 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 152 18 225 225 225 481), lower := (rows 53 74 262 152 18 32 64 128 256), losses := [] }

theorem u3274 : Upper (D 1) (R 1) [52,72,258,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3275 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 262 152 48 227 195 195 451), lower := (rows 53 74 262 152 48 32 64 128 256), losses := [] }

theorem u3275 : Upper (D 1) (R 1) [52,72,258,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3275
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3276 : Route 9 := (fun mask => (mask,id))

def c3276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3276 : Upper (D 1) (R 1) [52,72,258,144,64] 13 := by
  apply FastRouting.sound _ _ [52,72,258,144,64] 13 (by decide) (choices 1) [1,2,128] r3276 c3276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u801
  · exact u802
  · exact u803

def b3277 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 53 74 262 152 144 99 99 227 355), lower := (rows 53 74 262 152 144 32 64 128 256), losses := [] }

theorem u3277 : Upper (D 1) (R 1) [52,72,258,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3277
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3278 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 324 11 18 176 240 176 432), lower := (rows 53 74 324 11 18 32 64 128 256), losses := [] }

theorem u3278 : Upper (D 1) (R 1) [52,72,320,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3278
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3279 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 11 48 178 210 146 402), lower := (rows 53 74 324 11 48 32 64 128 256), losses := [] }

theorem u3279 : Upper (D 1) (R 1) [52,72,320,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3279
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3280_2 : Upper (D 1) (R 1) [52,72,320,3,128,2] 13 :=
  permutation_upper _ _ _ [52,72,320,3,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u804

theorem m3280_16 : Upper (D 1) (R 1) [52,72,320,3,128,16] 13 :=
  permutation_upper _ _ _ [52,72,320,3,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u805

def r3280 : Route 9 := (fun mask => (mask,id))

def c3280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3280 : Upper (D 1) (R 1) [52,72,320,3,128] 13 := by
  apply FastRouting.sound _ _ [52,72,320,3,128] 13 (by decide) (choices 1) [2,16,128] r3280 c3280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3280_2
  · exact m3280_16
  · exact u806

def b3281 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 74 324 26 17 162 226 162 418), lower := (rows 53 74 324 26 17 32 64 128 256), losses := [] }

theorem u3281 : Upper (D 1) (R 1) [52,72,320,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3281
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3282 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 26 18 161 225 161 417), lower := (rows 53 74 324 26 18 32 64 128 256), losses := [] }

theorem u3282 : Upper (D 1) (R 1) [52,72,320,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3283 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 26 48 163 195 131 387), lower := (rows 53 74 324 26 48 32 64 128 256), losses := [] }

theorem u3283 : Upper (D 1) (R 1) [52,72,320,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3284 : Route 9 := (fun mask => (mask,id))

def c3284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3284 : Upper (D 1) (R 1) [52,72,320,18,128] 13 := by
  apply FastRouting.sound _ _ [52,72,320,18,128] 13 (by decide) (choices 1) [1,2,128] r3284 c3284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u807
  · exact u808
  · exact u809

def b3285 : PairBound 9 := { available := 178, camps := [], pairs := [(3,6)], upper := (rows 53 74 324 137 18 178 242 178 434), lower := (rows 53 74 324 137 18 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 18 50 0 146 274), good := (rows 445 442 260 137 434 32 0 128 256) }] }

theorem u3285 : Upper (D 1) (R 1) [52,72,320,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3286 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 137 48 178 210 146 402), lower := (rows 53 74 324 137 48 32 64 128 256), losses := [] }

theorem u3286 : Upper (D 1) (R 1) [52,72,320,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3286
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3287_2 : Upper (D 1) (R 1) [52,72,320,129,128,2] 13 :=
  permutation_upper _ _ _ [52,72,320,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u810

theorem m3287_16 : Upper (D 1) (R 1) [52,72,320,129,128,16] 13 :=
  permutation_upper _ _ _ [52,72,320,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u811

def r3287 : Route 9 := (fun mask => (mask,id))

def c3287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3287 : Upper (D 1) (R 1) [52,72,320,129,128] 13 := by
  apply FastRouting.sound _ _ [52,72,320,129,128] 13 (by decide) (choices 1) [2,16] r3287 c3287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3287_2
  · exact m3287_16

def b3288 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 74 324 138 17 178 242 178 434), lower := (rows 53 74 324 138 17 32 64 128 256), losses := [] }

theorem u3288 : Upper (D 1) (R 1) [52,72,320,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3288
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3289 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 324 138 18 177 241 177 433), lower := (rows 53 74 324 138 18 32 64 128 256), losses := [] }

theorem u3289 : Upper (D 1) (R 1) [52,72,320,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3289
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3290 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 138 48 179 211 147 403), lower := (rows 53 74 324 138 48 32 64 128 256), losses := [] }

theorem u3290 : Upper (D 1) (R 1) [52,72,320,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3290
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3291_1 : Upper (D 1) (R 1) [52,72,320,130,128,1] 13 :=
  permutation_upper _ _ _ [52,72,320,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u812

theorem m3291_2 : Upper (D 1) (R 1) [52,72,320,130,128,2] 13 :=
  permutation_upper _ _ _ [52,72,320,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u813

theorem m3291_16 : Upper (D 1) (R 1) [52,72,320,130,128,16] 13 :=
  permutation_upper _ _ _ [52,72,320,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u814

def r3291 : Route 9 := (fun mask => (mask,id))

def c3291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3291 : Upper (D 1) (R 1) [52,72,320,130,128] 13 := by
  apply FastRouting.sound _ _ [52,72,320,130,128] 13 (by decide) (choices 1) [1,2,16] r3291 c3291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3291_1
  · exact m3291_2
  · exact m3291_16

def b3292 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 74 324 152 17 162 226 162 418), lower := (rows 53 74 324 152 17 32 64 128 256), losses := [] }

theorem u3292 : Upper (D 1) (R 1) [52,72,320,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3293 : Route 9 := (fun mask => (mask,id))

def c3293 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3293 : Upper (D 1) (R 1) [52,72,320,144,2] 13 := by
  apply FastRouting.sound _ _ [52,72,320,144,2] 13 (by decide) (choices 1) [1,2,128] r3293 c3293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u815
  · exact u816
  · exact u817

def b3294 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 152 48 163 195 131 387), lower := (rows 53 74 324 152 48 32 64 128 256), losses := [] }

theorem u3294 : Upper (D 1) (R 1) [52,72,320,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3294
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3295 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 53 74 324 152 144 35 99 163 291), lower := (rows 53 74 324 152 144 32 64 128 256), losses := [] }

theorem u3295 : Upper (D 1) (R 1) [52,72,320,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3296 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 388 11 18 240 240 240 496), lower := (rows 53 74 388 11 18 32 64 128 256), losses := [] }

theorem u3296 : Upper (D 1) (R 1) [52,72,384,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3296
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3297 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 388 11 48 242 210 210 466), lower := (rows 53 74 388 11 48 32 64 128 256), losses := [] }

theorem u3297 : Upper (D 1) (R 1) [52,72,384,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3297
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3298_2 : Upper (D 1) (R 1) [52,72,384,3,64,2] 13 :=
  permutation_upper _ _ _ [52,72,384,3,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u818

theorem m3298_16 : Upper (D 1) (R 1) [52,72,384,3,64,16] 13 :=
  permutation_upper _ _ _ [52,72,384,3,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u819

def r3298 : Route 9 := (fun mask => (mask,id))

def c3298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3298 : Upper (D 1) (R 1) [52,72,384,3,64] 13 := by
  apply FastRouting.sound _ _ [52,72,384,3,64] 13 (by decide) (choices 1) [2,16,128] r3298 c3298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3298_2
  · exact m3298_16
  · exact u820

def b3299 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 388 11 144 114 114 242 370), lower := (rows 53 74 388 11 144 32 64 128 256), losses := [] }

theorem u3299 : Upper (D 1) (R 1) [52,72,384,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3299
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3299
end Delivery.IrregularNine14.P01
