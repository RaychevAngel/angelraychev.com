import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0053
import IrregularNine14P05C0054

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6720 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 8, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 164 25 49 302 334 398 270), lower := (rows 7 74 164 25 49 32 64 128 256), losses := [] }

theorem u6720 : Upper (D 5) (R 5) [6,72,160,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6720
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6721 : Route 9 := (fun mask => (mask,id))

def c6721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6721 : Upper (D 5) (R 5) [6,72,160,17,34] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,34] 13 (by decide) (choices 1) [1,4,8,256] r6721 c6721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3231
  · exact u3232
  · exact u3233
  · exact u3234

def b6722 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 164 25 52 299 331 395 267), lower := (rows 7 74 164 25 52 32 64 128 256), losses := [] }

theorem u6722 : Upper (D 5) (R 5) [6,72,160,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6722
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6723 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 421, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 25 56 295 327 391 263), lower := (rows 7 74 164 25 56 32 64 128 256), losses := [] }

theorem u6723 : Upper (D 5) (R 5) [6,72,160,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6723
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6724 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 8, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 164 25 273 46 110 174 302), lower := (rows 7 74 164 25 273 32 64 128 256), losses := [] }

theorem u6724 : Upper (D 5) (R 5) [6,72,160,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6724
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6725 : Route 9 := (fun mask => (mask,id))

def c6725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6725 : Upper (D 5) (R 5) [6,72,160,17,258] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,258] 13 (by decide) (choices 1) [1,4,8] r6725 c6725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3235
  · exact u3236
  · exact u3237

def r6726 : Route 9 := (fun mask => (mask,id))

def c6726 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6726 : Upper (D 5) (R 5) [6,72,160,17,260] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,260] 13 (by decide) (choices 1) [1,2,8] r6726 c6726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3238
  · exact u3239
  · exact u3240

def b6727 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 25 280 39 103 167 295), lower := (rows 7 74 164 25 280 32 64 128 256), losses := [] }

theorem u6727 : Upper (D 5) (R 5) [6,72,160,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6727
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6728 : Route 9 := (fun mask => (mask,id))

def c6728 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6728 : Upper (D 5) (R 5) [6,72,160,17,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,288] 13 (by decide) (choices 1) [1,2,4,8] r6728 c6728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3241
  · exact u3242
  · exact u3243
  · exact u3244

def b6729 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 164 26 21 297 361 425 297), lower := (rows 7 74 164 26 21 32 64 128 256), losses := [] }

theorem u6729 : Upper (D 5) (R 5) [6,72,160,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6729
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6730 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 74 164 26 25 293 357 421 293), lower := (rows 7 74 164 26 25 32 64 128 256), losses := [] }

theorem u6730 : Upper (D 5) (R 5) [6,72,160,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6730
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6731 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 74 164 26 28 289 353 417 289), lower := (rows 7 74 164 26 28 32 64 128 256), losses := [] }

theorem u6731 : Upper (D 5) (R 5) [6,72,160,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6731
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6732 : Route 9 := (fun mask => (mask,id))

def c6732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6732 : Upper (D 5) (R 5) [6,72,160,18,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18,33] 13 (by decide) (choices 1) [1,4,8,256] r6732 c6732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3245
  · exact u3246
  · exact u3247
  · exact u3248

def b6733 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 164 26 52 297 329 393 265), lower := (rows 7 74 164 26 52 32 64 128 256), losses := [] }

theorem u6733 : Upper (D 5) (R 5) [6,72,160,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6733
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6734 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 420, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 26 56 293 325 389 261), lower := (rows 7 74 164 26 56 32 64 128 256), losses := [] }

theorem u6734 : Upper (D 5) (R 5) [6,72,160,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6735 : Route 9 := (fun mask => (mask,id))

def c6735 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6735 : Upper (D 5) (R 5) [6,72,160,18,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18,257] 13 (by decide) (choices 1) [1,4,8] r6735 c6735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3249
  · exact u3250
  · exact u3251

def r6736 : Route 9 := (fun mask => (mask,id))

def c6736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6736 : Upper (D 5) (R 5) [6,72,160,18,260] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18,260] 13 (by decide) (choices 1) [1,8] r6736 c6736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3252
  · exact u3253

def b6737 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 26 280 37 101 165 293), lower := (rows 7 74 164 26 280 32 64 128 256), losses := [] }

theorem u6737 : Upper (D 5) (R 5) [6,72,160,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6738 : Route 9 := (fun mask => (mask,id))

def c6738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6738 : Upper (D 5) (R 5) [6,72,160,18,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18,288] 13 (by decide) (choices 1) [1,4,8] r6738 c6738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3254
  · exact u3255
  · exact u3256

def b6739 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 28 19 297 361 425 297), lower := (rows 7 74 164 28 19 32 64 128 256), losses := [] }

theorem u6739 : Upper (D 5) (R 5) [6,72,160,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6739
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6740 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 164 28 25 291 355 419 291), lower := (rows 7 74 164 28 25 32 64 128 256), losses := [] }

theorem u6740 : Upper (D 5) (R 5) [6,72,160,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6741 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 28 26 289 353 417 289), lower := (rows 7 74 164 28 26 32 64 128 256), losses := [] }

theorem u6741 : Upper (D 5) (R 5) [6,72,160,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6742 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 28 49 299 331 395 267), lower := (rows 7 74 164 28 49 32 64 128 256), losses := [] }

theorem u6742 : Upper (D 5) (R 5) [6,72,160,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6742
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6743 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 28 50 297 329 393 265), lower := (rows 7 74 164 28 50 32 64 128 256), losses := [] }

theorem u6743 : Upper (D 5) (R 5) [6,72,160,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6743
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6744 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 164 28 56 291 323 387 259), lower := (rows 7 74 164 28 56 32 64 128 256), losses := [] }

theorem u6744 : Upper (D 5) (R 5) [6,72,160,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6744
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6745 : Route 9 := (fun mask => (mask,id))

def c6745 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6745 : Upper (D 5) (R 5) [6,72,160,20,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,20,257] 13 (by decide) (choices 1) [1,2,8] r6745 c6745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3257
  · exact u3258
  · exact u3259

def r6746 : Route 9 := (fun mask => (mask,id))

def c6746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6746 : Upper (D 5) (R 5) [6,72,160,20,258] 13 := by
  apply FastRouting.sound _ _ [6,72,160,20,258] 13 (by decide) (choices 1) [1,8] r6746 c6746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3260
  · exact u3261

def b6747 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 28 280 35 99 163 291), lower := (rows 7 74 164 28 280 32 64 128 256), losses := [] }

theorem u6747 : Upper (D 5) (R 5) [6,72,160,20,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6747
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6748 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 28 304 43 75 139 267), lower := (rows 7 74 164 28 304 32 64 128 256), losses := [] }

theorem u6748 : Upper (D 5) (R 5) [6,72,160,20,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6748
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6749 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 41 19 316 348 412 284), lower := (rows 7 74 164 41 19 32 64 128 256), losses := [] }

theorem u6749 : Upper (D 5) (R 5) [6,72,160,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6750 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 164 41 21 314 346 410 282), lower := (rows 7 74 164 41 21 32 64 128 256), losses := [] }

theorem u6750 : Upper (D 5) (R 5) [6,72,160,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6751 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 74 164 41 22 313 345 409 281), lower := (rows 7 74 164 41 22 32 64 128 256), losses := [] }

theorem u6751 : Upper (D 5) (R 5) [6,72,160,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6752 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 41 25 310 342 406 278), lower := (rows 7 74 164 41 25 32 64 128 256), losses := [] }

theorem u6752 : Upper (D 5) (R 5) [6,72,160,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6752
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6753 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 41 26 309 341 405 277), lower := (rows 7 74 164 41 26 32 64 128 256), losses := [] }

theorem u6753 : Upper (D 5) (R 5) [6,72,160,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6753
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6754 : PairBound 9 := { available := 275, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 41 28 307 339 403 275), lower := (rows 7 74 164 41 28 32 64 128 256), losses := [] }

theorem u6754 : Upper (D 5) (R 5) [6,72,160,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6755 : Route 9 := (fun mask => (mask,id))

def c6755 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6755 : Upper (D 5) (R 5) [6,72,160,33,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,257] 13 (by decide) (choices 1) [2,4,8,16] r6755 c6755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3262
  · exact u3263
  · exact u3264
  · exact u3265

def r6756 : Route 9 := (fun mask => (mask,id))

def c6756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6756 : Upper (D 5) (R 5) [6,72,160,33,258] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,258] 13 (by decide) (choices 1) [1,4,8,16] r6756 c6756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3266
  · exact u3267
  · exact u3268
  · exact u3269

def r6757 : Route 9 := (fun mask => (mask,id))

def c6757 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6757 : Upper (D 5) (R 5) [6,72,160,33,260] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,260] 13 (by decide) (choices 1) [1,2,8,16] r6757 c6757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3270
  · exact u3271
  · exact u3272
  · exact u3273

def r6758 : Route 9 := (fun mask => (mask,id))

def c6758 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6758 : Upper (D 5) (R 5) [6,72,160,33,264] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,264] 13 (by decide) (choices 1) [1,2,4,16] r6758 c6758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3274
  · exact u3275
  · exact u3276
  · exact u3277

def b6759 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 164 42 21 313 345 409 281), lower := (rows 7 74 164 42 21 32 64 128 256), losses := [] }

theorem u6759 : Upper (D 5) (R 5) [6,72,160,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6759
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6760 : PairBound 9 := { available := 277, camps := [{ cop := 4, region := 420, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 42 25 309 341 405 277), lower := (rows 7 74 164 42 25 32 64 128 256), losses := [] }

theorem u6760 : Upper (D 5) (R 5) [6,72,160,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6760
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6761 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 42 28 305 337 401 273), lower := (rows 7 74 164 42 28 32 64 128 256), losses := [] }

theorem u6761 : Upper (D 5) (R 5) [6,72,160,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6761
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6762 : Route 9 := (fun mask => (mask,id))

def c6762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6762 : Upper (D 5) (R 5) [6,72,160,34,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,257] 13 (by decide) (choices 1) [1,4,8,16] r6762 c6762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3278
  · exact u3279
  · exact u3280
  · exact u3281

def r6763 : Route 9 := (fun mask => (mask,id))

def c6763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6763 : Upper (D 5) (R 5) [6,72,160,34,260] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,260] 13 (by decide) (choices 1) [1,8,16] r6763 c6763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3282
  · exact u3283
  · exact u3284

def r6764 : Route 9 := (fun mask => (mask,id))

def c6764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6764 : Upper (D 5) (R 5) [6,72,160,34,264] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34,264] 13 (by decide) (choices 1) [1,4,16] r6764 c6764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3285
  · exact u3286
  · exact u3287

def b6765 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 56 19 301 333 397 269), lower := (rows 7 74 164 56 19 32 64 128 256), losses := [] }

theorem u6765 : Upper (D 5) (R 5) [6,72,160,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6765
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6766 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 164 56 21 299 331 395 267), lower := (rows 7 74 164 56 21 32 64 128 256), losses := [] }

theorem u6766 : Upper (D 5) (R 5) [6,72,160,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6766
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6767 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 74 164 56 22 297 329 393 265), lower := (rows 7 74 164 56 22 32 64 128 256), losses := [] }

theorem u6767 : Upper (D 5) (R 5) [6,72,160,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6767
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6768 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 421, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 56 25 295 327 391 263), lower := (rows 7 74 164 56 25 32 64 128 256), losses := [] }

theorem u6768 : Upper (D 5) (R 5) [6,72,160,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6768
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6769 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 56 26 293 325 389 261), lower := (rows 7 74 164 56 26 32 64 128 256), losses := [] }

theorem u6769 : Upper (D 5) (R 5) [6,72,160,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6769
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6770 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 164 56 28 291 323 387 259), lower := (rows 7 74 164 56 28 32 64 128 256), losses := [] }

theorem u6770 : Upper (D 5) (R 5) [6,72,160,48,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6770
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6771 : Route 9 := (fun mask => (mask,id))

def c6771 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6771 : Upper (D 5) (R 5) [6,72,160,48,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,257] 13 (by decide) (choices 1) [1,2,4,8] r6771 c6771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3288
  · exact u3289
  · exact u3290
  · exact u3291

def r6772 : Route 9 := (fun mask => (mask,id))

def c6772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6772 : Upper (D 5) (R 5) [6,72,160,48,258] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,258] 13 (by decide) (choices 1) [1,4,8] r6772 c6772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3292
  · exact u3293
  · exact u3294

def r6773 : Route 9 := (fun mask => (mask,id))

def c6773 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6773 : Upper (D 5) (R 5) [6,72,160,48,260] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,260] 13 (by decide) (choices 1) [1,2,8] r6773 c6773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3295
  · exact u3296
  · exact u3297

def b6774 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 56 280 39 71 135 263), lower := (rows 7 74 164 56 280 32 64 128 256), losses := [] }

theorem u6774 : Upper (D 5) (R 5) [6,72,160,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6774
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6775 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 265 19 60 124 188 316), lower := (rows 7 74 164 265 19 32 64 128 256), losses := [] }

theorem u6775 : Upper (D 5) (R 5) [6,72,160,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6775
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6776 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 164 265 21 58 122 186 314), lower := (rows 7 74 164 265 21 32 64 128 256), losses := [] }

theorem u6776 : Upper (D 5) (R 5) [6,72,160,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6776
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6777 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 74 164 265 22 57 121 185 313), lower := (rows 7 74 164 265 22 32 64 128 256), losses := [] }

theorem u6777 : Upper (D 5) (R 5) [6,72,160,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6777
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6778 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 164 265 25 54 118 182 310), lower := (rows 7 74 164 265 25 32 64 128 256), losses := [] }

theorem u6778 : Upper (D 5) (R 5) [6,72,160,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6778
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6779 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 265 26 53 117 181 309), lower := (rows 7 74 164 265 26 32 64 128 256), losses := [] }

theorem u6779 : Upper (D 5) (R 5) [6,72,160,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6779
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6779
end Delivery.IrregularNine14.P05
