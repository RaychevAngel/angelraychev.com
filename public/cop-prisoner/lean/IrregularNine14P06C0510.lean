import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0204
import IrregularNine14P06C0205

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30600 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 84 140 19 356 356 484 356), lower := (rows 11 35 84 140 19 32 64 128 256), losses := [] }

theorem u30600 : Upper (D 6) (R 6) [10,33,80,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30601 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 84 140 21 354 354 482 354), lower := (rows 11 35 84 140 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 490 482 92 140 508 32 64 128 256) }] }

theorem u30601 : Upper (D 6) (R 6) [10,33,80,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30602 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 84 140 22 353 353 481 353), lower := (rows 11 35 84 140 22 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 489 481 92 140 508 32 64 128 256) }] }

theorem u30602 : Upper (D 6) (R 6) [10,33,80,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30603 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 84 140 49 358 326 454 326), lower := (rows 11 35 84 140 49 32 64 128 256), losses := [] }

theorem u30603 : Upper (D 6) (R 6) [10,33,80,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30604 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 84 140 50 357 325 453 325), lower := (rows 11 35 84 140 50 32 64 128 256), losses := [] }

theorem u30604 : Upper (D 6) (R 6) [10,33,80,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30605 : Route 9 := (fun mask => (mask,id))

def c30605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30605 : Upper (D 6) (R 6) [10,33,80,132,36] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,36] 13 (by decide) (choices 1) [1,2,64,256] r30605 c30605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12240
  · exact u12241
  · exact u12242
  · exact u12243

def b30606 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 140 81 294 358 422 294), lower := (rows 11 35 84 140 81 32 64 128 256), losses := [] }

theorem u30606 : Upper (D 6) (R 6) [10,33,80,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30607 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 140 82 293 357 421 293), lower := (rows 11 35 84 140 82 32 64 128 256), losses := [] }

theorem u30607 : Upper (D 6) (R 6) [10,33,80,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30608 : PairBound 9 := { available := 291, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 35 84 140 84 291 355 419 291), lower := (rows 11 35 84 140 84 32 64 128 256), losses := [] }

theorem u30608 : Upper (D 6) (R 6) [10,33,80,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30609 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 140 112 295 327 391 263), lower := (rows 11 35 84 140 112 32 64 128 256), losses := [] }

theorem u30609 : Upper (D 6) (R 6) [10,33,80,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30610 : Route 9 := (fun mask => (mask,id))

def c30610 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30610 : Upper (D 6) (R 6) [10,33,80,132,257] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,257] 13 (by decide) (choices 1) [2,4,64] r30610 c30610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12244
  · exact u12245
  · exact u12246

def r30611 : Route 9 := (fun mask => (mask,id))

def c30611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30611 : Upper (D 6) (R 6) [10,33,80,132,258] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,258] 13 (by decide) (choices 1) [1,4,64] r30611 c30611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12247
  · exact u12248
  · exact u12249

def r30612 : Route 9 := (fun mask => (mask,id))

def c30612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30612 : Upper (D 6) (R 6) [10,33,80,132,260] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,260] 13 (by decide) (choices 1) [1,2,64] r30612 c30612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12250
  · exact u12251
  · exact u12252

def r30613 : Route 9 := (fun mask => (mask,id))

def c30613 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30613 : Upper (D 6) (R 6) [10,33,80,132,288] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,288] 13 (by decide) (choices 1) [1,2,4,64] r30613 c30613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12253
  · exact u12254
  · exact u12255
  · exact u12256

def b30614 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 140 336 39 103 167 295), lower := (rows 11 35 84 140 336 32 64 128 256), losses := [] }

theorem u30614 : Upper (D 6) (R 6) [10,33,80,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30615 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 84 200 19 292 356 420 292), lower := (rows 11 35 84 200 19 32 64 128 256), losses := [] }

theorem u30615 : Upper (D 6) (R 6) [10,33,80,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30616 : Route 9 := (fun mask => (mask,id))

def c30616 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30616 : Upper (D 6) (R 6) [10,33,80,192,5] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,5] 13 (by decide) (choices 1) [2,4,256] r30616 c30616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12257
  · exact u12258
  · exact u12259

def r30617 : Route 9 := (fun mask => (mask,id))

def c30617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30617 : Upper (D 6) (R 6) [10,33,80,192,6] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,6] 13 (by decide) (choices 1) [1,4,256] r30617 c30617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12260
  · exact u12261
  · exact u12262

def b30618 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 84 200 49 294 326 390 262), lower := (rows 11 35 84 200 49 32 64 128 256), losses := [] }

theorem u30618 : Upper (D 6) (R 6) [10,33,80,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30619 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 84 200 50 293 325 389 261), lower := (rows 11 35 84 200 50 32 64 128 256), losses := [] }

theorem u30619 : Upper (D 6) (R 6) [10,33,80,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30620 : Route 9 := (fun mask => (mask,id))

def c30620 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30620 : Upper (D 6) (R 6) [10,33,80,192,36] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,36] 13 (by decide) (choices 1) [1,2,4,256] r30620 c30620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12263
  · exact u12264
  · exact u12265
  · exact u12266

def r30621 : Route 9 := (fun mask => (mask,id))

def c30621 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30621 : Upper (D 6) (R 6) [10,33,80,192,257] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,257] 13 (by decide) (choices 1) [2,4] r30621 c30621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12267
  · exact u12268

def r30622 : Route 9 := (fun mask => (mask,id))

def c30622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30622 : Upper (D 6) (R 6) [10,33,80,192,258] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,258] 13 (by decide) (choices 1) [1,4] r30622 c30622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12269
  · exact u12270

def r30623 : Route 9 := (fun mask => (mask,id))

def c30623 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30623 : Upper (D 6) (R 6) [10,33,80,192,260] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,260] 13 (by decide) (choices 1) [1,2,4] r30623 c30623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12271
  · exact u12272
  · exact u12273

def r30624 : Route 9 := (fun mask => (mask,id))

def c30624 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30624 : Upper (D 6) (R 6) [10,33,80,192,288] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,288] 13 (by decide) (choices 1) [1,2,4] r30624 c30624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12274
  · exact u12275
  · exact u12276

def b30625 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 84 392 19 100 100 228 356), lower := (rows 11 35 84 392 19 32 64 128 256), losses := [] }

theorem u30625 : Upper (D 6) (R 6) [10,33,80,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30626 : Route 9 := (fun mask => (mask,id))

def c30626 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30626 : Upper (D 6) (R 6) [10,33,80,384,5] 13 := by
  apply FastRouting.sound _ _ [10,33,80,384,5] 13 (by decide) (choices 1) [2,4,64] r30626 c30626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12277
  · exact u12278
  · exact u12279

def r30627 : Route 9 := (fun mask => (mask,id))

def c30627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30627 : Upper (D 6) (R 6) [10,33,80,384,6] 13 := by
  apply FastRouting.sound _ _ [10,33,80,384,6] 13 (by decide) (choices 1) [1,4,64] r30627 c30627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12280
  · exact u12281
  · exact u12282

def b30628 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 84 392 49 102 70 198 326), lower := (rows 11 35 84 392 49 32 64 128 256), losses := [] }

theorem u30628 : Upper (D 6) (R 6) [10,33,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30629 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 84 392 50 101 69 197 325), lower := (rows 11 35 84 392 50 32 64 128 256), losses := [] }

theorem u30629 : Upper (D 6) (R 6) [10,33,80,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30630 : Route 9 := (fun mask => (mask,id))

def c30630 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30630 : Upper (D 6) (R 6) [10,33,80,384,36] 13 := by
  apply FastRouting.sound _ _ [10,33,80,384,36] 13 (by decide) (choices 1) [1,2,4,64] r30630 c30630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12283
  · exact u12284
  · exact u12285
  · exact u12286

def b30631 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 392 81 38 102 166 294), lower := (rows 11 35 84 392 81 32 64 128 256), losses := [] }

theorem u30631 : Upper (D 6) (R 6) [10,33,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30632 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 392 82 37 101 165 293), lower := (rows 11 35 84 392 82 32 64 128 256), losses := [] }

theorem u30632 : Upper (D 6) (R 6) [10,33,80,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30633 : PairBound 9 := { available := 39, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 35 84 392 84 39 103 167 295), lower := (rows 11 35 84 392 84 32 64 128 256), losses := [] }

theorem u30633 : Upper (D 6) (R 6) [10,33,80,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30634 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 392 112 39 71 135 263), lower := (rows 11 35 84 392 112 32 64 128 256), losses := [] }

theorem u30634 : Upper (D 6) (R 6) [10,33,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30635 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 25 22 484 452 452 452), lower := (rows 11 35 100 25 22 32 64 128 256), losses := [] }

theorem u30635 : Upper (D 6) (R 6) [10,33,96,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30636 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 100 25 82 420 452 388 388), lower := (rows 11 35 100 25 82 32 64 128 256), losses := [] }

theorem u30636 : Upper (D 6) (R 6) [10,33,96,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30637 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 100 25 84 422 454 390 390), lower := (rows 11 35 100 25 84 32 64 128 256), losses := [] }

theorem u30637 : Upper (D 6) (R 6) [10,33,96,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30638 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 100 25 146 356 324 452 324), lower := (rows 11 35 100 25 146 32 64 128 256), losses := [] }

theorem u30638 : Upper (D 6) (R 6) [10,33,96,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30639 : Route 9 := (fun mask => (mask,id))

def c30639 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30639 : Upper (D 6) (R 6) [10,33,96,17,132] 13 := by
  apply FastRouting.sound _ _ [10,33,96,17,132] 13 (by decide) (choices 1) [2,4,64,256] r30639 c30639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12287
  · exact u12288
  · exact u12289
  · exact u12290

def r30640 : Route 9 := (fun mask => (mask,id))

def c30640 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30640 : Upper (D 6) (R 6) [10,33,96,17,192] 13 := by
  apply FastRouting.sound _ _ [10,33,96,17,192] 13 (by decide) (choices 1) [2,4,256] r30640 c30640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12291
  · exact u12292
  · exact u12293

def r30641 : Route 9 := (fun mask => (mask,id))

def c30641 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30641 : Upper (D 6) (R 6) [10,33,96,17,384] 13 := by
  apply FastRouting.sound _ _ [10,33,96,17,384] 13 (by decide) (choices 1) [2,4,64] r30641 c30641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12294
  · exact u12295
  · exact u12296

def b30642 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 28 19 484 452 452 452), lower := (rows 11 35 100 28 19 32 64 128 256), losses := [] }

theorem u30642 : Upper (D 6) (R 6) [10,33,96,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30643 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 28 21 482 450 450 450), lower := (rows 11 35 100 28 21 32 64 128 256), losses := [] }

theorem u30643 : Upper (D 6) (R 6) [10,33,96,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30644 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 28 22 481 449 449 449), lower := (rows 11 35 100 28 22 32 64 128 256), losses := [] }

theorem u30644 : Upper (D 6) (R 6) [10,33,96,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30645 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 484, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 11 35 100 28 81 422 454 390 390), lower := (rows 11 35 100 28 81 32 64 128 256), losses := [] }

theorem u30645 : Upper (D 6) (R 6) [10,33,96,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30646 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 35 100 28 82 421 453 389 389), lower := (rows 11 35 100 28 82 32 64 128 256), losses := [] }

theorem u30646 : Upper (D 6) (R 6) [10,33,96,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30647 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 100 28 84 419 451 387 387), lower := (rows 11 35 100 28 84 32 64 128 256), losses := [] }

theorem u30647 : Upper (D 6) (R 6) [10,33,96,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30648 : Route 9 := (fun mask => (mask,id))

def c30648 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30648 : Upper (D 6) (R 6) [10,33,96,20,129] 13 := by
  apply FastRouting.sound _ _ [10,33,96,20,129] 13 (by decide) (choices 1) [2,4,64,256] r30648 c30648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12297
  · exact u12298
  · exact u12299
  · exact u12300

def r30649 : Route 9 := (fun mask => (mask,id))

def c30649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30649 : Upper (D 6) (R 6) [10,33,96,20,130] 13 := by
  apply FastRouting.sound _ _ [10,33,96,20,130] 13 (by decide) (choices 1) [1,4,64,256] r30649 c30649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12301
  · exact u12302
  · exact u12303
  · exact u12304

def b30650 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 100 28 148 355 323 451 323), lower := (rows 11 35 100 28 148 32 64 128 256), losses := [] }

theorem u30650 : Upper (D 6) (R 6) [10,33,96,20,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30651 : Route 9 := (fun mask => (mask,id))

def c30651 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30651 : Upper (D 6) (R 6) [10,33,96,20,192] 13 := by
  apply FastRouting.sound _ _ [10,33,96,20,192] 13 (by decide) (choices 1) [1,2,4,256] r30651 c30651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12305
  · exact u12306
  · exact u12307
  · exact u12308

def r30652 : Route 9 := (fun mask => (mask,id))

def c30652 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30652 : Upper (D 6) (R 6) [10,33,96,20,384] 13 := by
  apply FastRouting.sound _ _ [10,33,96,20,384] 13 (by decide) (choices 1) [1,2,4,64] r30652 c30652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12309
  · exact u12310
  · exact u12311
  · exact u12312

def b30653 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 27, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 100 88 19 420 452 388 388), lower := (rows 11 35 100 88 19 32 64 128 256), losses := [] }

theorem u30653 : Upper (D 6) (R 6) [10,33,96,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30654 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 11 35 100 88 21 422 454 390 390), lower := (rows 11 35 100 88 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 494 486 100 92 508 32 64 128 256) }] }

theorem u30654 : Upper (D 6) (R 6) [10,33,96,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30655 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 457, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 35 100 88 22 421 453 389 389), lower := (rows 11 35 100 88 22 32 64 128 256), losses := [] }

theorem u30655 : Upper (D 6) (R 6) [10,33,96,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30656 : Route 9 := (fun mask => (mask,id))

def c30656 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30656 : Upper (D 6) (R 6) [10,33,96,80,129] 13 := by
  apply FastRouting.sound _ _ [10,33,96,80,129] 13 (by decide) (choices 1) [2,4,256] r30656 c30656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12313
  · exact u12314
  · exact u12315

def r30657 : Route 9 := (fun mask => (mask,id))

def c30657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30657 : Upper (D 6) (R 6) [10,33,96,80,130] 13 := by
  apply FastRouting.sound _ _ [10,33,96,80,130] 13 (by decide) (choices 1) [1,4,256] r30657 c30657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12316
  · exact u12317
  · exact u12318

def r30658 : Route 9 := (fun mask => (mask,id))

def c30658 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30658 : Upper (D 6) (R 6) [10,33,96,80,132] 13 := by
  apply FastRouting.sound _ _ [10,33,96,80,132] 13 (by decide) (choices 1) [1,2,4,256] r30658 c30658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12319
  · exact u12320
  · exact u12321
  · exact u12322

def r30659 : Route 9 := (fun mask => (mask,id))

def c30659 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30659 : Upper (D 6) (R 6) [10,33,96,80,384] 13 := by
  apply FastRouting.sound _ _ [10,33,96,80,384] 13 (by decide) (choices 1) [1,2,4] r30659 c30659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12323
  · exact u12324
  · exact u12325

#print axioms u30659
end Delivery.IrregularNine14.P06
