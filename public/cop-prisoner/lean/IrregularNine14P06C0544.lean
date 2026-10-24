import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0253
import IrregularNine14P06C0254
import IrregularNine14P06C0255

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32640 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 131 37 28 82 356 356 484 356), lower := (rows 11 131 37 28 82 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 44 76 140 268), good := (rows 506 146 508 508 82 32 64 128 256) }] }

theorem u32640 : Upper (D 6) (R 6) [10,129,33,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32641 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 37 28 84 354 354 482 354), lower := (rows 11 131 37 28 84 32 64 128 256), losses := [] }

theorem u32641 : Upper (D 6) (R 6) [10,129,33,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32642 : Route 9 := (fun mask => (mask,id))

def c32642 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32642 : Upper (D 6) (R 6) [10,129,33,20,96] 13 := by
  apply FastRouting.sound _ _ [10,129,33,20,96] 13 (by decide) (choices 1) [2,4,64,256] r32642 c32642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15235
  · exact u15236
  · exact u15237
  · exact u15238

def b32643 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 131 37 28 274 100 100 228 356), lower := (rows 11 131 37 28 274 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 44 76 140 268), good := (rows 506 146 508 508 274 32 64 128 256) }] }

theorem u32643 : Upper (D 6) (R 6) [10,129,33,20,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32644 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 37 28 276 98 98 226 354), lower := (rows 11 131 37 28 276 32 64 128 256), losses := [] }

theorem u32644 : Upper (D 6) (R 6) [10,129,33,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32645 : Route 9 := (fun mask => (mask,id))

def c32645 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32645 : Upper (D 6) (R 6) [10,129,33,20,288] 13 := by
  apply FastRouting.sound _ _ [10,129,33,20,288] 13 (by decide) (choices 1) [2,4,64] r32645 c32645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15239
  · exact u15240
  · exact u15241

def r32646 : Route 9 := (fun mask => (mask,id))

def c32646 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32646 : Upper (D 6) (R 6) [10,129,33,20,320] 13 := by
  apply FastRouting.sound _ _ [10,129,33,20,320] 13 (by decide) (choices 1) [2,4,64] r32646 c32646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15242
  · exact u15243
  · exact u15244

def b32647 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 360, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 131 37 56 22 356 324 452 324), lower := (rows 11 131 37 56 22 32 64 128 256), losses := [] }

theorem u32647 : Upper (D 6) (R 6) [10,129,33,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32648 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 131 37 56 82 356 324 452 324), lower := (rows 11 131 37 56 82 32 64 128 256), losses := [] }

theorem u32648 : Upper (D 6) (R 6) [10,129,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32649 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 131 37 56 84 358 326 454 326), lower := (rows 11 131 37 56 84 32 64 128 256), losses := [{ target := 5, region := (rows 9 14 4 8 20 0 84 148 276), good := (rows 11 131 471 475 470 0 64 128 256) }] }

theorem u32649 : Upper (D 6) (R 6) [10,129,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32650 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 131 37 56 274 100 68 196 324), lower := (rows 11 131 37 56 274 32 64 128 256), losses := [] }

theorem u32650 : Upper (D 6) (R 6) [10,129,33,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32651 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 131 37 56 276 102 70 198 326), lower := (rows 11 131 37 56 276 32 64 128 256), losses := [{ target := 5, region := (rows 9 14 4 8 20 0 84 148 276), good := (rows 11 131 471 475 470 0 64 128 256) }] }

theorem u32651 : Upper (D 6) (R 6) [10,129,33,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32652 : Route 9 := (fun mask => (mask,id))

def c32652 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32652 : Upper (D 6) (R 6) [10,129,33,48,320] 13 := by
  apply FastRouting.sound _ _ [10,129,33,48,320] 13 (by decide) (choices 1) [2,4,64] r32652 c32652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15245
  · exact u15246
  · exact u15247

def r32653 : Route 9 := (fun mask => (mask,id))

def c32653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32653 : Upper (D 6) (R 6) [10,129,33,68,6] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,6] 13 (by decide) (choices 1) [16,64,256] r32653 c32653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15248
  · exact u15249
  · exact u15250

def r32654 : Route 9 := (fun mask => (mask,id))

def c32654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32654 : Upper (D 6) (R 6) [10,129,33,68,34] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,34] 13 (by decide) (choices 1) [4,16,64,256] r32654 c32654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15251
  · exact u15252
  · exact u15253
  · exact u15254

def b32655 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 37 76 52 370 338 466 338), lower := (rows 11 131 37 76 52 32 64 128 256), losses := [] }

theorem u32655 : Upper (D 6) (R 6) [10,129,33,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32656 : Route 9 := (fun mask => (mask,id))

def c32656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32656 : Upper (D 6) (R 6) [10,129,33,68,66] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,66] 13 (by decide) (choices 1) [4,16,256] r32656 c32656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15255
  · exact u15256
  · exact u15257

def b32657 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 131 37 76 84 306 370 434 306), lower := (rows 11 131 37 76 84 32 64 128 256), losses := [] }

theorem u32657 : Upper (D 6) (R 6) [10,129,33,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32658 : Route 9 := (fun mask => (mask,id))

def c32658 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32658 : Upper (D 6) (R 6) [10,129,33,68,96] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,96] 13 (by decide) (choices 1) [2,4,16,256] r32658 c32658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15258
  · exact u15259
  · exact u15260
  · exact u15261

def r32659 : Route 9 := (fun mask => (mask,id))

def c32659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32659 : Upper (D 6) (R 6) [10,129,33,68,258] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,258] 13 (by decide) (choices 1) [4,16,64] r32659 c32659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15262
  · exact u15263
  · exact u15264

def r32660 : Route 9 := (fun mask => (mask,id))

def c32660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32660 : Upper (D 6) (R 6) [10,129,33,68,260] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,260] 13 (by decide) (choices 1) [2,16,64] r32660 c32660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15265
  · exact u15266
  · exact u15267

def r32661 : Route 9 := (fun mask => (mask,id))

def c32661 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32661 : Upper (D 6) (R 6) [10,129,33,68,288] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,288] 13 (by decide) (choices 1) [2,4,16,64] r32661 c32661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15268
  · exact u15269
  · exact u15270
  · exact u15271

def r32662 : Route 9 := (fun mask => (mask,id))

def c32662 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32662 : Upper (D 6) (R 6) [10,129,33,68,320] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,320] 13 (by decide) (choices 1) [2,4,16] r32662 c32662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15272
  · exact u15273
  · exact u15274

def b32663 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 37 88 22 356 356 484 356), lower := (rows 11 131 37 88 22 32 64 128 256), losses := [] }

theorem u32663 : Upper (D 6) (R 6) [10,129,33,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32664 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 131 37 88 50 356 324 452 324), lower := (rows 11 131 37 88 50 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 55 87 151 279), good := (rows 493 485 485 504 508 32 64 128 256) }] }

theorem u32664 : Upper (D 6) (R 6) [10,129,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32665 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 37 88 52 358 326 454 326), lower := (rows 11 131 37 88 52 32 64 128 256), losses := [] }

theorem u32665 : Upper (D 6) (R 6) [10,129,33,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32666 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 131 37 88 82 292 356 420 292), lower := (rows 11 131 37 88 82 32 64 128 256), losses := [] }

theorem u32666 : Upper (D 6) (R 6) [10,129,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32667 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 37 88 84 294 358 422 294), lower := (rows 11 131 37 88 84 32 64 128 256), losses := [] }

theorem u32667 : Upper (D 6) (R 6) [10,129,33,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32668 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 37 88 112 294 326 390 262), lower := (rows 11 131 37 88 112 32 64 128 256), losses := [] }

theorem u32668 : Upper (D 6) (R 6) [10,129,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32669 : Route 9 := (fun mask => (mask,id))

def c32669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32669 : Upper (D 6) (R 6) [10,129,33,80,258] 13 := by
  apply FastRouting.sound _ _ [10,129,33,80,258] 13 (by decide) (choices 1) [4,64] r32669 c32669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15275
  · exact u15276

def r32670 : Route 9 := (fun mask => (mask,id))

def c32670 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32670 : Upper (D 6) (R 6) [10,129,33,80,260] 13 := by
  apply FastRouting.sound _ _ [10,129,33,80,260] 13 (by decide) (choices 1) [2,4,64] r32670 c32670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15277
  · exact u15278
  · exact u15279

def r32671 : Route 9 := (fun mask => (mask,id))

def c32671 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32671 : Upper (D 6) (R 6) [10,129,33,80,288] 13 := by
  apply FastRouting.sound _ _ [10,129,33,80,288] 13 (by decide) (choices 1) [2,4,64] r32671 c32671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15280
  · exact u15281
  · exact u15282

def b32672 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 37 88 336 38 102 166 294), lower := (rows 11 131 37 88 336 32 64 128 256), losses := [] }

theorem u32672 : Upper (D 6) (R 6) [10,129,33,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32673 : PairBound 9 := { available := 340, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 360, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 131 37 104 22 372 340 468 340), lower := (rows 11 131 37 104 22 32 64 128 256), losses := [] }

theorem u32673 : Upper (D 6) (R 6) [10,129,33,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32674 : Route 9 := (fun mask => (mask,id))

def c32674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32674 : Upper (D 6) (R 6) [10,129,33,96,66] 13 := by
  apply FastRouting.sound _ _ [10,129,33,96,66] 13 (by decide) (choices 1) [4,16,256] r32674 c32674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15283
  · exact u15284
  · exact u15285

def r32675 : Route 9 := (fun mask => (mask,id))

def c32675 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32675 : Upper (D 6) (R 6) [10,129,33,96,68] 13 := by
  apply FastRouting.sound _ _ [10,129,33,96,68] 13 (by decide) (choices 1) [2,4,16,256] r32675 c32675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15286
  · exact u15287
  · exact u15288
  · exact u15289

def r32676 : Route 9 := (fun mask => (mask,id))

def c32676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32676 : Upper (D 6) (R 6) [10,129,33,96,258] 13 := by
  apply FastRouting.sound _ _ [10,129,33,96,258] 13 (by decide) (choices 1) [4,16,64] r32676 c32676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15290
  · exact u15291
  · exact u15292

def r32677 : Route 9 := (fun mask => (mask,id))

def c32677 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32677 : Upper (D 6) (R 6) [10,129,33,96,260] 13 := by
  apply FastRouting.sound _ _ [10,129,33,96,260] 13 (by decide) (choices 1) [2,4,16,64] r32677 c32677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15293
  · exact u15294
  · exact u15295
  · exact u15296

def r32678 : Route 9 := (fun mask => (mask,id))

def c32678 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32678 : Upper (D 6) (R 6) [10,129,33,96,320] 13 := by
  apply FastRouting.sound _ _ [10,129,33,96,320] 13 (by decide) (choices 1) [2,4,16] r32678 c32678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15297
  · exact u15298
  · exact u15299

def r32679 : Route 9 := (fun mask => (mask,id))

def c32679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32679 : Upper (D 6) (R 6) [10,129,33,260,6] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,6] 13 (by decide) (choices 1) [16,64] r32679 c32679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15300
  · exact u15301

def r32680 : Route 9 := (fun mask => (mask,id))

def c32680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32680 : Upper (D 6) (R 6) [10,129,33,260,34] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,34] 13 (by decide) (choices 1) [4,16,64] r32680 c32680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15302
  · exact u15303
  · exact u15304

def b32681 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 37 268 52 114 82 210 338), lower := (rows 11 131 37 268 52 32 64 128 256), losses := [] }

theorem u32681 : Upper (D 6) (R 6) [10,129,33,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32682 : Route 9 := (fun mask => (mask,id))

def c32682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32682 : Upper (D 6) (R 6) [10,129,33,260,66] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,66] 13 (by decide) (choices 1) [4,16,64] r32682 c32682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15305
  · exact u15306
  · exact u15307

def r32683 : Route 9 := (fun mask => (mask,id))

def c32683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32683 : Upper (D 6) (R 6) [10,129,33,260,68] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,68] 13 (by decide) (choices 1) [2,16,64] r32683 c32683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15308
  · exact u15309
  · exact u15310

def r32684 : Route 9 := (fun mask => (mask,id))

def c32684 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32684 : Upper (D 6) (R 6) [10,129,33,260,96] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,96] 13 (by decide) (choices 1) [2,4,16,64] r32684 c32684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15311
  · exact u15312
  · exact u15313
  · exact u15314

def b32685 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 37 280 22 100 100 228 356), lower := (rows 11 131 37 280 22 32 64 128 256), losses := [] }

theorem u32685 : Upper (D 6) (R 6) [10,129,33,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32686 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 131 37 280 50 100 68 196 324), lower := (rows 11 131 37 280 50 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 55 87 151 279), good := (rows 493 485 485 504 508 32 64 128 256) }] }

theorem u32686 : Upper (D 6) (R 6) [10,129,33,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32687 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 37 280 52 102 70 198 326), lower := (rows 11 131 37 280 52 32 64 128 256), losses := [] }

theorem u32687 : Upper (D 6) (R 6) [10,129,33,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32688 : Route 9 := (fun mask => (mask,id))

def c32688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32688 : Upper (D 6) (R 6) [10,129,33,272,66] 13 := by
  apply FastRouting.sound _ _ [10,129,33,272,66] 13 (by decide) (choices 1) [4,64] r32688 c32688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15315
  · exact u15316

def r32689 : Route 9 := (fun mask => (mask,id))

def c32689 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32689 : Upper (D 6) (R 6) [10,129,33,272,68] 13 := by
  apply FastRouting.sound _ _ [10,129,33,272,68] 13 (by decide) (choices 1) [2,4,64] r32689 c32689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15317
  · exact u15318
  · exact u15319

def r32690 : Route 9 := (fun mask => (mask,id))

def c32690 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32690 : Upper (D 6) (R 6) [10,129,33,272,96] 13 := by
  apply FastRouting.sound _ _ [10,129,33,272,96] 13 (by decide) (choices 1) [2,4,64] r32690 c32690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15320
  · exact u15321
  · exact u15322

def b32691 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 360, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 131 37 296 22 116 84 212 340), lower := (rows 11 131 37 296 22 32 64 128 256), losses := [] }

theorem u32691 : Upper (D 6) (R 6) [10,129,33,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32692 : Route 9 := (fun mask => (mask,id))

def c32692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32692 : Upper (D 6) (R 6) [10,129,33,288,66] 13 := by
  apply FastRouting.sound _ _ [10,129,33,288,66] 13 (by decide) (choices 1) [4,16,64] r32692 c32692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15323
  · exact u15324
  · exact u15325

def r32693 : Route 9 := (fun mask => (mask,id))

def c32693 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32693 : Upper (D 6) (R 6) [10,129,33,288,68] 13 := by
  apply FastRouting.sound _ _ [10,129,33,288,68] 13 (by decide) (choices 1) [2,4,16,64] r32693 c32693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15326
  · exact u15327
  · exact u15328
  · exact u15329

def r32694 : Route 9 := (fun mask => (mask,id))

def c32694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32694 : Upper (D 6) (R 6) [10,129,33,320,6] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320,6] 13 (by decide) (choices 1) [4,16,64] r32694 c32694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15330
  · exact u15331
  · exact u15332

def r32695 : Route 9 := (fun mask => (mask,id))

def c32695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32695 : Upper (D 6) (R 6) [10,129,33,320,34] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320,34] 13 (by decide) (choices 1) [4,16,64] r32695 c32695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15333
  · exact u15334
  · exact u15335

def b32696 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 37 328 52 118 86 214 342), lower := (rows 11 131 37 328 52 32 64 128 256), losses := [] }

theorem u32696 : Upper (D 6) (R 6) [10,129,33,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32697 : Route 9 := (fun mask => (mask,id))

def c32697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32697 : Upper (D 6) (R 6) [10,129,33,320,66] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320,66] 13 (by decide) (choices 1) [4,16] r32697 c32697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15336
  · exact u15337

def r32698 : Route 9 := (fun mask => (mask,id))

def c32698 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32698 : Upper (D 6) (R 6) [10,129,33,320,68] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320,68] 13 (by decide) (choices 1) [2,4,16] r32698 c32698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15338
  · exact u15339
  · exact u15340

def r32699 : Route 9 := (fun mask => (mask,id))

def c32699 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32699 : Upper (D 6) (R 6) [10,129,33,320,96] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320,96] 13 (by decide) (choices 1) [2,4,16] r32699 c32699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15341
  · exact u15342
  · exact u15343

#print axioms u32699
end Delivery.IrregularNine14.P06
