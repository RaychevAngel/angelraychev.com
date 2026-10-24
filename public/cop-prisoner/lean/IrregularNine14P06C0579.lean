import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0306
import IrregularNine14P06C0307

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34740 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 460, targets := 32 },{ cop := 3, region := 368, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 25 35 133 14 112 358 326 454 326), lower := (rows 25 35 133 14 112 32 64 128 256), losses := [] }

theorem u34740 : Upper (D 6) (R 6) [24,33,129,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34741 : Route 9 := (fun mask => (mask,id))

def c34741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34741 : Upper (D 6) (R 6) [24,33,129,6,258] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6,258] 13 (by decide) (choices 1) [4,64] r34741 c34741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18392
  · exact u18393

def r34742 : Route 9 := (fun mask => (mask,id))

def c34742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34742 : Upper (D 6) (R 6) [24,33,129,6,260] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6,260] 13 (by decide) (choices 1) [2,64] r34742 c34742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18394
  · exact u18395

def b34743 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 3, region := 368, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 25 35 133 14 304 102 70 198 326), lower := (rows 25 35 133 14 304 32 64 128 256), losses := [] }

theorem u34743 : Upper (D 6) (R 6) [24,33,129,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34744 : Route 9 := (fun mask => (mask,id))

def c34744 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34744 : Upper (D 6) (R 6) [24,33,129,6,320] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6,320] 13 (by decide) (choices 1) [2,4,64] r34744 c34744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18396
  · exact u18397
  · exact u18398

def b34745 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 133 42 82 356 324 452 324), lower := (rows 25 35 133 42 82 32 64 128 256), losses := [] }

theorem u34745 : Upper (D 6) (R 6) [24,33,129,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34746 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 133 42 84 358 326 454 326), lower := (rows 25 35 133 42 84 32 64 128 256), losses := [] }

theorem u34746 : Upper (D 6) (R 6) [24,33,129,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34747 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 133 42 274 100 68 196 324), lower := (rows 25 35 133 42 274 32 64 128 256), losses := [] }

theorem u34747 : Upper (D 6) (R 6) [24,33,129,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34748 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 133 42 276 102 70 198 326), lower := (rows 25 35 133 42 276 32 64 128 256), losses := [] }

theorem u34748 : Upper (D 6) (R 6) [24,33,129,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34749 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 133 42 336 102 70 198 326), lower := (rows 25 35 133 42 336 32 64 128 256), losses := [] }

theorem u34749 : Upper (D 6) (R 6) [24,33,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34750 : Route 9 := (fun mask => (mask,id))

def c34750 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34750 : Upper (D 6) (R 6) [24,33,129,36,66] 13 := by
  apply FastRouting.sound _ _ [24,33,129,36,66] 13 (by decide) (choices 1) [2,4,64,256] r34750 c34750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18399
  · exact u18400
  · exact u18401
  · exact u18402

def b34751 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 133 44 84 354 322 450 322), lower := (rows 25 35 133 44 84 32 64 128 256), losses := [] }

theorem u34751 : Upper (D 6) (R 6) [24,33,129,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34752 : Route 9 := (fun mask => (mask,id))

def c34752 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34752 : Upper (D 6) (R 6) [24,33,129,36,258] 13 := by
  apply FastRouting.sound _ _ [24,33,129,36,258] 13 (by decide) (choices 1) [2,4,64] r34752 c34752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18403
  · exact u18404
  · exact u18405

def b34753 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 133 44 276 98 66 194 322), lower := (rows 25 35 133 44 276 32 64 128 256), losses := [] }

theorem u34753 : Upper (D 6) (R 6) [24,33,129,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34754 : Route 9 := (fun mask => (mask,id))

def c34754 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34754 : Upper (D 6) (R 6) [24,33,129,36,320] 13 := by
  apply FastRouting.sound _ _ [24,33,129,36,320] 13 (by decide) (choices 1) [2,4,64] r34754 c34754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18406
  · exact u18407
  · exact u18408

def b34755 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 133 74 82 292 356 420 292), lower := (rows 25 35 133 74 82 32 64 128 256), losses := [] }

theorem u34755 : Upper (D 6) (R 6) [24,33,129,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34756 : Route 9 := (fun mask => (mask,id))

def c34756 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34756 : Upper (D 6) (R 6) [24,33,129,66,68] 13 := by
  apply FastRouting.sound _ _ [24,33,129,66,68] 13 (by decide) (choices 1) [2,4,256] r34756 c34756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18409
  · exact u18410
  · exact u18411

def b34757 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 133 74 112 294 326 390 262), lower := (rows 25 35 133 74 112 32 64 128 256), losses := [] }

theorem u34757 : Upper (D 6) (R 6) [24,33,129,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34758 : Route 9 := (fun mask => (mask,id))

def c34758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34758 : Upper (D 6) (R 6) [24,33,129,66,258] 13 := by
  apply FastRouting.sound _ _ [24,33,129,66,258] 13 (by decide) (choices 1) [4,64] r34758 c34758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18412
  · exact u18413

def r34759 : Route 9 := (fun mask => (mask,id))

def c34759 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34759 : Upper (D 6) (R 6) [24,33,129,66,260] 13 := by
  apply FastRouting.sound _ _ [24,33,129,66,260] 13 (by decide) (choices 1) [2,4,64] r34759 c34759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18414
  · exact u18415
  · exact u18416

def r34760 : Route 9 := (fun mask => (mask,id))

def c34760 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34760 : Upper (D 6) (R 6) [24,33,129,66,288] 13 := by
  apply FastRouting.sound _ _ [24,33,129,66,288] 13 (by decide) (choices 1) [2,4,64] r34760 c34760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18417
  · exact u18418
  · exact u18419

def r34761 : Route 9 := (fun mask => (mask,id))

def c34761 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34761 : Upper (D 6) (R 6) [24,33,129,66,320] 13 := by
  apply FastRouting.sound _ _ [24,33,129,66,320] 13 (by decide) (choices 1) [2,4] r34761 c34761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18420
  · exact u18421

def b34762 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 17, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 133 76 84 290 354 418 290), lower := (rows 25 35 133 76 84 32 64 128 256), losses := [] }

theorem u34762 : Upper (D 6) (R 6) [24,33,129,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34763 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 1, region := 388, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 25 35 133 76 112 294 326 390 262), lower := (rows 25 35 133 76 112 32 64 128 256), losses := [] }

theorem u34763 : Upper (D 6) (R 6) [24,33,129,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34764 : Route 9 := (fun mask => (mask,id))

def c34764 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34764 : Upper (D 6) (R 6) [24,33,129,68,258] 13 := by
  apply FastRouting.sound _ _ [24,33,129,68,258] 13 (by decide) (choices 1) [2,4,64] r34764 c34764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18422
  · exact u18423
  · exact u18424

def r34765 : Route 9 := (fun mask => (mask,id))

def c34765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34765 : Upper (D 6) (R 6) [24,33,129,68,260] 13 := by
  apply FastRouting.sound _ _ [24,33,129,68,260] 13 (by decide) (choices 1) [2,64] r34765 c34765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18425
  · exact u18426

def r34766 : Route 9 := (fun mask => (mask,id))

def c34766 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34766 : Upper (D 6) (R 6) [24,33,129,68,288] 13 := by
  apply FastRouting.sound _ _ [24,33,129,68,288] 13 (by decide) (choices 1) [2,4,64] r34766 c34766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18427
  · exact u18428
  · exact u18429

def r34767 : Route 9 := (fun mask => (mask,id))

def c34767 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34767 : Upper (D 6) (R 6) [24,33,129,68,320] 13 := by
  apply FastRouting.sound _ _ [24,33,129,68,320] 13 (by decide) (choices 1) [2,4] r34767 c34767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18430
  · exact u18431

def r34768 : Route 9 := (fun mask => (mask,id))

def c34768 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34768 : Upper (D 6) (R 6) [24,33,129,96,258] 13 := by
  apply FastRouting.sound _ _ [24,33,129,96,258] 13 (by decide) (choices 1) [2,4,64] r34768 c34768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18432
  · exact u18433
  · exact u18434

def r34769 : Route 9 := (fun mask => (mask,id))

def c34769 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34769 : Upper (D 6) (R 6) [24,33,129,96,260] 13 := by
  apply FastRouting.sound _ _ [24,33,129,96,260] 13 (by decide) (choices 1) [2,4,64] r34769 c34769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18435
  · exact u18436
  · exact u18437

def b34770 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 1, region := 132, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 25 35 133 104 336 38 70 134 262), lower := (rows 25 35 133 104 336 32 64 128 256), losses := [] }

theorem u34770 : Upper (D 6) (R 6) [24,33,129,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34771 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 134 11 52 356 324 452 324), lower := (rows 25 35 134 11 52 32 64 128 256), losses := [] }

theorem u34771 : Upper (D 6) (R 6) [24,33,130,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34772 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 134 11 84 356 356 484 356), lower := (rows 25 35 134 11 84 32 64 128 256), losses := [] }

theorem u34772 : Upper (D 6) (R 6) [24,33,130,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34773 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 134 11 112 356 324 452 324), lower := (rows 25 35 134 11 112 32 64 128 256), losses := [] }

theorem u34773 : Upper (D 6) (R 6) [24,33,130,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34774 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 134 11 276 100 100 228 356), lower := (rows 25 35 134 11 276 32 64 128 256), losses := [] }

theorem u34774 : Upper (D 6) (R 6) [24,33,130,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34775 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 134 11 304 100 68 196 324), lower := (rows 25 35 134 11 304 32 64 128 256), losses := [] }

theorem u34775 : Upper (D 6) (R 6) [24,33,130,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34776 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 134 11 336 100 100 228 356), lower := (rows 25 35 134 11 336 32 64 128 256), losses := [] }

theorem u34776 : Upper (D 6) (R 6) [24,33,130,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34777 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 35 134 13 22 352 352 480 352), lower := (rows 25 35 134 13 22 32 64 128 256), losses := [] }

theorem u34777 : Upper (D 6) (R 6) [24,33,130,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34778 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 35 134 13 50 356 324 452 324), lower := (rows 25 35 134 13 50 32 64 128 256), losses := [] }

theorem u34778 : Upper (D 6) (R 6) [24,33,130,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34779 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 134 13 52 354 322 450 322), lower := (rows 25 35 134 13 52 32 64 128 256), losses := [] }

theorem u34779 : Upper (D 6) (R 6) [24,33,130,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34780 : Route 9 := (fun mask => (mask,id))

def c34780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34780 : Upper (D 6) (R 6) [24,33,130,5,66] 13 := by
  apply FastRouting.sound _ _ [24,33,130,5,66] 13 (by decide) (choices 1) [4,64,256] r34780 c34780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18438
  · exact u18439
  · exact u18440

def b34781 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 134 13 84 354 354 482 354), lower := (rows 25 35 134 13 84 32 64 128 256), losses := [] }

theorem u34781 : Upper (D 6) (R 6) [24,33,130,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34782 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 134 13 112 358 326 454 326), lower := (rows 25 35 134 13 112 32 64 128 256), losses := [] }

theorem u34782 : Upper (D 6) (R 6) [24,33,130,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34783 : Route 9 := (fun mask => (mask,id))

def c34783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34783 : Upper (D 6) (R 6) [24,33,130,5,258] 13 := by
  apply FastRouting.sound _ _ [24,33,130,5,258] 13 (by decide) (choices 1) [4,64] r34783 c34783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18441
  · exact u18442

def b34784 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 134 13 276 98 98 226 354), lower := (rows 25 35 134 13 276 32 64 128 256), losses := [] }

theorem u34784 : Upper (D 6) (R 6) [24,33,130,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34785 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 134 13 304 102 70 198 326), lower := (rows 25 35 134 13 304 32 64 128 256), losses := [] }

theorem u34785 : Upper (D 6) (R 6) [24,33,130,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34786 : Route 9 := (fun mask => (mask,id))

def c34786 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34786 : Upper (D 6) (R 6) [24,33,130,5,320] 13 := by
  apply FastRouting.sound _ _ [24,33,130,5,320] 13 (by decide) (choices 1) [2,4,64] r34786 c34786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18443
  · exact u18444
  · exact u18445

def b34787 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 134 14 52 353 321 449 321), lower := (rows 25 35 134 14 52 32 64 128 256), losses := [] }

theorem u34787 : Upper (D 6) (R 6) [24,33,130,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34788 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 2, region := 8, targets := 32 }], pairs := [(2,0),(3,0),(3,5)], upper := (rows 25 35 134 14 81 356 356 484 356), lower := (rows 25 35 134 14 81 32 64 128 256), losses := [] }

theorem u34788 : Upper (D 6) (R 6) [24,33,130,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34789 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 134 14 84 353 353 481 353), lower := (rows 25 35 134 14 84 32 64 128 256), losses := [] }

theorem u34789 : Upper (D 6) (R 6) [24,33,130,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34790 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 134 14 112 357 325 453 325), lower := (rows 25 35 134 14 112 32 64 128 256), losses := [] }

theorem u34790 : Upper (D 6) (R 6) [24,33,130,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34791 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 2, region := 8, targets := 32 }], pairs := [(2,0),(3,0),(3,5)], upper := (rows 25 35 134 14 273 100 100 228 356), lower := (rows 25 35 134 14 273 32 64 128 256), losses := [] }

theorem u34791 : Upper (D 6) (R 6) [24,33,130,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34792 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 134 14 276 97 97 225 353), lower := (rows 25 35 134 14 276 32 64 128 256), losses := [] }

theorem u34792 : Upper (D 6) (R 6) [24,33,130,6,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34793 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 134 14 304 101 69 197 325), lower := (rows 25 35 134 14 304 32 64 128 256), losses := [] }

theorem u34793 : Upper (D 6) (R 6) [24,33,130,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34794 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 134 14 336 101 101 229 357), lower := (rows 25 35 134 14 336 32 64 128 256), losses := [] }

theorem u34794 : Upper (D 6) (R 6) [24,33,130,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34795 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 134 41 82 356 324 452 324), lower := (rows 25 35 134 41 82 32 64 128 256), losses := [] }

theorem u34795 : Upper (D 6) (R 6) [24,33,130,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34796 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 134 41 84 358 326 454 326), lower := (rows 25 35 134 41 84 32 64 128 256), losses := [] }

theorem u34796 : Upper (D 6) (R 6) [24,33,130,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34797 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 134 41 274 100 68 196 324), lower := (rows 25 35 134 41 274 32 64 128 256), losses := [] }

theorem u34797 : Upper (D 6) (R 6) [24,33,130,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34798 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 134 41 276 102 70 198 326), lower := (rows 25 35 134 41 276 32 64 128 256), losses := [] }

theorem u34798 : Upper (D 6) (R 6) [24,33,130,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34799 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 134 41 336 102 70 198 326), lower := (rows 25 35 134 41 336 32 64 128 256), losses := [] }

theorem u34799 : Upper (D 6) (R 6) [24,33,130,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34799
end Delivery.IrregularNine14.P06
