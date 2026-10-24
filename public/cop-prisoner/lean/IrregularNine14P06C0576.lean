import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0303
import IrregularNine14P06C0304

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34560 : Route 9 := (fun mask => (mask,id))

def c34560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34560 : Upper (D 6) (R 6) [10,384,48,68,66] 13 := by
  apply FastRouting.sound _ _ [10,384,48,68,66] 13 (by decide) (choices 1) [1,4] r34560 c34560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18211
  · exact u18212

def b34561 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 386 52 76 84 35 99 163 291), lower := (rows 11 386 52 76 84 32 64 128 256), losses := [] }

theorem u34561 : Upper (D 6) (R 6) [10,384,48,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34562 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 386 52 76 112 39 71 135 263), lower := (rows 11 386 52 76 112 32 64 128 256), losses := [] }

theorem u34562 : Upper (D 6) (R 6) [10,384,48,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34563 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 52 104 19 101 69 197 325), lower := (rows 11 386 52 104 19 32 64 128 256), losses := [] }

theorem u34563 : Upper (D 6) (R 6) [10,384,48,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34564 : Route 9 := (fun mask => (mask,id))

def c34564 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34564 : Upper (D 6) (R 6) [10,384,48,96,5] 13 := by
  apply FastRouting.sound _ _ [10,384,48,96,5] 13 (by decide) (choices 1) [1,2,4,64] r34564 c34564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18213
  · exact u18214
  · exact u18215
  · exact u18216

def r34565 : Route 9 := (fun mask => (mask,id))

def c34565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34565 : Upper (D 6) (R 6) [10,384,48,96,6] 13 := by
  apply FastRouting.sound _ _ [10,384,48,96,6] 13 (by decide) (choices 1) [1,4,64] r34565 c34565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18217
  · exact u18218
  · exact u18219

def r34566 : Route 9 := (fun mask => (mask,id))

def c34566 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34566 : Upper (D 6) (R 6) [10,384,48,96,65] 13 := by
  apply FastRouting.sound _ _ [10,384,48,96,65] 13 (by decide) (choices 1) [1,2,4] r34566 c34566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18220
  · exact u18221
  · exact u18222

def r34567 : Route 9 := (fun mask => (mask,id))

def c34567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34567 : Upper (D 6) (R 6) [10,384,48,96,66] 13 := by
  apply FastRouting.sound _ _ [10,384,48,96,66] 13 (by decide) (choices 1) [1,4] r34567 c34567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18223
  · exact u18224

def b34568 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 386 52 104 84 39 71 135 263), lower := (rows 11 386 52 104 84 32 64 128 256), losses := [] }

theorem u34568 : Upper (D 6) (R 6) [10,384,48,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34569 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 100 13 19 116 116 244 372), lower := (rows 11 386 100 13 19 32 64 128 256), losses := [] }

theorem u34569 : Upper (D 6) (R 6) [10,384,96,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34570 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 386 100 13 21 114 114 242 370), lower := (rows 11 386 100 13 21 32 64 128 256), losses := [] }

theorem u34570 : Upper (D 6) (R 6) [10,384,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34571 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 100 13 22 113 113 241 369), lower := (rows 11 386 100 13 22 32 64 128 256), losses := [] }

theorem u34571 : Upper (D 6) (R 6) [10,384,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34572 : Route 9 := (fun mask => (mask,id))

def c34572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34572 : Upper (D 6) (R 6) [10,384,96,5,33] 13 := by
  apply FastRouting.sound _ _ [10,384,96,5,33] 13 (by decide) (choices 1) [2,4,16,64] r34572 c34572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18225
  · exact u18226
  · exact u18227
  · exact u18228

def r34573 : Route 9 := (fun mask => (mask,id))

def c34573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34573 : Upper (D 6) (R 6) [10,384,96,5,34] 13 := by
  apply FastRouting.sound _ _ [10,384,96,5,34] 13 (by decide) (choices 1) [1,4,16,64] r34573 c34573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18229
  · exact u18230
  · exact u18231
  · exact u18232

def b34574 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 386 100 13 52 115 83 211 339), lower := (rows 11 386 100 13 52 32 64 128 256), losses := [] }

theorem u34574 : Upper (D 6) (R 6) [10,384,96,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34575 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 386 100 13 112 55 87 151 279), lower := (rows 11 386 100 13 112 32 64 128 256), losses := [] }

theorem u34575 : Upper (D 6) (R 6) [10,384,96,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34576 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 100 25 19 100 100 228 356), lower := (rows 11 386 100 25 19 32 64 128 256), losses := [] }

theorem u34576 : Upper (D 6) (R 6) [10,384,96,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34577 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 386 100 25 21 102 102 230 358), lower := (rows 11 386 100 25 21 32 64 128 256), losses := [] }

theorem u34577 : Upper (D 6) (R 6) [10,384,96,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34578 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 100 25 22 101 101 229 357), lower := (rows 11 386 100 25 22 32 64 128 256), losses := [] }

theorem u34578 : Upper (D 6) (R 6) [10,384,96,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34579 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 386 100 25 49 102 70 198 326), lower := (rows 11 386 100 25 49 32 64 128 256), losses := [] }

theorem u34579 : Upper (D 6) (R 6) [10,384,96,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34580 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 100 25 50 101 69 197 325), lower := (rows 11 386 100 25 50 32 64 128 256), losses := [] }

theorem u34580 : Upper (D 6) (R 6) [10,384,96,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34581 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 386 100 25 52 103 71 199 327), lower := (rows 11 386 100 25 52 32 64 128 256), losses := [] }

theorem u34581 : Upper (D 6) (R 6) [10,384,96,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34582 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 386 100 25 112 39 71 135 263), lower := (rows 11 386 100 25 112 32 64 128 256), losses := [] }

theorem u34582 : Upper (D 6) (R 6) [10,384,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34583 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 100 28 19 101 101 229 357), lower := (rows 11 386 100 28 19 32 64 128 256), losses := [] }

theorem u34583 : Upper (D 6) (R 6) [10,384,96,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34584 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 386 100 28 21 99 99 227 355), lower := (rows 11 386 100 28 21 32 64 128 256), losses := [] }

theorem u34584 : Upper (D 6) (R 6) [10,384,96,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34585 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 100 28 22 97 97 225 353), lower := (rows 11 386 100 28 22 32 64 128 256), losses := [] }

theorem u34585 : Upper (D 6) (R 6) [10,384,96,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34586 : Route 9 := (fun mask => (mask,id))

def c34586 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34586 : Upper (D 6) (R 6) [10,384,96,20,33] 13 := by
  apply FastRouting.sound _ _ [10,384,96,20,33] 13 (by decide) (choices 1) [1,2,4,64] r34586 c34586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18233
  · exact u18234
  · exact u18235
  · exact u18236

def b34587 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 451, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 11 386 100 28 50 101 69 197 325), lower := (rows 11 386 100 28 50 32 64 128 256), losses := [] }

theorem u34587 : Upper (D 6) (R 6) [10,384,96,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34588 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 386 100 28 52 99 67 195 323), lower := (rows 11 386 100 28 52 32 64 128 256), losses := [] }

theorem u34588 : Upper (D 6) (R 6) [10,384,96,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34589 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 386 100 28 112 39 71 135 263), lower := (rows 11 386 100 28 112 32 64 128 256), losses := [] }

theorem u34589 : Upper (D 6) (R 6) [10,384,96,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34590 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 100 41 19 116 84 212 340), lower := (rows 11 386 100 41 19 32 64 128 256), losses := [] }

theorem u34590 : Upper (D 6) (R 6) [10,384,96,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34591 : PairBound 9 := { available := 86, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 386 100 41 21 118 86 214 342), lower := (rows 11 386 100 41 21 32 64 128 256), losses := [] }

theorem u34591 : Upper (D 6) (R 6) [10,384,96,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34592 : Route 9 := (fun mask => (mask,id))

def c34592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34592 : Upper (D 6) (R 6) [10,384,96,33,6] 13 := by
  apply FastRouting.sound _ _ [10,384,96,33,6] 13 (by decide) (choices 1) [1,4,16,64] r34592 c34592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18237
  · exact u18238
  · exact u18239
  · exact u18240

def r34593 : Route 9 := (fun mask => (mask,id))

def c34593 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34593 : Upper (D 6) (R 6) [10,384,96,33,65] 13 := by
  apply FastRouting.sound _ _ [10,384,96,33,65] 13 (by decide) (choices 1) [2,4,16] r34593 c34593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18241
  · exact u18242
  · exact u18243

def r34594 : Route 9 := (fun mask => (mask,id))

def c34594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34594 : Upper (D 6) (R 6) [10,384,96,33,66] 13 := by
  apply FastRouting.sound _ _ [10,384,96,33,66] 13 (by decide) (choices 1) [1,4,16] r34594 c34594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18244
  · exact u18245
  · exact u18246

def b34595 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 386 100 41 84 55 87 151 279), lower := (rows 11 386 100 41 84 32 64 128 256), losses := [] }

theorem u34595 : Upper (D 6) (R 6) [10,384,96,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34596 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 100 56 19 101 69 197 325), lower := (rows 11 386 100 56 19 32 64 128 256), losses := [] }

theorem u34596 : Upper (D 6) (R 6) [10,384,96,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34597 : Route 9 := (fun mask => (mask,id))

def c34597 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34597 : Upper (D 6) (R 6) [10,384,96,48,5] 13 := by
  apply FastRouting.sound _ _ [10,384,96,48,5] 13 (by decide) (choices 1) [1,2,4,64] r34597 c34597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18247
  · exact u18248
  · exact u18249
  · exact u18250

def r34598 : Route 9 := (fun mask => (mask,id))

def c34598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34598 : Upper (D 6) (R 6) [10,384,96,48,6] 13 := by
  apply FastRouting.sound _ _ [10,384,96,48,6] 13 (by decide) (choices 1) [1,4,64] r34598 c34598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18251
  · exact u18252
  · exact u18253

def r34599 : Route 9 := (fun mask => (mask,id))

def c34599 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34599 : Upper (D 6) (R 6) [10,384,96,48,65] 13 := by
  apply FastRouting.sound _ _ [10,384,96,48,65] 13 (by decide) (choices 1) [1,2,4] r34599 c34599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18254
  · exact u18255
  · exact u18256

def r34600 : Route 9 := (fun mask => (mask,id))

def c34600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34600 : Upper (D 6) (R 6) [10,384,96,48,66] 13 := by
  apply FastRouting.sound _ _ [10,384,96,48,66] 13 (by decide) (choices 1) [1,4] r34600 c34600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18257
  · exact u18258

def b34601 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 386 100 56 84 39 71 135 263), lower := (rows 11 386 100 56 84 32 64 128 256), losses := [] }

theorem u34601 : Upper (D 6) (R 6) [10,384,96,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34602 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 35 69 14 22 480 480 480 480), lower := (rows 25 35 69 14 22 32 64 128 256), losses := [] }

theorem u34602 : Upper (D 6) (R 6) [24,33,65,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34603 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 35 69 14 50 484 452 452 452), lower := (rows 25 35 69 14 50 32 64 128 256), losses := [] }

theorem u34603 : Upper (D 6) (R 6) [24,33,65,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34604 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 69 14 52 482 450 450 450), lower := (rows 25 35 69 14 52 32 64 128 256), losses := [] }

theorem u34604 : Upper (D 6) (R 6) [24,33,65,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34605 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 460, targets := 32 },{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6),(2,5),(3,5)], upper := (rows 25 35 69 14 112 422 454 390 390), lower := (rows 25 35 69 14 112 32 64 128 256), losses := [] }

theorem u34605 : Upper (D 6) (R 6) [24,33,65,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34606 : Route 9 := (fun mask => (mask,id))

def c34606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34606 : Upper (D 6) (R 6) [24,33,65,6,130] 13 := by
  apply FastRouting.sound _ _ [24,33,65,6,130] 13 (by decide) (choices 1) [4,64,256] r34606 c34606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18259
  · exact u18260
  · exact u18261

def b34607 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 332, targets := 32 },{ cop := 3, region := 496, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 25 35 69 14 176 358 326 454 326), lower := (rows 25 35 69 14 176 32 64 128 256), losses := [] }

theorem u34607 : Upper (D 6) (R 6) [24,33,65,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34608 : Route 9 := (fun mask => (mask,id))

def c34608 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34608 : Upper (D 6) (R 6) [24,33,65,6,384] 13 := by
  apply FastRouting.sound _ _ [24,33,65,6,384] 13 (by decide) (choices 1) [2,4,64] r34608 c34608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18262
  · exact u18263
  · exact u18264

def b34609 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 69 42 82 420 452 388 388), lower := (rows 25 35 69 42 82 32 64 128 256), losses := [] }

theorem u34609 : Upper (D 6) (R 6) [24,33,65,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34610 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 69 42 146 356 324 452 324), lower := (rows 25 35 69 42 146 32 64 128 256), losses := [] }

theorem u34610 : Upper (D 6) (R 6) [24,33,65,34,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34611 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 69 42 148 358 326 454 326), lower := (rows 25 35 69 42 148 32 64 128 256), losses := [] }

theorem u34611 : Upper (D 6) (R 6) [24,33,65,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34612 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 69 42 208 294 326 390 262), lower := (rows 25 35 69 42 208 32 64 128 256), losses := [] }

theorem u34612 : Upper (D 6) (R 6) [24,33,65,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34613 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 69 42 400 102 70 198 326), lower := (rows 25 35 69 42 400 32 64 128 256), losses := [] }

theorem u34613 : Upper (D 6) (R 6) [24,33,65,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34614 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 25 35 69 44 82 422 454 390 390), lower := (rows 25 35 69 44 82 32 64 128 256), losses := [] }

theorem u34614 : Upper (D 6) (R 6) [24,33,65,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34615 : Route 9 := (fun mask => (mask,id))

def c34615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34615 : Upper (D 6) (R 6) [24,33,65,36,130] 13 := by
  apply FastRouting.sound _ _ [24,33,65,36,130] 13 (by decide) (choices 1) [2,4,64,256] r34615 c34615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18265
  · exact u18266
  · exact u18267
  · exact u18268

def b34616 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 69 44 148 354 322 450 322), lower := (rows 25 35 69 44 148 32 64 128 256), losses := [] }

theorem u34616 : Upper (D 6) (R 6) [24,33,65,36,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34617 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 25 35 69 44 208 294 326 390 262), lower := (rows 25 35 69 44 208 32 64 128 256), losses := [] }

theorem u34617 : Upper (D 6) (R 6) [24,33,65,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34618 : Route 9 := (fun mask => (mask,id))

def c34618 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34618 : Upper (D 6) (R 6) [24,33,65,36,384] 13 := by
  apply FastRouting.sound _ _ [24,33,65,36,384] 13 (by decide) (choices 1) [2,4,64] r34618 c34618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18269
  · exact u18270
  · exact u18271

def b34619 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 25 35 69 104 146 294 326 390 262), lower := (rows 25 35 69 104 146 32 64 128 256), losses := [] }

theorem u34619 : Upper (D 6) (R 6) [24,33,65,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34619
end Delivery.IrregularNine14.P06
