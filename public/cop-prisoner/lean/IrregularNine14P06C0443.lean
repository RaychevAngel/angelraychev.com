import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0138
import IrregularNine14P06C0139

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26580 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 324 13 82 36 114 178 306), lower := (rows 41 131 324 13 82 36 64 128 256), losses := [] }

theorem u26580 : Upper (D 6) (R 6) [40,129,320,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26581 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 41 131 324 13 82 48 102 166 294), lower := (rows 41 131 324 13 82 48 64 128 256), losses := [] }

theorem u26581 : Upper (D 6) (R 6) [40,129,320,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26581 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26582 : Route 9 := (fun mask => (mask,id))

def c26582 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26582 : Upper (D 6) (R 6) [40,129,320,5,96,2] 13 := by
  apply FastRouting.sound _ _ [40,129,320,5,96,2] 13 (by decide) (choices 1) [2,4,16] r26582 c26582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8305
  · exact u8306
  · exact u8307

def b26583 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 324 13 112 36 82 146 274), lower := (rows 41 131 324 13 112 36 64 128 256), losses := [] }

theorem u26583 : Upper (D 6) (R 6) [40,129,320,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26584 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 324 13 112 48 70 134 262), lower := (rows 41 131 324 13 112 48 64 128 256), losses := [] }

theorem u26584 : Upper (D 6) (R 6) [40,129,320,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26584 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26585 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 41 131 324 14 21 34 112 240 368), lower := (rows 41 131 324 14 21 34 64 128 256), losses := [] }

theorem u26585 : Upper (D 6) (R 6) [40,129,320,6,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26586 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 131 324 14 21 48 98 226 354), lower := (rows 41 131 324 14 21 48 64 128 256), losses := [] }

theorem u26586 : Upper (D 6) (R 6) [40,129,320,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26586 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26587 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(0,1),(1,2),(4,1)], upper := (rows 41 131 324 14 21 96 114 178 306), lower := (rows 41 131 324 14 21 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 100 64 128 256), good := (rows 57 129 356 61 53 96 96 128 256) }] }

theorem u26587 : Upper (D 6) (R 6) [40,129,320,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26588 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 131 324 14 50 33 84 212 340), lower := (rows 41 131 324 14 50 33 64 128 256), losses := [] }

theorem u26588 : Upper (D 6) (R 6) [40,129,320,6,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26589 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 41 131 324 14 50 36 81 209 337), lower := (rows 41 131 324 14 50 36 64 128 256), losses := [] }

theorem u26589 : Upper (D 6) (R 6) [40,129,320,6,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26590 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 131 324 14 50 48 69 197 325), lower := (rows 41 131 324 14 50 48 64 128 256), losses := [] }

theorem u26590 : Upper (D 6) (R 6) [40,129,320,6,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26590 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26591 : PairBound 9 := { available := 21, camps := [], pairs := [(0,1),(0,2),(4,0)], upper := (rows 41 131 324 14 50 96 85 149 277), lower := (rows 41 131 324 14 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 100 64 128 256), good := (rows 56 130 356 62 50 96 96 128 256) },{ target := 1, region := (rows 9 0 4 8 16 100 64 128 256), good := (rows 41 129 356 45 48 96 96 128 256) },{ target := 2, region := (rows 9 2 0 8 24 100 64 128 256), good := (rows 57 131 352 59 50 96 96 128 256) }] }

theorem u26591 : Upper (D 6) (R 6) [40,129,320,6,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26592 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 131 324 14 52 33 82 210 338), lower := (rows 41 131 324 14 52 33 64 128 256), losses := [] }

theorem u26592 : Upper (D 6) (R 6) [40,129,320,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26593 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 41 131 324 14 52 34 81 209 337), lower := (rows 41 131 324 14 52 34 64 128 256), losses := [] }

theorem u26593 : Upper (D 6) (R 6) [40,129,320,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26594 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 131 324 14 52 48 67 195 323), lower := (rows 41 131 324 14 52 48 64 128 256), losses := [] }

theorem u26594 : Upper (D 6) (R 6) [40,129,320,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26594 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26595 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 131 324 14 52 96 83 147 275), lower := (rows 41 131 324 14 52 96 64 128 256), losses := [] }

theorem u26595 : Upper (D 6) (R 6) [40,129,320,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26596 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 324 14 81 34 116 180 308), lower := (rows 41 131 324 14 81 34 64 128 256), losses := [] }

theorem u26596 : Upper (D 6) (R 6) [40,129,320,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26597 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 324 14 81 36 114 178 306), lower := (rows 41 131 324 14 81 36 64 128 256), losses := [] }

theorem u26597 : Upper (D 6) (R 6) [40,129,320,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26598 : Route 9 := (fun mask => (mask,id))

def c26598 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26598 : Upper (D 6) (R 6) [40,129,320,6,65,16] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6,65,16] 13 (by decide) (choices 1) [2,4,32] r26598 c26598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8308
  · exact u8309
  · exact u8310

def b26599 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 14 82 33 116 180 308), lower := (rows 41 131 324 14 82 33 64 128 256), losses := [] }

theorem u26599 : Upper (D 6) (R 6) [40,129,320,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26600 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 324 14 82 36 113 177 305), lower := (rows 41 131 324 14 82 36 64 128 256), losses := [] }

theorem u26600 : Upper (D 6) (R 6) [40,129,320,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26601 : Route 9 := (fun mask => (mask,id))

def c26601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26601 : Upper (D 6) (R 6) [40,129,320,6,66,16] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6,66,16] 13 (by decide) (choices 1) [1,4,32] r26601 c26601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8311
  · exact u8312
  · exact u8313

def b26602 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 14 112 33 86 150 278), lower := (rows 41 131 324 14 112 33 64 128 256), losses := [] }

theorem u26602 : Upper (D 6) (R 6) [40,129,320,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26603 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 324 14 112 34 85 149 277), lower := (rows 41 131 324 14 112 34 64 128 256), losses := [] }

theorem u26603 : Upper (D 6) (R 6) [40,129,320,6,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26604 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 41 131 324 14 112 36 83 147 275), lower := (rows 41 131 324 14 112 36 64 128 256), losses := [] }

theorem u26604 : Upper (D 6) (R 6) [40,129,320,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26605 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 324 14 112 48 71 135 263), lower := (rows 41 131 324 14 112 48 64 128 256), losses := [] }

theorem u26605 : Upper (D 6) (R 6) [40,129,320,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26605 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26606 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 131 324 25 22 34 100 228 356), lower := (rows 41 131 324 25 22 34 64 128 256), losses := [] }

theorem u26606 : Upper (D 6) (R 6) [40,129,320,17,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26607 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 324 25 22 36 98 226 354), lower := (rows 41 131 324 25 22 36 64 128 256), losses := [] }

theorem u26607 : Upper (D 6) (R 6) [40,129,320,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26608 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 324 25 22 96 102 166 294), lower := (rows 41 131 324 25 22 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 24 16 100 64 128 256), good := (rows 41 129 356 25 61 96 96 128 256) }] }

theorem u26608 : Upper (D 6) (R 6) [40,129,320,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26609 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 131 324 25 82 34 100 164 292), lower := (rows 41 131 324 25 82 34 64 128 256), losses := [] }

theorem u26609 : Upper (D 6) (R 6) [40,129,320,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26610 : Route 9 := (fun mask => (mask,id))

def c26610 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26610 : Upper (D 6) (R 6) [40,129,320,17,66,4] 13 := by
  apply FastRouting.sound _ _ [40,129,320,17,66,4] 13 (by decide) (choices 1) [2,4,32] r26610 c26610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8314
  · exact u8315
  · exact u8316

def b26611 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 324 26 21 34 100 228 356), lower := (rows 41 131 324 26 21 34 64 128 256), losses := [] }

theorem u26611 : Upper (D 6) (R 6) [40,129,320,18,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26612 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 194, targets := 4 },{ cop := 1, region := 356, targets := 1 }], pairs := [(0,1),(1,2),(2,0)], upper := (rows 41 131 324 26 21 36 98 226 354), lower := (rows 41 131 324 26 21 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 129 356 57 53 36 64 128 256) }] }

theorem u26612 : Upper (D 6) (R 6) [40,129,320,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26613 : Route 9 := (fun mask => (mask,id))

def c26613 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26613 : Upper (D 6) (R 6) [40,129,320,18,5,64] 13 := by
  apply FastRouting.sound _ _ [40,129,320,18,5,64] 13 (by decide) (choices 1) [2,4,32] r26613 c26613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8317
  · exact u8318
  · exact u8319

def b26614 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 26 52 33 70 198 326), lower := (rows 41 131 324 26 52 33 64 128 256), losses := [] }

theorem u26614 : Upper (D 6) (R 6) [40,129,320,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26615 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 41 131 324 26 52 34 69 197 325), lower := (rows 41 131 324 26 52 34 64 128 256), losses := [] }

theorem u26615 : Upper (D 6) (R 6) [40,129,320,18,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26616 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 131 324 26 52 36 67 195 323), lower := (rows 41 131 324 26 52 36 64 128 256), losses := [] }

theorem u26616 : Upper (D 6) (R 6) [40,129,320,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26617 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 131 324 26 52 96 71 135 263), lower := (rows 41 131 324 26 52 96 64 128 256), losses := [] }

theorem u26617 : Upper (D 6) (R 6) [40,129,320,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26618 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 324 26 81 34 100 164 292), lower := (rows 41 131 324 26 81 34 64 128 256), losses := [] }

theorem u26618 : Upper (D 6) (R 6) [40,129,320,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26619 : Route 9 := (fun mask => (mask,id))

def c26619 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26619 : Upper (D 6) (R 6) [40,129,320,18,65,4] 13 := by
  apply FastRouting.sound _ _ [40,129,320,18,65,4] 13 (by decide) (choices 1) [2,4,32] r26619 c26619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8320
  · exact u8321
  · exact u8322

def b26620 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 26 112 33 70 134 262), lower := (rows 41 131 324 26 112 33 64 128 256), losses := [] }

theorem u26620 : Upper (D 6) (R 6) [40,129,320,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26621 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 41 131 324 26 112 34 69 133 261), lower := (rows 41 131 324 26 112 34 64 128 256), losses := [] }

theorem u26621 : Upper (D 6) (R 6) [40,129,320,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26622 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 41 131 324 26 112 36 71 135 263), lower := (rows 41 131 324 26 112 36 64 128 256), losses := [] }

theorem u26622 : Upper (D 6) (R 6) [40,129,320,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26623 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 28 82 33 102 166 294), lower := (rows 41 131 324 28 82 33 64 128 256), losses := [] }

theorem u26623 : Upper (D 6) (R 6) [40,129,320,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26624 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 41 131 324 28 82 34 101 165 293), lower := (rows 41 131 324 28 82 34 64 128 256), losses := [] }

theorem u26624 : Upper (D 6) (R 6) [40,129,320,20,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26625 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 41 131 324 28 82 36 99 163 291), lower := (rows 41 131 324 28 82 36 64 128 256), losses := [] }

theorem u26625 : Upper (D 6) (R 6) [40,129,320,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26626 : Route 9 := (fun mask => (mask,id))

def c26626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26626 : Upper (D 6) (R 6) [40,129,320,65,6,2] 13 := by
  apply FastRouting.sound _ _ [40,129,320,65,6,2] 13 (by decide) (choices 1) [4,16,32] r26626 c26626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8323
  · exact u8324
  · exact u8325

def b26627 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 324 73 22 36 114 178 306), lower := (rows 41 131 324 73 22 36 64 128 256), losses := [] }

theorem u26627 : Upper (D 6) (R 6) [40,129,320,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26628 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 41 131 324 73 22 48 102 166 294), lower := (rows 41 131 324 73 22 48 64 128 256), losses := [] }

theorem u26628 : Upper (D 6) (R 6) [40,129,320,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26628 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26629 : Route 9 := (fun mask => (mask,id))

def c26629 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26629 : Upper (D 6) (R 6) [40,129,320,65,36,2] 13 := by
  apply FastRouting.sound _ _ [40,129,320,65,36,2] 13 (by decide) (choices 1) [2,4,16] r26629 c26629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8326
  · exact u8327
  · exact u8328

def b26630 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 131 324 73 52 36 82 146 274), lower := (rows 41 131 324 73 52 36 64 128 256), losses := [] }

theorem u26630 : Upper (D 6) (R 6) [40,129,320,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26631 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 324 73 52 48 70 134 262), lower := (rows 41 131 324 73 52 48 64 128 256), losses := [] }

theorem u26631 : Upper (D 6) (R 6) [40,129,320,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26631 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26632 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 324 74 21 34 116 180 308), lower := (rows 41 131 324 74 21 34 64 128 256), losses := [] }

theorem u26632 : Upper (D 6) (R 6) [40,129,320,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26633 : Route 9 := (fun mask => (mask,id))

def c26633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26633 : Upper (D 6) (R 6) [40,129,320,66,5,4] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,5,4] 13 (by decide) (choices 1) [2,16,32] r26633 c26633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8329
  · exact u8330
  · exact u8331

def r26634 : Route 9 := (fun mask => (mask,id))

def c26634 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26634 : Upper (D 6) (R 6) [40,129,320,66,5,16] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,5,16] 13 (by decide) (choices 1) [2,4,32] r26634 c26634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8332
  · exact u8333
  · exact u8334

def b26635 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 74 22 33 116 180 308), lower := (rows 41 131 324 74 22 33 64 128 256), losses := [] }

theorem u26635 : Upper (D 6) (R 6) [40,129,320,66,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26636 : Route 9 := (fun mask => (mask,id))

def c26636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26636 : Upper (D 6) (R 6) [40,129,320,66,6,4] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,6,4] 13 (by decide) (choices 1) [1,16,32] r26636 c26636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8335
  · exact u8336
  · exact u8337

def r26637 : Route 9 := (fun mask => (mask,id))

def c26637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26637 : Upper (D 6) (R 6) [40,129,320,66,6,16] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,6,16] 13 (by decide) (choices 1) [1,4,32] r26637 c26637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8338
  · exact u8339
  · exact u8340

def b26638 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 131 324 74 50 33 84 148 276), lower := (rows 41 131 324 74 50 33 64 128 256), losses := [] }

theorem u26638 : Upper (D 6) (R 6) [40,129,320,66,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26639 : Route 9 := (fun mask => (mask,id))

def c26639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26639 : Upper (D 6) (R 6) [40,129,320,66,34,4] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,34,4] 13 (by decide) (choices 1) [1,4,16] r26639 c26639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8341
  · exact u8342
  · exact u8343

#print axioms u26639
end Delivery.IrregularNine14.P06
