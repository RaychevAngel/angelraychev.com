import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0009

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7620 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 28 274 33 65 164 292), lower := (rows 35 194 76 28 274 33 65 128 256), losses := [] }

theorem u7620 : Upper (D 6) (R 6) [34,192,72,20,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7621 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 194 76 28 274 33 68 161 289), lower := (rows 35 194 76 28 274 33 68 128 256), losses := [] }

theorem u7621 : Upper (D 6) (R 6) [34,192,72,20,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7622 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 28 274 33 96 133 261), lower := (rows 35 194 76 28 274 33 96 128 256), losses := [] }

theorem u7622 : Upper (D 6) (R 6) [34,192,72,20,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7623 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 76 28 304 33 65 134 262), lower := (rows 35 194 76 28 304 33 65 128 256), losses := [] }

theorem u7623 : Upper (D 6) (R 6) [34,192,72,20,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7624 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 76 28 304 33 66 133 261), lower := (rows 35 194 76 28 304 33 66 128 256), losses := [] }

theorem u7624 : Upper (D 6) (R 6) [34,192,72,20,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7625 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 76, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 194 76 28 304 33 68 131 259), lower := (rows 35 194 76 28 304 33 68 128 256), losses := [] }

theorem u7625 : Upper (D 6) (R 6) [34,192,72,20,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7626 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 194 76 44 273 33 66 148 276), lower := (rows 35 194 76 44 273 33 66 128 256), losses := [] }

theorem u7626 : Upper (D 6) (R 6) [34,192,72,36,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7627 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 76 44 273 33 68 146 274), lower := (rows 35 194 76 44 273 33 68 128 256), losses := [] }

theorem u7627 : Upper (D 6) (R 6) [34,192,72,36,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7628 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 76 44 273 33 80 134 262), lower := (rows 35 194 76 44 273 33 80 128 256), losses := [] }

theorem u7628 : Upper (D 6) (R 6) [34,192,72,36,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7628 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7629 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 76 44 273 48 65 134 262), lower := (rows 35 194 76 44 273 48 65 128 256), losses := [] }

theorem u7629 : Upper (D 6) (R 6) [34,192,72,36,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7629 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7630 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 76 44 273 48 66 133 261), lower := (rows 35 194 76 44 273 48 66 128 256), losses := [] }

theorem u7630 : Upper (D 6) (R 6) [34,192,72,36,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7630 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7631 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 76 44 273 48 68 131 259), lower := (rows 35 194 76 44 273 48 68 128 256), losses := [] }

theorem u7631 : Upper (D 6) (R 6) [34,192,72,36,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7631 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7632 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 76 44 274 33 65 148 276), lower := (rows 35 194 76 44 274 33 65 128 256), losses := [] }

theorem u7632 : Upper (D 6) (R 6) [34,192,72,36,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7633 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 76 44 274 33 68 145 273), lower := (rows 35 194 76 44 274 33 68 128 256), losses := [] }

theorem u7633 : Upper (D 6) (R 6) [34,192,72,36,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7634 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 76 44 274 33 80 133 261), lower := (rows 35 194 76 44 274 33 80 128 256), losses := [] }

theorem u7634 : Upper (D 6) (R 6) [34,192,72,36,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7634 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7635 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 35 194 76 56 273 36 65 134 262), lower := (rows 35 194 76 56 273 36 65 128 256), losses := [] }

theorem u7635 : Upper (D 6) (R 6) [34,192,72,48,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7636 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 76 56 273 36 66 133 261), lower := (rows 35 194 76 56 273 36 66 128 256), losses := [] }

theorem u7636 : Upper (D 6) (R 6) [34,192,72,48,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7637 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 56 273 36 68 131 259), lower := (rows 35 194 76 56 273 36 68 128 256), losses := [] }

theorem u7637 : Upper (D 6) (R 6) [34,192,72,48,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7638 : Route 9 := (fun mask => (mask,id))

def c7638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7638 : Upper (D 6) (R 6) [34,192,72,48,258,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,258,4,1] 13 (by decide) (choices 1) [1,4] r7638 c7638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u587
  · exact u588

def b7639 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 56 274 36 68 129 257), lower := (rows 35 194 76 56 274 36 68 128 256), losses := [] }

theorem u7639 : Upper (D 6) (R 6) [34,192,72,48,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7640 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 76 56 276 33 65 134 262), lower := (rows 35 194 76 56 276 33 65 128 256), losses := [] }

theorem u7640 : Upper (D 6) (R 6) [34,192,72,48,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7641 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 76 56 276 33 66 133 261), lower := (rows 35 194 76 56 276 33 66 128 256), losses := [] }

theorem u7641 : Upper (D 6) (R 6) [34,192,72,48,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7642 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 194 76 56 276 33 68 131 259), lower := (rows 35 194 76 56 276 33 68 128 256), losses := [] }

theorem u7642 : Upper (D 6) (R 6) [34,192,72,48,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7643 : PairBound 9 := { available := 48, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 76 265 21 36 66 176 304), lower := (rows 35 194 76 265 21 36 66 128 256), losses := [] }

theorem u7643 : Upper (D 6) (R 6) [34,192,72,257,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7644 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 194 76 265 21 36 80 162 290), lower := (rows 35 194 76 265 21 36 80 128 256), losses := [] }

theorem u7644 : Upper (D 6) (R 6) [34,192,72,257,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7644 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7645 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 116, targets := 2 },{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 194 76 265 21 36 96 146 274), lower := (rows 35 194 76 265 21 36 96 128 256), losses := [] }

theorem u7645 : Upper (D 6) (R 6) [34,192,72,257,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7646 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 76 265 21 48 66 164 292), lower := (rows 35 194 76 265 21 48 66 128 256), losses := [] }

theorem u7646 : Upper (D 6) (R 6) [34,192,72,257,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7646 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7647 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 194 76 265 21 48 68 162 290), lower := (rows 35 194 76 265 21 48 68 128 256), losses := [] }

theorem u7647 : Upper (D 6) (R 6) [34,192,72,257,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7647 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7648 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 76 265 21 48 96 134 262), lower := (rows 35 194 76 265 21 48 96 128 256), losses := [] }

theorem u7648 : Upper (D 6) (R 6) [34,192,72,257,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7648 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7649 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 178, targets := 1 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 35 194 76 265 22 36 65 176 304), lower := (rows 35 194 76 265 22 36 65 128 256), losses := [] }

theorem u7649 : Upper (D 6) (R 6) [34,192,72,257,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7650 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 194 76 265 22 36 80 161 289), lower := (rows 35 194 76 265 22 36 80 128 256), losses := [] }

theorem u7650 : Upper (D 6) (R 6) [34,192,72,257,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7650 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7651 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 194 76 265 22 36 96 145 273), lower := (rows 35 194 76 265 22 36 96 128 256), losses := [] }

theorem u7651 : Upper (D 6) (R 6) [34,192,72,257,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7652 : Route 9 := (fun mask => (mask,id))

def c7652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7652 : Upper (D 6) (R 6) [34,192,72,258,5,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258,5,4,1] 13 (by decide) (choices 1) [16,32] r7652 c7652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u589
  · exact u590

def b7653 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 194 76 266 21 36 80 161 289), lower := (rows 35 194 76 266 21 36 80 128 256), losses := [] }

theorem u7653 : Upper (D 6) (R 6) [34,192,72,258,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7653 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7654 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 35 194 76 266 21 36 96 145 273), lower := (rows 35 194 76 266 21 36 96 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 32 97 144 272), good := (rows 99 194 72 266 475 96 96 128 256) }] }

theorem u7654 : Upper (D 6) (R 6) [34,192,72,258,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7655 : PairBound 9 := { available := 36, camps := [], pairs := [(1,0),(2,0)], upper := (rows 35 194 76 266 21 48 65 164 292), lower := (rows 35 194 76 266 21 48 65 128 256), losses := [{ target := 0, region := (rows 0 66 70 73 16 48 64 145 273), good := (rows 430 206 78 270 444 432 462 128 256) }] }

theorem u7655 : Upper (D 6) (R 6) [34,192,72,258,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7655 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7656 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 76 266 21 48 68 161 289), lower := (rows 35 194 76 266 21 48 68 128 256), losses := [] }

theorem u7656 : Upper (D 6) (R 6) [34,192,72,258,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7656 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7657 : Route 9 := (fun mask => (mask,id))

def c7657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7657 : Upper (D 6) (R 6) [34,192,72,258,5,16,32] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258,5,16,32] 13 (by decide) (choices 1) [1,4] r7657 c7657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u591
  · exact u592

def b7658 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 296, targets := 66 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 35 194 76 280 21 33 66 164 292), lower := (rows 35 194 76 280 21 33 66 128 256), losses := [] }

theorem u7658 : Upper (D 6) (R 6) [34,192,72,272,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7659 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 194 76 280 21 33 68 162 290), lower := (rows 35 194 76 280 21 33 68 128 256), losses := [] }

theorem u7659 : Upper (D 6) (R 6) [34,192,72,272,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7660 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 76 280 21 33 96 134 262), lower := (rows 35 194 76 280 21 33 96 128 256), losses := [] }

theorem u7660 : Upper (D 6) (R 6) [34,192,72,272,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7661 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 76 280 52 33 65 134 262), lower := (rows 35 194 76 280 52 33 65 128 256), losses := [] }

theorem u7661 : Upper (D 6) (R 6) [34,192,72,272,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7662 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 76 280 52 33 66 133 261), lower := (rows 35 194 76 280 52 33 66 128 256), losses := [] }

theorem u7662 : Upper (D 6) (R 6) [34,192,72,272,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7663 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 194 76 280 52 33 68 131 259), lower := (rows 35 194 76 280 52 33 68 128 256), losses := [] }

theorem u7663 : Upper (D 6) (R 6) [34,192,72,272,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7664 : Route 9 := (fun mask => (mask,id))

def c7664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7664 : Upper (D 6) (R 6) [34,192,72,288,5,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,5,4,1] 13 (by decide) (choices 1) [2,16] r7664 c7664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u593
  · exact u594

def b7665 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 76 296 21 36 66 145 273), lower := (rows 35 194 76 296 21 36 66 128 256), losses := [] }

theorem u7665 : Upper (D 6) (R 6) [34,192,72,288,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7666 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 194 76 296 21 36 80 131 259), lower := (rows 35 194 76 296 21 36 80 128 256), losses := [] }

theorem u7666 : Upper (D 6) (R 6) [34,192,72,288,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7666 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7667 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 76 296 21 48 65 134 262), lower := (rows 35 194 76 296 21 48 65 128 256), losses := [] }

theorem u7667 : Upper (D 6) (R 6) [34,192,72,288,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7667 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7668 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 76 296 21 48 66 133 261), lower := (rows 35 194 76 296 21 48 66 128 256), losses := [] }

theorem u7668 : Upper (D 6) (R 6) [34,192,72,288,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7668 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7669 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 76 296 21 48 68 131 259), lower := (rows 35 194 76 296 21 48 68 128 256), losses := [] }

theorem u7669 : Upper (D 6) (R 6) [34,192,72,288,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7669 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7670 : Route 9 := (fun mask => (mask,id))

def c7670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7670 : Upper (D 6) (R 6) [34,192,72,288,6,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,6,4,1] 13 (by decide) (choices 1) [1,16] r7670 c7670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u595
  · exact u596

def b7671 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 194 76 296 22 36 80 129 257), lower := (rows 35 194 76 296 22 36 80 128 256), losses := [] }

theorem u7671 : Upper (D 6) (R 6) [34,192,72,288,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7671 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7672 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 100 25 28 288 65 134 262), lower := (rows 35 194 100 25 28 288 65 128 256), losses := [] }

theorem u7672 : Upper (D 6) (R 6) [34,192,96,17,12,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7672 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7673 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 100 25 28 288 66 133 261), lower := (rows 35 194 100 25 28 288 66 128 256), losses := [] }

theorem u7673 : Upper (D 6) (R 6) [34,192,96,17,12,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7673 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7674 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 100 25 28 288 68 131 259), lower := (rows 35 194 100 25 28 288 68 128 256), losses := [] }

theorem u7674 : Upper (D 6) (R 6) [34,192,96,17,12,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7674 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7675 : Route 9 := (fun mask => (mask,id))

def c7675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7675 : Upper (D 6) (R 6) [34,192,96,17,258,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,258,4,1] 13 (by decide) (choices 1) [4,8] r7675 c7675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u597
  · exact u598

def b7676 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 25 274 36 68 137 265), lower := (rows 35 194 100 25 274 36 68 128 256), losses := [] }

theorem u7676 : Upper (D 6) (R 6) [34,192,96,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7677 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 100 25 274 36 72 133 261), lower := (rows 35 194 100 25 274 36 72 128 256), losses := [] }

theorem u7677 : Upper (D 6) (R 6) [34,192,96,17,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7677 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7678 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 100 25 276 33 66 140 268), lower := (rows 35 194 100 25 276 33 66 128 256), losses := [] }

theorem u7678 : Upper (D 6) (R 6) [34,192,96,17,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7679 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 194 100 25 276 33 68 138 266), lower := (rows 35 194 100 25 276 33 68 128 256), losses := [] }

theorem u7679 : Upper (D 6) (R 6) [34,192,96,17,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7679
end Delivery.IrregularNine14.P06
