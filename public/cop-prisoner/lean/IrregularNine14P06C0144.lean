import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0011

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8640 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 97 131 292 25 84 34 72 134 262), lower := (rows 97 131 292 25 84 34 72 128 256), losses := [] }

theorem u8640 : Upper (D 6) (R 6) [96,129,288,17,68,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8640 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8641 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 293, targets := 2 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 131 292 26 28 33 66 196 324), lower := (rows 97 131 292 26 28 33 66 128 256), losses := [] }

theorem u8641 : Upper (D 6) (R 6) [96,129,288,18,12,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8642 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 163, targets := 4 },{ cop := 8, region := 101, targets := 2 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 97 131 292 26 28 33 68 194 322), lower := (rows 97 131 292 26 28 33 68 128 256), losses := [] }

theorem u8642 : Upper (D 6) (R 6) [96,129,288,18,12,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8643 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 325, targets := 2 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 131 292 26 28 34 65 196 324), lower := (rows 97 131 292 26 28 34 65 128 256), losses := [] }

theorem u8643 : Upper (D 6) (R 6) [96,129,288,18,12,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8644 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 325, targets := 2 },{ cop := 6, region := 163, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 131 292 26 28 34 68 193 321), lower := (rows 97 131 292 26 28 34 68 128 256), losses := [] }

theorem u8644 : Upper (D 6) (R 6) [96,129,288,18,12,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8645 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 81, targets := 2 },{ cop := 3, region := 292, targets := 1 }], pairs := [(0,1),(2,0),(4,1)], upper := (rows 97 131 292 26 84 34 65 140 268), lower := (rows 97 131 292 26 84 34 65 128 256), losses := [] }

theorem u8645 : Upper (D 6) (R 6) [96,129,288,18,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8646 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 97 131 292 26 84 34 68 137 265), lower := (rows 97 131 292 26 84 34 68 128 256), losses := [] }

theorem u8646 : Upper (D 6) (R 6) [96,129,288,18,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8647 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 131 292 26 84 34 72 133 261), lower := (rows 97 131 292 26 84 34 72 128 256), losses := [] }

theorem u8647 : Upper (D 6) (R 6) [96,129,288,18,68,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8647 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8648 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 300, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 131 292 28 82 34 65 140 268), lower := (rows 97 131 292 28 82 34 65 128 256), losses := [] }

theorem u8648 : Upper (D 6) (R 6) [96,129,288,20,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8649 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 65, targets := 2 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 97 131 292 28 82 34 68 137 265), lower := (rows 97 131 292 28 82 34 68 128 256), losses := [{ target := 2, region := (rows 17 10 0 8 16 58 64 136 264), good := (rows 97 163 288 443 115 34 64 128 256) }] }

theorem u8649 : Upper (D 6) (R 6) [96,129,288,20,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8650 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 28 82 34 72 133 261), lower := (rows 97 131 292 28 82 34 72 128 256), losses := [] }

theorem u8650 : Upper (D 6) (R 6) [96,129,288,20,66,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8650 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8651 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 131 292 28 88 34 65 134 262), lower := (rows 97 131 292 28 88 34 65 128 256), losses := [] }

theorem u8651 : Upper (D 6) (R 6) [96,129,288,20,72,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8652 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 292 28 88 34 66 133 261), lower := (rows 97 131 292 28 88 34 66 128 256), losses := [] }

theorem u8652 : Upper (D 6) (R 6) [96,129,288,20,72,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8653 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 131 292 28 88 34 68 131 259), lower := (rows 97 131 292 28 88 34 68 128 256), losses := [] }

theorem u8653 : Upper (D 6) (R 6) [96,129,288,20,72,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8654 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 390, targets := 1 }], pairs := [(1,0)], upper := (rows 97 134 262 11 21 40 80 224 352), lower := (rows 97 134 262 11 21 40 80 128 256), losses := [] }

theorem u8654 : Upper (D 6) (R 6) [96,132,258,3,5,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8654 [(5,3),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8655 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 262 11 21 40 96 208 336), lower := (rows 97 134 262 11 21 40 96 128 256), losses := [] }

theorem u8655 : Upper (D 6) (R 6) [96,132,258,3,5,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8655 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8656 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 390, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 134 262 11 28 33 80 224 352), lower := (rows 97 134 262 11 28 33 80 128 256), losses := [] }

theorem u8656 : Upper (D 6) (R 6) [96,132,258,3,12,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8656 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8657 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 134 262 11 28 33 96 208 336), lower := (rows 97 134 262 11 28 33 96 128 256), losses := [] }

theorem u8657 : Upper (D 6) (R 6) [96,132,258,3,12,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8658 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 134 262 11 52 33 72 208 336), lower := (rows 97 134 262 11 52 33 72 128 256), losses := [] }

theorem u8658 : Upper (D 6) (R 6) [96,132,258,3,36,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8658 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8659 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 262 11 52 33 80 200 328), lower := (rows 97 134 262 11 52 33 80 128 256), losses := [] }

theorem u8659 : Upper (D 6) (R 6) [96,132,258,3,36,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8659 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8660 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 134 262 26 52 33 65 200 328), lower := (rows 97 134 262 26 52 33 65 128 256), losses := [] }

theorem u8660 : Upper (D 6) (R 6) [96,132,258,18,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8661 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 262 26 52 33 72 193 321), lower := (rows 97 134 262 26 52 33 72 128 256), losses := [] }

theorem u8661 : Upper (D 6) (R 6) [96,132,258,18,36,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8661 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8662 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 134 262 42 84 33 65 152 280), lower := (rows 97 134 262 42 84 33 65 128 256), losses := [] }

theorem u8662 : Upper (D 6) (R 6) [96,132,258,34,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8663 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 262 42 84 33 72 145 273), lower := (rows 97 134 262 42 84 33 72 128 256), losses := [] }

theorem u8663 : Upper (D 6) (R 6) [96,132,258,34,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8663 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8664 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 262 42 84 33 80 137 265), lower := (rows 97 134 262 42 84 33 80 128 256), losses := [] }

theorem u8664 : Upper (D 6) (R 6) [96,132,258,34,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8664 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8665 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 390, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 97 134 262 42 88 33 65 148 276), lower := (rows 97 134 262 42 88 33 65 128 256), losses := [] }

theorem u8665 : Upper (D 6) (R 6) [96,132,258,34,72,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8666 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(4,0)], upper := (rows 97 134 262 42 88 33 68 145 273), lower := (rows 97 134 262 42 88 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 32 70 128 256), good := (rows 96 198 326 122 88 32 68 128 256) }] }

theorem u8666 : Upper (D 6) (R 6) [96,132,258,34,72,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8667 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 81, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 134 262 42 88 33 80 133 261), lower := (rows 97 134 262 42 88 33 80 128 256), losses := [] }

theorem u8667 : Upper (D 6) (R 6) [96,132,258,34,72,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8667 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8668 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 134 268 11 21 34 80 224 352), lower := (rows 97 134 268 11 21 34 80 128 256), losses := [{ target := 0, region := (rows 0 26 12 8 16 126 80 209 337), good := (rows 480 166 302 430 502 34 498 128 256) }] }

theorem u8668 : Upper (D 6) (R 6) [96,132,264,3,5,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8668 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8669 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 134 268 11 21 34 96 208 336), lower := (rows 97 134 268 11 21 34 96 128 256), losses := [] }

theorem u8669 : Upper (D 6) (R 6) [96,132,264,3,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8670 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 134 268 11 21 48 96 194 322), lower := (rows 97 134 268 11 21 48 96 128 256), losses := [] }

theorem u8670 : Upper (D 6) (R 6) [96,132,264,3,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8670 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8671 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 97 134 268 13 19 34 80 224 352), lower := (rows 97 134 268 13 19 34 80 128 256), losses := [] }

theorem u8671 : Upper (D 6) (R 6) [96,132,264,5,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8671 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8672 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 134 268 13 19 34 96 208 336), lower := (rows 97 134 268 13 19 34 96 128 256), losses := [] }

theorem u8672 : Upper (D 6) (R 6) [96,132,264,5,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8673 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(1,0)], upper := (rows 97 134 268 26 21 33 66 224 352), lower := (rows 97 134 268 26 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 90 129 257), good := (rows 480 198 332 94 478 416 66 128 256) }] }

theorem u8673 : Upper (D 6) (R 6) [96,132,264,18,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8674 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 134 268 26 21 33 96 194 322), lower := (rows 97 134 268 26 21 33 96 128 256), losses := [] }

theorem u8674 : Upper (D 6) (R 6) [96,132,264,18,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8675 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 134 268 26 21 34 96 193 321), lower := (rows 97 134 268 26 21 34 96 128 256), losses := [] }

theorem u8675 : Upper (D 6) (R 6) [96,132,264,18,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8676 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 134 268 26 52 33 65 194 322), lower := (rows 97 134 268 26 52 33 65 128 256), losses := [] }

theorem u8676 : Upper (D 6) (R 6) [96,132,264,18,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8677 : Route 9 := (fun mask => (mask,id))

def c8677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8677 : Upper (D 6) (R 6) [96,132,264,18,36,1,2] 13 := by
  apply FastRouting.sound _ _ [96,132,264,18,36,1,2] 13 (by decide) (choices 1) [1,64] r8677 c8677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u661
  · exact u662

def b8678 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 134 268 42 84 33 65 146 274), lower := (rows 97 134 268 42 84 33 65 128 256), losses := [] }

theorem u8678 : Upper (D 6) (R 6) [96,132,264,34,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8679 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 97 134 268 42 84 33 66 145 273), lower := (rows 97 134 268 42 84 33 66 128 256), losses := [] }

theorem u8679 : Upper (D 6) (R 6) [96,132,264,34,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8680 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 268 42 84 33 80 131 259), lower := (rows 97 134 268 42 84 33 80 128 256), losses := [] }

theorem u8680 : Upper (D 6) (R 6) [96,132,264,34,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8680 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8681 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 65, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 134 268 56 84 34 65 131 259), lower := (rows 97 134 268 56 84 34 65 128 256), losses := [{ target := 1, region := (rows 41 0 4 40 22 32 109 128 256), good := (rows 105 212 349 121 84 121 65 128 256) }] }

theorem u8681 : Upper (D 6) (R 6) [96,132,264,48,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8682 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 134 268 56 84 34 66 129 257), lower := (rows 97 134 268 56 84 34 66 128 256), losses := [] }

theorem u8682 : Upper (D 6) (R 6) [96,132,264,48,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8683 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 276, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 134 292 11 21 34 72 208 336), lower := (rows 97 134 292 11 21 34 72 128 256), losses := [] }

theorem u8683 : Upper (D 6) (R 6) [96,132,288,3,5,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8683 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8684 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 81, targets := 2 }], pairs := [(0,1),(4,1)], upper := (rows 97 134 292 11 21 34 80 200 328), lower := (rows 97 134 292 11 21 34 80 128 256), losses := [] }

theorem u8684 : Upper (D 6) (R 6) [96,132,288,3,5,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8684 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8685 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 97 134 292 11 28 34 65 208 336), lower := (rows 97 134 292 11 28 34 65 128 256), losses := [] }

theorem u8685 : Upper (D 6) (R 6) [96,132,288,3,12,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8686 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 260, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 134 292 11 28 34 80 193 321), lower := (rows 97 134 292 11 28 34 80 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 24 32 88 137 265), good := (rows 485 132 292 477 476 32 80 128 256) }] }

theorem u8686 : Upper (D 6) (R 6) [96,132,288,3,12,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8686 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8687 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 97 134 292 11 84 33 66 152 280), lower := (rows 97 134 292 11 84 33 66 128 256), losses := [] }

theorem u8687 : Upper (D 6) (R 6) [96,132,288,3,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8688 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 134 292 11 84 33 72 146 274), lower := (rows 97 134 292 11 84 33 72 128 256), losses := [] }

theorem u8688 : Upper (D 6) (R 6) [96,132,288,3,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8688 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8689 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 11 84 33 80 138 266), lower := (rows 97 134 292 11 84 33 80 128 256), losses := [] }

theorem u8689 : Upper (D 6) (R 6) [96,132,288,3,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8689 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8690 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 97 134 292 11 84 34 65 152 280), lower := (rows 97 134 292 11 84 34 65 128 256), losses := [] }

theorem u8690 : Upper (D 6) (R 6) [96,132,288,3,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8691 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 276, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 134 292 11 84 34 72 145 273), lower := (rows 97 134 292 11 84 34 72 128 256), losses := [] }

theorem u8691 : Upper (D 6) (R 6) [96,132,288,3,68,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8691 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8692 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 11 84 34 80 137 265), lower := (rows 97 134 292 11 84 34 80 128 256), losses := [] }

theorem u8692 : Upper (D 6) (R 6) [96,132,288,3,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8692 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8693 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 134 292 11 84 40 65 146 274), lower := (rows 97 134 292 11 84 40 65 128 256), losses := [] }

theorem u8693 : Upper (D 6) (R 6) [96,132,288,3,68,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8693 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8694 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 276, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 134 292 11 84 40 66 145 273), lower := (rows 97 134 292 11 84 40 66 128 256), losses := [] }

theorem u8694 : Upper (D 6) (R 6) [96,132,288,3,68,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8694 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8695 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 134 292 11 84 40 80 131 259), lower := (rows 97 134 292 11 84 40 80 128 256), losses := [] }

theorem u8695 : Upper (D 6) (R 6) [96,132,288,3,68,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8695 [(5,3),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8696 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 134 292 11 88 34 65 148 276), lower := (rows 97 134 292 11 88 34 65 128 256), losses := [] }

theorem u8696 : Upper (D 6) (R 6) [96,132,288,3,72,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8697 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(4,0),(4,1)], upper := (rows 97 134 292 11 88 34 68 145 273), lower := (rows 97 134 292 11 88 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 42 70 128 256), good := (rows 96 230 356 122 120 98 68 128 256) },{ target := 1, region := (rows 37 0 4 8 24 32 70 136 264), good := (rows 97 197 357 473 472 97 69 128 256) }] }

theorem u8697 : Upper (D 6) (R 6) [96,132,288,3,72,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8698 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 11 88 34 80 133 261), lower := (rows 97 134 292 11 88 34 80 128 256), losses := [] }

theorem u8698 : Upper (D 6) (R 6) [96,132,288,3,72,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8698 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8699 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 134 292 13 88 34 65 146 274), lower := (rows 97 134 292 13 88 34 65 128 256), losses := [] }

theorem u8699 : Upper (D 6) (R 6) [96,132,288,5,72,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8699
end Delivery.IrregularNine14.P06
