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

def b8700 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 134 292 13 88 34 66 145 273), lower := (rows 97 134 292 13 88 34 66 128 256), losses := [] }

theorem u8700 : Upper (D 6) (R 6) [96,132,288,5,72,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8701 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 13 88 34 80 131 259), lower := (rows 97 134 292 13 88 34 80 128 256), losses := [] }

theorem u8701 : Upper (D 6) (R 6) [96,132,288,5,72,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8701 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8702 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 97 134 292 25 26 34 65 196 324), lower := (rows 97 134 292 25 26 34 65 128 256), losses := [] }

theorem u8702 : Upper (D 6) (R 6) [96,132,288,17,10,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8703 : Route 9 := (fun mask => (mask,id))

def c8703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8703 : Upper (D 6) (R 6) [96,132,288,17,10,2,4] 13 := by
  apply FastRouting.sound _ _ [96,132,288,17,10,2,4] 13 (by decide) (choices 1) [1,64] r8703 c8703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u663
  · exact u664

def b8704 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 134 292 25 84 34 65 138 266), lower := (rows 97 134 292 25 84 34 65 128 256), losses := [] }

theorem u8704 : Upper (D 6) (R 6) [96,132,288,17,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8705 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 134 292 25 84 34 66 137 265), lower := (rows 97 134 292 25 84 34 66 128 256), losses := [] }

theorem u8705 : Upper (D 6) (R 6) [96,132,288,17,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8706 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 97 134 292 25 84 34 72 131 259), lower := (rows 97 134 292 25 84 34 72 128 256), losses := [] }

theorem u8706 : Upper (D 6) (R 6) [96,132,288,17,68,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8706 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8707 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 138, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 97 134 292 26 84 33 65 138 266), lower := (rows 97 134 292 26 84 33 65 128 256), losses := [] }

theorem u8707 : Upper (D 6) (R 6) [96,132,288,18,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8708 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 97 134 292 26 84 33 66 137 265), lower := (rows 97 134 292 26 84 33 66 128 256), losses := [] }

theorem u8708 : Upper (D 6) (R 6) [96,132,288,18,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8709 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 97 134 292 26 84 33 72 131 259), lower := (rows 97 134 292 26 84 33 72 128 256), losses := [] }

theorem u8709 : Upper (D 6) (R 6) [96,132,288,18,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8709 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8710 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 81, targets := 2 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 134 292 26 84 34 65 137 265), lower := (rows 97 134 292 26 84 34 65 128 256), losses := [] }

theorem u8710 : Upper (D 6) (R 6) [96,132,288,18,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8711 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 276, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 134 292 26 84 34 72 129 257), lower := (rows 97 134 292 26 84 34 72 128 256), losses := [] }

theorem u8711 : Upper (D 6) (R 6) [96,132,288,18,68,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8711 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8712 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 134 292 28 82 33 65 138 266), lower := (rows 97 134 292 28 82 33 65 128 256), losses := [] }

theorem u8712 : Upper (D 6) (R 6) [96,132,288,20,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8713 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 97 134 292 28 82 33 66 137 265), lower := (rows 97 134 292 28 82 33 66 128 256), losses := [] }

theorem u8713 : Upper (D 6) (R 6) [96,132,288,20,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8714 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 97 134 292 28 82 33 72 131 259), lower := (rows 97 134 292 28 82 33 72 128 256), losses := [] }

theorem u8714 : Upper (D 6) (R 6) [96,132,288,20,66,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8714 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8715 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 134 292 28 82 34 65 137 265), lower := (rows 97 134 292 28 82 34 65 128 256), losses := [] }

theorem u8715 : Upper (D 6) (R 6) [96,132,288,20,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8716 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 28 82 34 72 129 257), lower := (rows 97 134 292 28 82 34 72 128 256), losses := [] }

theorem u8716 : Upper (D 6) (R 6) [96,132,288,20,66,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8716 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8717 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 325, targets := 2 },{ cop := 4, region := 65, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 276 11 50 36 65 196 324), lower := (rows 97 138 276 11 50 36 65 128 256), losses := [] }

theorem u8717 : Upper (D 6) (R 6) [96,136,272,3,34,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8718 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 138 276 11 50 36 68 193 321), lower := (rows 97 138 276 11 50 36 68 128 256), losses := [] }

theorem u8718 : Upper (D 6) (R 6) [96,136,272,3,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8719 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 309, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 276 11 52 33 66 196 324), lower := (rows 97 138 276 11 52 33 66 128 256), losses := [] }

theorem u8719 : Upper (D 6) (R 6) [96,136,272,3,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8720 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 97 138 276 11 52 33 68 194 322), lower := (rows 97 138 276 11 52 33 68 128 256), losses := [] }

theorem u8720 : Upper (D 6) (R 6) [96,136,272,3,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8721 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 226, targets := 1 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 97 138 276 13 19 34 68 224 352), lower := (rows 97 138 276 13 19 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 92 129 257), good := (rows 481 200 348 461 477 32 68 128 256) }] }

theorem u8721 : Upper (D 6) (R 6) [96,136,272,5,3,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8722 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 138 276 13 19 34 96 196 324), lower := (rows 97 138 276 13 19 34 96 128 256), losses := [] }

theorem u8722 : Upper (D 6) (R 6) [96,136,272,5,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8723 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 81, targets := 4 },{ cop := 4, region := 293, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 138 276 42 82 36 65 133 261), lower := (rows 97 138 276 42 82 36 65 128 256), losses := [] }

theorem u8723 : Upper (D 6) (R 6) [96,136,272,34,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8724 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 138 276 42 82 36 68 129 257), lower := (rows 97 138 276 42 82 36 68 128 256), losses := [] }

theorem u8724 : Upper (D 6) (R 6) [96,136,272,34,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8725 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 138 276 42 84 33 65 134 262), lower := (rows 97 138 276 42 84 33 65 128 256), losses := [] }

theorem u8725 : Upper (D 6) (R 6) [96,136,272,34,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8726 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 309, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 276 42 84 33 66 133 261), lower := (rows 97 138 276 42 84 33 66 128 256), losses := [] }

theorem u8726 : Upper (D 6) (R 6) [96,136,272,34,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8727 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 138, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 97 138 276 42 84 33 68 131 259), lower := (rows 97 138 276 42 84 33 68 128 256), losses := [] }

theorem u8727 : Upper (D 6) (R 6) [96,136,272,34,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8728 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 309, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 11 84 33 66 148 276), lower := (rows 97 138 292 11 84 33 66 128 256), losses := [] }

theorem u8728 : Upper (D 6) (R 6) [96,136,288,3,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8729 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 97 138 292 11 84 33 68 146 274), lower := (rows 97 138 292 11 84 33 68 128 256), losses := [] }

theorem u8729 : Upper (D 6) (R 6) [96,136,288,3,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8730 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 11 84 33 80 134 262), lower := (rows 97 138 292 11 84 33 80 128 256), losses := [] }

theorem u8730 : Upper (D 6) (R 6) [96,136,288,3,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8730 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8731 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 138 292 13 84 34 65 146 274), lower := (rows 97 138 292 13 84 34 65 128 256), losses := [] }

theorem u8731 : Upper (D 6) (R 6) [96,136,288,5,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8732 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 138 292 13 84 34 66 145 273), lower := (rows 97 138 292 13 84 34 66 128 256), losses := [] }

theorem u8732 : Upper (D 6) (R 6) [96,136,288,5,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8733 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 13 84 34 80 131 259), lower := (rows 97 138 292 13 84 34 80 128 256), losses := [] }

theorem u8733 : Upper (D 6) (R 6) [96,136,288,5,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8733 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8734 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 138, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 97 138 292 14 84 33 65 146 274), lower := (rows 97 138 292 14 84 33 65 128 256), losses := [] }

theorem u8734 : Upper (D 6) (R 6) [96,136,288,6,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8735 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 309, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 14 84 33 66 145 273), lower := (rows 97 138 292 14 84 33 66 128 256), losses := [] }

theorem u8735 : Upper (D 6) (R 6) [96,136,288,6,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8736 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 14 84 33 80 131 259), lower := (rows 97 138 292 14 84 33 80 128 256), losses := [] }

theorem u8736 : Upper (D 6) (R 6) [96,136,288,6,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8736 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8737 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 138 292 25 84 34 65 134 262), lower := (rows 97 138 292 25 84 34 65 128 256), losses := [] }

theorem u8737 : Upper (D 6) (R 6) [96,136,288,17,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8738 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 138 292 25 84 34 66 133 261), lower := (rows 97 138 292 25 84 34 66 128 256), losses := [] }

theorem u8738 : Upper (D 6) (R 6) [96,136,288,17,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8739 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 138 292 25 84 34 68 131 259), lower := (rows 97 138 292 25 84 34 68 128 256), losses := [] }

theorem u8739 : Upper (D 6) (R 6) [96,136,288,17,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8740 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 138, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 97 138 292 26 84 33 65 134 262), lower := (rows 97 138 292 26 84 33 65 128 256), losses := [] }

theorem u8740 : Upper (D 6) (R 6) [96,136,288,18,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8741 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 309, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 26 84 33 66 133 261), lower := (rows 97 138 292 26 84 33 66 128 256), losses := [] }

theorem u8741 : Upper (D 6) (R 6) [96,136,288,18,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8742 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 97 138 292 26 84 33 68 131 259), lower := (rows 97 138 292 26 84 33 68 128 256), losses := [] }

theorem u8742 : Upper (D 6) (R 6) [96,136,288,18,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8743 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 138 292 28 82 33 65 134 262), lower := (rows 97 138 292 28 82 33 65 128 256), losses := [] }

theorem u8743 : Upper (D 6) (R 6) [96,136,288,20,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8744 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 301, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 138 292 28 82 33 66 133 261), lower := (rows 97 138 292 28 82 33 66 128 256), losses := [] }

theorem u8744 : Upper (D 6) (R 6) [96,136,288,20,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8745 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 33, targets := 6 },{ cop := 8, region := 101, targets := 2 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 292 28 82 33 68 131 259), lower := (rows 97 138 292 28 82 33 68 128 256), losses := [] }

theorem u8745 : Upper (D 6) (R 6) [96,136,288,20,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8746 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 138 292 76 19 34 65 148 276), lower := (rows 97 138 292 76 19 34 65 128 256), losses := [] }

theorem u8746 : Upper (D 6) (R 6) [96,136,288,68,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8747 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 179, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 97 138 292 76 19 34 68 145 273), lower := (rows 97 138 292 76 19 34 68 128 256), losses := [] }

theorem u8747 : Upper (D 6) (R 6) [96,136,288,68,3,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8748 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 97 138 292 76 19 34 80 133 261), lower := (rows 97 138 292 76 19 34 80 128 256), losses := [] }

theorem u8748 : Upper (D 6) (R 6) [96,136,288,68,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8748 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8749 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 138 292 76 19 48 65 134 262), lower := (rows 97 138 292 76 19 48 65 128 256), losses := [] }

theorem u8749 : Upper (D 6) (R 6) [96,136,288,68,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8749 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8750 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 97 138 292 76 19 48 66 133 261), lower := (rows 97 138 292 76 19 48 66 128 256), losses := [] }

theorem u8750 : Upper (D 6) (R 6) [96,136,288,68,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8750 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8751 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 179, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 97 138 292 76 19 48 68 131 259), lower := (rows 97 138 292 76 19 48 68 128 256), losses := [] }

theorem u8751 : Upper (D 6) (R 6) [96,136,288,68,3,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8751 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8752 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 138 292 76 21 34 65 146 274), lower := (rows 97 138 292 76 21 34 65 128 256), losses := [] }

theorem u8752 : Upper (D 6) (R 6) [96,136,288,68,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8753 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 138 292 76 21 34 66 145 273), lower := (rows 97 138 292 76 21 34 66 128 256), losses := [] }

theorem u8753 : Upper (D 6) (R 6) [96,136,288,68,5,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8754 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 97 138 292 76 21 34 80 131 259), lower := (rows 97 138 292 76 21 34 80 128 256), losses := [] }

theorem u8754 : Upper (D 6) (R 6) [96,136,288,68,5,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8754 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8755 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 146, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 97 138 292 76 22 33 65 146 274), lower := (rows 97 138 292 76 22 33 65 128 256), losses := [] }

theorem u8755 : Upper (D 6) (R 6) [96,136,288,68,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8756 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,1),(0,2),(3,0)], upper := (rows 97 138 292 76 22 33 66 145 273), lower := (rows 97 138 292 76 22 33 66 128 256), losses := [] }

theorem u8756 : Upper (D 6) (R 6) [96,136,288,68,6,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8757 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 97 138 292 76 22 33 80 131 259), lower := (rows 97 138 292 76 22 33 80 128 256), losses := [] }

theorem u8757 : Upper (D 6) (R 6) [96,136,288,68,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8757 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8758 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 2 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 138 292 76 22 34 65 145 273), lower := (rows 97 138 292 76 22 34 65 128 256), losses := [] }

theorem u8758 : Upper (D 6) (R 6) [96,136,288,68,6,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8759 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 97 138 292 76 22 34 80 129 257), lower := (rows 97 138 292 76 22 34 80 128 256), losses := [] }

theorem u8759 : Upper (D 6) (R 6) [96,136,288,68,6,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8759 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8759
end Delivery.IrregularNine14.P06
