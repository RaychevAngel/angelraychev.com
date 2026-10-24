import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0005

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4680 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 70 25 276 96 96 133 261), lower := (rows 11 162 70 25 276 96 96 128 256), losses := [] }

theorem u4680 : Upper (D 6) (R 6) [10,160,66,17,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4681 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 25 304 36 65 196 324), lower := (rows 11 162 70 25 304 36 65 128 256), losses := [] }

theorem u4681 : Upper (D 6) (R 6) [10,160,66,17,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4682 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 25 304 36 68 193 321), lower := (rows 11 162 70 25 304 36 68 128 256), losses := [] }

theorem u4682 : Upper (D 6) (R 6) [10,160,66,17,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4683 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 25 304 96 65 132 260), lower := (rows 11 162 70 25 304 96 65 128 256), losses := [] }

theorem u4683 : Upper (D 6) (R 6) [10,160,66,17,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4684 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 25 304 96 68 133 261), lower := (rows 11 162 70 25 304 96 68 128 256), losses := [] }

theorem u4684 : Upper (D 6) (R 6) [10,160,66,17,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4685 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 25 336 36 65 164 292), lower := (rows 11 162 70 25 336 36 65 128 256), losses := [] }

theorem u4685 : Upper (D 6) (R 6) [10,160,66,17,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4686 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 25 336 36 68 161 289), lower := (rows 11 162 70 25 336 36 68 128 256), losses := [] }

theorem u4686 : Upper (D 6) (R 6) [10,160,66,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4687 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 25 336 36 96 133 261), lower := (rows 11 162 70 25 336 36 96 128 256), losses := [] }

theorem u4687 : Upper (D 6) (R 6) [10,160,66,17,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4688 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 5, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 162 70 28 49 96 65 388 260), lower := (rows 11 162 70 28 49 96 65 128 256), losses := [] }

theorem u4688 : Upper (D 6) (R 6) [10,160,66,20,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4689 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 386, targets := 68 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 70 28 49 96 68 385 257), lower := (rows 11 162 70 28 49 96 68 128 256), losses := [] }

theorem u4689 : Upper (D 6) (R 6) [10,160,66,20,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4690 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 162 70 28 49 96 320 133 261), lower := (rows 11 162 70 28 49 96 320 128 256), losses := [{ target := 5, region := (rows 1 2 5 24 16 0 345 145 273), good := (rows 463 130 70 476 477 64 320 128 320) }] }

theorem u4690 : Upper (D 6) (R 6) [10,160,66,20,33,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4690 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4691 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 166, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 28 273 36 65 224 352), lower := (rows 11 162 70 28 273 36 65 128 256), losses := [] }

theorem u4691 : Upper (D 6) (R 6) [10,160,66,20,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4692 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 28 273 36 96 193 321), lower := (rows 11 162 70 28 273 36 96 128 256), losses := [] }

theorem u4692 : Upper (D 6) (R 6) [10,160,66,20,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4693 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 28 273 96 65 164 292), lower := (rows 11 162 70 28 273 96 65 128 256), losses := [] }

theorem u4693 : Upper (D 6) (R 6) [10,160,66,20,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4694 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 28 273 96 68 161 289), lower := (rows 11 162 70 28 273 96 68 128 256), losses := [] }

theorem u4694 : Upper (D 6) (R 6) [10,160,66,20,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4695 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 70 28 273 96 96 133 261), lower := (rows 11 162 70 28 273 96 96 128 256), losses := [] }

theorem u4695 : Upper (D 6) (R 6) [10,160,66,20,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4696 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 162 70 28 304 33 65 196 324), lower := (rows 11 162 70 28 304 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 97 97 132 260), good := (rows 105 224 508 412 368 97 97 128 256) }] }

theorem u4696 : Upper (D 6) (R 6) [10,160,66,20,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4697 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 68, targets := 33 }], pairs := [(2,0),(2,5),(4,1)], upper := (rows 11 162 70 28 304 33 68 193 321), lower := (rows 11 162 70 28 304 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 49 33 76 129 257), good := (rows 505 176 68 92 304 433 68 128 256) }] }

theorem u4697 : Upper (D 6) (R 6) [10,160,66,20,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4698 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 162 70 28 304 36 65 193 321), lower := (rows 11 162 70 28 304 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 44 21 44 65 193 321), good := (rows 505 168 508 60 312 60 465 128 256) }] }

theorem u4698 : Upper (D 6) (R 6) [10,160,66,20,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4699 : Route 9 := (fun mask => (mask,id))

def c4699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4699 : Upper (D 6) (R 6) [10,160,66,20,288,64,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,288,64,1] 13 (by decide) (choices 1) [1,4] r4699 c4699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u350
  · exact u351

def b4700 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 28 304 96 68 129 257), lower := (rows 11 162 70 28 304 96 68 128 256), losses := [] }

theorem u4700 : Upper (D 6) (R 6) [10,160,66,20,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4701 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 68, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 162 70 28 336 33 65 164 292), lower := (rows 11 162 70 28 336 33 65 128 256), losses := [] }

theorem u4701 : Upper (D 6) (R 6) [10,160,66,20,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4702 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 70 28 336 33 68 161 289), lower := (rows 11 162 70 28 336 33 68 128 256), losses := [] }

theorem u4702 : Upper (D 6) (R 6) [10,160,66,20,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4703 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 28 336 33 96 133 261), lower := (rows 11 162 70 28 336 33 96 128 256), losses := [] }

theorem u4703 : Upper (D 6) (R 6) [10,160,66,20,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4704 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 6, region := 166, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 56 273 36 65 196 324), lower := (rows 11 162 70 56 273 36 65 128 256), losses := [] }

theorem u4704 : Upper (D 6) (R 6) [10,160,66,48,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4705 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 56 273 36 68 193 321), lower := (rows 11 162 70 56 273 36 68 128 256), losses := [] }

theorem u4705 : Upper (D 6) (R 6) [10,160,66,48,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4706 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 70 56 273 96 65 132 260), lower := (rows 11 162 70 56 273 96 65 128 256), losses := [] }

theorem u4706 : Upper (D 6) (R 6) [10,160,66,48,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4707 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 56 273 96 68 133 261), lower := (rows 11 162 70 56 273 96 68 128 256), losses := [] }

theorem u4707 : Upper (D 6) (R 6) [10,160,66,48,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4708 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 70 56 276 33 65 196 324), lower := (rows 11 162 70 56 276 33 65 128 256), losses := [] }

theorem u4708 : Upper (D 6) (R 6) [10,160,66,48,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4709 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 162 70 56 276 33 68 193 321), lower := (rows 11 162 70 56 276 33 68 128 256), losses := [] }

theorem u4709 : Upper (D 6) (R 6) [10,160,66,48,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4710 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 70 56 336 33 65 132 260), lower := (rows 11 162 70 56 336 33 65 128 256), losses := [] }

theorem u4710 : Upper (D 6) (R 6) [10,160,66,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4711 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 162 70 56 336 33 68 133 261), lower := (rows 11 162 70 56 336 33 68 128 256), losses := [] }

theorem u4711 : Upper (D 6) (R 6) [10,160,66,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4712 : Route 9 := (fun mask => (mask,id))

def c4712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4712 : Upper (D 6) (R 6) [10,160,66,48,320,4,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,320,4,1] 13 (by decide) (choices 1) [1,4] r4712 c4712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u352
  · exact u353

def b4713 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 70 56 336 36 68 129 257), lower := (rows 11 162 70 56 336 36 68 128 256), losses := [] }

theorem u4713 : Upper (D 6) (R 6) [10,160,66,48,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4714 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 70 88 49 36 65 388 260), lower := (rows 11 162 70 88 49 36 65 128 256), losses := [] }

theorem u4714 : Upper (D 6) (R 6) [10,160,66,80,33,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4715 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 386, targets := 68 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 70 88 49 36 68 385 257), lower := (rows 11 162 70 88 49 36 68 128 256), losses := [] }

theorem u4715 : Upper (D 6) (R 6) [10,160,66,80,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4716 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 162 70 88 49 36 320 133 261), lower := (rows 11 162 70 88 49 36 320 128 256), losses := [{ target := 5, region := (rows 1 2 5 24 16 0 345 145 273), good := (rows 463 130 70 472 477 4 320 128 320) }] }

theorem u4716 : Upper (D 6) (R 6) [10,160,66,80,33,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4716 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4717 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 386, targets := 65 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(1,6),(2,5)], upper := (rows 11 162 70 88 52 33 65 388 260), lower := (rows 11 162 70 88 52 33 65 128 256), losses := [] }

theorem u4717 : Upper (D 6) (R 6) [10,160,66,80,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4718 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 419, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 70 88 52 33 68 385 257), lower := (rows 11 162 70 88 52 33 68 128 256), losses := [] }

theorem u4718 : Upper (D 6) (R 6) [10,160,66,80,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4719 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 162 70 88 52 33 320 133 261), lower := (rows 11 162 70 88 52 33 320 128 256), losses := [{ target := 5, region := (rows 1 2 7 24 16 0 371 161 289), good := (rows 463 454 70 88 476 453 320 128 320) }] }

theorem u4719 : Upper (D 6) (R 6) [10,160,66,80,36,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4719 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4720 : Route 9 := (fun mask => (mask,id))

def c4720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4720 : Upper (D 6) (R 6) [10,160,66,80,36,256,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,36,256,1] 13 (by decide) (choices 1) [1,4] r4720 c4720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u354
  · exact u355

def b4721 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 162 70 88 52 288 68 129 257), lower := (rows 11 162 70 88 52 288 68 128 256), losses := [] }

theorem u4721 : Upper (D 6) (R 6) [10,160,66,80,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4721 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4722 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 88 273 33 68 164 292), lower := (rows 11 162 70 88 273 33 68 128 256), losses := [] }

theorem u4722 : Upper (D 6) (R 6) [10,160,66,80,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4723 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 88 273 33 96 132 260), lower := (rows 11 162 70 88 273 33 96 128 256), losses := [] }

theorem u4723 : Upper (D 6) (R 6) [10,160,66,80,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4724 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 70 88 273 36 65 164 292), lower := (rows 11 162 70 88 273 36 65 128 256), losses := [] }

theorem u4724 : Upper (D 6) (R 6) [10,160,66,80,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4725 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 88 273 36 68 161 289), lower := (rows 11 162 70 88 273 36 68 128 256), losses := [] }

theorem u4725 : Upper (D 6) (R 6) [10,160,66,80,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4726 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 88 273 36 96 133 261), lower := (rows 11 162 70 88 273 36 96 128 256), losses := [] }

theorem u4726 : Upper (D 6) (R 6) [10,160,66,80,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4727 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 162 70 88 276 33 65 164 292), lower := (rows 11 162 70 88 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 97 97 132 260), good := (rows 105 224 508 120 412 97 97 128 256) }] }

theorem u4727 : Upper (D 6) (R 6) [10,160,66,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4728 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 70 88 276 33 68 161 289), lower := (rows 11 162 70 88 276 33 68 128 256), losses := [] }

theorem u4728 : Upper (D 6) (R 6) [10,160,66,80,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4729 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 88 276 33 96 133 261), lower := (rows 11 162 70 88 276 33 96 128 256), losses := [] }

theorem u4729 : Upper (D 6) (R 6) [10,160,66,80,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4730 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 162 70 88 276 36 65 161 289), lower := (rows 11 162 70 88 276 36 65 128 256), losses := [{ target := 6, region := (rows 9 10 4 8 16 52 0 136 264), good := (rows 395 162 38 443 308 36 1 128 256) }] }

theorem u4730 : Upper (D 6) (R 6) [10,160,66,80,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4731 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 88 276 36 96 129 257), lower := (rows 11 162 70 88 276 36 96 128 256), losses := [] }

theorem u4731 : Upper (D 6) (R 6) [10,160,66,80,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4732 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 162 70 88 304 33 65 132 260), lower := (rows 11 162 70 88 304 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 97 97 132 260), good := (rows 105 224 508 120 376 97 97 128 256) }] }

theorem u4732 : Upper (D 6) (R 6) [10,160,66,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4733 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 68, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 11 162 70 88 304 33 68 133 261), lower := (rows 11 162 70 88 304 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 32 103 128 256), good := (rows 78 230 70 88 376 100 68 128 256) }] }

theorem u4733 : Upper (D 6) (R 6) [10,160,66,80,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4734 : Route 9 := (fun mask => (mask,id))

def c4734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4734 : Upper (D 6) (R 6) [10,160,66,80,288,4,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,288,4,1] 13 (by decide) (choices 1) [1,4] r4734 c4734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u356
  · exact u357

def b4735 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 88 304 36 68 129 257), lower := (rows 11 162 70 88 304 36 68 128 256), losses := [] }

theorem u4735 : Upper (D 6) (R 6) [10,160,66,80,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4736 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 265 49 36 68 208 336), lower := (rows 11 162 70 265 49 36 68 128 256), losses := [] }

theorem u4736 : Upper (D 6) (R 6) [10,160,66,257,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4737 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 265, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 70 265 49 36 80 196 324), lower := (rows 11 162 70 265 49 36 80 128 256), losses := [] }

theorem u4737 : Upper (D 6) (R 6) [10,160,66,257,33,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4737 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4738 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 265 49 96 68 148 276), lower := (rows 11 162 70 265 49 96 68 128 256), losses := [] }

theorem u4738 : Upper (D 6) (R 6) [10,160,66,257,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4739 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 265, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 11 162 70 265 49 96 80 132 260), lower := (rows 11 162 70 265 49 96 80 128 256), losses := [] }

theorem u4739 : Upper (D 6) (R 6) [10,160,66,257,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4739 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4739
end Delivery.IrregularNine14.P06
