import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5820 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 240, targets := 3 }], pairs := [(2,5),(3,5),(4,0),(4,1)], upper := (rows 35 259 13 26 84 160 192 224 352), lower := (rows 35 259 13 26 84 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 7 11 17 0 224 128 256), good := (rows 95 287 29 30 84 192 192 192 256) }] }

theorem u5820 : Upper (D 7) (R 7) [34,257,9,18,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5821 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 13 26 112 160 68 192 448), lower := (rows 35 259 13 26 112 160 68 128 256), losses := [] }

theorem u5821 : Upper (D 7) (R 7) [34,257,9,18,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5821 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5822 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 13 26 112 160 192 196 324), lower := (rows 35 259 13 26 112 160 192 128 256), losses := [] }

theorem u5822 : Upper (D 7) (R 7) [34,257,9,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5823 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 0, region := 80, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 259 13 28 82 160 96 192 448), lower := (rows 35 259 13 28 82 160 96 128 256), losses := [] }

theorem u5823 : Upper (D 7) (R 7) [34,257,9,20,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5824 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 208, targets := 1 }], pairs := [(2,5),(3,0),(3,5),(4,0)], upper := (rows 35 259 13 28 82 160 192 224 352), lower := (rows 35 259 13 28 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 19 511 511 511 511), good := (rows 498 498 508 508 498 480 480 480 480) },{ target := 5, region := (rows 1 2 7 31 17 0 224 128 256), good := (rows 95 287 29 28 94 192 192 192 256) }] }

theorem u5824 : Upper (D 7) (R 7) [34,257,9,20,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5825 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 6, region := 176, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 259 13 28 112 160 66 192 448), lower := (rows 35 259 13 28 112 160 66 128 256), losses := [] }

theorem u5825 : Upper (D 7) (R 7) [34,257,9,20,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5826 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 13 28 112 160 192 194 322), lower := (rows 35 259 13 28 112 160 192 128 256), losses := [] }

theorem u5826 : Upper (D 7) (R 7) [34,257,9,20,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5827 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 13 56 82 160 68 192 448), lower := (rows 35 259 13 56 82 160 68 128 256), losses := [] }

theorem u5827 : Upper (D 7) (R 7) [34,257,9,48,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5827 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5828 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 259 13 56 82 160 192 196 324), lower := (rows 35 259 13 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 29 17 228 228 132 260), good := (rows 122 282 508 120 122 224 224 224 256) }] }

theorem u5828 : Upper (D 7) (R 7) [34,257,9,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5829 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 13 74 52 160 80 192 448), lower := (rows 35 259 13 74 52 160 80 128 256), losses := [] }

theorem u5829 : Upper (D 7) (R 7) [34,257,9,66,36,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5829 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5830 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 240, targets := 3 }], pairs := [(2,5),(3,0),(4,0),(4,1)], upper := (rows 35 259 13 74 52 160 192 208 336), lower := (rows 35 259 13 74 52 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 244 244 148 276), good := (rows 106 266 508 106 500 224 224 224 256) },{ target := 5, region := (rows 1 2 7 9 16 0 240 144 272), good := (rows 79 271 13 78 468 192 192 192 256) }] }

theorem u5830 : Upper (D 7) (R 7) [34,257,9,66,36,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5831 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 259 13 74 112 160 68 144 400), lower := (rows 35 259 13 74 112 160 68 128 256), losses := [] }

theorem u5831 : Upper (D 7) (R 7) [34,257,9,66,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5831 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5832 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 13 74 112 160 80 132 388), lower := (rows 35 259 13 74 112 160 80 128 256), losses := [] }

theorem u5832 : Upper (D 7) (R 7) [34,257,9,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5832 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5833 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 13 74 112 160 192 148 276), lower := (rows 35 259 13 74 112 160 192 128 256), losses := [] }

theorem u5833 : Upper (D 7) (R 7) [34,257,9,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5834 : Route 9 := (fun mask => (mask,id))

def c5834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5834 : Upper (D 7) (R 7) [34,257,9,66,132,128,16] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,132,128,16] 13 (by decide) (choices 1) [32,64] r5834 c5834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u428
  · exact u429

def b5835 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 240, targets := 3 }], pairs := [(2,7),(3,7),(4,0),(4,1)], upper := (rows 35 259 13 74 148 160 96 208 336), lower := (rows 35 259 13 74 148 160 96 128 256), losses := [] }

theorem u5835 : Upper (D 7) (R 7) [34,257,9,66,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5836 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 35 259 13 74 208 48 68 160 416), lower := (rows 35 259 13 74 208 48 68 128 256), losses := [] }

theorem u5836 : Upper (D 7) (R 7) [34,257,9,66,192,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5836 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5837 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,7),(3,7),(4,0)], upper := (rows 35 259 13 74 208 48 96 132 388), lower := (rows 35 259 13 74 208 48 96 128 256), losses := [] }

theorem u5837 : Upper (D 7) (R 7) [34,257,9,66,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5837 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5838 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 13 74 208 48 192 164 292), lower := (rows 35 259 13 74 208 48 192 128 256), losses := [] }

theorem u5838 : Upper (D 7) (R 7) [34,257,9,66,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5838 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5839 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 259 13 74 208 160 68 176 304), lower := (rows 35 259 13 74 208 160 68 128 256), losses := [] }

theorem u5839 : Upper (D 7) (R 7) [34,257,9,66,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5839 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5840 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 13 74 208 160 80 164 292), lower := (rows 35 259 13 74 208 160 80 128 256), losses := [] }

theorem u5840 : Upper (D 7) (R 7) [34,257,9,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5840 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5841 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 240, targets := 3 }], pairs := [(2,7),(3,7),(4,0),(4,1)], upper := (rows 35 259 13 74 208 160 96 148 276), lower := (rows 35 259 13 74 208 160 96 128 256), losses := [] }

theorem u5841 : Upper (D 7) (R 7) [34,257,9,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5842 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 208, targets := 1 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 259 13 76 146 160 80 224 352), lower := (rows 35 259 13 76 146 160 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 19 255 87 223 351), good := (rows 498 498 508 492 498 160 496 160 256) }] }

theorem u5842 : Upper (D 7) (R 7) [34,257,9,68,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5842 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5843 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 259 13 76 146 160 96 208 336), lower := (rows 35 259 13 76 146 160 96 128 256), losses := [] }

theorem u5843 : Upper (D 7) (R 7) [34,257,9,68,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5844 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(2,7),(3,0),(3,7),(4,7)], upper := (rows 35 259 13 88 22 160 96 192 448), lower := (rows 35 259 13 88 22 160 96 128 256), losses := [] }

theorem u5844 : Upper (D 7) (R 7) [34,257,9,80,6,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5845 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 232, targets := 3 }], pairs := [(2,5),(3,0),(3,1),(3,5)], upper := (rows 35 259 13 88 22 160 192 224 352), lower := (rows 35 259 13 88 22 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 7 9 19 0 224 128 256), good := (rows 95 287 29 88 22 192 192 192 256) }] }

theorem u5845 : Upper (D 7) (R 7) [34,257,9,80,6,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5846 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 259 13 88 146 36 96 192 448), lower := (rows 35 259 13 88 146 36 96 128 256), losses := [] }

theorem u5846 : Upper (D 7) (R 7) [34,257,9,80,130,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5846 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5847 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 13 88 146 36 192 224 352), lower := (rows 35 259 13 88 146 36 192 128 256), losses := [] }

theorem u5847 : Upper (D 7) (R 7) [34,257,9,80,130,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5847 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5848 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 259 13 88 146 96 68 160 416), lower := (rows 35 259 13 88 146 96 68 128 256), losses := [] }

theorem u5848 : Upper (D 7) (R 7) [34,257,9,80,130,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5848 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5849 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 35 259 13 88 146 96 96 132 388), lower := (rows 35 259 13 88 146 96 96 128 256), losses := [] }

theorem u5849 : Upper (D 7) (R 7) [34,257,9,80,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5850 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 259 13 88 146 96 192 164 292), lower := (rows 35 259 13 88 146 96 192 128 256), losses := [] }

theorem u5850 : Upper (D 7) (R 7) [34,257,9,80,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5851 : Route 9 := (fun mask => (mask,id))

def c5851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5851 : Upper (D 7) (R 7) [34,257,9,80,130,128,4] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,130,128,4] 13 (by decide) (choices 1) [32,64] r5851 c5851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u430
  · exact u431

def b5852 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 35 259 13 88 146 160 96 196 324), lower := (rows 35 259 13 88 146 160 96 128 256), losses := [{ target := 6, region := (rows 17 2 12 8 16 176 0 128 256), good := (rows 35 259 13 61 179 160 32 160 256) }] }

theorem u5852 : Upper (D 7) (R 7) [34,257,9,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5853 : PairBound 9 := { available := 132, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 2, region := 386, targets := 32 },{ cop := 2, region := 386, targets := 64 }], pairs := [(0,7),(1,5),(1,6),(1,7)], upper := (rows 35 259 13 88 176 96 66 132 388), lower := (rows 35 259 13 88 176 96 66 128 256), losses := [] }

theorem u5853 : Upper (D 7) (R 7) [34,257,9,80,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5854 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 13 88 176 96 68 130 386), lower := (rows 35 259 13 88 176 96 68 128 256), losses := [] }

theorem u5854 : Upper (D 7) (R 7) [34,257,9,80,160,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5854 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5855 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 13 88 176 96 192 134 262), lower := (rows 35 259 13 88 176 96 192 128 256), losses := [] }

theorem u5855 : Upper (D 7) (R 7) [34,257,9,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5856 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 13 104 82 160 68 144 400), lower := (rows 35 259 13 104 82 160 68 128 256), losses := [] }

theorem u5856 : Upper (D 7) (R 7) [34,257,9,96,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5856 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5857 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 13 104 82 160 80 132 388), lower := (rows 35 259 13 104 82 160 80 128 256), losses := [] }

theorem u5857 : Upper (D 7) (R 7) [34,257,9,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5857 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5858 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 259 13 104 82 160 192 148 276), lower := (rows 35 259 13 104 82 160 192 128 256), losses := [] }

theorem u5858 : Upper (D 7) (R 7) [34,257,9,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5859 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 13 104 146 160 68 208 336), lower := (rows 35 259 13 104 146 160 68 128 256), losses := [] }

theorem u5859 : Upper (D 7) (R 7) [34,257,9,96,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5859 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5860 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 13 104 146 160 80 196 324), lower := (rows 35 259 13 104 146 160 80 128 256), losses := [] }

theorem u5860 : Upper (D 7) (R 7) [34,257,9,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5860 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5861 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,5)], upper := (rows 35 259 13 104 148 160 66 208 336), lower := (rows 35 259 13 104 148 160 66 128 256), losses := [] }

theorem u5861 : Upper (D 7) (R 7) [34,257,9,96,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5862 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 13 104 148 160 80 194 322), lower := (rows 35 259 13 104 148 160 80 128 256), losses := [] }

theorem u5862 : Upper (D 7) (R 7) [34,257,9,96,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5862 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5863 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 232, targets := 3 },{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 259 13 200 22 96 80 160 416), lower := (rows 35 259 13 200 22 96 80 128 256), losses := [] }

theorem u5863 : Upper (D 7) (R 7) [34,257,9,192,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5863 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5864 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 35 259 13 200 22 96 96 144 400), lower := (rows 35 259 13 200 22 96 96 128 256), losses := [] }

theorem u5864 : Upper (D 7) (R 7) [34,257,9,192,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5865 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 259 13 200 22 96 192 176 304), lower := (rows 35 259 13 200 22 96 192 128 256), losses := [] }

theorem u5865 : Upper (D 7) (R 7) [34,257,9,192,6,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5866 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 259 13 200 82 36 80 160 416), lower := (rows 35 259 13 200 82 36 80 128 256), losses := [] }

theorem u5866 : Upper (D 7) (R 7) [34,257,9,192,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5866 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5867 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 136, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 259 13 200 82 36 96 144 400), lower := (rows 35 259 13 200 82 36 96 128 256), losses := [] }

theorem u5867 : Upper (D 7) (R 7) [34,257,9,192,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5867 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5868 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 13 200 82 36 192 176 304), lower := (rows 35 259 13 200 82 36 192 128 256), losses := [] }

theorem u5868 : Upper (D 7) (R 7) [34,257,9,192,66,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5868 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5869 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 168, targets := 3 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 259 13 200 82 160 68 176 304), lower := (rows 35 259 13 200 82 160 68 128 256), losses := [] }

theorem u5869 : Upper (D 7) (R 7) [34,257,9,192,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5869 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5870 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 35 259 13 200 82 160 80 164 292), lower := (rows 35 259 13 200 82 160 80 128 256), losses := [] }

theorem u5870 : Upper (D 7) (R 7) [34,257,9,192,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5870 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5871 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 72, targets := 3 },{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 128 }], pairs := [(3,0),(3,1),(4,0),(4,7)], upper := (rows 35 259 13 200 82 160 96 148 276), lower := (rows 35 259 13 200 82 160 96 128 256), losses := [] }

theorem u5871 : Upper (D 7) (R 7) [34,257,9,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5872 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 168, targets := 3 },{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(3,1)], upper := (rows 35 259 13 200 84 160 66 176 304), lower := (rows 35 259 13 200 84 160 66 128 256), losses := [] }

theorem u5872 : Upper (D 7) (R 7) [34,257,9,192,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5873 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 259 13 200 84 160 80 162 290), lower := (rows 35 259 13 200 84 160 80 128 256), losses := [] }

theorem u5873 : Upper (D 7) (R 7) [34,257,9,192,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5873 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5874 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 419, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(1,6),(3,0),(3,1)], upper := (rows 35 259 13 200 84 160 96 146 274), lower := (rows 35 259 13 200 84 160 96 128 256), losses := [] }

theorem u5874 : Upper (D 7) (R 7) [34,257,9,192,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5875 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 0, region := 80, targets := 128 }], pairs := [(3,0),(4,0),(4,1),(4,7)], upper := (rows 35 259 13 200 112 160 66 148 276), lower := (rows 35 259 13 200 112 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 29 172 67 132 260), good := (rows 114 338 508 248 112 160 66 160 256) }] }

theorem u5875 : Upper (D 7) (R 7) [34,257,9,192,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5876 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 4, region := 259, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 259 13 200 112 160 68 146 274), lower := (rows 35 259 13 200 112 160 68 128 256), losses := [] }

theorem u5876 : Upper (D 7) (R 7) [34,257,9,192,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5876 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5877 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 13 200 112 160 80 134 262), lower := (rows 35 259 13 200 112 160 80 128 256), losses := [] }

theorem u5877 : Upper (D 7) (R 7) [34,257,9,192,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5877 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5878 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 386, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 259 14 28 81 160 96 192 448), lower := (rows 35 259 14 28 81 160 96 128 256), losses := [] }

theorem u5878 : Upper (D 7) (R 7) [34,257,10,20,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5879 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(2,5),(3,1),(3,5),(4,1)], upper := (rows 35 259 14 28 81 160 192 224 352), lower := (rows 35 259 14 28 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 19 511 511 511 511), good := (rows 497 497 508 508 497 480 480 480 480) },{ target := 5, region := (rows 1 2 7 27 17 0 224 128 256), good := (rows 95 287 14 28 93 192 192 192 256) }] }

theorem u5879 : Upper (D 7) (R 7) [34,257,10,20,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5879
end Delivery.IrregularNine14.P07
