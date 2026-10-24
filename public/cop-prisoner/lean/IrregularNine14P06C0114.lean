import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6840 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 44 81 96 66 148 276), lower := (rows 35 131 268 44 81 96 66 128 256), losses := [] }

theorem u6840 : Upper (D 6) (R 6) [34,129,264,36,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6841 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 44 81 96 68 146 274), lower := (rows 35 131 268 44 81 96 68 128 256), losses := [] }

theorem u6841 : Upper (D 6) (R 6) [34,129,264,36,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6842 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 44 81 96 80 134 262), lower := (rows 35 131 268 44 81 96 80 128 256), losses := [] }

theorem u6842 : Upper (D 6) (R 6) [34,129,264,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6842 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6843 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 44 82 96 65 148 276), lower := (rows 35 131 268 44 82 96 65 128 256), losses := [] }

theorem u6843 : Upper (D 6) (R 6) [34,129,264,36,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6844 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 44 82 96 68 145 273), lower := (rows 35 131 268 44 82 96 68 128 256), losses := [] }

theorem u6844 : Upper (D 6) (R 6) [34,129,264,36,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6845 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 44 82 96 80 133 261), lower := (rows 35 131 268 44 82 96 80 128 256), losses := [] }

theorem u6845 : Upper (D 6) (R 6) [34,129,264,36,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6845 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6846 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 131 268 56 21 96 66 196 324), lower := (rows 35 131 268 56 21 96 66 128 256), losses := [] }

theorem u6846 : Upper (D 6) (R 6) [34,129,264,48,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6847 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 5, region := 131, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 268 56 21 96 68 194 322), lower := (rows 35 131 268 56 21 96 68 128 256), losses := [] }

theorem u6847 : Upper (D 6) (R 6) [34,129,264,48,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6848 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 268 56 22 96 65 196 324), lower := (rows 35 131 268 56 22 96 65 128 256), losses := [] }

theorem u6848 : Upper (D 6) (R 6) [34,129,264,48,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6849 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 5, region := 131, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 268 56 22 96 68 193 321), lower := (rows 35 131 268 56 22 96 68 128 256), losses := [] }

theorem u6849 : Upper (D 6) (R 6) [34,129,264,48,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6850 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 56 81 36 66 196 324), lower := (rows 35 131 268 56 81 36 66 128 256), losses := [] }

theorem u6850 : Upper (D 6) (R 6) [34,129,264,48,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6851 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 130, targets := 36 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 131 268 56 81 36 68 194 322), lower := (rows 35 131 268 56 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 124 124 129 257), good := (rows 482 386 364 124 508 100 100 128 256) }] }

theorem u6851 : Upper (D 6) (R 6) [34,129,264,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6852 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 56 82 36 65 196 324), lower := (rows 35 131 268 56 82 36 65 128 256), losses := [] }

theorem u6852 : Upper (D 6) (R 6) [34,129,264,48,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6853 : PairBound 9 := { available := 65, camps := [], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 268 56 82 36 68 193 321), lower := (rows 35 131 268 56 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 25 17 100 100 128 256), good := (rows 122 154 364 120 122 100 100 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 100 129 257), good := (rows 481 385 364 120 120 100 100 128 256) }] }

theorem u6853 : Upper (D 6) (R 6) [34,129,264,48,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6854 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 268 73 22 36 80 224 352), lower := (rows 35 131 268 73 22 36 80 128 256), losses := [] }

theorem u6854 : Upper (D 6) (R 6) [34,129,264,65,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6854 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6855 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 131 268 73 22 36 96 208 336), lower := (rows 35 131 268 73 22 36 96 128 256), losses := [] }

theorem u6855 : Upper (D 6) (R 6) [34,129,264,65,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6856 : Route 9 := (fun mask => (mask,id))

def c6856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6856 : Upper (D 6) (R 6) [34,129,264,65,6,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,6,64,4] 13 (by decide) (choices 1) [16,32] r6856 c6856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u519
  · exact u520

def b6857 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 268 73 22 96 80 164 292), lower := (rows 35 131 268 73 22 96 80 128 256), losses := [] }

theorem u6857 : Upper (D 6) (R 6) [34,129,264,65,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6857 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6858 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 131 268 73 22 96 96 148 276), lower := (rows 35 131 268 73 22 96 96 128 256), losses := [] }

theorem u6858 : Upper (D 6) (R 6) [34,129,264,65,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6859 : PairBound 9 := { available := 48, camps := [], pairs := [(2,0),(3,1),(4,0)], upper := (rows 35 131 268 73 82 36 68 176 304), lower := (rows 35 131 268 73 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 108 108 153 281), good := (rows 498 402 492 508 498 100 100 128 256) },{ target := 1, region := (rows 1 0 4 9 16 100 100 144 272), good := (rows 105 137 364 105 496 100 100 128 256) }] }

theorem u6859 : Upper (D 6) (R 6) [34,129,264,65,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6860 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 131 268 73 82 36 80 164 292), lower := (rows 35 131 268 73 82 36 80 128 256), losses := [] }

theorem u6860 : Upper (D 6) (R 6) [34,129,264,65,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6860 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6861 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 131 268 73 82 36 96 148 276), lower := (rows 35 131 268 73 82 36 96 128 256), losses := [] }

theorem u6861 : Upper (D 6) (R 6) [34,129,264,65,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6862 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 268 73 84 36 66 176 304), lower := (rows 35 131 268 73 84 36 66 128 256), losses := [] }

theorem u6862 : Upper (D 6) (R 6) [34,129,264,65,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6863 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 268 73 84 36 80 162 290), lower := (rows 35 131 268 73 84 36 80 128 256), losses := [] }

theorem u6863 : Upper (D 6) (R 6) [34,129,264,65,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6863 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6864 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 131 268 73 84 36 96 146 274), lower := (rows 35 131 268 73 84 36 96 128 256), losses := [] }

theorem u6864 : Upper (D 6) (R 6) [34,129,264,65,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6865 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 268 73 112 36 66 148 276), lower := (rows 35 131 268 73 112 36 66 128 256), losses := [] }

theorem u6865 : Upper (D 6) (R 6) [34,129,264,65,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6866 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 268 73 112 36 68 146 274), lower := (rows 35 131 268 73 112 36 68 128 256), losses := [] }

theorem u6866 : Upper (D 6) (R 6) [34,129,264,65,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6867 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 268 73 112 36 80 134 262), lower := (rows 35 131 268 73 112 36 80 128 256), losses := [] }

theorem u6867 : Upper (D 6) (R 6) [34,129,264,65,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6867 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6868 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 268 74 21 36 80 224 352), lower := (rows 35 131 268 74 21 36 80 128 256), losses := [] }

theorem u6868 : Upper (D 6) (R 6) [34,129,264,66,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6868 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6869 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,0),(3,0),(3,2)], upper := (rows 35 131 268 74 21 36 96 208 336), lower := (rows 35 131 268 74 21 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 11 16 52 117 144 272), good := (rows 106 202 364 74 508 100 96 128 256) }] }

theorem u6869 : Upper (D 6) (R 6) [34,129,264,66,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6870 : Route 9 := (fun mask => (mask,id))

def c6870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6870 : Upper (D 6) (R 6) [34,129,264,66,5,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,5,64,4] 13 (by decide) (choices 1) [16,32] r6870 c6870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u521
  · exact u522

def b6871 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 268 74 21 96 80 164 292), lower := (rows 35 131 268 74 21 96 80 128 256), losses := [] }

theorem u6871 : Upper (D 6) (R 6) [34,129,264,66,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6871 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6872 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 268 74 21 96 96 148 276), lower := (rows 35 131 268 74 21 96 96 128 256), losses := [] }

theorem u6872 : Upper (D 6) (R 6) [34,129,264,66,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6873 : PairBound 9 := { available := 48, camps := [], pairs := [(2,0),(3,0),(4,1)], upper := (rows 35 131 268 74 81 36 68 176 304), lower := (rows 35 131 268 74 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 9 16 116 116 144 272), good := (rows 106 138 364 106 508 100 100 128 256) },{ target := 1, region := (rows 1 0 4 8 17 100 100 145 273), good := (rows 497 401 364 104 497 100 100 128 256) }] }

theorem u6873 : Upper (D 6) (R 6) [34,129,264,66,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6874 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 131 268 74 81 36 80 164 292), lower := (rows 35 131 268 74 81 36 80 128 256), losses := [] }

theorem u6874 : Upper (D 6) (R 6) [34,129,264,66,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6874 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6875 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 131 268 74 81 36 96 148 276), lower := (rows 35 131 268 74 81 36 96 128 256), losses := [] }

theorem u6875 : Upper (D 6) (R 6) [34,129,264,66,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6876 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 268 74 84 36 65 176 304), lower := (rows 35 131 268 74 84 36 65 128 256), losses := [] }

theorem u6876 : Upper (D 6) (R 6) [34,129,264,66,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6877 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 268 74 84 36 80 161 289), lower := (rows 35 131 268 74 84 36 80 128 256), losses := [] }

theorem u6877 : Upper (D 6) (R 6) [34,129,264,66,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6877 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6878 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 268 74 84 36 96 145 273), lower := (rows 35 131 268 74 84 36 96 128 256), losses := [] }

theorem u6878 : Upper (D 6) (R 6) [34,129,264,66,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6879 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 268 74 112 36 65 148 276), lower := (rows 35 131 268 74 112 36 65 128 256), losses := [] }

theorem u6879 : Upper (D 6) (R 6) [34,129,264,66,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6880 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 268 74 112 36 68 145 273), lower := (rows 35 131 268 74 112 36 68 128 256), losses := [] }

theorem u6880 : Upper (D 6) (R 6) [34,129,264,66,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6881 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 74 112 36 80 133 261), lower := (rows 35 131 268 74 112 36 80 128 256), losses := [] }

theorem u6881 : Upper (D 6) (R 6) [34,129,264,66,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6881 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6882 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 76 21 96 66 176 304), lower := (rows 35 131 268 76 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 123 67 144 272), good := (rows 98 226 300 108 508 96 98 128 256) }] }

theorem u6882 : Upper (D 6) (R 6) [34,129,264,68,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6883 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 268 76 21 96 80 162 290), lower := (rows 35 131 268 76 21 96 80 128 256), losses := [] }

theorem u6883 : Upper (D 6) (R 6) [34,129,264,68,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6883 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6884 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 76 21 96 96 146 274), lower := (rows 35 131 268 76 21 96 96 128 256), losses := [] }

theorem u6884 : Upper (D 6) (R 6) [34,129,264,68,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6885 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 76 22 96 65 176 304), lower := (rows 35 131 268 76 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 109 104 19 104 64 193 321), good := (rows 446 406 300 492 22 492 508 128 256) }] }

theorem u6885 : Upper (D 6) (R 6) [34,129,264,68,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6886 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 268 76 22 96 80 161 289), lower := (rows 35 131 268 76 22 96 80 128 256), losses := [] }

theorem u6886 : Upper (D 6) (R 6) [34,129,264,68,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6886 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6887 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 76 22 96 96 145 273), lower := (rows 35 131 268 76 22 96 96 128 256), losses := [] }

theorem u6887 : Upper (D 6) (R 6) [34,129,264,68,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6888 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 292, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 88 21 96 66 164 292), lower := (rows 35 131 268 88 21 96 66 128 256), losses := [] }

theorem u6888 : Upper (D 6) (R 6) [34,129,264,80,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6889 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 88 21 96 68 162 290), lower := (rows 35 131 268 88 21 96 68 128 256), losses := [] }

theorem u6889 : Upper (D 6) (R 6) [34,129,264,80,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6890 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 268 88 21 96 96 134 262), lower := (rows 35 131 268 88 21 96 96 128 256), losses := [] }

theorem u6890 : Upper (D 6) (R 6) [34,129,264,80,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6891 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 292, targets := 3 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 88 22 96 65 164 292), lower := (rows 35 131 268 88 22 96 65 128 256), losses := [] }

theorem u6891 : Upper (D 6) (R 6) [34,129,264,80,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6892 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 88 22 96 68 161 289), lower := (rows 35 131 268 88 22 96 68 128 256), losses := [] }

theorem u6892 : Upper (D 6) (R 6) [34,129,264,80,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6893 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 268 88 22 96 96 133 261), lower := (rows 35 131 268 88 22 96 96 128 256), losses := [] }

theorem u6893 : Upper (D 6) (R 6) [34,129,264,80,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6894 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 194, targets := 36 },{ cop := 0, region := 72, targets := 1 }], pairs := [(1,2),(1,5),(3,0)], upper := (rows 35 131 268 104 21 36 66 208 336), lower := (rows 35 131 268 104 21 36 66 128 256), losses := [] }

theorem u6894 : Upper (D 6) (R 6) [34,129,264,96,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6895 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 131, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 268 104 21 36 80 194 322), lower := (rows 35 131 268 104 21 36 80 128 256), losses := [] }

theorem u6895 : Upper (D 6) (R 6) [34,129,264,96,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6895 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6896 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 72, targets := 6 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(3,2)], upper := (rows 35 131 268 104 22 36 65 208 336), lower := (rows 35 131 268 104 22 36 65 128 256), losses := [] }

theorem u6896 : Upper (D 6) (R 6) [34,129,264,96,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6897 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 268 104 22 36 80 193 321), lower := (rows 35 131 268 104 22 36 80 128 256), losses := [] }

theorem u6897 : Upper (D 6) (R 6) [34,129,264,96,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6897 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6898 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 104 81 36 66 148 276), lower := (rows 35 131 268 104 81 36 66 128 256), losses := [] }

theorem u6898 : Upper (D 6) (R 6) [34,129,264,96,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6899 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 104 81 36 68 146 274), lower := (rows 35 131 268 104 81 36 68 128 256), losses := [] }

theorem u6899 : Upper (D 6) (R 6) [34,129,264,96,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6899
end Delivery.IrregularNine14.P06
