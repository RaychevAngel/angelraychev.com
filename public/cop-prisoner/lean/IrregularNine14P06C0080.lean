import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4800 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 130, targets := 68 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 70 328 49 36 68 145 273), lower := (rows 11 162 70 328 49 36 68 128 256), losses := [] }

theorem u4800 : Upper (D 6) (R 6) [10,160,66,320,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4801 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 265, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 70 328 49 36 80 133 261), lower := (rows 11 162 70 328 49 36 80 128 256), losses := [] }

theorem u4801 : Upper (D 6) (R 6) [10,160,66,320,33,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4801 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4802 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 130, targets := 65 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(1,6),(2,5)], upper := (rows 11 162 70 328 52 33 65 148 276), lower := (rows 11 162 70 328 52 33 65 128 256), losses := [] }

theorem u4802 : Upper (D 6) (R 6) [10,160,66,320,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4803 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 11 162 70 328 52 33 68 145 273), lower := (rows 11 162 70 328 52 33 68 128 256), losses := [] }

theorem u4803 : Upper (D 6) (R 6) [10,160,66,320,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4804 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 162 70 328 52 33 80 133 261), lower := (rows 11 162 70 328 52 33 80 128 256), losses := [] }

theorem u4804 : Upper (D 6) (R 6) [10,160,66,320,36,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4804 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4805 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 7, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 162 84 13 273 96 66 164 292), lower := (rows 11 162 84 13 273 96 66 128 256), losses := [] }

theorem u4805 : Upper (D 6) (R 6) [10,160,80,5,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4806 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 13 273 96 68 162 290), lower := (rows 11 162 84 13 273 96 68 128 256), losses := [] }

theorem u4806 : Upper (D 6) (R 6) [10,160,80,5,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4807 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 84 13 273 96 96 134 262), lower := (rows 11 162 84 13 273 96 96 128 256), losses := [] }

theorem u4807 : Upper (D 6) (R 6) [10,160,80,5,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4808 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 84 13 274 36 65 224 352), lower := (rows 11 162 84 13 274 36 65 128 256), losses := [] }

theorem u4808 : Upper (D 6) (R 6) [10,160,80,5,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4809 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,2)], upper := (rows 11 162 84 13 274 36 96 193 321), lower := (rows 11 162 84 13 274 36 96 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 32 98 129 257), good := (rows 475 226 80 409 338 96 96 128 256) }] }

theorem u4809 : Upper (D 6) (R 6) [10,160,80,5,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4810 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 84 13 274 96 65 164 292), lower := (rows 11 162 84 13 274 96 65 128 256), losses := [] }

theorem u4810 : Upper (D 6) (R 6) [10,160,80,5,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4811 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 84 13 274 96 68 161 289), lower := (rows 11 162 84 13 274 96 68 128 256), losses := [] }

theorem u4811 : Upper (D 6) (R 6) [10,160,80,5,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4812 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 84 13 274 96 96 133 261), lower := (rows 11 162 84 13 274 96 96 128 256), losses := [] }

theorem u4812 : Upper (D 6) (R 6) [10,160,80,5,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4813 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 13 276 96 65 162 290), lower := (rows 11 162 84 13 276 96 65 128 256), losses := [] }

theorem u4813 : Upper (D 6) (R 6) [10,160,80,5,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4814 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 7, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 162 84 13 276 96 66 161 289), lower := (rows 11 162 84 13 276 96 66 128 256), losses := [] }

theorem u4814 : Upper (D 6) (R 6) [10,160,80,5,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4815 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 84 13 276 96 96 131 259), lower := (rows 11 162 84 13 276 96 96 128 256), losses := [] }

theorem u4815 : Upper (D 6) (R 6) [10,160,80,5,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4816 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 13 304 36 65 194 322), lower := (rows 11 162 84 13 304 36 65 128 256), losses := [] }

theorem u4816 : Upper (D 6) (R 6) [10,160,80,5,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4817 : Route 9 := (fun mask => (mask,id))

def c4817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4817 : Upper (D 6) (R 6) [10,160,80,5,288,4,2] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,288,4,2] 13 (by decide) (choices 1) [1,64] r4817 c4817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u360
  · exact u361

def b4818 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 13 304 96 65 134 262), lower := (rows 11 162 84 13 304 96 65 128 256), losses := [] }

theorem u4818 : Upper (D 6) (R 6) [10,160,80,5,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4819 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(4,1)], upper := (rows 11 162 84 13 304 96 66 133 261), lower := (rows 11 162 84 13 304 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 100 64 136 264), good := (rows 409 160 116 445 304 96 96 128 256) }] }

theorem u4819 : Upper (D 6) (R 6) [10,160,80,5,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4820 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 84 13 304 96 68 131 259), lower := (rows 11 162 84 13 304 96 68 128 256), losses := [] }

theorem u4820 : Upper (D 6) (R 6) [10,160,80,5,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4821 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 84 44 274 33 65 196 324), lower := (rows 11 162 84 44 274 33 65 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 32 64 132 260), good := (rows 26 162 468 446 274 32 64 128 256) }] }

theorem u4821 : Upper (D 6) (R 6) [10,160,80,36,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4822 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 84 44 274 33 68 193 321), lower := (rows 11 162 84 44 274 33 68 128 256), losses := [] }

theorem u4822 : Upper (D 6) (R 6) [10,160,80,36,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4823 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 84 73 52 288 65 134 262), lower := (rows 11 162 84 73 52 288 65 128 256), losses := [] }

theorem u4823 : Upper (D 6) (R 6) [10,160,80,65,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4823 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4824 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 84 73 52 288 66 133 261), lower := (rows 11 162 84 73 52 288 66 128 256), losses := [] }

theorem u4824 : Upper (D 6) (R 6) [10,160,80,65,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4824 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4825 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 162 84 73 52 288 68 131 259), lower := (rows 11 162 84 73 52 288 68 128 256), losses := [] }

theorem u4825 : Upper (D 6) (R 6) [10,160,80,65,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4825 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4826 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 84 73 274 36 65 164 292), lower := (rows 11 162 84 73 274 36 65 128 256), losses := [] }

theorem u4826 : Upper (D 6) (R 6) [10,160,80,65,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4827 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 84 73 274 36 68 161 289), lower := (rows 11 162 84 73 274 36 68 128 256), losses := [] }

theorem u4827 : Upper (D 6) (R 6) [10,160,80,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4828 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 162 84 73 274 36 96 133 261), lower := (rows 11 162 84 73 274 36 96 128 256), losses := [] }

theorem u4828 : Upper (D 6) (R 6) [10,160,80,65,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4829 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 84 73 304 36 65 134 262), lower := (rows 11 162 84 73 304 36 65 128 256), losses := [] }

theorem u4829 : Upper (D 6) (R 6) [10,160,80,65,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4830 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 84 73 304 36 66 133 261), lower := (rows 11 162 84 73 304 36 66 128 256), losses := [] }

theorem u4830 : Upper (D 6) (R 6) [10,160,80,65,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4831 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 84 73 304 36 68 131 259), lower := (rows 11 162 84 73 304 36 68 128 256), losses := [] }

theorem u4831 : Upper (D 6) (R 6) [10,160,80,65,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4832 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 104 274 33 65 132 260), lower := (rows 11 162 84 104 274 33 65 128 256), losses := [] }

theorem u4832 : Upper (D 6) (R 6) [10,160,80,96,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4833 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 84 104 274 33 68 133 261), lower := (rows 11 162 84 104 274 33 68 128 256), losses := [] }

theorem u4833 : Upper (D 6) (R 6) [10,160,80,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4834 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 104 276 33 65 134 262), lower := (rows 11 162 84 104 276 33 65 128 256), losses := [] }

theorem u4834 : Upper (D 6) (R 6) [10,160,80,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4835 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 104 276 33 66 133 261), lower := (rows 11 162 84 104 276 33 66 128 256), losses := [] }

theorem u4835 : Upper (D 6) (R 6) [10,160,80,96,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4836 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 84 104 276 33 68 131 259), lower := (rows 11 162 84 104 276 33 68 128 256), losses := [] }

theorem u4836 : Upper (D 6) (R 6) [10,160,80,96,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4837 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 84 265 21 96 66 164 292), lower := (rows 11 162 84 265 21 96 66 128 256), losses := [] }

theorem u4837 : Upper (D 6) (R 6) [10,160,80,257,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4838 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 84 265 21 96 68 162 290), lower := (rows 11 162 84 265 21 96 68 128 256), losses := [] }

theorem u4838 : Upper (D 6) (R 6) [10,160,80,257,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4839 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 84 265 21 96 96 134 262), lower := (rows 11 162 84 265 21 96 96 128 256), losses := [] }

theorem u4839 : Upper (D 6) (R 6) [10,160,80,257,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4840 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 150, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 265 22 96 65 164 292), lower := (rows 11 162 84 265 22 96 65 128 256), losses := [] }

theorem u4840 : Upper (D 6) (R 6) [10,160,80,257,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4841 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 84 265 22 96 68 161 289), lower := (rows 11 162 84 265 22 96 68 128 256), losses := [] }

theorem u4841 : Upper (D 6) (R 6) [10,160,80,257,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4842 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 84 265 22 96 96 133 261), lower := (rows 11 162 84 265 22 96 96 128 256), losses := [] }

theorem u4842 : Upper (D 6) (R 6) [10,160,80,257,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4843 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 84 265 49 36 66 196 324), lower := (rows 11 162 84 265 49 36 66 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 148 276), good := (rows 75 194 476 329 477 388 66 128 256) }] }

theorem u4843 : Upper (D 6) (R 6) [10,160,80,257,33,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4844 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 84 265 49 36 68 194 322), lower := (rows 11 162 84 265 49 36 68 128 256), losses := [] }

theorem u4844 : Upper (D 6) (R 6) [10,160,80,257,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4845 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 162 84 265 49 96 66 132 260), lower := (rows 11 162 84 265 49 96 66 128 256), losses := [] }

theorem u4845 : Upper (D 6) (R 6) [10,160,80,257,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4846 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 84 265 49 96 68 134 262), lower := (rows 11 162 84 265 49 96 68 128 256), losses := [] }

theorem u4846 : Upper (D 6) (R 6) [10,160,80,257,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4847 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 268 21 96 65 162 290), lower := (rows 11 162 84 268 21 96 65 128 256), losses := [] }

theorem u4847 : Upper (D 6) (R 6) [10,160,80,260,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4848 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 84 268 21 96 66 161 289), lower := (rows 11 162 84 268 21 96 66 128 256), losses := [] }

theorem u4848 : Upper (D 6) (R 6) [10,160,80,260,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4849 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 162 84 268 21 96 96 131 259), lower := (rows 11 162 84 268 21 96 96 128 256), losses := [] }

theorem u4849 : Upper (D 6) (R 6) [10,160,80,260,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4850 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 84 268 22 33 65 224 352), lower := (rows 11 162 84 268 22 33 65 128 256), losses := [] }

theorem u4850 : Upper (D 6) (R 6) [10,160,80,260,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4851 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 162 84 268 22 33 96 193 321), lower := (rows 11 162 84 268 22 33 96 128 256), losses := [] }

theorem u4851 : Upper (D 6) (R 6) [10,160,80,260,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4852 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 84 268 22 96 65 161 289), lower := (rows 11 162 84 268 22 96 65 128 256), losses := [] }

theorem u4852 : Upper (D 6) (R 6) [10,160,80,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4853 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 84 268 22 96 96 129 257), lower := (rows 11 162 84 268 22 96 96 128 256), losses := [] }

theorem u4853 : Upper (D 6) (R 6) [10,160,80,260,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4854 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 84 268 49 96 65 134 262), lower := (rows 11 162 84 268 49 96 65 128 256), losses := [] }

theorem u4854 : Upper (D 6) (R 6) [10,160,80,260,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4855 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 11 162 84 268 49 96 66 133 261), lower := (rows 11 162 84 268 49 96 66 128 256), losses := [] }

theorem u4855 : Upper (D 6) (R 6) [10,160,80,260,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4856 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 130, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 11 162 84 268 49 96 68 131 259), lower := (rows 11 162 84 268 49 96 68 128 256), losses := [] }

theorem u4856 : Upper (D 6) (R 6) [10,160,80,260,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4857 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 162 84 268 52 33 65 194 322), lower := (rows 11 162 84 268 52 33 65 128 256), losses := [] }

theorem u4857 : Upper (D 6) (R 6) [10,160,80,260,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4858 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 162 84 268 52 33 66 193 321), lower := (rows 11 162 84 268 52 33 66 128 256), losses := [] }

theorem u4858 : Upper (D 6) (R 6) [10,160,80,260,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4859 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 162 84 296 21 33 66 196 324), lower := (rows 11 162 84 296 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 67 148 276), good := (rows 74 226 468 296 468 96 66 128 256) }] }

theorem u4859 : Upper (D 6) (R 6) [10,160,80,288,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4859
end Delivery.IrregularNine14.P06
