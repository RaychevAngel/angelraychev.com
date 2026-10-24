import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4800 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 276 160 66 176 304), lower := (rows 35 67 13 200 276 160 66 128 256), losses := [] }

theorem u4800 : Upper (D 7) (R 7) [34,65,9,192,260,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4801 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 168, targets := 1 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 200 276 160 80 162 290), lower := (rows 35 67 13 200 276 160 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 20 175 84 131 259), good := (rows 426 490 508 232 380 160 80 160 256) }] }

theorem u4801 : Upper (D 7) (R 7) [34,65,9,192,260,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4801 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4802 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(3,5),(4,5)], upper := (rows 35 67 13 200 276 160 96 146 274), lower := (rows 35 67 13 200 276 160 96 128 256), losses := [] }

theorem u4802 : Upper (D 7) (R 7) [34,65,9,192,260,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4803 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 304 160 66 148 276), lower := (rows 35 67 13 200 304 160 66 128 256), losses := [] }

theorem u4803 : Upper (D 7) (R 7) [34,65,9,192,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4804 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 200 304 160 68 146 274), lower := (rows 35 67 13 200 304 160 68 128 256), losses := [] }

theorem u4804 : Upper (D 7) (R 7) [34,65,9,192,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4804 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4805 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 140, targets := 32 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5)], upper := (rows 35 67 13 200 304 160 80 134 262), lower := (rows 35 67 13 200 304 160 80 128 256), losses := [] }

theorem u4805 : Upper (D 7) (R 7) [34,65,9,192,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4805 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4806 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 400 48 66 164 292), lower := (rows 35 67 13 200 400 48 66 128 256), losses := [] }

theorem u4806 : Upper (D 7) (R 7) [34,65,9,192,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4806 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4807 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 13 200 400 48 68 162 290), lower := (rows 35 67 13 200 400 48 68 128 256), losses := [] }

theorem u4807 : Upper (D 7) (R 7) [34,65,9,192,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4807 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4808 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 200 400 48 96 134 262), lower := (rows 35 67 13 200 400 48 96 128 256), losses := [] }

theorem u4808 : Upper (D 7) (R 7) [34,65,9,192,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4808 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4809 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 396, targets := 32 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 35 67 13 266 52 160 80 192 448), lower := (rows 35 67 13 266 52 160 80 128 256), losses := [] }

theorem u4809 : Upper (D 7) (R 7) [34,65,9,258,36,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4809 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4810 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 240, targets := 3 }], pairs := [(0,6),(1,5),(4,0),(4,1)], upper := (rows 35 67 13 266 52 160 192 208 336), lower := (rows 35 67 13 266 52 160 192 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 240 144 272), good := (rows 67 67 15 266 468 192 192 192 256) },{ target := 6, region := (rows 3 2 12 8 16 224 0 128 256), good := (rows 35 35 13 271 52 160 160 160 256) }] }

theorem u4810 : Upper (D 7) (R 7) [34,65,9,258,36,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4811 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 35 67 13 266 84 160 80 160 416), lower := (rows 35 67 13 266 84 160 80 128 256), losses := [] }

theorem u4811 : Upper (D 7) (R 7) [34,65,9,258,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4811 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4812 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,5),(3,5),(4,0),(4,5)], upper := (rows 35 67 13 266 84 160 96 144 400), lower := (rows 35 67 13 266 84 160 96 128 256), losses := [] }

theorem u4812 : Upper (D 7) (R 7) [34,65,9,258,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4813 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 240, targets := 3 }], pairs := [(0,6),(1,5),(4,0),(4,1)], upper := (rows 35 67 13 266 84 160 192 176 304), lower := (rows 35 67 13 266 84 160 192 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 15 266 84 192 192 192 256) },{ target := 6, region := (rows 3 2 12 8 16 240 0 144 272), good := (rows 35 35 13 271 436 160 160 160 256) }] }

theorem u4813 : Upper (D 7) (R 7) [34,65,9,258,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4814 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 1, region := 424, targets := 1 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 35 67 13 266 148 160 80 224 352), lower := (rows 35 67 13 266 148 160 80 128 256), losses := [] }

theorem u4814 : Upper (D 7) (R 7) [34,65,9,258,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4814 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4815 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,5),(3,5),(4,0),(4,5)], upper := (rows 35 67 13 266 148 160 96 208 336), lower := (rows 35 67 13 266 148 160 96 128 256), losses := [] }

theorem u4815 : Upper (D 7) (R 7) [34,65,9,258,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4816 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 266 208 160 68 176 304), lower := (rows 35 67 13 266 208 160 68 128 256), losses := [] }

theorem u4816 : Upper (D 7) (R 7) [34,65,9,258,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4816 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4817 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 13 266 208 160 80 164 292), lower := (rows 35 67 13 266 208 160 80 128 256), losses := [] }

theorem u4817 : Upper (D 7) (R 7) [34,65,9,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4817 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4818 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,5),(3,5),(4,0),(4,5)], upper := (rows 35 67 13 266 208 160 96 148 276), lower := (rows 35 67 13 266 208 160 96 128 256), losses := [] }

theorem u4818 : Upper (D 7) (R 7) [34,65,9,258,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4819 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 428, targets := 2 },{ cop := 0, region := 208, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 35 67 13 268 146 160 80 224 352), lower := (rows 35 67 13 268 146 160 80 128 256), losses := [] }

theorem u4819 : Upper (D 7) (R 7) [34,65,9,260,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4819 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4820 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 268 146 160 96 208 336), lower := (rows 35 67 13 268 146 160 96 128 256), losses := [] }

theorem u4820 : Upper (D 7) (R 7) [34,65,9,260,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4821 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 268 208 160 66 176 304), lower := (rows 35 67 13 268 208 160 66 128 256), losses := [] }

theorem u4821 : Upper (D 7) (R 7) [34,65,9,260,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4822 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 13 268 208 160 80 162 290), lower := (rows 35 67 13 268 208 160 80 128 256), losses := [] }

theorem u4822 : Upper (D 7) (R 7) [34,65,9,260,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4822 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4823 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 80, targets := 1 }], pairs := [(2,5),(3,5),(4,0),(4,5)], upper := (rows 35 67 13 268 208 160 96 146 274), lower := (rows 35 67 13 268 208 160 96 128 256), losses := [] }

theorem u4823 : Upper (D 7) (R 7) [34,65,9,260,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4824 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7)], upper := (rows 35 67 13 280 84 160 66 160 416), lower := (rows 35 67 13 280 84 160 66 128 256), losses := [] }

theorem u4824 : Upper (D 7) (R 7) [34,65,9,272,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4825 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 280 84 160 96 130 386), lower := (rows 35 67 13 280 84 160 96 128 256), losses := [] }

theorem u4825 : Upper (D 7) (R 7) [34,65,9,272,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4826 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(4,0)], upper := (rows 35 67 13 280 84 160 192 162 290), lower := (rows 35 67 13 280 84 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 231 231 131 259), good := (rows 482 482 508 280 124 224 224 224 256) },{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 15 280 84 192 192 192 256) }] }

theorem u4826 : Upper (D 7) (R 7) [34,65,9,272,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4827 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 280 146 36 96 192 448), lower := (rows 35 67 13 280 146 36 96 128 256), losses := [] }

theorem u4827 : Upper (D 7) (R 7) [34,65,9,272,130,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4827 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4828 : Route 9 := (fun mask => (mask,id))

def c4828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4828 : Upper (D 7) (R 7) [34,65,9,272,130,4,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,130,4,128] 13 (by decide) (choices 1) [32,64] r4828 c4828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u374
  · exact u375

def b4829 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 280 146 160 68 224 352), lower := (rows 35 67 13 280 146 160 68 128 256), losses := [] }

theorem u4829 : Upper (D 7) (R 7) [34,65,9,272,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4829 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4830 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 280 146 160 96 196 324), lower := (rows 35 67 13 280 146 160 96 128 256), losses := [] }

theorem u4830 : Upper (D 7) (R 7) [34,65,9,272,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4831 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 280 208 36 66 160 416), lower := (rows 35 67 13 280 208 36 66 128 256), losses := [] }

theorem u4831 : Upper (D 7) (R 7) [34,65,9,272,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4831 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4832 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 280 208 36 96 130 386), lower := (rows 35 67 13 280 208 36 96 128 256), losses := [] }

theorem u4832 : Upper (D 7) (R 7) [34,65,9,272,192,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4832 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4833 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 280 208 36 192 162 290), lower := (rows 35 67 13 280 208 36 192 128 256), losses := [] }

theorem u4833 : Upper (D 7) (R 7) [34,65,9,272,192,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4833 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4834 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 280 208 160 66 164 292), lower := (rows 35 67 13 280 208 160 66 128 256), losses := [] }

theorem u4834 : Upper (D 7) (R 7) [34,65,9,272,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4835 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 280 208 160 68 162 290), lower := (rows 35 67 13 280 208 160 68 128 256), losses := [] }

theorem u4835 : Upper (D 7) (R 7) [34,65,9,272,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4835 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4836 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 80, targets := 1 }], pairs := [(2,5),(3,5),(4,0),(4,5)], upper := (rows 35 67 13 280 208 160 96 134 262), lower := (rows 35 67 13 280 208 160 96 128 256), losses := [] }

theorem u4836 : Upper (D 7) (R 7) [34,65,9,272,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4837 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 13 296 84 160 66 144 400), lower := (rows 35 67 13 296 84 160 66 128 256), losses := [] }

theorem u4837 : Upper (D 7) (R 7) [34,65,9,288,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4838 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 296 84 160 80 130 386), lower := (rows 35 67 13 296 84 160 80 128 256), losses := [] }

theorem u4838 : Upper (D 7) (R 7) [34,65,9,288,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4838 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4839 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(0,6),(1,5),(2,7),(4,5)], upper := (rows 35 67 13 296 84 160 192 146 274), lower := (rows 35 67 13 296 84 160 192 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 224 0 128 256), good := (rows 35 35 13 296 52 160 160 160 256) },{ target := 7, region := (rows 1 2 7 9 18 32 64 0 259), good := (rows 319 351 269 296 84 32 64 0 256) }] }

theorem u4839 : Upper (D 7) (R 7) [34,65,9,288,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4840 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 296 146 160 68 208 336), lower := (rows 35 67 13 296 146 160 68 128 256), losses := [] }

theorem u4840 : Upper (D 7) (R 7) [34,65,9,288,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4840 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4841 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 428, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 67 13 296 146 160 80 196 324), lower := (rows 35 67 13 296 146 160 80 128 256), losses := [] }

theorem u4841 : Upper (D 7) (R 7) [34,65,9,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4841 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4842 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 296 148 160 66 208 336), lower := (rows 35 67 13 296 148 160 66 128 256), losses := [] }

theorem u4842 : Upper (D 7) (R 7) [34,65,9,288,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4843 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 1, region := 424, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 67 13 296 148 160 80 194 322), lower := (rows 35 67 13 296 148 160 80 128 256), losses := [] }

theorem u4843 : Upper (D 7) (R 7) [34,65,9,288,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4843 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4844 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 296 208 160 66 148 276), lower := (rows 35 67 13 296 208 160 66 128 256), losses := [] }

theorem u4844 : Upper (D 7) (R 7) [34,65,9,288,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4845 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 296 208 160 68 146 274), lower := (rows 35 67 13 296 208 160 68 128 256), losses := [] }

theorem u4845 : Upper (D 7) (R 7) [34,65,9,288,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4845 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4846 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 13 296 208 160 80 134 262), lower := (rows 35 67 13 296 208 160 80 128 256), losses := [] }

theorem u4846 : Upper (D 7) (R 7) [34,65,9,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4846 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4847 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 328 52 160 66 144 400), lower := (rows 35 67 13 328 52 160 66 128 256), losses := [] }

theorem u4847 : Upper (D 7) (R 7) [34,65,9,320,36,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4848 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 396, targets := 32 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5)], upper := (rows 35 67 13 328 52 160 80 130 386), lower := (rows 35 67 13 328 52 160 80 128 256), losses := [] }

theorem u4848 : Upper (D 7) (R 7) [34,65,9,320,36,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4848 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4849 : PairBound 9 := { available := 18, camps := [], pairs := [(0,6),(1,5),(2,7),(3,7)], upper := (rows 35 67 13 328 52 160 192 146 274), lower := (rows 35 67 13 328 52 160 192 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 15 328 84 192 192 192 256) },{ target := 6, region := (rows 3 2 4 8 16 224 0 128 256), good := (rows 35 35 13 296 52 160 160 160 256) },{ target := 7, region := (rows 1 2 7 10 17 32 64 0 259), good := (rows 319 351 285 328 52 32 64 0 256) }] }

theorem u4849 : Upper (D 7) (R 7) [34,65,9,320,36,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4850 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 328 146 160 68 176 304), lower := (rows 35 67 13 328 146 160 68 128 256), losses := [] }

theorem u4850 : Upper (D 7) (R 7) [34,65,9,320,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4850 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4851 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 428, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 13 328 146 160 80 164 292), lower := (rows 35 67 13 328 146 160 80 128 256), losses := [] }

theorem u4851 : Upper (D 7) (R 7) [34,65,9,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4851 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4852 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 328 146 160 96 148 276), lower := (rows 35 67 13 328 146 160 96 128 256), losses := [] }

theorem u4852 : Upper (D 7) (R 7) [34,65,9,320,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4853 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 328 148 160 66 176 304), lower := (rows 35 67 13 328 148 160 66 128 256), losses := [] }

theorem u4853 : Upper (D 7) (R 7) [34,65,9,320,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4854 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 424, targets := 1 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 328 148 160 80 162 290), lower := (rows 35 67 13 328 148 160 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 20 183 84 131 259), good := (rows 426 490 508 328 252 160 112 160 256) }] }

theorem u4854 : Upper (D 7) (R 7) [34,65,9,320,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4854 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4855 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 328 148 160 96 146 274), lower := (rows 35 67 13 328 148 160 96 128 256), losses := [] }

theorem u4855 : Upper (D 7) (R 7) [34,65,9,320,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4856 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7)], upper := (rows 35 67 13 392 84 160 66 176 304), lower := (rows 35 67 13 392 84 160 66 128 256), losses := [] }

theorem u4856 : Upper (D 7) (R 7) [34,65,9,384,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4857 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 35 67 13 392 84 160 80 162 290), lower := (rows 35 67 13 392 84 160 80 128 256), losses := [] }

theorem u4857 : Upper (D 7) (R 7) [34,65,9,384,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4857 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4858 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 392 84 160 96 146 274), lower := (rows 35 67 13 392 84 160 96 128 256), losses := [] }

theorem u4858 : Upper (D 7) (R 7) [34,65,9,384,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4859 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 392 112 160 66 148 276), lower := (rows 35 67 13 392 112 160 66 128 256), losses := [] }

theorem u4859 : Upper (D 7) (R 7) [34,65,9,384,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4859
end Delivery.IrregularNine14.P07
