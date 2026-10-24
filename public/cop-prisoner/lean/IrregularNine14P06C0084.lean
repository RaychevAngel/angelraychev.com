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

def b5040 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 260, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 162 262 28 81 96 96 133 261), lower := (rows 11 162 262 28 81 96 96 128 256), losses := [] }

theorem u5040 : Upper (D 6) (R 6) [10,160,258,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5041 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 262 28 112 33 65 196 324), lower := (rows 11 162 262 28 112 33 65 128 256), losses := [] }

theorem u5041 : Upper (D 6) (R 6) [10,160,258,20,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5042 : Route 9 := (fun mask => (mask,id))

def c5042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5042 : Upper (D 6) (R 6) [10,160,258,20,96,1,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,96,1,4] 13 (by decide) (choices 1) [1,64] r5042 c5042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u374
  · exact u375

def b5043 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(0,2),(2,5),(4,1)], upper := (rows 11 162 262 28 112 36 65 193 321), lower := (rows 11 162 262 28 112 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 193 321), good := (rows 505 160 292 60 496 36 465 128 256) },{ target := 2, region := (rows 9 18 0 8 16 32 73 201 329), good := (rows 459 162 258 475 498 32 449 128 256) }] }

theorem u5043 : Upper (D 6) (R 6) [10,160,258,20,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5044 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 262 44 81 96 65 148 276), lower := (rows 11 162 262 44 81 96 65 128 256), losses := [] }

theorem u5044 : Upper (D 6) (R 6) [10,160,258,36,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5045 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 262 44 81 96 68 145 273), lower := (rows 11 162 262 44 81 96 68 128 256), losses := [] }

theorem u5045 : Upper (D 6) (R 6) [10,160,258,36,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5046 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 262 44 81 96 80 133 261), lower := (rows 11 162 262 44 81 96 80 128 256), losses := [] }

theorem u5046 : Upper (D 6) (R 6) [10,160,258,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5046 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5047 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 262 56 81 36 65 196 324), lower := (rows 11 162 262 56 81 36 65 128 256), losses := [] }

theorem u5047 : Upper (D 6) (R 6) [10,160,258,48,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5048 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 262 56 81 36 68 193 321), lower := (rows 11 162 262 56 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 128 256), good := (rows 10 226 358 120 120 100 100 128 256) }] }

theorem u5048 : Upper (D 6) (R 6) [10,160,258,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5049 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 262 56 84 33 65 196 324), lower := (rows 11 162 262 56 84 33 65 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 32 64 144 272), good := (rows 14 162 262 446 468 32 64 128 256) }] }

theorem u5049 : Upper (D 6) (R 6) [10,160,258,48,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5050 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 262 56 84 33 68 193 321), lower := (rows 11 162 262 56 84 33 68 128 256), losses := [] }

theorem u5050 : Upper (D 6) (R 6) [10,160,258,48,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5051 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 4, region := 454, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 162 262 73 49 36 68 208 336), lower := (rows 11 162 262 73 49 36 68 128 256), losses := [] }

theorem u5051 : Upper (D 6) (R 6) [10,160,258,65,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5052 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 162 262 73 49 36 80 196 324), lower := (rows 11 162 262 73 49 36 80 128 256), losses := [] }

theorem u5052 : Upper (D 6) (R 6) [10,160,258,65,33,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5052 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5053 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 262 73 52 96 65 148 276), lower := (rows 11 162 262 73 52 96 65 128 256), losses := [] }

theorem u5053 : Upper (D 6) (R 6) [10,160,258,65,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5054 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(4,0),(4,1)], upper := (rows 11 162 262 73 52 96 68 145 273), lower := (rows 11 162 262 73 52 96 68 128 256), losses := [] }

theorem u5054 : Upper (D 6) (R 6) [10,160,258,65,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5055 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 11 162 262 73 52 96 80 133 261), lower := (rows 11 162 262 73 52 96 80 128 256), losses := [] }

theorem u5055 : Upper (D 6) (R 6) [10,160,258,65,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5055 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5056 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 262 73 84 36 65 176 304), lower := (rows 11 162 262 73 84 36 65 128 256), losses := [] }

theorem u5056 : Upper (D 6) (R 6) [10,160,258,65,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5057 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 262 73 84 36 80 161 289), lower := (rows 11 162 262 73 84 36 80 128 256), losses := [] }

theorem u5057 : Upper (D 6) (R 6) [10,160,258,65,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5057 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5058 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 2, region := 112, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 11 162 262 73 84 36 96 145 273), lower := (rows 11 162 262 73 84 36 96 128 256), losses := [] }

theorem u5058 : Upper (D 6) (R 6) [10,160,258,65,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5059 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 262 73 84 48 65 164 292), lower := (rows 11 162 262 73 84 48 65 128 256), losses := [] }

theorem u5059 : Upper (D 6) (R 6) [10,160,258,65,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5059 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5060 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 262 73 84 48 68 161 289), lower := (rows 11 162 262 73 84 48 68 128 256), losses := [] }

theorem u5060 : Upper (D 6) (R 6) [10,160,258,65,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5060 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5061 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 11 162 262 73 84 48 96 133 261), lower := (rows 11 162 262 73 84 48 96 128 256), losses := [] }

theorem u5061 : Upper (D 6) (R 6) [10,160,258,65,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5061 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5062 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 262 73 112 36 65 148 276), lower := (rows 11 162 262 73 112 36 65 128 256), losses := [] }

theorem u5062 : Upper (D 6) (R 6) [10,160,258,65,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5063 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 262 73 112 36 68 145 273), lower := (rows 11 162 262 73 112 36 68 128 256), losses := [] }

theorem u5063 : Upper (D 6) (R 6) [10,160,258,65,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5064 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 162 262 73 112 36 80 133 261), lower := (rows 11 162 262 73 112 36 80 128 256), losses := [] }

theorem u5064 : Upper (D 6) (R 6) [10,160,258,65,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5064 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5065 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 262 76 21 33 80 224 352), lower := (rows 11 162 262 76 21 33 80 128 256), losses := [] }

theorem u5065 : Upper (D 6) (R 6) [10,160,258,68,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5065 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5066 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 104, targets := 2 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 162 262 76 21 33 96 208 336), lower := (rows 11 162 262 76 21 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 98 128 256), good := (rows 74 226 334 76 28 96 96 128 256) }] }

theorem u5066 : Upper (D 6) (R 6) [10,160,258,68,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5067 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 262 76 21 96 65 176 304), lower := (rows 11 162 262 76 21 96 65 128 256), losses := [] }

theorem u5067 : Upper (D 6) (R 6) [10,160,258,68,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5068 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 262 76 21 96 80 161 289), lower := (rows 11 162 262 76 21 96 80 128 256), losses := [] }

theorem u5068 : Upper (D 6) (R 6) [10,160,258,68,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5068 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5069 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 262 76 21 96 96 145 273), lower := (rows 11 162 262 76 21 96 96 128 256), losses := [] }

theorem u5069 : Upper (D 6) (R 6) [10,160,258,68,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5070 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,1),(3,5)], upper := (rows 11 162 262 76 52 33 65 208 336), lower := (rows 11 162 262 76 52 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 24 97 97 153 281), good := (rows 505 224 260 508 508 481 481 128 256) }] }

theorem u5070 : Upper (D 6) (R 6) [10,160,258,68,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5071 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 262 76 52 33 80 193 321), lower := (rows 11 162 262 76 52 33 80 128 256), losses := [] }

theorem u5071 : Upper (D 6) (R 6) [10,160,258,68,36,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5071 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5072 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(0,5),(3,5),(4,0)], upper := (rows 11 162 262 76 52 96 65 145 273), lower := (rows 11 162 262 76 52 96 65 128 256), losses := [] }

theorem u5072 : Upper (D 6) (R 6) [10,160,258,68,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5073 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 262 76 52 96 80 129 257), lower := (rows 11 162 262 76 52 96 80 128 256), losses := [] }

theorem u5073 : Upper (D 6) (R 6) [10,160,258,68,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5073 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5074 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 262 76 81 33 68 176 304), lower := (rows 11 162 262 76 81 33 68 128 256), losses := [] }

theorem u5074 : Upper (D 6) (R 6) [10,160,258,68,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5075 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 162 262 76 81 33 80 164 292), lower := (rows 11 162 262 76 81 33 80 128 256), losses := [] }

theorem u5075 : Upper (D 6) (R 6) [10,160,258,68,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5075 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5076 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 11 162 262 76 81 33 96 148 276), lower := (rows 11 162 262 76 81 33 96 128 256), losses := [] }

theorem u5076 : Upper (D 6) (R 6) [10,160,258,68,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5077 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 262 76 112 33 65 148 276), lower := (rows 11 162 262 76 112 33 65 128 256), losses := [] }

theorem u5077 : Upper (D 6) (R 6) [10,160,258,68,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5078 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 179, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 262 76 112 33 68 145 273), lower := (rows 11 162 262 76 112 33 68 128 256), losses := [] }

theorem u5078 : Upper (D 6) (R 6) [10,160,258,68,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5079 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 262 76 112 33 80 133 261), lower := (rows 11 162 262 76 112 33 80 128 256), losses := [] }

theorem u5079 : Upper (D 6) (R 6) [10,160,258,68,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5079 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5080 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(0,5),(3,5),(4,0)], upper := (rows 11 162 262 76 112 36 65 145 273), lower := (rows 11 162 262 76 112 36 65 128 256), losses := [] }

theorem u5080 : Upper (D 6) (R 6) [10,160,258,68,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5081 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 262 76 112 36 80 129 257), lower := (rows 11 162 262 76 112 36 80 128 256), losses := [] }

theorem u5081 : Upper (D 6) (R 6) [10,160,258,68,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5081 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5082 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 262 88 21 36 65 224 352), lower := (rows 11 162 262 88 21 36 65 128 256), losses := [] }

theorem u5082 : Upper (D 6) (R 6) [10,160,258,80,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5083 : Route 9 := (fun mask => (mask,id))

def c5083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5083 : Upper (D 6) (R 6) [10,160,258,80,5,4,32] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,5,4,32] 13 (by decide) (choices 1) [1,64] r5083 c5083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u376
  · exact u377

def b5084 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 262 88 21 96 65 164 292), lower := (rows 11 162 262 88 21 96 65 128 256), losses := [] }

theorem u5084 : Upper (D 6) (R 6) [10,160,258,80,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5085 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 262 88 21 96 68 161 289), lower := (rows 11 162 262 88 21 96 68 128 256), losses := [] }

theorem u5085 : Upper (D 6) (R 6) [10,160,258,80,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5086 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 262 88 21 96 96 133 261), lower := (rows 11 162 262 88 21 96 96 128 256), losses := [] }

theorem u5086 : Upper (D 6) (R 6) [10,160,258,80,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5087 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 262 88 49 36 65 196 324), lower := (rows 11 162 262 88 49 36 65 128 256), losses := [] }

theorem u5087 : Upper (D 6) (R 6) [10,160,258,80,33,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5088 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 162 262 88 49 36 68 193 321), lower := (rows 11 162 262 88 49 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 128 256), good := (rows 10 226 358 120 120 100 100 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 100 144 272), good := (rows 9 224 356 504 505 100 100 128 256) }] }

theorem u5088 : Upper (D 6) (R 6) [10,160,258,80,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5089 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,1),(3,2)], upper := (rows 11 162 262 88 52 33 65 196 324), lower := (rows 11 162 262 88 52 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 97 97 144 272), good := (rows 105 224 260 504 508 97 97 128 256) },{ target := 2, region := (rows 1 2 0 24 16 97 97 128 256), good := (rows 107 226 258 120 120 97 97 128 256) }] }

theorem u5089 : Upper (D 6) (R 6) [10,160,258,80,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5090 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 262 88 52 33 68 193 321), lower := (rows 11 162 262 88 52 33 68 128 256), losses := [] }

theorem u5090 : Upper (D 6) (R 6) [10,160,258,80,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5091 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 32 },{ cop := 0, region := 260, targets := 64 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 11 162 262 88 52 96 65 133 261), lower := (rows 11 162 262 88 52 96 65 128 256), losses := [{ target := 6, region := (rows 1 34 37 8 50 32 0 193 321), good := (rows 415 182 278 408 54 438 389 128 256) }] }

theorem u5091 : Upper (D 6) (R 6) [10,160,258,80,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5092 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 162 262 88 52 96 68 129 257), lower := (rows 11 162 262 88 52 96 68 128 256), losses := [] }

theorem u5092 : Upper (D 6) (R 6) [10,160,258,80,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5093 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 262 104 84 33 65 148 276), lower := (rows 11 162 262 104 84 33 65 128 256), losses := [] }

theorem u5093 : Upper (D 6) (R 6) [10,160,258,96,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5094 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 262 104 84 33 68 145 273), lower := (rows 11 162 262 104 84 33 68 128 256), losses := [] }

theorem u5094 : Upper (D 6) (R 6) [10,160,258,96,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5095 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 162 262 104 84 33 80 133 261), lower := (rows 11 162 262 104 84 33 80 128 256), losses := [] }

theorem u5095 : Upper (D 6) (R 6) [10,160,258,96,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5095 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5096 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 454, targets := 1 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 162 276 13 49 96 66 196 324), lower := (rows 11 162 276 13 49 96 66 128 256), losses := [] }

theorem u5096 : Upper (D 6) (R 6) [10,160,272,5,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5097 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 454, targets := 1 },{ cop := 3, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 162 276 13 49 96 68 194 322), lower := (rows 11 162 276 13 49 96 68 128 256), losses := [] }

theorem u5097 : Upper (D 6) (R 6) [10,160,272,5,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5098 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 52 96 65 194 322), lower := (rows 11 162 276 13 52 96 65 128 256), losses := [] }

theorem u5098 : Upper (D 6) (R 6) [10,160,272,5,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5099 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 7, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 162 276 13 52 96 66 193 321), lower := (rows 11 162 276 13 52 96 66 128 256), losses := [] }

theorem u5099 : Upper (D 6) (R 6) [10,160,272,5,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5099
end Delivery.IrregularNine14.P06
