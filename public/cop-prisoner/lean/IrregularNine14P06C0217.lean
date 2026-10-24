import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0043

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13020 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 69 56 148 34 321 449 321), lower := (rows 11 38 69 56 148 34 64 128 256), losses := [] }

theorem u13020 : Upper (D 6) (R 6) [10,36,65,48,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13021 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 56 148 96 323 387 259), lower := (rows 11 38 69 56 148 96 64 128 256), losses := [] }

theorem u13021 : Upper (D 6) (R 6) [10,36,65,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13022 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 69 56 148 288 67 195 323), lower := (rows 11 38 69 56 148 288 64 128 256), losses := [] }

theorem u13022 : Upper (D 6) (R 6) [10,36,65,48,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13022 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13023 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 69 56 400 33 70 198 326), lower := (rows 11 38 69 56 400 33 64 128 256), losses := [] }

theorem u13023 : Upper (D 6) (R 6) [10,36,65,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13024 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 69 56 400 34 69 197 325), lower := (rows 11 38 69 56 400 34 64 128 256), losses := [] }

theorem u13024 : Upper (D 6) (R 6) [10,36,65,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13025 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 56 400 36 67 195 323), lower := (rows 11 38 69 56 400 36 64 128 256), losses := [] }

theorem u13025 : Upper (D 6) (R 6) [10,36,65,48,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13026 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 56 400 96 71 135 263), lower := (rows 11 38 69 56 400 96 64 128 256), losses := [] }

theorem u13026 : Upper (D 6) (R 6) [10,36,65,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13027 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 69 88 400 33 102 166 294), lower := (rows 11 38 69 88 400 33 64 128 256), losses := [] }

theorem u13027 : Upper (D 6) (R 6) [10,36,65,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13028 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 38 69 88 400 34 101 165 293), lower := (rows 11 38 69 88 400 34 64 128 256), losses := [] }

theorem u13028 : Upper (D 6) (R 6) [10,36,65,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13029 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 88 400 36 99 163 291), lower := (rows 11 38 69 88 400 36 64 128 256), losses := [] }

theorem u13029 : Upper (D 6) (R 6) [10,36,65,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13030 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 137 82 36 368 432 304), lower := (rows 11 38 69 137 82 36 64 128 256), losses := [] }

theorem u13030 : Upper (D 6) (R 6) [10,36,65,129,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13031 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 393, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 69 137 82 48 356 420 292), lower := (rows 11 38 69 137 82 48 64 128 256), losses := [] }

theorem u13031 : Upper (D 6) (R 6) [10,36,65,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13031 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13032 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 69 137 82 288 116 180 308), lower := (rows 11 38 69 137 82 288 64 128 256), losses := [] }

theorem u13032 : Upper (D 6) (R 6) [10,36,65,129,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13032 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13033 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 69 137 112 34 340 404 276), lower := (rows 11 38 69 137 112 34 64 128 256), losses := [] }

theorem u13033 : Upper (D 6) (R 6) [10,36,65,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13034 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 137 112 36 338 402 274), lower := (rows 11 38 69 137 112 36 64 128 256), losses := [] }

theorem u13034 : Upper (D 6) (R 6) [10,36,65,129,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13035 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 69 137 112 48 326 390 262), lower := (rows 11 38 69 137 112 48 64 128 256), losses := [] }

theorem u13035 : Upper (D 6) (R 6) [10,36,65,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13035 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13036 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 69 137 112 288 86 150 278), lower := (rows 11 38 69 137 112 288 64 128 256), losses := [] }

theorem u13036 : Upper (D 6) (R 6) [10,36,65,129,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13036 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13037 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 137 274 36 112 240 368), lower := (rows 11 38 69 137 274 36 64 128 256), losses := [] }

theorem u13037 : Upper (D 6) (R 6) [10,36,65,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13038 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 69 137 274 48 100 228 356), lower := (rows 11 38 69 137 274 48 64 128 256), losses := [] }

theorem u13038 : Upper (D 6) (R 6) [10,36,65,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13038 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13039 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 137 274 96 116 180 308), lower := (rows 11 38 69 137 274 96 64 128 256), losses := [] }

theorem u13039 : Upper (D 6) (R 6) [10,36,65,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13040 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 69 137 276 34 112 240 368), lower := (rows 11 38 69 137 276 34 64 128 256), losses := [] }

theorem u13040 : Upper (D 6) (R 6) [10,36,65,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13041 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 69 137 276 48 98 226 354), lower := (rows 11 38 69 137 276 48 64 128 256), losses := [] }

theorem u13041 : Upper (D 6) (R 6) [10,36,65,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13041 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13042 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 137 276 96 114 178 306), lower := (rows 11 38 69 137 276 96 64 128 256), losses := [] }

theorem u13042 : Upper (D 6) (R 6) [10,36,65,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13043 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 69 137 304 34 84 212 340), lower := (rows 11 38 69 137 304 34 64 128 256), losses := [] }

theorem u13043 : Upper (D 6) (R 6) [10,36,65,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13044 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 137 304 36 82 210 338), lower := (rows 11 38 69 137 304 36 64 128 256), losses := [] }

theorem u13044 : Upper (D 6) (R 6) [10,36,65,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13045 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 69 137 304 48 70 198 326), lower := (rows 11 38 69 137 304 48 64 128 256), losses := [] }

theorem u13045 : Upper (D 6) (R 6) [10,36,65,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13045 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13046 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 137 304 96 86 150 278), lower := (rows 11 38 69 137 304 96 64 128 256), losses := [] }

theorem u13046 : Upper (D 6) (R 6) [10,36,65,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13047 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 69 137 336 34 116 180 308), lower := (rows 11 38 69 137 336 34 64 128 256), losses := [] }

theorem u13047 : Upper (D 6) (R 6) [10,36,65,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13048 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 137 336 36 114 178 306), lower := (rows 11 38 69 137 336 36 64 128 256), losses := [] }

theorem u13048 : Upper (D 6) (R 6) [10,36,65,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13049 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 137, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 69 137 336 48 102 166 294), lower := (rows 11 38 69 137 336 48 64 128 256), losses := [] }

theorem u13049 : Upper (D 6) (R 6) [10,36,65,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13049 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13050 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 69 140 49 34 336 464 336), lower := (rows 11 38 69 140 49 34 64 128 256), losses := [] }

theorem u13050 : Upper (D 6) (R 6) [10,36,65,132,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13051 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 69 140 49 48 322 450 322), lower := (rows 11 38 69 140 49 48 64 128 256), losses := [] }

theorem u13051 : Upper (D 6) (R 6) [10,36,65,132,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13051 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13052 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 140 49 96 338 402 274), lower := (rows 11 38 69 140 49 96 64 128 256), losses := [] }

theorem u13052 : Upper (D 6) (R 6) [10,36,65,132,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13053 : Route 9 := (fun mask => (mask,id))

def c13053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13053 : Upper (D 6) (R 6) [10,36,65,132,33,256] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,33,256] 13 (by decide) (choices 1) [2,16] r13053 c13053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2601
  · exact u2602

def b13054 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 69 140 82 33 368 432 304), lower := (rows 11 38 69 140 82 33 64 128 256), losses := [] }

theorem u13054 : Upper (D 6) (R 6) [10,36,65,132,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13055 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 393, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 69 140 82 48 353 417 289), lower := (rows 11 38 69 140 82 48 64 128 256), losses := [] }

theorem u13055 : Upper (D 6) (R 6) [10,36,65,132,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13055 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13056 : Route 9 := (fun mask => (mask,id))

def c13056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13056 : Upper (D 6) (R 6) [10,36,65,132,66,256] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,66,256] 13 (by decide) (choices 1) [1,16,32] r13056 c13056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2603
  · exact u2604
  · exact u2605

def b13057 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 69 140 112 33 338 402 274), lower := (rows 11 38 69 140 112 33 64 128 256), losses := [] }

theorem u13057 : Upper (D 6) (R 6) [10,36,65,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13058 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 11 38 69 140 112 34 337 401 273), lower := (rows 11 38 69 140 112 34 64 128 256), losses := [] }

theorem u13058 : Upper (D 6) (R 6) [10,36,65,132,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13059 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 69 140 112 48 323 387 259), lower := (rows 11 38 69 140 112 48 64 128 256), losses := [] }

theorem u13059 : Upper (D 6) (R 6) [10,36,65,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13059 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13060 : Route 9 := (fun mask => (mask,id))

def c13060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13060 : Upper (D 6) (R 6) [10,36,65,132,96,256] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,96,256] 13 (by decide) (choices 1) [1,2,16] r13060 c13060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2606
  · exact u2607
  · exact u2608

def b13061 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 69 140 273 34 112 240 368), lower := (rows 11 38 69 140 273 34 64 128 256), losses := [] }

theorem u13061 : Upper (D 6) (R 6) [10,36,65,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13062 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 200, targets := 1 }], pairs := [(3,0),(4,2)], upper := (rows 11 38 69 140 273 48 98 226 354), lower := (rows 11 38 69 140 273 48 64 128 256), losses := [] }

theorem u13062 : Upper (D 6) (R 6) [10,36,65,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13062 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13063 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 140 273 96 114 178 306), lower := (rows 11 38 69 140 273 96 64 128 256), losses := [] }

theorem u13063 : Upper (D 6) (R 6) [10,36,65,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13064 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 69 140 274 33 112 240 368), lower := (rows 11 38 69 140 274 33 64 128 256), losses := [] }

theorem u13064 : Upper (D 6) (R 6) [10,36,65,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13065 : Route 9 := (fun mask => (mask,id))

def c13065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13065 : Upper (D 6) (R 6) [10,36,65,132,258,16] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,258,16] 13 (by decide) (choices 1) [1,32] r13065 c13065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2609
  · exact u2610

def b13066 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 140 274 96 113 177 305), lower := (rows 11 38 69 140 274 96 64 128 256), losses := [] }

theorem u13066 : Upper (D 6) (R 6) [10,36,65,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13067 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 69 140 304 33 82 210 338), lower := (rows 11 38 69 140 304 33 64 128 256), losses := [] }

theorem u13067 : Upper (D 6) (R 6) [10,36,65,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13068 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 69 140 304 34 81 209 337), lower := (rows 11 38 69 140 304 34 64 128 256), losses := [] }

theorem u13068 : Upper (D 6) (R 6) [10,36,65,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13069 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 69 140 304 48 67 195 323), lower := (rows 11 38 69 140 304 48 64 128 256), losses := [] }

theorem u13069 : Upper (D 6) (R 6) [10,36,65,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13069 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13070 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 140 304 96 83 147 275), lower := (rows 11 38 69 140 304 96 64 128 256), losses := [] }

theorem u13070 : Upper (D 6) (R 6) [10,36,65,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13071 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 69 140 336 33 114 178 306), lower := (rows 11 38 69 140 336 33 64 128 256), losses := [] }

theorem u13071 : Upper (D 6) (R 6) [10,36,65,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13072 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 69 140 336 34 113 177 305), lower := (rows 11 38 69 140 336 34 64 128 256), losses := [] }

theorem u13072 : Upper (D 6) (R 6) [10,36,65,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13073 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 137, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 69 140 336 48 99 163 291), lower := (rows 11 38 69 140 336 48 64 128 256), losses := [] }

theorem u13073 : Upper (D 6) (R 6) [10,36,65,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13073 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13074 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 38 69 152 82 33 356 420 292), lower := (rows 11 38 69 152 82 33 64 128 256), losses := [] }

theorem u13074 : Upper (D 6) (R 6) [10,36,65,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13075 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 152 82 36 353 417 289), lower := (rows 11 38 69 152 82 36 64 128 256), losses := [] }

theorem u13075 : Upper (D 6) (R 6) [10,36,65,144,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13076 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,6),(2,1)], upper := (rows 11 38 69 152 82 288 101 165 293), lower := (rows 11 38 69 152 82 288 64 128 256), losses := [] }

theorem u13076 : Upper (D 6) (R 6) [10,36,65,144,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13076 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13077 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 38 69 152 112 33 326 390 262), lower := (rows 11 38 69 152 112 33 64 128 256), losses := [] }

theorem u13077 : Upper (D 6) (R 6) [10,36,65,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13078 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 324, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 69 152 112 34 325 389 261), lower := (rows 11 38 69 152 112 34 64 128 256), losses := [] }

theorem u13078 : Upper (D 6) (R 6) [10,36,65,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13079 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 152 112 36 323 387 259), lower := (rows 11 38 69 152 112 36 64 128 256), losses := [] }

theorem u13079 : Upper (D 6) (R 6) [10,36,65,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13079
end Delivery.IrregularNine14.P06
