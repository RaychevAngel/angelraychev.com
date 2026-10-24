import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0057

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16020 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 35 100 280 146 96 195 131 387), lower := (rows 13 35 100 280 146 96 64 128 256), losses := [] }

theorem u16020 : Upper (D 7) (R 7) [12,33,96,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16021 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 13 35 100 280 146 160 67 195 323), lower := (rows 13 35 100 280 146 160 64 128 256), losses := [{ target := 7, region := (rows 17 2 6 24 16 32 82 0 274), good := (rows 13 359 100 345 351 32 64 0 256) }] }

theorem u16021 : Upper (D 7) (R 7) [12,33,96,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16022 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 35 100 280 208 33 194 130 386), lower := (rows 13 35 100 280 208 33 64 128 256), losses := [] }

theorem u16022 : Upper (D 7) (R 7) [12,33,96,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16023 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 13 35 100 280 208 34 195 131 387), lower := (rows 13 35 100 280 208 34 64 128 256), losses := [] }

theorem u16023 : Upper (D 7) (R 7) [12,33,96,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16024 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 13 35 100 280 208 160 67 131 259), lower := (rows 13 35 100 280 208 160 64 128 256), losses := [] }

theorem u16024 : Upper (D 7) (R 7) [12,33,96,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16025 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 100 392 82 33 210 146 402), lower := (rows 13 35 100 392 82 33 64 128 256), losses := [] }

theorem u16025 : Upper (D 7) (R 7) [12,33,96,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16026 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 13 35 100 392 82 34 209 145 401), lower := (rows 13 35 100 392 82 34 64 128 256), losses := [] }

theorem u16026 : Upper (D 7) (R 7) [12,33,96,384,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16027 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 100 392 82 48 195 131 387), lower := (rows 13 35 100 392 82 48 64 128 256), losses := [] }

theorem u16027 : Upper (D 7) (R 7) [12,33,96,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16027 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16028 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7),(3,5),(4,5),(4,7)], upper := (rows 13 35 100 392 82 160 83 147 275), lower := (rows 13 35 100 392 82 160 64 128 256), losses := [] }

theorem u16028 : Upper (D 7) (R 7) [12,33,96,384,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16029 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 100 392 146 33 82 210 338), lower := (rows 13 35 100 392 146 33 64 128 256), losses := [] }

theorem u16029 : Upper (D 7) (R 7) [12,33,96,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16030 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 13 35 100 392 146 34 81 209 337), lower := (rows 13 35 100 392 146 34 64 128 256), losses := [] }

theorem u16030 : Upper (D 7) (R 7) [12,33,96,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16031 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 128 }], pairs := [(2,7),(3,5),(4,5)], upper := (rows 13 35 100 392 146 48 67 195 323), lower := (rows 13 35 100 392 146 48 64 128 256), losses := [] }

theorem u16031 : Upper (D 7) (R 7) [12,33,96,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16031 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16032 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 35 100 392 146 96 83 147 275), lower := (rows 13 35 100 392 146 96 64 128 256), losses := [] }

theorem u16032 : Upper (D 7) (R 7) [12,33,96,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16033 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 100 392 208 33 82 146 274), lower := (rows 13 35 100 392 208 33 64 128 256), losses := [] }

theorem u16033 : Upper (D 7) (R 7) [12,33,96,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16034 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 13 35 100 392 208 34 83 147 275), lower := (rows 13 35 100 392 208 34 64 128 256), losses := [] }

theorem u16034 : Upper (D 7) (R 7) [12,33,96,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16035 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 100 392 208 48 67 131 259), lower := (rows 13 35 100 392 208 48 64 128 256), losses := [] }

theorem u16035 : Upper (D 7) (R 7) [12,33,96,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16035 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16036 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 196 265 82 34 240 176 432), lower := (rows 13 35 196 265 82 34 64 128 256), losses := [] }

theorem u16036 : Upper (D 7) (R 7) [12,33,192,257,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16037 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,0),(3,6),(4,0)], upper := (rows 13 35 196 265 82 48 226 162 418), lower := (rows 13 35 196 265 82 48 64 128 256), losses := [] }

theorem u16037 : Upper (D 7) (R 7) [12,33,192,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16037 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16038 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 344, targets := 128 }], pairs := [(2,0),(3,7),(4,0),(4,7)], upper := (rows 13 35 196 265 82 160 114 178 306), lower := (rows 13 35 196 265 82 160 64 128 256), losses := [] }

theorem u16038 : Upper (D 7) (R 7) [12,33,192,257,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16039 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 196 265 112 34 210 146 402), lower := (rows 13 35 196 265 112 34 64 128 256), losses := [] }

theorem u16039 : Upper (D 7) (R 7) [12,33,192,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16040 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 196 265 112 48 194 130 386), lower := (rows 13 35 196 265 112 48 64 128 256), losses := [] }

theorem u16040 : Upper (D 7) (R 7) [12,33,192,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16040 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16041 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 344, targets := 128 }], pairs := [(2,0),(3,7),(4,0),(4,7)], upper := (rows 13 35 196 265 112 160 82 146 274), lower := (rows 13 35 196 265 112 160 64 128 256), losses := [] }

theorem u16041 : Upper (D 7) (R 7) [12,33,192,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16042 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 2 }], pairs := [(1,6),(1,7),(2,1),(4,1)], upper := (rows 13 35 196 266 81 34 240 176 432), lower := (rows 13 35 196 266 81 34 64 128 256), losses := [] }

theorem u16042 : Upper (D 7) (R 7) [12,33,192,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16043 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 13 35 196 266 81 48 226 162 418), lower := (rows 13 35 196 266 81 48 64 128 256), losses := [] }

theorem u16043 : Upper (D 7) (R 7) [12,33,192,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16043 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16044 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6),(3,7),(4,7)], upper := (rows 13 35 196 266 81 160 114 178 306), lower := (rows 13 35 196 266 81 160 64 128 256), losses := [] }

theorem u16044 : Upper (D 7) (R 7) [12,33,192,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16045 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 196 266 82 33 240 176 432), lower := (rows 13 35 196 266 82 33 64 128 256), losses := [] }

theorem u16045 : Upper (D 7) (R 7) [12,33,192,258,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16046 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 196, targets := 2 },{ cop := 1, region := 392, targets := 64 }], pairs := [(0,1),(2,1),(3,6)], upper := (rows 13 35 196 266 82 48 225 161 417), lower := (rows 13 35 196 266 82 48 64 128 256), losses := [{ target := 1, region := (rows 9 0 30 8 16 48 66 130 258), good := (rows 13 485 196 461 500 52 64 128 256) }] }

theorem u16046 : Upper (D 7) (R 7) [12,33,192,258,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16046 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16047 : Route 9 := (fun mask => (mask,id))

def c16047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16047 : Upper (D 7) (R 7) [12,33,192,258,66,128] 13 := by
  apply FastRouting.sound _ _ [12,33,192,258,66,128] 13 (by decide) (choices 1) [1,16,32] r16047 c16047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3462
  · exact u3463
  · exact u3464

def b16048 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 196 266 112 33 210 146 402), lower := (rows 13 35 196 266 112 33 64 128 256), losses := [] }

theorem u16048 : Upper (D 7) (R 7) [12,33,192,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16049 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 2 }], pairs := [(1,6),(1,7),(2,1),(4,1)], upper := (rows 13 35 196 266 112 34 209 145 401), lower := (rows 13 35 196 266 112 34 64 128 256), losses := [] }

theorem u16049 : Upper (D 7) (R 7) [12,33,192,258,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16050 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 196 266 112 48 195 131 387), lower := (rows 13 35 196 266 112 48 64 128 256), losses := [] }

theorem u16050 : Upper (D 7) (R 7) [12,33,192,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16050 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16051 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 48, targets := 3 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 13 35 196 266 112 160 83 147 275), lower := (rows 13 35 196 266 112 160 64 128 256), losses := [] }

theorem u16051 : Upper (D 7) (R 7) [12,33,192,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16052 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(3,6)], upper := (rows 13 35 196 280 81 34 226 162 418), lower := (rows 13 35 196 280 81 34 64 128 256), losses := [] }

theorem u16052 : Upper (D 7) (R 7) [12,33,192,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16053 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6),(3,7),(4,7)], upper := (rows 13 35 196 280 81 160 98 162 290), lower := (rows 13 35 196 280 81 160 64 128 256), losses := [] }

theorem u16053 : Upper (D 7) (R 7) [12,33,192,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16054 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 196 280 82 33 226 162 418), lower := (rows 13 35 196 280 82 33 64 128 256), losses := [] }

theorem u16054 : Upper (D 7) (R 7) [12,33,192,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16055 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 196, targets := 2 }], pairs := [(0,1),(1,6),(1,7),(2,1)], upper := (rows 13 35 196 280 82 34 225 161 417), lower := (rows 13 35 196 280 82 34 64 128 256), losses := [{ target := 1, region := (rows 25 0 54 24 16 32 66 130 258), good := (rows 13 485 196 285 477 484 64 128 256) }] }

theorem u16055 : Upper (D 7) (R 7) [12,33,192,272,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16056 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6),(3,6),(3,7),(4,7)], upper := (rows 13 35 196 280 82 160 99 163 291), lower := (rows 13 35 196 280 82 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 24 16 183 0 131 259), good := (rows 431 419 164 312 442 160 0 160 256) }] }

theorem u16056 : Upper (D 7) (R 7) [12,33,192,272,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16057 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 196 280 112 33 194 130 386), lower := (rows 13 35 196 280 112 33 64 128 256), losses := [] }

theorem u16057 : Upper (D 7) (R 7) [12,33,192,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16058 : Route 9 := (fun mask => (mask,id))

def c16058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16058 : Upper (D 7) (R 7) [12,33,192,272,96,2] 13 := by
  apply FastRouting.sound _ _ [12,33,192,272,96,2] 13 (by decide) (choices 1) [1,2,128] r16058 c16058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3465
  · exact u3466
  · exact u3467

def b16059 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 48, targets := 3 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 13 35 196 280 112 160 67 131 259), lower := (rows 13 35 196 280 112 160 64 128 256), losses := [] }

theorem u16059 : Upper (D 7) (R 7) [12,33,192,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16060 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 196 296 82 33 210 146 402), lower := (rows 13 35 196 296 82 33 64 128 256), losses := [] }

theorem u16060 : Upper (D 7) (R 7) [12,33,192,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16061 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 32 }], pairs := [(1,6),(1,7),(2,5),(4,5)], upper := (rows 13 35 196 296 82 34 209 145 401), lower := (rows 13 35 196 296 82 34 64 128 256), losses := [] }

theorem u16061 : Upper (D 7) (R 7) [12,33,192,288,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16062 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,5),(3,6),(4,5)], upper := (rows 13 35 196 296 82 48 195 131 387), lower := (rows 13 35 196 296 82 48 64 128 256), losses := [] }

theorem u16062 : Upper (D 7) (R 7) [12,33,192,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16062 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16063 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 344, targets := 128 }], pairs := [(2,5),(3,7),(4,5),(4,7)], upper := (rows 13 35 196 296 82 160 83 147 275), lower := (rows 13 35 196 296 82 160 64 128 256), losses := [] }

theorem u16063 : Upper (D 7) (R 7) [12,33,192,288,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16064 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 196 328 146 33 114 178 306), lower := (rows 13 35 196 328 146 33 64 128 256), losses := [] }

theorem u16064 : Upper (D 7) (R 7) [12,33,192,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16065 : Route 9 := (fun mask => (mask,id))

def c16065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16065 : Upper (D 7) (R 7) [12,33,192,320,130,2] 13 := by
  apply FastRouting.sound _ _ [12,33,192,320,130,2] 13 (by decide) (choices 1) [1,16,32] r16065 c16065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3468
  · exact u3469
  · exact u3470

def b16066 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(3,7),(4,6)], upper := (rows 13 35 196 328 146 48 99 163 291), lower := (rows 13 35 196 328 146 48 64 128 256), losses := [] }

theorem u16066 : Upper (D 7) (R 7) [12,33,192,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16066 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16067 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 196 328 176 33 82 146 274), lower := (rows 13 35 196 328 176 33 64 128 256), losses := [] }

theorem u16067 : Upper (D 7) (R 7) [12,33,192,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16068 : Route 9 := (fun mask => (mask,id))

def c16068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16068 : Upper (D 7) (R 7) [12,33,192,320,160,2] 13 := by
  apply FastRouting.sound _ _ [12,33,192,320,160,2] 13 (by decide) (choices 1) [1,2,16] r16068 c16068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3471
  · exact u3472
  · exact u3473

def b16069 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 196 328 176 48 67 131 259), lower := (rows 13 35 196 328 176 48 64 128 256), losses := [] }

theorem u16069 : Upper (D 7) (R 7) [12,33,192,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16069 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16070 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 73 208 34 480 416 416), lower := (rows 13 50 7 73 208 34 64 128 256), losses := [] }

theorem u16070 : Upper (D 7) (R 7) [12,48,3,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16071 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 73 208 160 354 418 290), lower := (rows 13 50 7 73 208 160 64 128 256), losses := [] }

theorem u16071 : Upper (D 7) (R 7) [12,48,3,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16072 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 13 50 7 73 208 288 226 162 418), lower := (rows 13 50 7 73 208 288 64 128 256), losses := [] }

theorem u16072 : Upper (D 7) (R 7) [12,48,3,65,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16072 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16073 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 73 336 34 224 160 416), lower := (rows 13 50 7 73 336 34 64 128 256), losses := [] }

theorem u16073 : Upper (D 7) (R 7) [12,48,3,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16074 : Route 9 := (fun mask => (mask,id))

def c16074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16074 : Upper (D 7) (R 7) [12,48,3,65,320,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,65,320,128] 13 (by decide) (choices 1) [2,32,128] r16074 c16074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3474
  · exact u3475
  · exact u3476

def b16075 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 7 73 400 34 224 224 480), lower := (rows 13 50 7 73 400 34 64 128 256), losses := [] }

theorem u16075 : Upper (D 7) (R 7) [12,48,3,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16076 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 7 73 400 96 226 162 418), lower := (rows 13 50 7 73 400 96 64 128 256), losses := [] }

theorem u16076 : Upper (D 7) (R 7) [12,48,3,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16077 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 73 400 160 98 226 354), lower := (rows 13 50 7 73 400 160 64 128 256), losses := [] }

theorem u16077 : Upper (D 7) (R 7) [12,48,3,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16078 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 7 104 145 34 448 448 448), lower := (rows 13 50 7 104 145 34 64 128 256), losses := [] }

theorem u16078 : Upper (D 7) (R 7) [12,48,3,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16079 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 50 7 104 145 96 450 386 386), lower := (rows 13 50 7 104 145 96 64 128 256), losses := [] }

theorem u16079 : Upper (D 7) (R 7) [12,48,3,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16079
end Delivery.IrregularNine14.P07
