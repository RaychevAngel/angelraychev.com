import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10020 : Route 9 := (fun mask => (mask,id))

def c10020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10020 : Upper (D 7) (R 7) [36,320,9,192,130,2,32] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,130,2,32] 13 (by decide) (choices 1) [1,16] r10020 c10020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u779
  · exact u780

def b10021 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 13 200 146 48 65 162 290), lower := (rows 37 322 13 200 146 48 65 128 256), losses := [] }

theorem u10021 : Upper (D 7) (R 7) [36,320,9,192,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10021 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10022 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 13 200 146 48 66 161 289), lower := (rows 37 322 13 200 146 48 66 128 256), losses := [] }

theorem u10022 : Upper (D 7) (R 7) [36,320,9,192,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10022 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10023 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 13 200 146 48 96 131 259), lower := (rows 37 322 13 200 146 48 96 128 256), losses := [] }

theorem u10023 : Upper (D 7) (R 7) [36,320,9,192,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10023 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10024 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 322 13 200 176 34 65 146 274), lower := (rows 37 322 13 200 176 34 65 128 256), losses := [] }

theorem u10024 : Upper (D 7) (R 7) [36,320,9,192,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10025 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 8, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,6)], upper := (rows 37 322 13 200 176 34 66 145 273), lower := (rows 37 322 13 200 176 34 66 128 256), losses := [] }

theorem u10025 : Upper (D 7) (R 7) [36,320,9,192,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10026 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 13 200 176 34 80 131 259), lower := (rows 37 322 13 200 176 34 80 128 256), losses := [] }

theorem u10026 : Upper (D 7) (R 7) [36,320,9,192,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10026 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10027 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 322 14 25 112 160 65 130 386), lower := (rows 37 322 14 25 112 160 65 128 256), losses := [] }

theorem u10027 : Upper (D 7) (R 7) [36,320,10,17,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10028 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 322 14 25 112 160 66 129 385), lower := (rows 37 322 14 25 112 160 66 128 256), losses := [] }

theorem u10028 : Upper (D 7) (R 7) [36,320,10,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10029 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 14 25 112 160 192 131 259), lower := (rows 37 322 14 25 112 160 192 128 256), losses := [] }

theorem u10029 : Upper (D 7) (R 7) [36,320,10,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10030 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(1,7),(4,0)], upper := (rows 37 322 14 25 208 160 65 162 290), lower := (rows 37 322 14 25 208 160 65 128 256), losses := [] }

theorem u10030 : Upper (D 7) (R 7) [36,320,10,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10031 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 322 14 25 208 160 66 161 289), lower := (rows 37 322 14 25 208 160 66 128 256), losses := [] }

theorem u10031 : Upper (D 7) (R 7) [36,320,10,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10032 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,7),(4,0),(4,1)], upper := (rows 37 322 14 25 208 160 96 131 259), lower := (rows 37 322 14 25 208 160 96 128 256), losses := [] }

theorem u10032 : Upper (D 7) (R 7) [36,320,10,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10033 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 322 14 73 50 160 65 144 400), lower := (rows 37 322 14 73 50 160 65 128 256), losses := [] }

theorem u10033 : Upper (D 7) (R 7) [36,320,10,65,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10034 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 14 73 50 160 80 129 385), lower := (rows 37 322 14 73 50 160 80 128 256), losses := [] }

theorem u10034 : Upper (D 7) (R 7) [36,320,10,65,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10034 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10035 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,0),(4,6)], upper := (rows 37 322 14 73 50 160 192 145 273), lower := (rows 37 322 14 73 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 370 30 104 114 224 224 224 256) },{ target := 1, region := (rows 1 0 4 9 16 224 224 128 256), good := (rows 109 352 12 105 112 224 224 224 256) }] }

theorem u10035 : Upper (D 7) (R 7) [36,320,10,65,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10036 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 14 73 145 160 66 176 304), lower := (rows 37 322 14 73 145 160 66 128 256), losses := [] }

theorem u10036 : Upper (D 7) (R 7) [36,320,10,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10037 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 322 14 73 145 160 80 162 290), lower := (rows 37 322 14 73 145 160 80 128 256), losses := [] }

theorem u10037 : Upper (D 7) (R 7) [36,320,10,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10037 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10038 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 322 14 73 145 160 96 146 274), lower := (rows 37 322 14 73 145 160 96 128 256), losses := [] }

theorem u10038 : Upper (D 7) (R 7) [36,320,10,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10039 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 322 14 73 146 160 65 176 304), lower := (rows 37 322 14 73 146 160 65 128 256), losses := [] }

theorem u10039 : Upper (D 7) (R 7) [36,320,10,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10040 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(4,6)], upper := (rows 37 322 14 73 146 160 80 161 289), lower := (rows 37 322 14 73 146 160 80 128 256), losses := [] }

theorem u10040 : Upper (D 7) (R 7) [36,320,10,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10040 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10041 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 322 14 73 146 160 96 145 273), lower := (rows 37 322 14 73 146 160 96 128 256), losses := [] }

theorem u10041 : Upper (D 7) (R 7) [36,320,10,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10042 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 14 137 81 48 66 160 416), lower := (rows 37 322 14 137 81 48 66 128 256), losses := [] }

theorem u10042 : Upper (D 7) (R 7) [36,320,10,129,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10042 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10043 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 322 14 137 81 48 96 130 386), lower := (rows 37 322 14 137 81 48 96 128 256), losses := [] }

theorem u10043 : Upper (D 7) (R 7) [36,320,10,129,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10043 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10044 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 3, region := 80, targets := 2 },{ cop := 3, region := 80, targets := 32 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 37 322 14 137 81 48 192 162 290), lower := (rows 37 322 14 137 81 48 192 128 256), losses := [] }

theorem u10044 : Upper (D 7) (R 7) [36,320,10,129,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10044 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10045 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 5, region := 402, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 37 322 14 137 146 96 65 176 304), lower := (rows 37 322 14 137 146 96 65 128 256), losses := [] }

theorem u10045 : Upper (D 7) (R 7) [36,320,10,129,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10046 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 136, targets := 66 }], pairs := [(0,1),(3,1),(3,6)], upper := (rows 37 322 14 137 146 96 80 161 289), lower := (rows 37 322 14 137 146 96 80 128 256), losses := [{ target := 1, region := (rows 5 0 4 13 16 114 80 133 261), good := (rows 429 352 429 393 240 96 112 128 256) }] }

theorem u10046 : Upper (D 7) (R 7) [36,320,10,129,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10046 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10047 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 8, region := 98, targets := 129 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 37 322 14 137 146 96 96 145 273), lower := (rows 37 322 14 137 146 96 96 128 256), losses := [] }

theorem u10047 : Upper (D 7) (R 7) [36,320,10,129,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10048 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 5, region := 402, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 37 322 14 137 176 96 65 146 274), lower := (rows 37 322 14 137 176 96 65 128 256), losses := [] }

theorem u10048 : Upper (D 7) (R 7) [36,320,10,129,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10049 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 322 14 137 176 96 66 145 273), lower := (rows 37 322 14 137 176 96 66 128 256), losses := [] }

theorem u10049 : Upper (D 7) (R 7) [36,320,10,129,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10050 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(0,1),(4,0),(4,1)], upper := (rows 37 322 14 137 176 96 80 131 259), lower := (rows 37 322 14 137 176 96 80 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 152 255 220 128 256), good := (rows 101 352 125 249 240 96 112 240 256) }] }

theorem u10050 : Upper (D 7) (R 7) [36,320,10,129,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10050 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10051 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 322 14 137 208 48 65 162 290), lower := (rows 37 322 14 137 208 48 65 128 256), losses := [] }

theorem u10051 : Upper (D 7) (R 7) [36,320,10,129,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10051 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10052 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 14 137 208 48 66 161 289), lower := (rows 37 322 14 137 208 48 66 128 256), losses := [] }

theorem u10052 : Upper (D 7) (R 7) [36,320,10,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10052 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10053 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7),(4,0),(4,1)], upper := (rows 37 322 14 137 208 48 96 131 259), lower := (rows 37 322 14 137 208 48 96 128 256), losses := [] }

theorem u10053 : Upper (D 7) (R 7) [36,320,10,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10053 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10054 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7)], upper := (rows 37 322 28 11 81 160 66 160 416), lower := (rows 37 322 28 11 81 160 66 128 256), losses := [] }

theorem u10054 : Upper (D 7) (R 7) [36,320,24,3,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10055 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 322 28 11 81 160 96 130 386), lower := (rows 37 322 28 11 81 160 96 128 256), losses := [] }

theorem u10055 : Upper (D 7) (R 7) [36,320,24,3,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10056 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(4,1)], upper := (rows 37 322 28 11 81 160 192 162 290), lower := (rows 37 322 28 11 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 224 224 128 256), good := (rows 117 352 28 29 113 224 224 224 256) },{ target := 5, region := (rows 1 2 12 8 17 0 224 128 256), good := (rows 85 322 28 31 81 192 192 192 256) }] }

theorem u10056 : Upper (D 7) (R 7) [36,320,24,3,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10057 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,7)], upper := (rows 37 322 28 11 112 160 65 130 386), lower := (rows 37 322 28 11 112 160 65 128 256), losses := [] }

theorem u10057 : Upper (D 7) (R 7) [36,320,24,3,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10058 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 322 28 11 112 160 66 129 385), lower := (rows 37 322 28 11 112 160 66 128 256), losses := [] }

theorem u10058 : Upper (D 7) (R 7) [36,320,24,3,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10059 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 28 11 112 160 192 131 259), lower := (rows 37 322 28 11 112 160 192 128 256), losses := [] }

theorem u10059 : Upper (D 7) (R 7) [36,320,24,3,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10060 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 0, region := 450, targets := 1 },{ cop := 8, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 37 322 28 11 145 96 66 160 416), lower := (rows 37 322 28 11 145 96 66 128 256), losses := [] }

theorem u10060 : Upper (D 7) (R 7) [36,320,24,3,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10061 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 148, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 37 322 28 11 145 96 96 130 386), lower := (rows 37 322 28 11 145 96 96 128 256), losses := [] }

theorem u10061 : Upper (D 7) (R 7) [36,320,24,3,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10062 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 5, region := 258, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,7)], upper := (rows 37 322 28 11 145 96 192 162 290), lower := (rows 37 322 28 11 145 96 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 246 208 128 256), good := (rows 37 352 125 41 241 96 224 224 256) },{ target := 7, region := (rows 1 98 20 9 16 98 64 0 363), good := (rows 303 354 284 299 285 354 354 0 256) }] }

theorem u10062 : Upper (D 7) (R 7) [36,320,24,3,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10063 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 97, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(3,5)], upper := (rows 37 322 28 11 176 96 65 130 386), lower := (rows 37 322 28 11 176 96 65 128 256), losses := [] }

theorem u10063 : Upper (D 7) (R 7) [36,320,24,3,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10064 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 37 322 28 11 176 96 66 129 385), lower := (rows 37 322 28 11 176 96 66 128 256), losses := [] }

theorem u10064 : Upper (D 7) (R 7) [36,320,24,3,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10065 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 6, region := 48, targets := 3 }], pairs := [(1,5),(3,5),(4,0),(4,1)], upper := (rows 37 322 28 11 176 96 192 131 259), lower := (rows 37 322 28 11 176 96 192 128 256), losses := [] }

theorem u10065 : Upper (D 7) (R 7) [36,320,24,3,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10066 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 85, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 28 42 81 160 65 130 386), lower := (rows 37 322 28 42 81 160 65 128 256), losses := [] }

theorem u10066 : Upper (D 7) (R 7) [36,320,24,34,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10067 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 8, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 322 28 42 81 160 66 129 385), lower := (rows 37 322 28 42 81 160 66 128 256), losses := [] }

theorem u10067 : Upper (D 7) (R 7) [36,320,24,34,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10068 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 258, targets := 128 }], pairs := [(1,5),(1,7),(3,0),(4,5)], upper := (rows 37 322 28 42 81 160 192 131 259), lower := (rows 37 322 28 42 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 224 224 128 256), good := (rows 100 362 28 106 112 224 224 224 256) }] }

theorem u10068 : Upper (D 7) (R 7) [36,320,24,34,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10069 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 0, region := 450, targets := 1 },{ cop := 8, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 37 322 28 73 145 34 66 160 416), lower := (rows 37 322 28 73 145 34 66 128 256), losses := [] }

theorem u10069 : Upper (D 7) (R 7) [36,320,24,65,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10070 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 322 28 73 145 34 96 130 386), lower := (rows 37 322 28 73 145 34 96 128 256), losses := [] }

theorem u10070 : Upper (D 7) (R 7) [36,320,24,65,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10071 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 322 28 73 145 34 192 162 290), lower := (rows 37 322 28 73 145 34 192 128 256), losses := [] }

theorem u10071 : Upper (D 7) (R 7) [36,320,24,65,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10072 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(4,0)], upper := (rows 37 322 28 73 146 34 65 160 416), lower := (rows 37 322 28 73 146 34 65 128 256), losses := [] }

theorem u10072 : Upper (D 7) (R 7) [36,320,24,65,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10073 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 37 322 28 73 146 34 96 129 385), lower := (rows 37 322 28 73 146 34 96 128 256), losses := [] }

theorem u10073 : Upper (D 7) (R 7) [36,320,24,65,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10074 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 3, region := 290, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,1)], upper := (rows 37 322 28 73 146 34 192 161 289), lower := (rows 37 322 28 73 146 34 192 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 50 0 133 261), good := (rows 421 290 445 393 178 34 128 128 256) },{ target := 7, region := (rows 5 10 4 8 16 62 64 0 269), good := (rows 293 354 319 363 50 34 64 0 256) }] }

theorem u10074 : Upper (D 7) (R 7) [36,320,24,65,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10075 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 28 73 176 34 65 130 386), lower := (rows 37 322 28 73 176 34 65 128 256), losses := [] }

theorem u10075 : Upper (D 7) (R 7) [36,320,24,65,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10076 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 37 322 28 73 176 34 66 129 385), lower := (rows 37 322 28 73 176 34 66 128 256), losses := [] }

theorem u10076 : Upper (D 7) (R 7) [36,320,24,65,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10077 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 37 322 28 73 176 34 192 131 259), lower := (rows 37 322 28 73 176 34 192 128 256), losses := [] }

theorem u10077 : Upper (D 7) (R 7) [36,320,24,65,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10078 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 322 28 137 208 34 65 162 290), lower := (rows 37 322 28 137 208 34 65 128 256), losses := [] }

theorem u10078 : Upper (D 7) (R 7) [36,320,24,129,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10079 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,1),(3,6)], upper := (rows 37 322 28 137 208 34 66 161 289), lower := (rows 37 322 28 137 208 34 66 128 256), losses := [] }

theorem u10079 : Upper (D 7) (R 7) [36,320,24,129,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10079
end Delivery.IrregularNine14.P07
