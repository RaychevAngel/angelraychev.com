import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4020 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 41 274 96 65 196 324), lower := (rows 11 134 52 41 274 96 65 128 256), losses := [] }

theorem u4020 : Upper (D 6) (R 6) [10,132,48,33,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4021 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 134 52 41 274 96 68 193 321), lower := (rows 11 134 52 41 274 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 20 9 16 119 86 129 257), good := (rows 489 228 116 425 372 96 100 128 256) }] }

theorem u4021 : Upper (D 6) (R 6) [10,132,48,33,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4022 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 41 276 96 65 194 322), lower := (rows 11 134 52 41 276 96 65 128 256), losses := [] }

theorem u4022 : Upper (D 6) (R 6) [10,132,48,33,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4023 : Route 9 := (fun mask => (mask,id))

def c4023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4023 : Upper (D 6) (R 6) [10,132,48,33,260,64,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,260,64,2] 13 (by decide) (choices 1) [1,64] r4023 c4023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u294
  · exact u295

def b4024 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 52 73 274 96 65 164 292), lower := (rows 11 134 52 73 274 96 65 128 256), losses := [] }

theorem u4024 : Upper (D 6) (R 6) [10,132,48,65,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4025 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 134 52 73 274 96 68 161 289), lower := (rows 11 134 52 73 274 96 68 128 256), losses := [] }

theorem u4025 : Upper (D 6) (R 6) [10,132,48,65,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4026 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0),(3,1),(3,2)], upper := (rows 11 134 52 73 274 96 96 133 261), lower := (rows 11 134 52 73 274 96 96 128 256), losses := [] }

theorem u4026 : Upper (D 6) (R 6) [10,132,48,65,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4027 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 73 276 34 65 224 352), lower := (rows 11 134 52 73 276 34 65 128 256), losses := [] }

theorem u4027 : Upper (D 6) (R 6) [10,132,48,65,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4028 : Route 9 := (fun mask => (mask,id))

def c4028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4028 : Upper (D 6) (R 6) [10,132,48,65,260,2,32] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,260,2,32] 13 (by decide) (choices 1) [1,64] r4028 c4028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u296
  · exact u297

def b4029 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 52 73 276 96 65 162 290), lower := (rows 11 134 52 73 276 96 65 128 256), losses := [] }

theorem u4029 : Upper (D 6) (R 6) [10,132,48,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4030 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 1, region := 73, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 52 73 276 96 66 161 289), lower := (rows 11 134 52 73 276 96 66 128 256), losses := [] }

theorem u4030 : Upper (D 6) (R 6) [10,132,48,65,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4031 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 73 276 96 96 131 259), lower := (rows 11 134 52 73 276 96 96 128 256), losses := [] }

theorem u4031 : Upper (D 6) (R 6) [10,132,48,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4032 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 166, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 52 73 336 34 65 164 292), lower := (rows 11 134 52 73 336 34 65 128 256), losses := [] }

theorem u4032 : Upper (D 6) (R 6) [10,132,48,65,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4033 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,1),(3,5)], upper := (rows 11 134 52 73 336 34 68 161 289), lower := (rows 11 134 52 73 336 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 32 70 128 256), good := (rows 73 196 116 73 336 96 68 128 256) }] }

theorem u4033 : Upper (D 6) (R 6) [10,132,48,65,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4034 : Route 9 := (fun mask => (mask,id))

def c4034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4034 : Upper (D 6) (R 6) [10,132,48,65,320,2,32] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,320,2,32] 13 (by decide) (choices 1) [1,4] r4034 c4034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u298
  · exact u299

def b4035 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 130, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 134 52 76 273 96 65 162 290), lower := (rows 11 134 52 76 273 96 65 128 256), losses := [] }

theorem u4035 : Upper (D 6) (R 6) [10,132,48,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4036 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 134 52 76 273 96 66 161 289), lower := (rows 11 134 52 76 273 96 66 128 256), losses := [] }

theorem u4036 : Upper (D 6) (R 6) [10,132,48,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4037 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 52 76 273 96 96 131 259), lower := (rows 11 134 52 76 273 96 96 128 256), losses := [] }

theorem u4037 : Upper (D 6) (R 6) [10,132,48,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4038 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 134 52 76 274 33 65 224 352), lower := (rows 11 134 52 76 274 33 65 128 256), losses := [] }

theorem u4038 : Upper (D 6) (R 6) [10,132,48,68,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4039 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 134 52 76 274 33 96 193 321), lower := (rows 11 134 52 76 274 33 96 128 256), losses := [] }

theorem u4039 : Upper (D 6) (R 6) [10,132,48,68,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4040 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 134 52 76 274 96 65 161 289), lower := (rows 11 134 52 76 274 96 65 128 256), losses := [] }

theorem u4040 : Upper (D 6) (R 6) [10,132,48,68,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4041 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 52 76 274 96 96 129 257), lower := (rows 11 134 52 76 274 96 96 128 256), losses := [] }

theorem u4041 : Upper (D 6) (R 6) [10,132,48,68,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4042 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 52 104 82 33 65 388 260), lower := (rows 11 134 52 104 82 33 65 128 256), losses := [] }

theorem u4042 : Upper (D 6) (R 6) [10,132,48,96,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4043 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 2, region := 72, targets := 1 }], pairs := [(3,0),(4,0),(4,5)], upper := (rows 11 134 52 104 82 33 68 385 257), lower := (rows 11 134 52 104 82 33 68 128 256), losses := [] }

theorem u4043 : Upper (D 6) (R 6) [10,132,48,96,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4044 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 52 104 82 33 320 133 261), lower := (rows 11 134 52 104 82 33 320 128 256), losses := [] }

theorem u4044 : Upper (D 6) (R 6) [10,132,48,96,66,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4044 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4045 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 11 134 52 104 82 288 65 133 261), lower := (rows 11 134 52 104 82 288 65 128 256), losses := [] }

theorem u4045 : Upper (D 6) (R 6) [10,132,48,96,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4045 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4046 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 11 134 52 104 82 288 68 129 257), lower := (rows 11 134 52 104 82 288 68 128 256), losses := [] }

theorem u4046 : Upper (D 6) (R 6) [10,132,48,96,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4046 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4047 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 134 52 104 273 34 65 196 324), lower := (rows 11 134 52 104 273 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 20 72 16 35 64 128 256), good := (rows 42 166 52 104 308 34 104 128 256) }] }

theorem u4047 : Upper (D 6) (R 6) [10,132,48,96,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4048 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 134 52 104 273 34 68 193 321), lower := (rows 11 134 52 104 273 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 63 16 35 86 128 256), good := (rows 106 238 124 104 380 106 76 128 256) }] }

theorem u4048 : Upper (D 6) (R 6) [10,132,48,96,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4049 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 104 274 33 65 196 324), lower := (rows 11 134 52 104 274 33 65 128 256), losses := [] }

theorem u4049 : Upper (D 6) (R 6) [10,132,48,96,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4050 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1),(4,5)], upper := (rows 11 134 52 104 274 33 68 193 321), lower := (rows 11 134 52 104 274 33 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 70 129 257), good := (rows 475 198 84 72 338 401 68 128 256) }] }

theorem u4050 : Upper (D 6) (R 6) [10,132,48,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4051 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 104 276 33 65 194 322), lower := (rows 11 134 52 104 276 33 65 128 256), losses := [] }

theorem u4051 : Upper (D 6) (R 6) [10,132,48,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4052 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 134 52 104 276 33 66 193 321), lower := (rows 11 134 52 104 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 67 128 256), good := (rows 74 198 60 104 276 104 66 128 256) }] }

theorem u4052 : Upper (D 6) (R 6) [10,132,48,96,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4053 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 134 52 104 276 34 65 193 321), lower := (rows 11 134 52 104 276 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 16 35 64 128 256), good := (rows 42 166 52 104 276 34 104 128 256) }] }

theorem u4053 : Upper (D 6) (R 6) [10,132,48,96,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4054 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 134 52 104 336 33 65 134 262), lower := (rows 11 134 52 104 336 33 65 128 256), losses := [] }

theorem u4054 : Upper (D 6) (R 6) [10,132,48,96,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4055 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 134 52 104 336 33 66 133 261), lower := (rows 11 134 52 104 336 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 67 128 256), good := (rows 74 198 60 104 336 104 66 128 256) }] }

theorem u4055 : Upper (D 6) (R 6) [10,132,48,96,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4056 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1),(4,5)], upper := (rows 11 134 52 104 336 33 68 131 259), lower := (rows 11 134 52 104 336 33 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 70 129 257), good := (rows 475 198 84 72 336 401 68 128 256) }] }

theorem u4056 : Upper (D 6) (R 6) [10,132,48,96,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4057 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 134 52 104 336 34 65 133 261), lower := (rows 11 134 52 104 336 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 16 35 64 128 256), good := (rows 42 166 52 104 344 34 104 128 256) }] }

theorem u4057 : Upper (D 6) (R 6) [10,132,48,96,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4058 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 134 52 104 336 34 68 129 257), lower := (rows 11 134 52 104 336 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 44 17 32 70 129 257), good := (rows 473 204 124 104 336 104 76 128 256) }] }

theorem u4058 : Upper (D 6) (R 6) [10,132,48,96,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4059 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 265 84 34 65 224 352), lower := (rows 11 134 52 265 84 34 65 128 256), losses := [] }

theorem u4059 : Upper (D 6) (R 6) [10,132,48,257,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4060 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 265 84 34 96 193 321), lower := (rows 11 134 52 265 84 34 96 128 256), losses := [] }

theorem u4060 : Upper (D 6) (R 6) [10,132,48,257,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4061 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 134 52 268 82 33 65 224 352), lower := (rows 11 134 52 268 82 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 30 16 97 97 245 373), good := (rows 489 396 508 396 508 481 481 128 256) }] }

theorem u4061 : Upper (D 6) (R 6) [10,132,48,260,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4062 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(3,1),(4,0),(4,2)], upper := (rows 11 134 52 268 82 33 96 193 321), lower := (rows 11 134 52 268 82 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 32 100 128 256), good := (rows 26 214 116 332 82 96 96 128 256) },{ target := 1, region := (rows 1 0 4 12 16 33 101 161 289), good := (rows 489 204 508 332 80 481 480 128 256) }] }

theorem u4062 : Upper (D 6) (R 6) [10,132,48,260,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4063 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 52 296 81 34 65 196 324), lower := (rows 11 134 52 296 81 34 65 128 256), losses := [] }

theorem u4063 : Upper (D 6) (R 6) [10,132,48,288,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4064 : PairBound 9 := { available := 65, camps := [], pairs := [(2,0),(3,1),(4,1)], upper := (rows 11 134 52 296 81 34 68 193 321), lower := (rows 11 134 52 296 81 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 86 128 256), good := (rows 106 230 116 296 116 98 68 128 256) },{ target := 1, region := (rows 1 0 4 12 17 32 70 145 273), good := (rows 473 204 508 296 465 96 76 128 256) }] }

theorem u4064 : Upper (D 6) (R 6) [10,132,48,288,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4065 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 134 52 296 82 33 65 196 324), lower := (rows 11 134 52 296 82 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 28 16 97 97 148 276), good := (rows 105 396 508 360 508 97 97 128 256) }] }

theorem u4065 : Upper (D 6) (R 6) [10,132,48,288,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4066 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 11 134 52 296 82 33 68 193 321), lower := (rows 11 134 52 296 82 33 68 128 256), losses := [] }

theorem u4066 : Upper (D 6) (R 6) [10,132,48,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4067 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 134 52 296 84 33 65 194 322), lower := (rows 11 134 52 296 84 33 65 128 256), losses := [] }

theorem u4067 : Upper (D 6) (R 6) [10,132,48,288,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4068 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 11 134 52 296 84 33 66 193 321), lower := (rows 11 134 52 296 84 33 66 128 256), losses := [] }

theorem u4068 : Upper (D 6) (R 6) [10,132,48,288,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4069 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 134 52 296 84 34 65 193 321), lower := (rows 11 134 52 296 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 8 80 35 64 128 256), good := (rows 42 166 52 296 84 34 116 128 256) }] }

theorem u4069 : Upper (D 6) (R 6) [10,132,48,288,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4070 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 0, region := 80, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 134 52 328 82 33 65 164 292), lower := (rows 11 134 52 328 82 33 65 128 256), losses := [] }

theorem u4070 : Upper (D 6) (R 6) [10,132,48,320,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4071 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 11 134 52 328 82 33 68 161 289), lower := (rows 11 134 52 328 82 33 68 128 256), losses := [] }

theorem u4071 : Upper (D 6) (R 6) [10,132,48,320,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4072 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(4,0),(4,2)], upper := (rows 11 134 52 328 82 33 96 133 261), lower := (rows 11 134 52 328 82 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 32 100 128 256), good := (rows 26 214 116 328 82 96 96 128 256) },{ target := 5, region := (rows 21 6 4 24 16 0 64 134 262), good := (rows 395 391 415 328 475 1 64 128 256) }] }

theorem u4072 : Upper (D 6) (R 6) [10,132,48,320,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4073 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 134 52 328 84 33 65 162 290), lower := (rows 11 134 52 328 84 33 65 128 256), losses := [] }

theorem u4073 : Upper (D 6) (R 6) [10,132,48,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4074 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 11 134 52 328 84 33 66 161 289), lower := (rows 11 134 52 328 84 33 66 128 256), losses := [] }

theorem u4074 : Upper (D 6) (R 6) [10,132,48,320,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4075 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 328 84 33 96 131 259), lower := (rows 11 134 52 328 84 33 96 128 256), losses := [] }

theorem u4075 : Upper (D 6) (R 6) [10,132,48,320,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4076 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 134 52 328 84 34 65 161 289), lower := (rows 11 134 52 328 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 8 88 35 64 128 256), good := (rows 62 166 52 348 84 34 116 128 256) }] }

theorem u4076 : Upper (D 6) (R 6) [10,132,48,320,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4077 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 328 84 34 96 129 257), lower := (rows 11 134 52 328 84 34 96 128 256), losses := [] }

theorem u4077 : Upper (D 6) (R 6) [10,132,48,320,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4078 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 100 25 276 33 66 224 352), lower := (rows 11 134 100 25 276 33 66 128 256), losses := [] }

theorem u4078 : Upper (D 6) (R 6) [10,132,96,17,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4079 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 100 25 276 34 96 193 321), lower := (rows 11 134 100 25 276 34 96 128 256), losses := [] }

theorem u4079 : Upper (D 6) (R 6) [10,132,96,17,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4079
end Delivery.IrregularNine14.P06
