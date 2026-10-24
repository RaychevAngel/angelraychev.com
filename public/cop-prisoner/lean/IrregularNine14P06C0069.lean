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

def b4140 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 134 261 44 81 96 66 176 304), lower := (rows 11 134 261 44 81 96 66 128 256), losses := [] }

theorem u4140 : Upper (D 6) (R 6) [10,132,257,36,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4141 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 261 44 81 96 80 162 290), lower := (rows 11 134 261 44 81 96 80 128 256), losses := [] }

theorem u4141 : Upper (D 6) (R 6) [10,132,257,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4141 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4142 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 11 134 261 44 81 96 96 146 274), lower := (rows 11 134 261 44 81 96 96 128 256), losses := [] }

theorem u4142 : Upper (D 6) (R 6) [10,132,257,36,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4143 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,2),(4,5)], upper := (rows 11 134 261 44 82 48 65 224 352), lower := (rows 11 134 261 44 82 48 65 128 256), losses := [] }

theorem u4143 : Upper (D 6) (R 6) [10,132,257,36,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4143 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4144 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 11 134 261 44 82 48 96 193 321), lower := (rows 11 134 261 44 82 48 96 128 256), losses := [] }

theorem u4144 : Upper (D 6) (R 6) [10,132,257,36,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4144 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4145 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 },{ cop := 2, region := 104, targets := 2 }], pairs := [(3,1),(4,2),(4,5)], upper := (rows 11 134 261 44 82 96 65 176 304), lower := (rows 11 134 261 44 82 96 65 128 256), losses := [] }

theorem u4145 : Upper (D 6) (R 6) [10,132,257,36,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4146 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 261 44 82 96 80 161 289), lower := (rows 11 134 261 44 82 96 80 128 256), losses := [] }

theorem u4146 : Upper (D 6) (R 6) [10,132,257,36,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4146 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4147 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 0, region := 112, targets := 4 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 11 134 261 44 82 96 96 145 273), lower := (rows 11 134 261 44 82 96 96 128 256), losses := [] }

theorem u4147 : Upper (D 6) (R 6) [10,132,257,36,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4148 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 134 261 56 81 36 66 224 352), lower := (rows 11 134 261 56 81 36 66 128 256), losses := [] }

theorem u4148 : Upper (D 6) (R 6) [10,132,257,48,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4149 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 4, region := 390, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 134 261 56 81 36 96 194 322), lower := (rows 11 134 261 56 81 36 96 128 256), losses := [] }

theorem u4149 : Upper (D 6) (R 6) [10,132,257,48,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4150 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 80, targets := 34 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 134 261 56 84 34 65 224 352), lower := (rows 11 134 261 56 84 34 65 128 256), losses := [] }

theorem u4150 : Upper (D 6) (R 6) [10,132,257,48,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4151 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 120, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 134 261 56 84 34 96 193 321), lower := (rows 11 134 261 56 84 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 32 104 129 257), good := (rows 477 132 405 120 84 96 96 128 256) }] }

theorem u4151 : Upper (D 6) (R 6) [10,132,257,48,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4152 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 2, region := 104, targets := 2 }], pairs := [(3,1),(4,2),(4,6)], upper := (rows 11 134 261 104 50 33 68 208 336), lower := (rows 11 134 261 104 50 33 68 128 256), losses := [] }

theorem u4152 : Upper (D 6) (R 6) [10,132,257,96,34,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4153 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 261 104 50 33 80 196 324), lower := (rows 11 134 261 104 50 33 80 128 256), losses := [] }

theorem u4153 : Upper (D 6) (R 6) [10,132,257,96,34,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4153 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4154 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 134 261 104 52 34 65 208 336), lower := (rows 11 134 261 104 52 34 65 128 256), losses := [] }

theorem u4154 : Upper (D 6) (R 6) [10,132,257,96,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4155 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 261 104 52 34 80 193 321), lower := (rows 11 134 261 104 52 34 80 128 256), losses := [] }

theorem u4155 : Upper (D 6) (R 6) [10,132,257,96,36,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4155 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4156 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 262 25 52 96 65 224 352), lower := (rows 11 134 262 25 52 96 65 128 256), losses := [] }

theorem u4156 : Upper (D 6) (R 6) [10,132,258,17,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4157 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 11 134 262 25 52 96 96 193 321), lower := (rows 11 134 262 25 52 96 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 22 511 511 137 265), good := (rows 505 244 372 505 116 96 96 224 352) }] }

theorem u4157 : Upper (D 6) (R 6) [10,132,258,17,36,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4158 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 262 25 112 33 68 224 352), lower := (rows 11 134 262 25 112 33 68 128 256), losses := [] }

theorem u4158 : Upper (D 6) (R 6) [10,132,258,17,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4159 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 262 25 112 36 96 193 321), lower := (rows 11 134 262 25 112 36 96 128 256), losses := [] }

theorem u4159 : Upper (D 6) (R 6) [10,132,258,17,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4160 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 5, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 262 28 49 96 65 224 352), lower := (rows 11 134 262 28 49 96 65 128 256), losses := [] }

theorem u4160 : Upper (D 6) (R 6) [10,132,258,20,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4161 : Route 9 := (fun mask => (mask,id))

def c4161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4161 : Upper (D 6) (R 6) [10,132,258,20,33,64,32] 13 := by
  apply FastRouting.sound _ _ [10,132,258,20,33,64,32] 13 (by decide) (choices 1) [1,64] r4161 c4161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u312
  · exact u313

def b4162 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 262 28 112 33 65 224 352), lower := (rows 11 134 262 28 112 33 65 128 256), losses := [] }

theorem u4162 : Upper (D 6) (R 6) [10,132,258,20,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4163 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 262 28 112 33 96 193 321), lower := (rows 11 134 262 28 112 33 96 128 256), losses := [] }

theorem u4163 : Upper (D 6) (R 6) [10,132,258,20,96,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4164 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 262 41 52 96 65 208 336), lower := (rows 11 134 262 41 52 96 65 128 256), losses := [] }

theorem u4164 : Upper (D 6) (R 6) [10,132,258,33,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4165 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 262 41 52 96 80 193 321), lower := (rows 11 134 262 41 52 96 80 128 256), losses := [] }

theorem u4165 : Upper (D 6) (R 6) [10,132,258,33,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4165 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4166 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 262 41 84 48 65 224 352), lower := (rows 11 134 262 41 84 48 65 128 256), losses := [] }

theorem u4166 : Upper (D 6) (R 6) [10,132,258,33,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4166 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4167 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 262 41 84 48 96 193 321), lower := (rows 11 134 262 41 84 48 96 128 256), losses := [] }

theorem u4167 : Upper (D 6) (R 6) [10,132,258,33,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4167 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4168 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 262 41 84 96 65 176 304), lower := (rows 11 134 262 41 84 96 65 128 256), losses := [] }

theorem u4168 : Upper (D 6) (R 6) [10,132,258,33,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4169 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 262 41 84 96 80 161 289), lower := (rows 11 134 262 41 84 96 80 128 256), losses := [] }

theorem u4169 : Upper (D 6) (R 6) [10,132,258,33,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4169 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4170 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 2, region := 112, targets := 1 }], pairs := [(3,1),(3,2),(4,0)], upper := (rows 11 134 262 41 84 96 96 145 273), lower := (rows 11 134 262 41 84 96 96 128 256), losses := [] }

theorem u4170 : Upper (D 6) (R 6) [10,132,258,33,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4171 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 262 44 81 96 65 176 304), lower := (rows 11 134 262 44 81 96 65 128 256), losses := [] }

theorem u4171 : Upper (D 6) (R 6) [10,132,258,36,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4172 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 262 44 81 96 80 161 289), lower := (rows 11 134 262 44 81 96 80 128 256), losses := [] }

theorem u4172 : Upper (D 6) (R 6) [10,132,258,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4172 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4173 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 11 134 262 44 81 96 96 145 273), lower := (rows 11 134 262 44 81 96 96 128 256), losses := [] }

theorem u4173 : Upper (D 6) (R 6) [10,132,258,36,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4174 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 104, targets := 6 },{ cop := 5, region := 390, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 262 56 21 96 65 224 352), lower := (rows 11 134 262 56 21 96 65 128 256), losses := [] }

theorem u4174 : Upper (D 6) (R 6) [10,132,258,48,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4175 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 6 },{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 262 56 21 96 96 193 321), lower := (rows 11 134 262 56 21 96 96 128 256), losses := [] }

theorem u4175 : Upper (D 6) (R 6) [10,132,258,48,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4176 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 134 262 56 81 36 65 224 352), lower := (rows 11 134 262 56 81 36 65 128 256), losses := [] }

theorem u4176 : Upper (D 6) (R 6) [10,132,258,48,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4177 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 390, targets := 32 }], pairs := [(1,5),(2,5),(3,1)], upper := (rows 11 134 262 56 81 36 96 193 321), lower := (rows 11 134 262 56 81 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 111 145 273), good := (rows 505 228 356 504 473 100 96 128 256) }] }

theorem u4177 : Upper (D 6) (R 6) [10,132,258,48,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4178 : PairBound 9 := { available := 96, camps := [], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 134 262 56 84 33 65 224 352), lower := (rows 11 134 262 56 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 97 97 249 377), good := (rows 489 132 260 504 508 481 481 128 256) },{ target := 2, region := (rows 1 2 0 24 16 97 97 249 377), good := (rows 491 130 258 504 504 481 481 128 256) },{ target := 6, region := (rows 1 2 4 24 16 97 0 128 256), good := (rows 43 134 262 56 60 33 33 128 256) }] }

theorem u4178 : Upper (D 6) (R 6) [10,132,258,48,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4179 : Route 9 := (fun mask => (mask,id))

def c4179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4179 : Upper (D 6) (R 6) [10,132,258,48,68,1,32] 13 := by
  apply FastRouting.sound _ _ [10,132,258,48,68,1,32] 13 (by decide) (choices 1) [1,64] r4179 c4179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u314
  · exact u315

def b4180 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 390, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 262 104 21 33 80 224 352), lower := (rows 11 134 262 104 21 33 80 128 256), losses := [] }

theorem u4180 : Upper (D 6) (R 6) [10,132,258,96,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4180 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4181 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 262 104 21 33 96 208 336), lower := (rows 11 134 262 104 21 33 96 128 256), losses := [] }

theorem u4181 : Upper (D 6) (R 6) [10,132,258,96,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4182 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 262 104 52 33 65 208 336), lower := (rows 11 134 262 104 52 33 65 128 256), losses := [] }

theorem u4182 : Upper (D 6) (R 6) [10,132,258,96,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4183 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 262 104 52 33 80 193 321), lower := (rows 11 134 262 104 52 33 80 128 256), losses := [] }

theorem u4183 : Upper (D 6) (R 6) [10,132,258,96,36,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4183 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4184 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 276 41 52 96 65 194 322), lower := (rows 11 134 276 41 52 96 65 128 256), losses := [] }

theorem u4184 : Upper (D 6) (R 6) [10,132,272,33,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4185 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 112, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 11 134 276 41 52 96 66 193 321), lower := (rows 11 134 276 41 52 96 66 128 256), losses := [] }

theorem u4185 : Upper (D 6) (R 6) [10,132,272,33,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4186 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 276 41 82 96 65 164 292), lower := (rows 11 134 276 41 82 96 65 128 256), losses := [] }

theorem u4186 : Upper (D 6) (R 6) [10,132,272,33,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4187 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 11 134 276 41 82 96 68 161 289), lower := (rows 11 134 276 41 82 96 68 128 256), losses := [] }

theorem u4187 : Upper (D 6) (R 6) [10,132,272,33,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4188 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 276 41 82 96 96 133 261), lower := (rows 11 134 276 41 82 96 96 128 256), losses := [] }

theorem u4188 : Upper (D 6) (R 6) [10,132,272,33,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4189 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 276 41 84 96 65 162 290), lower := (rows 11 134 276 41 84 96 65 128 256), losses := [] }

theorem u4189 : Upper (D 6) (R 6) [10,132,272,33,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4190 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 11 134 276 41 84 96 66 161 289), lower := (rows 11 134 276 41 84 96 66 128 256), losses := [] }

theorem u4190 : Upper (D 6) (R 6) [10,132,272,33,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4191 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 276 41 84 96 96 131 259), lower := (rows 11 134 276 41 84 96 96 128 256), losses := [] }

theorem u4191 : Upper (D 6) (R 6) [10,132,272,33,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4192 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 134 276 104 21 33 66 224 352), lower := (rows 11 134 276 104 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 67 168 296), good := (rows 458 198 276 488 84 488 66 128 256) }] }

theorem u4192 : Upper (D 6) (R 6) [10,132,272,96,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4193 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 276 104 21 33 96 194 322), lower := (rows 11 134 276 104 21 33 96 128 256), losses := [] }

theorem u4193 : Upper (D 6) (R 6) [10,132,272,96,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4194 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 276 104 21 34 96 193 321), lower := (rows 11 134 276 104 21 34 96 128 256), losses := [] }

theorem u4194 : Upper (D 6) (R 6) [10,132,272,96,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4195 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 276 104 50 33 65 196 324), lower := (rows 11 134 276 104 50 33 65 128 256), losses := [] }

theorem u4195 : Upper (D 6) (R 6) [10,132,272,96,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4196 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 48, targets := 68 }], pairs := [(3,0),(4,2),(4,6)], upper := (rows 11 134 276 104 50 33 68 193 321), lower := (rows 11 134 276 104 50 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 70 128 256), good := (rows 74 198 348 104 122 32 68 128 256) }] }

theorem u4196 : Upper (D 6) (R 6) [10,132,272,96,34,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4197 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 276 104 52 33 65 194 322), lower := (rows 11 134 276 104 52 33 65 128 256), losses := [] }

theorem u4197 : Upper (D 6) (R 6) [10,132,272,96,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4198 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 134 276 104 52 33 66 193 321), lower := (rows 11 134 276 104 52 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 67 128 256), good := (rows 74 198 276 104 60 104 66 128 256) }] }

theorem u4198 : Upper (D 6) (R 6) [10,132,272,96,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4199 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 25 84 34 65 224 352), lower := (rows 11 134 292 25 84 34 65 128 256), losses := [] }

theorem u4199 : Upper (D 6) (R 6) [10,132,288,17,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4199
end Delivery.IrregularNine14.P06
