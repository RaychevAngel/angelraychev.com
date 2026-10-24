import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4140 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 6, region := 170, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 148 168 273 34 65 194 322), lower := (rows 13 98 148 168 273 34 65 128 256), losses := [] }

theorem u4140 : Upper (D 7) (R 7) [12,96,144,160,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4141 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 148 168 273 34 66 193 321), lower := (rows 13 98 148 168 273 34 66 128 256), losses := [] }

theorem u4141 : Upper (D 7) (R 7) [12,96,144,160,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4142 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 458, targets := 1 },{ cop := 1, region := 264, targets := 128 },{ cop := 4, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(3,7)], upper := (rows 13 98 148 266 19 33 192 224 352), lower := (rows 13 98 148 266 19 33 192 128 256), losses := [] }

theorem u4142 : Upper (D 7) (R 7) [12,96,144,258,3,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4143 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 266 19 96 192 161 289), lower := (rows 13 98 148 266 19 96 192 128 256), losses := [] }

theorem u4143 : Upper (D 7) (R 7) [12,96,144,258,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4144 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 426, targets := 1 },{ cop := 1, region := 264, targets := 128 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,7)], upper := (rows 13 98 148 296 19 160 65 194 322), lower := (rows 13 98 148 296 19 160 65 128 256), losses := [] }

theorem u4144 : Upper (D 7) (R 7) [12,96,144,288,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4145 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(1,7),(2,5),(4,7)], upper := (rows 13 98 148 296 19 160 66 193 321), lower := (rows 13 98 148 296 19 160 66 128 256), losses := [{ target := 7, region := (rows 1 42 4 8 17 32 123 0 273), good := (rows 351 98 340 362 339 98 66 0 256) }] }

theorem u4145 : Upper (D 7) (R 7) [12,96,144,288,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4146 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 98 148 296 81 34 65 130 386), lower := (rows 13 98 148 296 81 34 65 128 256), losses := [] }

theorem u4146 : Upper (D 7) (R 7) [12,96,144,288,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4147 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 148 296 81 34 66 129 385), lower := (rows 13 98 148 296 81 34 66 128 256), losses := [] }

theorem u4147 : Upper (D 7) (R 7) [12,96,144,288,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4148 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 298, targets := 128 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,1)], upper := (rows 13 98 148 296 81 34 192 131 259), lower := (rows 13 98 148 296 81 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 32 196 128 256), good := (rows 93 96 212 296 81 32 192 192 256) }] }

theorem u4148 : Upper (D 7) (R 7) [12,96,144,288,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4149 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 98 148 296 81 160 65 130 258), lower := (rows 13 98 148 296 81 160 65 128 256), losses := [] }

theorem u4149 : Upper (D 7) (R 7) [12,96,144,288,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4150 : Route 9 := (fun mask => (mask,id))

def c4150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4150 : Upper (D 7) (R 7) [12,96,144,288,65,128,2] 13 := by
  apply FastRouting.sound _ _ [12,96,144,288,65,128,2] 13 (by decide) (choices 1) [1,2] r4150 c4150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u322
  · exact u323

def b4151 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 148 392 19 33 66 224 352), lower := (rows 13 98 148 392 19 33 66 128 256), losses := [] }

theorem u4151 : Upper (D 7) (R 7) [12,96,144,384,3,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4152 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 148 392 19 34 96 193 321), lower := (rows 13 98 148 392 19 34 96 128 256), losses := [] }

theorem u4152 : Upper (D 7) (R 7) [12,96,144,384,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4153 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 6, region := 426, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 148 392 49 34 65 194 322), lower := (rows 13 98 148 392 49 34 65 128 256), losses := [] }

theorem u4153 : Upper (D 7) (R 7) [12,96,144,384,33,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4154 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 148 392 49 34 66 193 321), lower := (rows 13 98 148 392 49 34 66 128 256), losses := [] }

theorem u4154 : Upper (D 7) (R 7) [12,96,144,384,33,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4155 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 13 98 164 200 273 33 80 130 258), lower := (rows 13 98 164 200 273 33 80 128 256), losses := [] }

theorem u4155 : Upper (D 7) (R 7) [12,96,160,192,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4155 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4156 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 13 98 164 200 273 34 80 131 259), lower := (rows 13 98 164 200 273 34 80 128 256), losses := [] }

theorem u4156 : Upper (D 7) (R 7) [12,96,160,192,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4156 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4157 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 13 98 164 200 274 33 80 131 259), lower := (rows 13 98 164 200 274 33 80 128 256), losses := [] }

theorem u4157 : Upper (D 7) (R 7) [12,96,160,192,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4157 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4158 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 164 200 274 34 80 129 257), lower := (rows 13 98 164 200 274 34 80 128 256), losses := [] }

theorem u4158 : Upper (D 7) (R 7) [12,96,160,192,258,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4158 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4159 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 164 265 81 34 66 144 400), lower := (rows 13 98 164 265 81 34 66 128 256), losses := [] }

theorem u4159 : Upper (D 7) (R 7) [12,96,160,257,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4160 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 265 81 34 80 130 386), lower := (rows 13 98 164 265 81 34 80 128 256), losses := [] }

theorem u4160 : Upper (D 7) (R 7) [12,96,160,257,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4160 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4161 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 298, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 164 265 81 34 192 146 274), lower := (rows 13 98 164 265 81 34 192 128 256), losses := [] }

theorem u4161 : Upper (D 7) (R 7) [12,96,160,257,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4162 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 182, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 13 98 164 265 208 34 65 146 274), lower := (rows 13 98 164 265 208 34 65 128 256), losses := [] }

theorem u4162 : Upper (D 7) (R 7) [12,96,160,257,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4163 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 164 265 208 34 66 145 273), lower := (rows 13 98 164 265 208 34 66 128 256), losses := [] }

theorem u4163 : Upper (D 7) (R 7) [12,96,160,257,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4164 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 265 208 34 80 131 259), lower := (rows 13 98 164 265 208 34 80 128 256), losses := [] }

theorem u4164 : Upper (D 7) (R 7) [12,96,160,257,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4164 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4165 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 13 98 164 266 19 33 80 192 448), lower := (rows 13 98 164 266 19 33 80 128 256), losses := [] }

theorem u4165 : Upper (D 7) (R 7) [12,96,160,258,3,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4165 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4166 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 456, targets := 33 },{ cop := 2, region := 66, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(3,5)], upper := (rows 13 98 164 266 19 33 192 208 336), lower := (rows 13 98 164 266 19 33 192 128 256), losses := [] }

theorem u4166 : Upper (D 7) (R 7) [12,96,160,258,3,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4167 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 13 98 164 266 19 48 65 192 448), lower := (rows 13 98 164 266 19 48 65 128 256), losses := [] }

theorem u4167 : Upper (D 7) (R 7) [12,96,160,258,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4167 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4168 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 1 },{ cop := 4, region := 228, targets := 2 },{ cop := 4, region := 456, targets := 32 }], pairs := [(1,0),(2,1),(3,5)], upper := (rows 13 98 164 266 19 48 192 193 321), lower := (rows 13 98 164 266 19 48 192 128 256), losses := [] }

theorem u4168 : Upper (D 7) (R 7) [12,96,160,258,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4168 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4169 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 4, region := 164, targets := 66 }], pairs := [(1,7),(2,1),(2,6),(4,7)], upper := (rows 13 98 164 266 81 33 66 144 400), lower := (rows 13 98 164 266 81 33 66 128 256), losses := [] }

theorem u4169 : Upper (D 7) (R 7) [12,96,160,258,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4170 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 266 81 33 80 130 386), lower := (rows 13 98 164 266 81 33 80 128 256), losses := [] }

theorem u4170 : Upper (D 7) (R 7) [12,96,160,258,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4170 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4171 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,1)], upper := (rows 13 98 164 266 81 33 192 146 274), lower := (rows 13 98 164 266 81 33 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 49 196 128 256), good := (rows 125 96 228 264 113 49 192 192 256) }] }

theorem u4171 : Upper (D 7) (R 7) [12,96,160,258,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4172 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 164 266 146 33 65 208 336), lower := (rows 13 98 164 266 146 33 65 128 256), losses := [] }

theorem u4172 : Upper (D 7) (R 7) [12,96,160,258,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4173 : Route 9 := (fun mask => (mask,id))

def c4173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4173 : Upper (D 7) (R 7) [12,96,160,258,130,1,16] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,130,1,16] 13 (by decide) (choices 1) [1,64] r4173 c4173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u324
  · exact u325

def b4174 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 164 266 208 33 65 146 274), lower := (rows 13 98 164 266 208 33 65 128 256), losses := [] }

theorem u4174 : Upper (D 7) (R 7) [12,96,160,258,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4175 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 82, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,5),(4,0)], upper := (rows 13 98 164 266 208 33 66 145 273), lower := (rows 13 98 164 266 208 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 19 0 74 161 289), good := (rows 477 474 388 346 208 401 90 128 256) }] }

theorem u4175 : Upper (D 7) (R 7) [12,96,160,258,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4176 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 266 208 33 80 131 259), lower := (rows 13 98 164 266 208 33 80 128 256), losses := [] }

theorem u4176 : Upper (D 7) (R 7) [12,96,160,258,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4176 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4177 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 98 164 280 81 34 65 130 386), lower := (rows 13 98 164 280 81 34 65 128 256), losses := [] }

theorem u4177 : Upper (D 7) (R 7) [12,96,160,272,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4178 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 164 280 81 34 66 129 385), lower := (rows 13 98 164 280 81 34 66 128 256), losses := [] }

theorem u4178 : Upper (D 7) (R 7) [12,96,160,272,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4179 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 298, targets := 128 },{ cop := 6, region := 38, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 164 280 81 34 192 131 259), lower := (rows 13 98 164 280 81 34 192 128 256), losses := [] }

theorem u4179 : Upper (D 7) (R 7) [12,96,160,272,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4180 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 6, region := 166, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 164 280 145 34 65 194 322), lower := (rows 13 98 164 280 145 34 65 128 256), losses := [] }

theorem u4180 : Upper (D 7) (R 7) [12,96,160,272,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4181 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 164 280 145 34 66 193 321), lower := (rows 13 98 164 280 145 34 66 128 256), losses := [] }

theorem u4181 : Upper (D 7) (R 7) [12,96,160,272,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4182 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 164 280 146 33 65 194 322), lower := (rows 13 98 164 280 146 33 65 128 256), losses := [] }

theorem u4182 : Upper (D 7) (R 7) [12,96,160,272,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4183 : Route 9 := (fun mask => (mask,id))

def c4183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4183 : Upper (D 7) (R 7) [12,96,160,272,130,1,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,130,1,2] 13 (by decide) (choices 1) [1,64] r4183 c4183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u326
  · exact u327

def b4184 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 164 280 208 33 65 130 258), lower := (rows 13 98 164 280 208 33 65 128 256), losses := [] }

theorem u4184 : Upper (D 7) (R 7) [12,96,160,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4185 : Route 9 := (fun mask => (mask,id))

def c4185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4185 : Upper (D 7) (R 7) [12,96,160,272,192,1,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,192,1,2] 13 (by decide) (choices 1) [1,2] r4185 c4185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u328
  · exact u329

def b4186 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 164 280 208 34 65 131 259), lower := (rows 13 98 164 280 208 34 65 128 256), losses := [{ target := 7, region := (rows 1 83 4 24 16 123 65 0 321), good := (rows 367 354 36 314 378 34 355 0 256) }] }

theorem u4186 : Upper (D 7) (R 7) [12,96,160,272,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4187 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 164 280 208 34 66 129 257), lower := (rows 13 98 164 280 208 34 66 128 256), losses := [] }

theorem u4187 : Upper (D 7) (R 7) [12,96,160,272,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4188 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 4, region := 456, targets := 33 }], pairs := [(1,7),(3,0),(3,5),(4,7)], upper := (rows 13 98 164 328 19 33 66 144 400), lower := (rows 13 98 164 328 19 33 66 128 256), losses := [] }

theorem u4188 : Upper (D 7) (R 7) [12,96,160,320,3,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4189 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 13 98 164 328 19 33 80 130 386), lower := (rows 13 98 164 328 19 33 80 128 256), losses := [] }

theorem u4189 : Upper (D 7) (R 7) [12,96,160,320,3,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4189 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4190 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 456, targets := 33 },{ cop := 2, region := 66, targets := 1 },{ cop := 4, region := 164, targets := 64 }], pairs := [(1,0),(2,6),(3,0),(3,5)], upper := (rows 13 98 164 328 19 33 192 146 274), lower := (rows 13 98 164 328 19 33 192 128 256), losses := [] }

theorem u4190 : Upper (D 7) (R 7) [12,96,160,320,3,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4191 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 164 328 146 33 65 146 274), lower := (rows 13 98 164 328 146 33 65 128 256), losses := [] }

theorem u4191 : Upper (D 7) (R 7) [12,96,160,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4192 : Route 9 := (fun mask => (mask,id))

def c4192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4192 : Upper (D 7) (R 7) [12,96,160,320,130,1,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,320,130,1,2] 13 (by decide) (choices 1) [1,16] r4192 c4192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u330
  · exact u331

def r4193 : Route 9 := (fun mask => (mask,id))

def c4193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4193 : Upper (D 7) (R 7) [12,96,160,320,130,1,16] 13 := by
  apply FastRouting.sound _ _ [12,96,160,320,130,1,16] 13 (by decide) (choices 1) [1,2] r4193 c4193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u332
  · exact u333

def b4194 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 98 164 392 81 34 65 146 274), lower := (rows 13 98 164 392 81 34 65 128 256), losses := [] }

theorem u4194 : Upper (D 7) (R 7) [12,96,160,384,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4195 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 164 392 81 34 66 145 273), lower := (rows 13 98 164 392 81 34 66 128 256), losses := [] }

theorem u4195 : Upper (D 7) (R 7) [12,96,160,384,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4196 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 392 81 34 80 131 259), lower := (rows 13 98 164 392 81 34 80 128 256), losses := [] }

theorem u4196 : Upper (D 7) (R 7) [12,96,160,384,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4196 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4197 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 232, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 13 259 21 42 82 160 96 192 448), lower := (rows 13 259 21 42 82 160 96 128 256), losses := [] }

theorem u4197 : Upper (D 7) (R 7) [12,257,17,34,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4198 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 13 259 21 42 82 160 192 224 352), lower := (rows 13 259 21 42 82 160 192 128 256), losses := [{ target := 5, region := (rows 9 2 13 8 24 0 224 128 256), good := (rows 29 263 21 95 82 192 192 192 256) }] }

theorem u4198 : Upper (D 7) (R 7) [12,257,17,34,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4199 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 232, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 13 259 21 42 112 160 66 192 448), lower := (rows 13 259 21 42 112 160 66 128 256), losses := [] }

theorem u4199 : Upper (D 7) (R 7) [12,257,17,34,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4199
end Delivery.IrregularNine14.P07
