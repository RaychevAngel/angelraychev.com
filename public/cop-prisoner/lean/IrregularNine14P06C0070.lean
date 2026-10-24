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

def b4200 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 292 25 84 34 96 193 321), lower := (rows 11 134 292 25 84 34 96 128 256), losses := [] }

theorem u4200 : Upper (D 6) (R 6) [10,132,288,17,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4201 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 25 84 96 65 162 290), lower := (rows 11 134 292 25 84 96 65 128 256), losses := [] }

theorem u4201 : Upper (D 6) (R 6) [10,132,288,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4202 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 25 84 96 66 161 289), lower := (rows 11 134 292 25 84 96 66 128 256), losses := [] }

theorem u4202 : Upper (D 6) (R 6) [10,132,288,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4203 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 292 25 84 96 96 131 259), lower := (rows 11 134 292 25 84 96 96 128 256), losses := [] }

theorem u4203 : Upper (D 6) (R 6) [10,132,288,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4204 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 292 25 112 34 65 196 324), lower := (rows 11 134 292 25 112 34 65 128 256), losses := [] }

theorem u4204 : Upper (D 6) (R 6) [10,132,288,17,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4205 : Route 9 := (fun mask => (mask,id))

def c4205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4205 : Upper (D 6) (R 6) [10,132,288,17,96,2,4] 13 := by
  apply FastRouting.sound _ _ [10,132,288,17,96,2,4] 13 (by decide) (choices 1) [1,64] r4205 c4205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u316
  · exact u317

def b4206 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 28 81 34 65 224 352), lower := (rows 11 134 292 28 81 34 65 128 256), losses := [] }

theorem u4206 : Upper (D 6) (R 6) [10,132,288,20,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4207 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 292 28 81 34 96 193 321), lower := (rows 11 134 292 28 81 34 96 128 256), losses := [{ target := 5, region := (rows 9 10 4 8 16 0 64 144 272), good := (rows 11 134 260 415 465 2 64 128 256) }] }

theorem u4207 : Upper (D 6) (R 6) [10,132,288,20,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4208 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 292 28 81 96 65 162 290), lower := (rows 11 134 292 28 81 96 65 128 256), losses := [] }

theorem u4208 : Upper (D 6) (R 6) [10,132,288,20,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4209 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 28 81 96 66 161 289), lower := (rows 11 134 292 28 81 96 66 128 256), losses := [] }

theorem u4209 : Upper (D 6) (R 6) [10,132,288,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4210 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 292 28 81 96 96 131 259), lower := (rows 11 134 292 28 81 96 96 128 256), losses := [] }

theorem u4210 : Upper (D 6) (R 6) [10,132,288,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4211 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 28 82 33 65 224 352), lower := (rows 11 134 292 28 82 33 65 128 256), losses := [] }

theorem u4211 : Upper (D 6) (R 6) [10,132,288,20,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4212 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(3,0),(4,2)], upper := (rows 11 134 292 28 82 33 96 193 321), lower := (rows 11 134 292 28 82 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 32 100 128 256), good := (rows 26 222 356 92 90 96 96 128 256) }] }

theorem u4212 : Upper (D 6) (R 6) [10,132,288,20,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4213 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 28 82 96 65 161 289), lower := (rows 11 134 292 28 82 96 65 128 256), losses := [] }

theorem u4213 : Upper (D 6) (R 6) [10,132,288,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4214 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 292 28 82 96 96 129 257), lower := (rows 11 134 292 28 82 96 96 128 256), losses := [] }

theorem u4214 : Upper (D 6) (R 6) [10,132,288,20,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4215 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 292 41 82 96 65 148 276), lower := (rows 11 134 292 41 82 96 65 128 256), losses := [] }

theorem u4215 : Upper (D 6) (R 6) [10,132,288,33,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4216 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 134 292 41 82 96 68 145 273), lower := (rows 11 134 292 41 82 96 68 128 256), losses := [] }

theorem u4216 : Upper (D 6) (R 6) [10,132,288,33,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4217 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 292 41 82 96 80 133 261), lower := (rows 11 134 292 41 82 96 80 128 256), losses := [] }

theorem u4217 : Upper (D 6) (R 6) [10,132,288,33,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4217 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4218 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 292 41 84 48 65 194 322), lower := (rows 11 134 292 41 84 48 65 128 256), losses := [] }

theorem u4218 : Upper (D 6) (R 6) [10,132,288,33,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4218 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4219 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 11 134 292 41 84 48 66 193 321), lower := (rows 11 134 292 41 84 48 66 128 256), losses := [] }

theorem u4219 : Upper (D 6) (R 6) [10,132,288,33,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4219 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4220 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 292 41 84 96 65 146 274), lower := (rows 11 134 292 41 84 96 65 128 256), losses := [] }

theorem u4220 : Upper (D 6) (R 6) [10,132,288,33,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4221 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 11 134 292 41 84 96 66 145 273), lower := (rows 11 134 292 41 84 96 66 128 256), losses := [] }

theorem u4221 : Upper (D 6) (R 6) [10,132,288,33,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4222 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 292 41 84 96 80 131 259), lower := (rows 11 134 292 41 84 96 80 128 256), losses := [] }

theorem u4222 : Upper (D 6) (R 6) [10,132,288,33,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4222 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4223 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 130, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 134 292 56 84 33 65 194 322), lower := (rows 11 134 292 56 84 33 65 128 256), losses := [{ target := 0, region := (rows 0 26 12 8 16 32 64 144 272), good := (rows 14 134 292 446 470 32 64 128 256) }] }

theorem u4223 : Upper (D 6) (R 6) [10,132,288,48,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4224 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(1,5),(4,0),(4,5)], upper := (rows 11 134 292 56 84 33 66 193 321), lower := (rows 11 134 292 56 84 33 66 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 22 0 87 161 289), good := (rows 475 214 470 472 86 449 82 128 256) }] }

theorem u4224 : Upper (D 6) (R 6) [10,132,288,48,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4225 : Route 9 := (fun mask => (mask,id))

def c4225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4225 : Upper (D 6) (R 6) [10,132,288,48,68,2,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,48,68,2,1] 13 (by decide) (choices 1) [1,64] r4225 c4225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u318
  · exact u319

def b4226 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 73 21 96 66 176 304), lower := (rows 11 134 292 73 21 96 66 128 256), losses := [] }

theorem u4226 : Upper (D 6) (R 6) [10,132,288,65,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4227 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 134 292 73 21 96 80 162 290), lower := (rows 11 134 292 73 21 96 80 128 256), losses := [] }

theorem u4227 : Upper (D 6) (R 6) [10,132,288,65,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4227 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4228 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 292 73 21 96 96 146 274), lower := (rows 11 134 292 73 21 96 96 128 256), losses := [] }

theorem u4228 : Upper (D 6) (R 6) [10,132,288,65,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4229 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 292 73 50 96 65 148 276), lower := (rows 11 134 292 73 50 96 65 128 256), losses := [] }

theorem u4229 : Upper (D 6) (R 6) [10,132,288,65,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4230 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 134 292 73 50 96 68 145 273), lower := (rows 11 134 292 73 50 96 68 128 256), losses := [] }

theorem u4230 : Upper (D 6) (R 6) [10,132,288,65,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4231 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 292 73 50 96 80 133 261), lower := (rows 11 134 292 73 50 96 80 128 256), losses := [] }

theorem u4231 : Upper (D 6) (R 6) [10,132,288,65,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4231 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4232 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 292 73 84 34 65 176 304), lower := (rows 11 134 292 73 84 34 65 128 256), losses := [] }

theorem u4232 : Upper (D 6) (R 6) [10,132,288,65,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4233 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 292 73 84 34 80 161 289), lower := (rows 11 134 292 73 84 34 80 128 256), losses := [] }

theorem u4233 : Upper (D 6) (R 6) [10,132,288,65,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4233 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4234 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 292 73 84 34 96 145 273), lower := (rows 11 134 292 73 84 34 96 128 256), losses := [] }

theorem u4234 : Upper (D 6) (R 6) [10,132,288,65,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4235 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 162, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 134 292 73 84 48 65 162 290), lower := (rows 11 134 292 73 84 48 65 128 256), losses := [] }

theorem u4235 : Upper (D 6) (R 6) [10,132,288,65,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4235 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4236 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 9, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 134 292 73 84 48 66 161 289), lower := (rows 11 134 292 73 84 48 66 128 256), losses := [] }

theorem u4236 : Upper (D 6) (R 6) [10,132,288,65,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4236 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4237 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 134 292 73 84 48 96 131 259), lower := (rows 11 134 292 73 84 48 96 128 256), losses := [] }

theorem u4237 : Upper (D 6) (R 6) [10,132,288,65,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4237 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4238 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 292 73 112 34 65 148 276), lower := (rows 11 134 292 73 112 34 65 128 256), losses := [] }

theorem u4238 : Upper (D 6) (R 6) [10,132,288,65,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4239 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 80, targets := 1 }], pairs := [(0,5),(3,5),(4,0)], upper := (rows 11 134 292 73 112 34 68 145 273), lower := (rows 11 134 292 73 112 34 68 128 256), losses := [] }

theorem u4239 : Upper (D 6) (R 6) [10,132,288,65,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4240 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 292 73 112 34 80 133 261), lower := (rows 11 134 292 73 112 34 80 128 256), losses := [] }

theorem u4240 : Upper (D 6) (R 6) [10,132,288,65,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4240 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4241 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 48, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 134 292 76 50 33 65 208 336), lower := (rows 11 134 292 76 50 33 65 128 256), losses := [] }

theorem u4241 : Upper (D 6) (R 6) [10,132,288,68,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4242 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 292 76 50 33 80 193 321), lower := (rows 11 134 292 76 50 33 80 128 256), losses := [] }

theorem u4242 : Upper (D 6) (R 6) [10,132,288,68,34,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4242 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4243 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 134 292 76 50 96 65 145 273), lower := (rows 11 134 292 76 50 96 65 128 256), losses := [] }

theorem u4243 : Upper (D 6) (R 6) [10,132,288,68,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4244 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 11 134 292 76 50 96 80 129 257), lower := (rows 11 134 292 76 50 96 80 128 256), losses := [] }

theorem u4244 : Upper (D 6) (R 6) [10,132,288,68,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4244 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4245 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 76 82 33 65 176 304), lower := (rows 11 134 292 76 82 33 65 128 256), losses := [] }

theorem u4245 : Upper (D 6) (R 6) [10,132,288,68,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4246 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 292 76 82 33 80 161 289), lower := (rows 11 134 292 76 82 33 80 128 256), losses := [] }

theorem u4246 : Upper (D 6) (R 6) [10,132,288,68,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4246 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4247 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 134 292 76 82 33 96 145 273), lower := (rows 11 134 292 76 82 33 96 128 256), losses := [] }

theorem u4247 : Upper (D 6) (R 6) [10,132,288,68,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4248 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 292 76 82 48 65 161 289), lower := (rows 11 134 292 76 82 48 65 128 256), losses := [] }

theorem u4248 : Upper (D 6) (R 6) [10,132,288,68,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4248 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4249 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 292 76 82 48 96 129 257), lower := (rows 11 134 292 76 82 48 96 128 256), losses := [] }

theorem u4249 : Upper (D 6) (R 6) [10,132,288,68,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4249 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4250 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 292 76 112 33 65 146 274), lower := (rows 11 134 292 76 112 33 65 128 256), losses := [] }

theorem u4250 : Upper (D 6) (R 6) [10,132,288,68,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4251 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 134 292 76 112 33 66 145 273), lower := (rows 11 134 292 76 112 33 66 128 256), losses := [] }

theorem u4251 : Upper (D 6) (R 6) [10,132,288,68,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4252 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 134 292 76 112 33 80 131 259), lower := (rows 11 134 292 76 112 33 80 128 256), losses := [] }

theorem u4252 : Upper (D 6) (R 6) [10,132,288,68,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4252 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4253 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 134 292 76 112 34 65 145 273), lower := (rows 11 134 292 76 112 34 65 128 256), losses := [] }

theorem u4253 : Upper (D 6) (R 6) [10,132,288,68,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4254 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 134 292 76 112 34 80 129 257), lower := (rows 11 134 292 76 112 34 80 128 256), losses := [] }

theorem u4254 : Upper (D 6) (R 6) [10,132,288,68,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4254 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4255 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 88 21 34 65 224 352), lower := (rows 11 134 292 88 21 34 65 128 256), losses := [] }

theorem u4255 : Upper (D 6) (R 6) [10,132,288,80,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4256 : PairBound 9 := { available := 65, camps := [], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 292 88 21 34 96 193 321), lower := (rows 11 134 292 88 21 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 119 128 256), good := (rows 106 230 356 88 124 98 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 32 100 144 272), good := (rows 9 196 356 472 477 96 96 128 256) },{ target := 2, region := (rows 1 2 0 24 16 35 119 145 273), good := (rows 491 226 352 472 505 98 96 128 256) }] }

theorem u4256 : Upper (D 6) (R 6) [10,132,288,80,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4257 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 292 88 21 96 65 162 290), lower := (rows 11 134 292 88 21 96 65 128 256), losses := [] }

theorem u4257 : Upper (D 6) (R 6) [10,132,288,80,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4258 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 292 88 21 96 66 161 289), lower := (rows 11 134 292 88 21 96 66 128 256), losses := [] }

theorem u4258 : Upper (D 6) (R 6) [10,132,288,80,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4259 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 292 88 21 96 96 131 259), lower := (rows 11 134 292 88 21 96 96 128 256), losses := [] }

theorem u4259 : Upper (D 6) (R 6) [10,132,288,80,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4259
end Delivery.IrregularNine14.P06
