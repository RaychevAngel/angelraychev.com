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

def b4080 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 100 25 304 34 65 196 324), lower := (rows 11 134 100 25 304 34 65 128 256), losses := [] }

theorem u4080 : Upper (D 6) (R 6) [10,132,96,17,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4081 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 3 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 134 100 25 304 34 68 193 321), lower := (rows 11 134 100 25 304 34 68 128 256), losses := [] }

theorem u4081 : Upper (D 6) (R 6) [10,132,96,17,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4082 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 100 25 304 36 65 194 322), lower := (rows 11 134 100 25 304 36 65 128 256), losses := [] }

theorem u4082 : Upper (D 6) (R 6) [10,132,96,17,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4083 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 134 100 25 304 36 66 193 321), lower := (rows 11 134 100 25 304 36 66 128 256), losses := [] }

theorem u4083 : Upper (D 6) (R 6) [10,132,96,17,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4084 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 134 100 28 273 33 66 224 352), lower := (rows 11 134 100 28 273 33 66 128 256), losses := [] }

theorem u4084 : Upper (D 6) (R 6) [10,132,96,20,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4085 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 100 28 273 34 96 193 321), lower := (rows 11 134 100 28 273 34 96 128 256), losses := [] }

theorem u4085 : Upper (D 6) (R 6) [10,132,96,20,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4086 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 100 28 274 33 65 224 352), lower := (rows 11 134 100 28 274 33 65 128 256), losses := [] }

theorem u4086 : Upper (D 6) (R 6) [10,132,96,20,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4087 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 100 28 274 33 96 193 321), lower := (rows 11 134 100 28 274 33 96 128 256), losses := [] }

theorem u4087 : Upper (D 6) (R 6) [10,132,96,20,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4088 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 100 41 82 288 65 148 276), lower := (rows 11 134 100 41 82 288 65 128 256), losses := [] }

theorem u4088 : Upper (D 6) (R 6) [10,132,96,33,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4088 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4089 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 134 100 41 82 288 68 145 273), lower := (rows 11 134 100 41 82 288 68 128 256), losses := [] }

theorem u4089 : Upper (D 6) (R 6) [10,132,96,33,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4089 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4090 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 11 134 100 41 82 288 80 133 261), lower := (rows 11 134 100 41 82 288 80 128 256), losses := [] }

theorem u4090 : Upper (D 6) (R 6) [10,132,96,33,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4090 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4091 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 100 41 276 48 65 194 322), lower := (rows 11 134 100 41 276 48 65 128 256), losses := [] }

theorem u4091 : Upper (D 6) (R 6) [10,132,96,33,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4091 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4092 : Route 9 := (fun mask => (mask,id))

def c4092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4092 : Upper (D 6) (R 6) [10,132,96,33,260,16,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,260,16,2] 13 (by decide) (choices 1) [1,64] r4092 c4092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u300
  · exact u301

def b4093 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 100 56 81 288 65 134 262), lower := (rows 11 134 100 56 81 288 65 128 256), losses := [] }

theorem u4093 : Upper (D 6) (R 6) [10,132,96,48,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4093 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4094 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 11 134 100 56 81 288 66 133 261), lower := (rows 11 134 100 56 81 288 66 128 256), losses := [] }

theorem u4094 : Upper (D 6) (R 6) [10,132,96,48,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4094 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4095 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 134 100 56 81 288 68 131 259), lower := (rows 11 134 100 56 81 288 68 128 256), losses := [] }

theorem u4095 : Upper (D 6) (R 6) [10,132,96,48,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4095 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4096 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 11 134 100 56 82 288 65 133 261), lower := (rows 11 134 100 56 82 288 65 128 256), losses := [] }

theorem u4096 : Upper (D 6) (R 6) [10,132,96,48,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4096 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4097 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 134 100 56 82 288 68 129 257), lower := (rows 11 134 100 56 82 288 68 128 256), losses := [] }

theorem u4097 : Upper (D 6) (R 6) [10,132,96,48,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4097 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4098 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 100 56 276 33 65 194 322), lower := (rows 11 134 100 56 276 33 65 128 256), losses := [] }

theorem u4098 : Upper (D 6) (R 6) [10,132,96,48,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4099 : PairBound 9 := { available := 65, camps := [], pairs := [(1,5),(2,0),(4,5)], upper := (rows 11 134 100 56 276 33 66 193 321), lower := (rows 11 134 100 56 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 67 128 256), good := (rows 74 198 100 60 276 100 66 128 256) },{ target := 5, region := (rows 1 6 4 8 20 0 87 161 289), good := (rows 459 214 470 472 342 449 66 128 256) }] }

theorem u4099 : Upper (D 6) (R 6) [10,132,96,48,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4100 : PairBound 9 := { available := 65, camps := [], pairs := [(2,0),(3,1),(4,1)], upper := (rows 11 134 100 56 276 34 65 193 321), lower := (rows 11 134 100 56 276 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 8 16 35 64 128 256), good := (rows 42 166 100 56 276 34 100 128 256) },{ target := 1, region := (rows 1 0 4 12 20 32 65 193 321), good := (rows 457 156 508 56 284 32 449 128 256) }] }

theorem u4100 : Upper (D 6) (R 6) [10,132,96,48,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4101 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 100 56 336 33 65 134 262), lower := (rows 11 134 100 56 336 33 65 128 256), losses := [] }

theorem u4101 : Upper (D 6) (R 6) [10,132,96,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4102 : Route 9 := (fun mask => (mask,id))

def c4102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4102 : Upper (D 6) (R 6) [10,132,96,48,320,1,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,320,1,2] 13 (by decide) (choices 1) [1,4] r4102 c4102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u302
  · exact u303

def b4103 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(4,5)], upper := (rows 11 134 100 56 336 33 68 131 259), lower := (rows 11 134 100 56 336 33 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 70 129 257), good := (rows 475 198 68 24 336 401 68 128 256) }] }

theorem u4103 : Upper (D 6) (R 6) [10,132,96,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4104 : Route 9 := (fun mask => (mask,id))

def c4104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4104 : Upper (D 6) (R 6) [10,132,96,48,320,2,1] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,320,2,1] 13 (by decide) (choices 1) [1,4] r4104 c4104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u304
  · exact u305

def b4105 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 134 100 56 336 34 68 129 257), lower := (rows 11 134 100 56 336 34 68 128 256), losses := [] }

theorem u4105 : Upper (D 6) (R 6) [10,132,96,48,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4106 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 100 268 50 33 65 208 336), lower := (rows 11 134 100 268 50 33 65 128 256), losses := [] }

theorem u4106 : Upper (D 6) (R 6) [10,132,96,260,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4107 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 100 268 50 33 80 193 321), lower := (rows 11 134 100 268 50 33 80 128 256), losses := [] }

theorem u4107 : Upper (D 6) (R 6) [10,132,96,260,34,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4107 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4108 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 100 280 21 33 66 224 352), lower := (rows 11 134 100 280 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 54 36 24 16 32 127 164 292), good := (rows 74 454 486 346 478 486 66 128 256) }] }

theorem u4108 : Upper (D 6) (R 6) [10,132,96,272,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4109 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 100 280 21 34 96 193 321), lower := (rows 11 134 100 280 21 34 96 128 256), losses := [] }

theorem u4109 : Upper (D 6) (R 6) [10,132,96,272,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4110 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 194, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 134 100 296 21 33 66 208 336), lower := (rows 11 134 100 296 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 18 36 8 16 32 83 144 272), good := (rows 74 198 100 300 470 100 66 128 256) }] }

theorem u4110 : Upper (D 6) (R 6) [10,132,96,288,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4111 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 116, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 134 100 296 21 33 80 194 322), lower := (rows 11 134 100 296 21 33 80 128 256), losses := [] }

theorem u4111 : Upper (D 6) (R 6) [10,132,96,288,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4111 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4112 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,2)], upper := (rows 11 134 100 296 21 34 65 208 336), lower := (rows 11 134 100 296 21 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 8 16 35 64 128 256), good := (rows 42 166 100 296 52 34 100 128 256) },{ target := 2, region := (rows 1 2 0 24 16 35 81 144 272), good := (rows 107 162 96 296 505 34 97 128 256) }] }

theorem u4112 : Upper (D 6) (R 6) [10,132,96,288,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4113 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0)], upper := (rows 11 134 100 296 21 34 80 193 321), lower := (rows 11 134 100 296 21 34 80 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 80 128 256), good := (rows 42 166 100 296 116 34 84 128 256) }] }

theorem u4113 : Upper (D 6) (R 6) [10,132,96,288,5,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4113 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4114 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 134 100 296 81 33 66 148 276), lower := (rows 11 134 100 296 81 33 66 128 256), losses := [] }

theorem u4114 : Upper (D 6) (R 6) [10,132,96,288,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4115 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 11 134 100 296 81 33 68 146 274), lower := (rows 11 134 100 296 81 33 68 128 256), losses := [] }

theorem u4115 : Upper (D 6) (R 6) [10,132,96,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4116 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 100 296 81 33 80 134 262), lower := (rows 11 134 100 296 81 33 80 128 256), losses := [] }

theorem u4116 : Upper (D 6) (R 6) [10,132,96,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4116 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4117 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 100 296 81 34 65 148 276), lower := (rows 11 134 100 296 81 34 65 128 256), losses := [] }

theorem u4117 : Upper (D 6) (R 6) [10,132,96,288,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4118 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 134 100 296 81 34 68 145 273), lower := (rows 11 134 100 296 81 34 68 128 256), losses := [] }

theorem u4118 : Upper (D 6) (R 6) [10,132,96,288,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4119 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 100 296 81 34 80 133 261), lower := (rows 11 134 100 296 81 34 80 128 256), losses := [] }

theorem u4119 : Upper (D 6) (R 6) [10,132,96,288,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4119 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4120 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 100 296 82 33 65 148 276), lower := (rows 11 134 100 296 82 33 65 128 256), losses := [] }

theorem u4120 : Upper (D 6) (R 6) [10,132,96,288,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4121 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 296 82 33 68 145 273), lower := (rows 11 134 100 296 82 33 68 128 256), losses := [] }

theorem u4121 : Upper (D 6) (R 6) [10,132,96,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4122 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 100 296 82 33 80 133 261), lower := (rows 11 134 100 296 82 33 80 128 256), losses := [] }

theorem u4122 : Upper (D 6) (R 6) [10,132,96,288,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4122 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4123 : Route 9 := (fun mask => (mask,id))

def c4123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4123 : Upper (D 6) (R 6) [10,132,257,17,36,64,2] 13 := by
  apply FastRouting.sound _ _ [10,132,257,17,36,64,2] 13 (by decide) (choices 1) [32,64] r4123 c4123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u306
  · exact u307

def b4124 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 2, region := 120, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 261 25 52 96 96 194 322), lower := (rows 11 134 261 25 52 96 96 128 256), losses := [] }

theorem u4124 : Upper (D 6) (R 6) [10,132,257,17,36,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4125 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 134 261 25 112 34 68 224 352), lower := (rows 11 134 261 25 112 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 48 32 79 176 304), good := (rows 77 196 325 477 496 496 68 128 256) }] }

theorem u4125 : Upper (D 6) (R 6) [10,132,257,17,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4126 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 261 25 112 34 96 196 324), lower := (rows 11 134 261 25 112 34 96 128 256), losses := [] }

theorem u4126 : Upper (D 6) (R 6) [10,132,257,17,96,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4127 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 261 25 112 36 96 194 322), lower := (rows 11 134 261 25 112 36 96 128 256), losses := [] }

theorem u4127 : Upper (D 6) (R 6) [10,132,257,17,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4128 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(2,1),(4,2)], upper := (rows 11 134 261 28 49 96 66 224 352), lower := (rows 11 134 261 28 49 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 96 64 224 352), good := (rows 9 132 261 28 445 480 480 128 256) }] }

theorem u4128 : Upper (D 6) (R 6) [10,132,257,20,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4129 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 261 28 49 96 96 194 322), lower := (rows 11 134 261 28 49 96 96 128 256), losses := [] }

theorem u4129 : Upper (D 6) (R 6) [10,132,257,20,33,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4130 : Route 9 := (fun mask => (mask,id))

def c4130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4130 : Upper (D 6) (R 6) [10,132,257,20,34,64,1] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20,34,64,1] 13 (by decide) (choices 1) [32,64] r4130 c4130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u308
  · exact u309

def b4131 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 134 261 28 50 96 96 193 321), lower := (rows 11 134 261 28 50 96 96 128 256), losses := [] }

theorem u4131 : Upper (D 6) (R 6) [10,132,257,20,34,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4132 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 134 261 28 112 33 66 224 352), lower := (rows 11 134 261 28 112 33 66 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 48 32 75 176 304), good := (rows 74 198 324 478 496 496 66 128 256) }] }

theorem u4132 : Upper (D 6) (R 6) [10,132,257,20,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4133 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 261 28 112 33 96 194 322), lower := (rows 11 134 261 28 112 33 96 128 256), losses := [] }

theorem u4133 : Upper (D 6) (R 6) [10,132,257,20,96,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4134 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 134 261 28 112 34 96 193 321), lower := (rows 11 134 261 28 112 34 96 128 256), losses := [] }

theorem u4134 : Upper (D 6) (R 6) [10,132,257,20,96,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4135 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 2, region := 242, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 134 261 41 84 96 66 176 304), lower := (rows 11 134 261 41 84 96 66 128 256), losses := [] }

theorem u4135 : Upper (D 6) (R 6) [10,132,257,33,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4136 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 261 41 84 96 80 162 290), lower := (rows 11 134 261 41 84 96 80 128 256), losses := [] }

theorem u4136 : Upper (D 6) (R 6) [10,132,257,33,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4136 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4137 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 261 41 84 96 96 146 274), lower := (rows 11 134 261 41 84 96 96 128 256), losses := [] }

theorem u4137 : Upper (D 6) (R 6) [10,132,257,33,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4138 : Route 9 := (fun mask => (mask,id))

def c4138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4138 : Upper (D 6) (R 6) [10,132,257,36,34,64,1] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,34,64,1] 13 (by decide) (choices 1) [16,64] r4138 c4138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u310
  · exact u311

def b4139 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 11 134 261 44 50 96 80 193 321), lower := (rows 11 134 261 44 50 96 80 128 256), losses := [] }

theorem u4139 : Upper (D 6) (R 6) [10,132,257,36,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4139 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4139
end Delivery.IrregularNine14.P06
