import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0017
import IrregularNine14P09C0018

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4080 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 44 137 400 96 340 404 276), lower := (rows 35 67 44 137 400 96 64 128 256), losses := [] }

theorem u4080 : Upper (D 9) (R 9) [34,65,40,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4080 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4081 : Route 9 := (fun mask => (mask,id))

def c4081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4081 : Upper (D 9) (R 9) [34,65,40,129,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,384,256] 13 (by decide) (choices 1) [4,16] r4081 c4081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1046
  · exact u1047

def b4082 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 4, region := 35, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 140 208 33 336 400 272), lower := (rows 35 67 44 140 208 33 64 128 256), losses := [] }

theorem u4082 : Upper (D 9) (R 9) [34,65,40,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4082 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4083 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 44 140 208 48 321 385 257), lower := (rows 35 67 44 140 208 48 64 128 256), losses := [] }

theorem u4083 : Upper (D 9) (R 9) [34,65,40,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4083 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4084 : Route 9 := (fun mask => (mask,id))

def c4084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4084 : Upper (D 9) (R 9) [34,65,40,132,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,192,256] 13 (by decide) (choices 1) [1,16,256] r4084 c4084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1048
  · exact u1049
  · exact u1050

def b4085 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 35 67 44 140 273 48 448 448 448), lower := (rows 35 67 44 140 273 48 64 128 256), losses := [] }

theorem u4085 : Upper (D 9) (R 9) [34,65,40,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4085 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4086 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 44 140 273 96 464 400 400), lower := (rows 35 67 44 140 273 96 64 128 256), losses := [] }

theorem u4086 : Upper (D 9) (R 9) [34,65,40,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4086 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4087 : PairBound 9 := { available := 336, camps := [{ cop := 5, region := 12, targets := 321 }], pairs := [(2,0),(2,6),(2,8),(3,0),(3,6)], upper := (rows 35 67 44 140 273 160 336 464 336), lower := (rows 35 67 44 140 273 160 64 128 256), losses := [] }

theorem u4087 : Upper (D 9) (R 9) [34,65,40,132,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4087 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4088 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 194, targets := 256 }], pairs := [(1,5),(1,8),(2,0),(3,0),(4,5)], upper := (rows 35 67 44 140 273 288 208 208 464), lower := (rows 35 67 44 140 273 288 64 128 256), losses := [] }

theorem u4088 : Upper (D 9) (R 9) [34,65,40,132,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4088 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4089 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 140 336 33 464 400 400), lower := (rows 35 67 44 140 336 33 64 128 256), losses := [] }

theorem u4089 : Upper (D 9) (R 9) [34,65,40,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4089 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4090 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 140 336 48 449 385 385), lower := (rows 35 67 44 140 336 48 64 128 256), losses := [] }

theorem u4090 : Upper (D 9) (R 9) [34,65,40,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4090 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4091 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 12, targets := 321 }], pairs := [(2,0),(2,6),(2,8),(3,0),(3,6)], upper := (rows 35 67 44 140 336 160 337 401 273), lower := (rows 35 67 44 140 336 160 64 128 256), losses := [] }

theorem u4091 : Upper (D 9) (R 9) [34,65,40,132,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4091 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4092 : Route 9 := (fun mask => (mask,id))

def c4092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4092 : Upper (D 9) (R 9) [34,65,40,132,320,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,320,256] 13 (by decide) (choices 1) [1,16,128] r4092 c4092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1051
  · exact u1052
  · exact u1053

def b4093 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 140 400 33 336 464 336), lower := (rows 35 67 44 140 400 33 64 128 256), losses := [] }

theorem u4093 : Upper (D 9) (R 9) [34,65,40,132,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4093 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4094 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 44, targets := 321 }], pairs := [(2,0),(2,6),(2,8),(3,0)], upper := (rows 35 67 44 140 400 48 321 449 321), lower := (rows 35 67 44 140 400 48 64 128 256), losses := [] }

theorem u4094 : Upper (D 9) (R 9) [34,65,40,132,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4094 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4095 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 44 140 400 96 337 401 273), lower := (rows 35 67 44 140 400 96 64 128 256), losses := [] }

theorem u4095 : Upper (D 9) (R 9) [34,65,40,132,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4095 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4096 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 44, targets := 65 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 44 140 400 288 81 209 337), lower := (rows 35 67 44 140 400 288 64 128 256), losses := [] }

theorem u4096 : Upper (D 9) (R 9) [34,65,40,132,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4096 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4097 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 152 84 33 448 384 384), lower := (rows 35 67 44 152 84 33 64 128 256), losses := [] }

theorem u4097 : Upper (D 9) (R 9) [34,65,40,144,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4097 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4098 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 67 44 152 84 160 321 385 257), lower := (rows 35 67 44 152 84 160 64 128 256), losses := [] }

theorem u4098 : Upper (D 9) (R 9) [34,65,40,144,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4098 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4099 : Route 9 := (fun mask => (mask,id))

def c4099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4099 : Upper (D 9) (R 9) [34,65,40,144,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,68,256] 13 (by decide) (choices 1) [1,128,256] r4099 c4099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1054
  · exact u1055
  · exact u1056

def b4100 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 3, region := 36, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 67 44 152 273 36 448 448 448), lower := (rows 35 67 44 152 273 36 64 128 256), losses := [] }

theorem u4100 : Upper (D 9) (R 9) [34,65,40,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4100 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4101 : PairBound 9 := { available := 388, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 44 152 273 96 452 388 388), lower := (rows 35 67 44 152 273 96 64 128 256), losses := [] }

theorem u4101 : Upper (D 9) (R 9) [34,65,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4101 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4102 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 320 }], pairs := [(0,7),(1,7),(2,6),(2,8),(4,7)], upper := (rows 35 67 44 152 273 160 324 452 324), lower := (rows 35 67 44 152 273 160 64 128 256), losses := [] }

theorem u4102 : Upper (D 9) (R 9) [34,65,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4102 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4103 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 195, targets := 256 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,0)], upper := (rows 35 67 44 152 273 288 196 196 452), lower := (rows 35 67 44 152 273 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 304 0 128 256), good := (rows 35 3 44 188 305 288 0 128 288) }] }

theorem u4103 : Upper (D 9) (R 9) [34,65,40,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4103 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4104 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 152 276 33 448 448 448), lower := (rows 35 67 44 152 276 33 64 128 256), losses := [] }

theorem u4104 : Upper (D 9) (R 9) [34,65,40,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4104 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4105 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 44 152 276 96 449 385 385), lower := (rows 35 67 44 152 276 96 64 128 256), losses := [] }

theorem u4105 : Upper (D 9) (R 9) [34,65,40,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4105 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4106 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 67 44 152 276 160 321 449 321), lower := (rows 35 67 44 152 276 160 64 128 256), losses := [] }

theorem u4106 : Upper (D 9) (R 9) [34,65,40,144,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4106 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4107 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 195, targets := 256 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,0),(2,6)], upper := (rows 35 67 44 152 276 288 193 193 449), lower := (rows 35 67 44 152 276 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 34 66 44 188 308 288 64 128 288) },{ target := 6, region := (rows 1 2 12 8 16 304 0 128 256), good := (rows 35 3 44 188 308 288 0 128 288) }] }

theorem u4107 : Upper (D 9) (R 9) [34,65,40,144,260,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4107 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4108 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 152 336 33 452 388 388), lower := (rows 35 67 44 152 336 33 64 128 256), losses := [] }

theorem u4108 : Upper (D 9) (R 9) [34,65,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4108 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4109 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 67 44 152 336 36 449 385 385), lower := (rows 35 67 44 152 336 36 64 128 256), losses := [] }

theorem u4109 : Upper (D 9) (R 9) [34,65,40,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4109 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4110 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 67 44 152 336 160 325 389 261), lower := (rows 35 67 44 152 336 160 64 128 256), losses := [] }

theorem u4110 : Upper (D 9) (R 9) [34,65,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4110 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4111 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 195, targets := 256 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 44 152 336 288 197 133 389), lower := (rows 35 67 44 152 336 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 34 66 44 188 368 288 64 128 288) }] }

theorem u4111 : Upper (D 9) (R 9) [34,65,40,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4111 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4112 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 44 200 145 36 336 400 272), lower := (rows 35 67 44 200 145 36 64 128 256), losses := [] }

theorem u4112 : Upper (D 9) (R 9) [34,65,40,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4112 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4113 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 44 200 145 48 324 388 260), lower := (rows 35 67 44 200 145 48 64 128 256), losses := [] }

theorem u4113 : Upper (D 9) (R 9) [34,65,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4113 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4114 : Route 9 := (fun mask => (mask,id))

def c4114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4114 : Upper (D 9) (R 9) [34,65,40,192,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,129,256] 13 (by decide) (choices 1) [4,16,256] r4114 c4114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1057
  · exact u1058
  · exact u1059

def b4115 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 3, region := 35, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 200 148 33 336 400 272), lower := (rows 35 67 44 200 148 33 64 128 256), losses := [] }

theorem u4115 : Upper (D 9) (R 9) [34,65,40,192,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4115 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4116 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 67 44 200 148 48 321 385 257), lower := (rows 35 67 44 200 148 48 64 128 256), losses := [] }

theorem u4116 : Upper (D 9) (R 9) [34,65,40,192,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4116 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4117 : Route 9 := (fun mask => (mask,id))

def c4117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4117 : Upper (D 9) (R 9) [34,65,40,192,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,132,256] 13 (by decide) (choices 1) [1,16,256] r4117 c4117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1060
  · exact u1061
  · exact u1062

def b4118 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 200 273 36 464 400 400), lower := (rows 35 67 44 200 273 36 64 128 256), losses := [] }

theorem u4118 : Upper (D 9) (R 9) [34,65,40,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4118 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4119 : Route 9 := (fun mask => (mask,id))

def c4119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4119 : Upper (D 9) (R 9) [34,65,40,192,257,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,257,16] 13 (by decide) (choices 1) [4,128,256] r4119 c4119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1063
  · exact u1064
  · exact u1065

def b4120 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 35, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 67 44 200 273 160 340 404 276), lower := (rows 35 67 44 200 273 160 64 128 256), losses := [] }

theorem u4120 : Upper (D 9) (R 9) [34,65,40,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4120 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4121 : Route 9 := (fun mask => (mask,id))

def c4121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4121 : Upper (D 9) (R 9) [34,65,40,192,257,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,257,256] 13 (by decide) (choices 1) [4,16,128] r4121 c4121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1066
  · exact u1067
  · exact u1068

def b4122 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 44 200 276 33 464 400 400), lower := (rows 35 67 44 200 276 33 64 128 256), losses := [] }

theorem u4122 : Upper (D 9) (R 9) [34,65,40,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4122 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4123 : Route 9 := (fun mask => (mask,id))

def c4123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4123 : Upper (D 9) (R 9) [34,65,40,192,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260,16] 13 (by decide) (choices 1) [1,128,256] r4123 c4123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1069
  · exact u1070
  · exact u1071

def b4124 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 35, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 67 44 200 276 160 337 401 273), lower := (rows 35 67 44 200 276 160 64 128 256), losses := [] }

theorem u4124 : Upper (D 9) (R 9) [34,65,40,192,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4124 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4125 : Route 9 := (fun mask => (mask,id))

def c4125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4125 : Upper (D 9) (R 9) [34,65,40,192,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260,256] 13 (by decide) (choices 1) [1,16,128] r4125 c4125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1072
  · exact u1073
  · exact u1074

def b4126 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 44 200 400 33 340 404 276), lower := (rows 35 67 44 200 400 33 64 128 256), losses := [] }

theorem u4126 : Upper (D 9) (R 9) [34,65,40,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4126 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4127 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 200 400 36 337 401 273), lower := (rows 35 67 44 200 400 36 64 128 256), losses := [] }

theorem u4127 : Upper (D 9) (R 9) [34,65,40,192,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4127 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4128 : Route 9 := (fun mask => (mask,id))

def c4128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4128 : Upper (D 9) (R 9) [34,65,40,192,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,384,16] 13 (by decide) (choices 1) [1,4,256] r4128 c4128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1075
  · exact u1076
  · exact u1077

def r4129 : Route 9 := (fun mask => (mask,id))

def c4129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4129 : Upper (D 9) (R 9) [34,65,40,192,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,384,256] 13 (by decide) (choices 1) [1,4,16] r4129 c4129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1078
  · exact u1079
  · exact u1080

def b4130 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 392 84 33 464 400 400), lower := (rows 35 67 44 392 84 33 64 128 256), losses := [] }

theorem u4130 : Upper (D 9) (R 9) [34,65,40,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4130 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4131 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 392 84 48 449 385 385), lower := (rows 35 67 44 392 84 48 64 128 256), losses := [] }

theorem u4131 : Upper (D 9) (R 9) [34,65,40,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4131 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4132 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 35 67 44 392 84 160 337 401 273), lower := (rows 35 67 44 392 84 160 64 128 256), losses := [] }

theorem u4132 : Upper (D 9) (R 9) [34,65,40,384,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4132 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4133 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 67 44 392 145 36 336 464 336), lower := (rows 35 67 44 392 145 36 64 128 256), losses := [] }

theorem u4133 : Upper (D 9) (R 9) [34,65,40,384,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4133 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4134 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 35 67 44 392 145 48 324 452 324), lower := (rows 35 67 44 392 145 48 64 128 256), losses := [] }

theorem u4134 : Upper (D 9) (R 9) [34,65,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4134 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4135 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 44 392 145 96 340 404 276), lower := (rows 35 67 44 392 145 96 64 128 256), losses := [] }

theorem u4135 : Upper (D 9) (R 9) [34,65,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4135 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4136 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 67 44 392 145 288 84 212 340), lower := (rows 35 67 44 392 145 288 64 128 256), losses := [] }

theorem u4136 : Upper (D 9) (R 9) [34,65,40,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4136 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4137 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 392 148 33 336 464 336), lower := (rows 35 67 44 392 148 33 64 128 256), losses := [] }

theorem u4137 : Upper (D 9) (R 9) [34,65,40,384,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4137 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4138 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 52, targets := 321 }], pairs := [(2,0),(2,6),(2,8),(4,0)], upper := (rows 35 67 44 392 148 48 321 449 321), lower := (rows 35 67 44 392 148 48 64 128 256), losses := [] }

theorem u4138 : Upper (D 9) (R 9) [34,65,40,384,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4138 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4139 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 44 392 148 96 337 401 273), lower := (rows 35 67 44 392 148 96 64 128 256), losses := [] }

theorem u4139 : Upper (D 9) (R 9) [34,65,40,384,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4139 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4139
end Delivery.IrregularNine14.P09
