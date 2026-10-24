import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0086
import IrregularNine14P07C0087

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19080 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 152 274 33 193 193 449), lower := (rows 35 70 44 152 274 33 64 128 256), losses := [] }

theorem u19080 : Upper (D 7) (R 7) [34,68,40,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19081 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 152 274 96 193 129 385), lower := (rows 35 70 44 152 274 96 64 128 256), losses := [] }

theorem u19081 : Upper (D 7) (R 7) [34,68,40,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19082 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 44 152 274 160 65 193 321), lower := (rows 35 70 44 152 274 160 64 128 256), losses := [] }

theorem u19082 : Upper (D 7) (R 7) [34,68,40,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19083 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 152 336 33 195 131 387), lower := (rows 35 70 44 152 336 33 64 128 256), losses := [] }

theorem u19083 : Upper (D 7) (R 7) [34,68,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19084 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 152 336 34 193 129 385), lower := (rows 35 70 44 152 336 34 64 128 256), losses := [] }

theorem u19084 : Upper (D 7) (R 7) [34,68,40,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19085 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 44 152 336 160 67 131 259), lower := (rows 35 70 44 152 336 160 64 128 256), losses := [] }

theorem u19085 : Upper (D 7) (R 7) [34,68,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19086 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 265 81 34 208 144 400), lower := (rows 35 70 44 265 81 34 64 128 256), losses := [] }

theorem u19086 : Upper (D 7) (R 7) [34,68,40,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19087 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 265 81 48 194 130 386), lower := (rows 35 70 44 265 81 48 64 128 256), losses := [] }

theorem u19087 : Upper (D 7) (R 7) [34,68,40,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19087 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19088 : Route 9 := (fun mask => (mask,id))

def c19088 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19088 : Upper (D 7) (R 7) [34,68,40,257,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,65,128] 13 (by decide) (choices 1) [2,16,128] r19088 c19088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5218
  · exact u5219
  · exact u5220

def b19089 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 265 145 34 208 208 464), lower := (rows 35 70 44 265 145 34 64 128 256), losses := [] }

theorem u19089 : Upper (D 7) (R 7) [34,68,40,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19090 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 70 44 265 145 48 194 194 450), lower := (rows 35 70 44 265 145 48 64 128 256), losses := [] }

theorem u19090 : Upper (D 7) (R 7) [34,68,40,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19090 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19091 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 265 145 96 210 146 402), lower := (rows 35 70 44 265 145 96 64 128 256), losses := [] }

theorem u19091 : Upper (D 7) (R 7) [34,68,40,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19092 : Route 9 := (fun mask => (mask,id))

def c19092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19092 : Upper (D 7) (R 7) [34,68,40,257,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,129,128] 13 (by decide) (choices 1) [2,16] r19092 c19092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5221
  · exact u5222

def b19093 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 265 146 33 208 208 464), lower := (rows 35 70 44 265 146 33 64 128 256), losses := [] }

theorem u19093 : Upper (D 7) (R 7) [34,68,40,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19094 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 70 44 265 146 48 193 193 449), lower := (rows 35 70 44 265 146 48 64 128 256), losses := [] }

theorem u19094 : Upper (D 7) (R 7) [34,68,40,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19094 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19095 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 265 146 96 209 145 401), lower := (rows 35 70 44 265 146 96 64 128 256), losses := [] }

theorem u19095 : Upper (D 7) (R 7) [34,68,40,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19096 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(3,5),(4,5)], upper := (rows 35 70 44 265 146 160 81 209 337), lower := (rows 35 70 44 265 146 160 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 21 0 73 137 265), good := (rows 475 86 478 473 146 128 64 128 256) }] }

theorem u19096 : Upper (D 7) (R 7) [34,68,40,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19097 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 265 208 33 210 146 402), lower := (rows 35 70 44 265 208 33 64 128 256), losses := [] }

theorem u19097 : Upper (D 7) (R 7) [34,68,40,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19098 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 265 208 34 209 145 401), lower := (rows 35 70 44 265 208 34 64 128 256), losses := [] }

theorem u19098 : Upper (D 7) (R 7) [34,68,40,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19099 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 265 208 48 195 131 387), lower := (rows 35 70 44 265 208 48 64 128 256), losses := [] }

theorem u19099 : Upper (D 7) (R 7) [34,68,40,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19099 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19100 : Route 9 := (fun mask => (mask,id))

def c19100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19100 : Upper (D 7) (R 7) [34,68,40,257,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,192,128] 13 (by decide) (choices 1) [1,2,16] r19100 c19100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5223
  · exact u5224
  · exact u5225

def b19101 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 266 81 33 208 144 400), lower := (rows 35 70 44 266 81 33 64 128 256), losses := [] }

theorem u19101 : Upper (D 7) (R 7) [34,68,40,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19102 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 266 81 48 193 129 385), lower := (rows 35 70 44 266 81 48 64 128 256), losses := [] }

theorem u19102 : Upper (D 7) (R 7) [34,68,40,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19102 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19103 : Route 9 := (fun mask => (mask,id))

def c19103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19103 : Upper (D 7) (R 7) [34,68,40,258,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,258,65,128] 13 (by decide) (choices 1) [1,16,128] r19103 c19103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5226
  · exact u5227
  · exact u5228

def b19104 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 266 145 33 208 208 464), lower := (rows 35 70 44 266 145 33 64 128 256), losses := [] }

theorem u19104 : Upper (D 7) (R 7) [34,68,40,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19105 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 35 70 44 266 145 48 193 193 449), lower := (rows 35 70 44 266 145 48 64 128 256), losses := [] }

theorem u19105 : Upper (D 7) (R 7) [34,68,40,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19105 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19106 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 266 145 96 209 145 401), lower := (rows 35 70 44 266 145 96 64 128 256), losses := [] }

theorem u19106 : Upper (D 7) (R 7) [34,68,40,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19107 : Route 9 := (fun mask => (mask,id))

def c19107 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19107 : Upper (D 7) (R 7) [34,68,40,258,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,258,129,128] 13 (by decide) (choices 1) [1,16] r19107 c19107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5229
  · exact u5230

def b19108 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 266 208 33 209 145 401), lower := (rows 35 70 44 266 208 33 64 128 256), losses := [] }

theorem u19108 : Upper (D 7) (R 7) [34,68,40,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19109 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 266 208 48 193 129 385), lower := (rows 35 70 44 266 208 48 64 128 256), losses := [] }

theorem u19109 : Upper (D 7) (R 7) [34,68,40,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19109 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19110 : Route 9 := (fun mask => (mask,id))

def c19110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19110 : Upper (D 7) (R 7) [34,68,40,258,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,258,192,128] 13 (by decide) (choices 1) [1,16] r19110 c19110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5231
  · exact u5232

def b19111 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 280 145 33 194 194 450), lower := (rows 35 70 44 280 145 33 64 128 256), losses := [] }

theorem u19111 : Upper (D 7) (R 7) [34,68,40,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19112 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 280 145 34 193 193 449), lower := (rows 35 70 44 280 145 34 64 128 256), losses := [] }

theorem u19112 : Upper (D 7) (R 7) [34,68,40,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19113 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 280 145 96 195 131 387), lower := (rows 35 70 44 280 145 96 64 128 256), losses := [] }

theorem u19113 : Upper (D 7) (R 7) [34,68,40,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19114 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 280 145 160 67 195 323), lower := (rows 35 70 44 280 145 160 64 128 256), losses := [] }

theorem u19114 : Upper (D 7) (R 7) [34,68,40,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19115 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 280 146 33 193 193 449), lower := (rows 35 70 44 280 146 33 64 128 256), losses := [] }

theorem u19115 : Upper (D 7) (R 7) [34,68,40,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19116 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 280 146 96 193 129 385), lower := (rows 35 70 44 280 146 96 64 128 256), losses := [] }

theorem u19116 : Upper (D 7) (R 7) [34,68,40,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19117 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 280 146 160 65 193 321), lower := (rows 35 70 44 280 146 160 64 128 256), losses := [] }

theorem u19117 : Upper (D 7) (R 7) [34,68,40,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19118 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 280 208 33 195 131 387), lower := (rows 35 70 44 280 208 33 64 128 256), losses := [] }

theorem u19118 : Upper (D 7) (R 7) [34,68,40,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19119 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 280 208 34 193 129 385), lower := (rows 35 70 44 280 208 34 64 128 256), losses := [] }

theorem u19119 : Upper (D 7) (R 7) [34,68,40,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19120 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 280 208 160 67 131 259), lower := (rows 35 70 44 280 208 160 64 128 256), losses := [] }

theorem u19120 : Upper (D 7) (R 7) [34,68,40,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19121 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 35 70 44 392 81 33 210 146 402), lower := (rows 35 70 44 392 81 33 64 128 256), losses := [] }

theorem u19121 : Upper (D 7) (R 7) [34,68,40,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19122 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 392 81 34 209 145 401), lower := (rows 35 70 44 392 81 34 64 128 256), losses := [] }

theorem u19122 : Upper (D 7) (R 7) [34,68,40,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19123 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 392 81 48 195 131 387), lower := (rows 35 70 44 392 81 48 64 128 256), losses := [] }

theorem u19123 : Upper (D 7) (R 7) [34,68,40,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19123 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19124 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 83, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 44 392 81 160 83 147 275), lower := (rows 35 70 44 392 81 160 64 128 256), losses := [] }

theorem u19124 : Upper (D 7) (R 7) [34,68,40,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19125 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 392 145 33 82 210 338), lower := (rows 35 70 44 392 145 33 64 128 256), losses := [] }

theorem u19125 : Upper (D 7) (R 7) [34,68,40,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19126 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 392 145 34 81 209 337), lower := (rows 35 70 44 392 145 34 64 128 256), losses := [] }

theorem u19126 : Upper (D 7) (R 7) [34,68,40,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19127 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 44 392 145 48 67 195 323), lower := (rows 35 70 44 392 145 48 64 128 256), losses := [] }

theorem u19127 : Upper (D 7) (R 7) [34,68,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19127 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19128 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 392 145 96 83 147 275), lower := (rows 35 70 44 392 145 96 64 128 256), losses := [] }

theorem u19128 : Upper (D 7) (R 7) [34,68,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19129 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 392 146 33 81 209 337), lower := (rows 35 70 44 392 146 33 64 128 256), losses := [] }

theorem u19129 : Upper (D 7) (R 7) [34,68,40,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19130 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 70 44 392 146 48 65 193 321), lower := (rows 35 70 44 392 146 48 64 128 256), losses := [] }

theorem u19130 : Upper (D 7) (R 7) [34,68,40,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19130 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19131 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 392 146 96 81 145 273), lower := (rows 35 70 44 392 146 96 64 128 256), losses := [] }

theorem u19131 : Upper (D 7) (R 7) [34,68,40,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19132 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 392 208 33 83 147 275), lower := (rows 35 70 44 392 208 33 64 128 256), losses := [] }

theorem u19132 : Upper (D 7) (R 7) [34,68,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19133 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 392 208 34 81 145 273), lower := (rows 35 70 44 392 208 34 64 128 256), losses := [] }

theorem u19133 : Upper (D 7) (R 7) [34,68,40,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19134 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 392 208 48 67 131 259), lower := (rows 35 70 44 392 208 48 64 128 256), losses := [] }

theorem u19134 : Upper (D 7) (R 7) [34,68,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19134 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19135 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 112 34 456 392 392), lower := (rows 35 70 133 25 112 34 64 128 256), losses := [] }

theorem u19135 : Upper (D 7) (R 7) [34,68,129,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19136 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 133 25 112 40 450 386 386), lower := (rows 35 70 133 25 112 40 64 128 256), losses := [] }

theorem u19136 : Upper (D 7) (R 7) [34,68,129,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19136 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19137 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 133 25 112 160 330 394 266), lower := (rows 35 70 133 25 112 160 64 128 256), losses := [] }

theorem u19137 : Upper (D 7) (R 7) [34,68,129,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19138 : Route 9 := (fun mask => (mask,id))

def c19138 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19138 : Upper (D 7) (R 7) [34,68,129,17,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,96,256] 13 (by decide) (choices 1) [2,8,128] r19138 c19138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5233
  · exact u5234
  · exact u5235

def b19139 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 133 25 146 40 352 480 352), lower := (rows 35 70 133 25 146 40 64 128 256), losses := [] }

theorem u19139 : Upper (D 7) (R 7) [34,68,129,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19139 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19139
end Delivery.IrregularNine14.P07
