import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0131

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24060 : Route 9 := (fun mask => (mask,id))

def c24060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24060 : Upper (D 7) (R 7) [36,96,129,192,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,129,192,258,16] 13 (by decide) (choices 1) [1,2,8] r24060 c24060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7868
  · exact u7869
  · exact u7870

def b24061 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 200 280 33 82 146 274), lower := (rows 37 98 133 200 280 33 64 128 256), losses := [] }

theorem u24061 : Upper (D 7) (R 7) [36,96,129,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24062 : Route 9 := (fun mask => (mask,id))

def c24062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24062 : Upper (D 7) (R 7) [36,96,129,192,264,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,192,264,2] 13 (by decide) (choices 1) [1,2,16] r24062 c24062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7871
  · exact u7872
  · exact u7873

def b24063 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 98 133 200 280 48 67 131 259), lower := (rows 37 98 133 200 280 48 64 128 256), losses := [] }

theorem u24063 : Upper (D 7) (R 7) [36,96,129,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24063 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24064 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 134 11 81 40 464 400 400), lower := (rows 37 98 134 11 81 40 64 128 256), losses := [] }

theorem u24064 : Upper (D 7) (R 7) [36,96,130,3,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24064 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24065 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 134 11 81 48 456 392 392), lower := (rows 37 98 134 11 81 48 64 128 256), losses := [] }

theorem u24065 : Upper (D 7) (R 7) [36,96,130,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24065 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24066 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 11 81 160 344 408 280), lower := (rows 37 98 134 11 81 160 64 128 256), losses := [] }

theorem u24066 : Upper (D 7) (R 7) [36,96,130,3,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24067 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 208, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 98 134 11 81 288 216 152 408), lower := (rows 37 98 134 11 81 288 64 128 256), losses := [] }

theorem u24067 : Upper (D 7) (R 7) [36,96,130,3,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24067 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24068 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 134 11 88 33 464 400 400), lower := (rows 37 98 134 11 88 33 64 128 256), losses := [] }

theorem u24068 : Upper (D 7) (R 7) [36,96,130,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24069 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 134 11 88 48 449 385 385), lower := (rows 37 98 134 11 88 48 64 128 256), losses := [] }

theorem u24069 : Upper (D 7) (R 7) [36,96,130,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24069 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24070 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 11 88 160 337 401 273), lower := (rows 37 98 134 11 88 160 64 128 256), losses := [] }

theorem u24070 : Upper (D 7) (R 7) [36,96,130,3,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24071 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 208, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 98 134 11 88 288 209 145 401), lower := (rows 37 98 134 11 88 288 64 128 256), losses := [] }

theorem u24071 : Upper (D 7) (R 7) [36,96,130,3,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24071 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24072 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 134 11 152 33 336 464 336), lower := (rows 37 98 134 11 152 33 64 128 256), losses := [] }

theorem u24072 : Upper (D 7) (R 7) [36,96,130,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24073 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 98 134 11 152 48 321 449 321), lower := (rows 37 98 134 11 152 48 64 128 256), losses := [] }

theorem u24073 : Upper (D 7) (R 7) [36,96,130,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24073 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24074 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 11 152 96 337 401 273), lower := (rows 37 98 134 11 152 96 64 128 256), losses := [] }

theorem u24074 : Upper (D 7) (R 7) [36,96,130,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24075 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 208, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 98 134 11 152 288 81 209 337), lower := (rows 37 98 134 11 152 288 64 128 256), losses := [] }

theorem u24075 : Upper (D 7) (R 7) [36,96,130,3,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24075 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24076 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 134 11 208 33 344 408 280), lower := (rows 37 98 134 11 208 33 64 128 256), losses := [] }

theorem u24076 : Upper (D 7) (R 7) [36,96,130,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24077 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 134 11 208 40 337 401 273), lower := (rows 37 98 134 11 208 40 64 128 256), losses := [] }

theorem u24077 : Upper (D 7) (R 7) [36,96,130,3,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24077 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24078 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 134 11 208 48 329 393 265), lower := (rows 37 98 134 11 208 48 64 128 256), losses := [] }

theorem u24078 : Upper (D 7) (R 7) [36,96,130,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24078 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24079 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 208, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 98 134 11 208 288 89 153 281), lower := (rows 37 98 134 11 208 288 64 128 256), losses := [] }

theorem u24079 : Upper (D 7) (R 7) [36,96,130,3,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24079 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24080 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 134 11 273 40 208 208 464), lower := (rows 37 98 134 11 273 40 64 128 256), losses := [] }

theorem u24080 : Upper (D 7) (R 7) [36,96,130,3,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24080 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24081 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 37 98 134 11 273 48 200 200 456), lower := (rows 37 98 134 11 273 48 64 128 256), losses := [] }

theorem u24081 : Upper (D 7) (R 7) [36,96,130,3,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24081 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24082 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 11 273 96 216 152 408), lower := (rows 37 98 134 11 273 96 64 128 256), losses := [] }

theorem u24082 : Upper (D 7) (R 7) [36,96,130,3,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24083 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 11 273 160 88 216 344), lower := (rows 37 98 134 11 273 160 64 128 256), losses := [] }

theorem u24083 : Upper (D 7) (R 7) [36,96,130,3,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24084 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 134 11 280 33 208 208 464), lower := (rows 37 98 134 11 280 33 64 128 256), losses := [] }

theorem u24084 : Upper (D 7) (R 7) [36,96,130,3,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24085 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 464, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 98 134 11 280 48 193 193 449), lower := (rows 37 98 134 11 280 48 64 128 256), losses := [] }

theorem u24085 : Upper (D 7) (R 7) [36,96,130,3,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24085 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24086 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 11 280 96 209 145 401), lower := (rows 37 98 134 11 280 96 64 128 256), losses := [] }

theorem u24086 : Upper (D 7) (R 7) [36,96,130,3,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24087 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 11 280 160 81 209 337), lower := (rows 37 98 134 11 280 160 64 128 256), losses := [] }

theorem u24087 : Upper (D 7) (R 7) [36,96,130,3,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24088 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 134 11 336 33 216 152 408), lower := (rows 37 98 134 11 336 33 64 128 256), losses := [] }

theorem u24088 : Upper (D 7) (R 7) [36,96,130,3,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24089 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 134 11 336 40 209 145 401), lower := (rows 37 98 134 11 336 40 64 128 256), losses := [] }

theorem u24089 : Upper (D 7) (R 7) [36,96,130,3,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24089 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24090 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 134 11 336 48 201 137 393), lower := (rows 37 98 134 11 336 48 64 128 256), losses := [] }

theorem u24090 : Upper (D 7) (R 7) [36,96,130,3,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24090 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24091 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 11 336 160 89 153 281), lower := (rows 37 98 134 11 336 160 64 128 256), losses := [] }

theorem u24091 : Upper (D 7) (R 7) [36,96,130,3,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24092 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 134 11 400 33 88 216 344), lower := (rows 37 98 134 11 400 33 64 128 256), losses := [] }

theorem u24092 : Upper (D 7) (R 7) [36,96,130,3,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24093 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 134 11 400 40 81 209 337), lower := (rows 37 98 134 11 400 40 64 128 256), losses := [] }

theorem u24093 : Upper (D 7) (R 7) [36,96,130,3,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24093 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24094 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 134 11 400 48 73 201 329), lower := (rows 37 98 134 11 400 48 64 128 256), losses := [] }

theorem u24094 : Upper (D 7) (R 7) [36,96,130,3,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24094 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24095 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 11 400 96 89 153 281), lower := (rows 37 98 134 11 400 96 64 128 256), losses := [] }

theorem u24095 : Upper (D 7) (R 7) [36,96,130,3,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24096 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 134 25 26 33 448 448 448), lower := (rows 37 98 134 25 26 33 64 128 256), losses := [] }

theorem u24096 : Upper (D 7) (R 7) [36,96,130,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24097 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 25 26 96 449 385 385), lower := (rows 37 98 134 25 26 96 64 128 256), losses := [] }

theorem u24097 : Upper (D 7) (R 7) [36,96,130,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24098 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 25 26 160 321 449 321), lower := (rows 37 98 134 25 26 160 64 128 256), losses := [] }

theorem u24098 : Upper (D 7) (R 7) [36,96,130,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24099 : Route 9 := (fun mask => (mask,id))

def c24099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24099 : Upper (D 7) (R 7) [36,96,130,17,10,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,10,256] 13 (by decide) (choices 1) [1,128] r24099 c24099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7874
  · exact u7875

def b24100 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(2,6)], upper := (rows 37 98 134 25 88 33 450 386 386), lower := (rows 37 98 134 25 88 33 64 128 256), losses := [] }

theorem u24100 : Upper (D 7) (R 7) [36,96,130,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24101 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 25 88 34 449 385 385), lower := (rows 37 98 134 25 88 34 64 128 256), losses := [] }

theorem u24101 : Upper (D 7) (R 7) [36,96,130,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24102 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 25 88 160 323 387 259), lower := (rows 37 98 134 25 88 160 64 128 256), losses := [] }

theorem u24102 : Upper (D 7) (R 7) [36,96,130,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24103 : Route 9 := (fun mask => (mask,id))

def c24103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24103 : Upper (D 7) (R 7) [36,96,130,17,72,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,72,256] 13 (by decide) (choices 1) [1,2,128] r24103 c24103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7876
  · exact u7877
  · exact u7878

def b24104 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 98 134 25 152 33 322 450 322), lower := (rows 37 98 134 25 152 33 64 128 256), losses := [] }

theorem u24104 : Upper (D 7) (R 7) [36,96,130,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24105 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 25 152 34 321 449 321), lower := (rows 37 98 134 25 152 34 64 128 256), losses := [] }

theorem u24105 : Upper (D 7) (R 7) [36,96,130,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24106 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 25 152 96 323 387 259), lower := (rows 37 98 134 25 152 96 64 128 256), losses := [] }

theorem u24106 : Upper (D 7) (R 7) [36,96,130,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24107 : Route 9 := (fun mask => (mask,id))

def c24107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24107 : Upper (D 7) (R 7) [36,96,130,17,136,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,136,256] 13 (by decide) (choices 1) [1,2] r24107 c24107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7879
  · exact u7880

def b24108 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 25 208 33 330 394 266), lower := (rows 37 98 134 25 208 33 64 128 256), losses := [] }

theorem u24108 : Upper (D 7) (R 7) [36,96,130,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24109 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 25 208 34 329 393 265), lower := (rows 37 98 134 25 208 34 64 128 256), losses := [] }

theorem u24109 : Upper (D 7) (R 7) [36,96,130,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24110 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 98 134 25 208 40 323 387 259), lower := (rows 37 98 134 25 208 40 64 128 256), losses := [] }

theorem u24110 : Upper (D 7) (R 7) [36,96,130,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24110 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24111 : Route 9 := (fun mask => (mask,id))

def c24111 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24111 : Upper (D 7) (R 7) [36,96,130,17,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,192,256] 13 (by decide) (choices 1) [1,2,8] r24111 c24111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7881
  · exact u7882
  · exact u7883

def r24112 : Route 9 := (fun mask => (mask,id))

def c24112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24112 : Upper (D 7) (R 7) [36,96,130,17,258,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,258,1] 13 (by decide) (choices 1) [8,128] r24112 c24112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7884
  · exact u7885

def r24113 : Route 9 := (fun mask => (mask,id))

def c24113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24113 : Upper (D 7) (R 7) [36,96,130,17,258,8] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,258,8] 13 (by decide) (choices 1) [1,128] r24113 c24113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7886
  · exact u7887

def b24114 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 25 274 96 201 137 393), lower := (rows 37 98 134 25 274 96 64 128 256), losses := [] }

theorem u24114 : Upper (D 7) (R 7) [36,96,130,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24115 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 25 274 160 73 201 329), lower := (rows 37 98 134 25 274 160 64 128 256), losses := [] }

theorem u24115 : Upper (D 7) (R 7) [36,96,130,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24116 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 134 25 280 33 194 194 450), lower := (rows 37 98 134 25 280 33 64 128 256), losses := [] }

theorem u24116 : Upper (D 7) (R 7) [36,96,130,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24117 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 25 280 34 193 193 449), lower := (rows 37 98 134 25 280 34 64 128 256), losses := [] }

theorem u24117 : Upper (D 7) (R 7) [36,96,130,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24118 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 25 280 96 195 131 387), lower := (rows 37 98 134 25 280 96 64 128 256), losses := [] }

theorem u24118 : Upper (D 7) (R 7) [36,96,130,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24119 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 25 280 160 67 195 323), lower := (rows 37 98 134 25 280 160 64 128 256), losses := [] }

theorem u24119 : Upper (D 7) (R 7) [36,96,130,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24119
end Delivery.IrregularNine14.P07
