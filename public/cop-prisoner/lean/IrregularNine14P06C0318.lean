import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0094

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19080 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 98 164 14 273 34 69 197 325), lower := (rows 25 98 164 14 273 34 64 128 256), losses := [] }

theorem u19080 : Upper (D 6) (R 6) [24,96,160,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19081 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 337, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 98 164 14 273 36 67 195 323), lower := (rows 25 98 164 14 273 36 64 128 256), losses := [] }

theorem u19081 : Upper (D 6) (R 6) [24,96,160,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19082 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 164 14 273 96 71 135 263), lower := (rows 25 98 164 14 273 96 64 128 256), losses := [] }

theorem u19082 : Upper (D 6) (R 6) [24,96,160,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19083 : Route 9 := (fun mask => (mask,id))

def c19083 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19083 : Upper (D 6) (R 6) [24,96,160,6,320,1] 13 := by
  apply FastRouting.sound _ _ [24,96,160,6,320,1] 13 (by decide) (choices 1) [1,2,4] r19083 c19083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5658
  · exact u5659
  · exact u5660

def b19084 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 98 164 14 336 34 69 133 261), lower := (rows 25 98 164 14 336 34 64 128 256), losses := [] }

theorem u19084 : Upper (D 6) (R 6) [24,96,160,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19085 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 337, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 98 164 14 336 36 67 131 259), lower := (rows 25 98 164 14 336 36 64 128 256), losses := [] }

theorem u19085 : Upper (D 6) (R 6) [24,96,160,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19086 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 164 73 274 33 70 134 262), lower := (rows 25 98 164 73 274 33 64 128 256), losses := [] }

theorem u19086 : Upper (D 6) (R 6) [24,96,160,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19087 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(2,6)], upper := (rows 25 98 164 73 274 34 69 133 261), lower := (rows 25 98 164 73 274 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 16 50 0 137 265), good := (rows 445 34 164 397 306 34 0 128 256) }] }

theorem u19087 : Upper (D 6) (R 6) [24,96,160,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19088 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 73 274 36 71 135 263), lower := (rows 25 98 164 73 274 36 64 128 256), losses := [] }

theorem u19088 : Upper (D 6) (R 6) [24,96,160,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19089 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 164 73 276 33 70 134 262), lower := (rows 25 98 164 73 276 33 64 128 256), losses := [] }

theorem u19089 : Upper (D 6) (R 6) [24,96,160,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19090 : Route 9 := (fun mask => (mask,id))

def c19090 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19090 : Upper (D 6) (R 6) [24,96,160,65,260,2] 13 := by
  apply FastRouting.sound _ _ [24,96,160,65,260,2] 13 (by decide) (choices 1) [1,2,4] r19090 c19090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5661
  · exact u5662
  · exact u5663

def b19091 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 73 276 36 67 131 259), lower := (rows 25 98 164 73 276 36 64 128 256), losses := [] }

theorem u19091 : Upper (D 6) (R 6) [24,96,160,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19092 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 98 164 76 273 33 70 134 262), lower := (rows 25 98 164 76 273 33 64 128 256), losses := [] }

theorem u19092 : Upper (D 6) (R 6) [24,96,160,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19093 : Route 9 := (fun mask => (mask,id))

def c19093 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19093 : Upper (D 6) (R 6) [24,96,160,68,257,2] 13 := by
  apply FastRouting.sound _ _ [24,96,160,68,257,2] 13 (by decide) (choices 1) [1,2,4] r19093 c19093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5664
  · exact u5665
  · exact u5666

def b19094 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 76 273 36 67 131 259), lower := (rows 25 98 164 76 273 36 64 128 256), losses := [] }

theorem u19094 : Upper (D 6) (R 6) [24,96,160,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19095 : Route 9 := (fun mask => (mask,id))

def c19095 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19095 : Upper (D 6) (R 6) [24,96,160,68,258,1] 13 := by
  apply FastRouting.sound _ _ [24,96,160,68,258,1] 13 (by decide) (choices 1) [1,2,4] r19095 c19095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5667
  · exact u5668
  · exact u5669

def b19096 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(2,6)], upper := (rows 25 98 164 76 274 34 69 133 261), lower := (rows 25 98 164 76 274 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 16 50 0 129 257), good := (rows 445 34 164 12 306 34 0 128 256) }] }

theorem u19096 : Upper (D 6) (R 6) [24,96,160,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19097 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 76 274 36 67 131 259), lower := (rows 25 98 164 76 274 36 64 128 256), losses := [] }

theorem u19097 : Upper (D 6) (R 6) [24,96,160,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19098 : Route 9 := (fun mask => (mask,id))

def c19098 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19098 : Upper (D 6) (R 6) [24,96,160,68,260,1] 13 := by
  apply FastRouting.sound _ _ [24,96,160,68,260,1] 13 (by decide) (choices 1) [1,2] r19098 c19098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5670
  · exact u5671

def r19099 : Route 9 := (fun mask => (mask,id))

def c19099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19099 : Upper (D 6) (R 6) [24,96,160,68,260,2] 13 := by
  apply FastRouting.sound _ _ [24,96,160,68,260,2] 13 (by decide) (choices 1) [1,2] r19099 c19099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5672
  · exact u5673

def b19100 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 388, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 98 388 11 21 34 100 228 356), lower := (rows 25 98 388 11 21 34 64 128 256), losses := [] }

theorem u19100 : Upper (D 6) (R 6) [24,96,384,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19101 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 388 11 21 36 98 226 354), lower := (rows 25 98 388 11 21 36 64 128 256), losses := [] }

theorem u19101 : Upper (D 6) (R 6) [24,96,384,3,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19102 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 388 11 21 96 102 166 294), lower := (rows 25 98 388 11 21 96 64 128 256), losses := [] }

theorem u19102 : Upper (D 6) (R 6) [24,96,384,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19103 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 388 11 52 33 70 198 326), lower := (rows 25 98 388 11 52 33 64 128 256), losses := [] }

theorem u19103 : Upper (D 6) (R 6) [24,96,384,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19104 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 98 388 11 52 34 69 197 325), lower := (rows 25 98 388 11 52 34 64 128 256), losses := [] }

theorem u19104 : Upper (D 6) (R 6) [24,96,384,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19105 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 25 98 388 11 52 36 67 195 323), lower := (rows 25 98 388 11 52 36 64 128 256), losses := [] }

theorem u19105 : Upper (D 6) (R 6) [24,96,384,3,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19106 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 388 11 52 96 71 135 263), lower := (rows 25 98 388 11 52 96 64 128 256), losses := [] }

theorem u19106 : Upper (D 6) (R 6) [24,96,384,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19107 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 49, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 98 388 14 49 33 70 198 326), lower := (rows 25 98 388 14 49 33 64 128 256), losses := [] }

theorem u19107 : Upper (D 6) (R 6) [24,96,384,6,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19108 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 25 98 388 14 49 34 69 197 325), lower := (rows 25 98 388 14 49 34 64 128 256), losses := [] }

theorem u19108 : Upper (D 6) (R 6) [24,96,384,6,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19109 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 25 98 388 14 49 36 67 195 323), lower := (rows 25 98 388 14 49 36 64 128 256), losses := [] }

theorem u19109 : Upper (D 6) (R 6) [24,96,384,6,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19110 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 388 14 49 96 71 135 263), lower := (rows 25 98 388 14 49 96 64 128 256), losses := [] }

theorem u19110 : Upper (D 6) (R 6) [24,96,384,6,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19111 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 25 98 388 14 52 33 67 195 323), lower := (rows 25 98 388 14 52 33 64 128 256), losses := [] }

theorem u19111 : Upper (D 6) (R 6) [24,96,384,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19112 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(2,1),(2,5)], upper := (rows 25 98 388 14 52 34 65 193 321), lower := (rows 25 98 388 14 52 34 64 128 256), losses := [] }

theorem u19112 : Upper (D 6) (R 6) [24,96,384,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19113 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 388 14 52 96 67 131 259), lower := (rows 25 98 388 14 52 96 64 128 256), losses := [] }

theorem u19113 : Upper (D 6) (R 6) [24,96,384,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19114 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 98 388 41 84 33 70 134 262), lower := (rows 25 98 388 41 84 33 64 128 256), losses := [] }

theorem u19114 : Upper (D 6) (R 6) [24,96,384,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19115 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 388 41 84 34 71 135 263), lower := (rows 25 98 388 41 84 34 64 128 256), losses := [] }

theorem u19115 : Upper (D 6) (R 6) [24,96,384,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19116 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 388 41 84 36 67 131 259), lower := (rows 25 98 388 41 84 36 64 128 256), losses := [] }

theorem u19116 : Upper (D 6) (R 6) [24,96,384,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19117 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 388 44 84 33 67 131 259), lower := (rows 25 98 388 44 84 33 64 128 256), losses := [] }

theorem u19117 : Upper (D 6) (R 6) [24,96,384,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19118 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 42, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 25 98 388 44 84 34 67 131 259), lower := (rows 25 98 388 44 84 34 64 128 256), losses := [] }

theorem u19118 : Upper (D 6) (R 6) [24,96,384,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19119 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 25 131 261 14 50 36 96 224 352), lower := (rows 25 131 261 14 50 36 64 128 256), losses := [] }

theorem u19119 : Upper (D 6) (R 6) [24,129,257,6,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19120 : Route 9 := (fun mask => (mask,id))

def c19120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19120 : Upper (D 6) (R 6) [24,129,257,6,34,64] 13 := by
  apply FastRouting.sound _ _ [24,129,257,6,34,64] 13 (by decide) (choices 1) [4,32] r19120 c19120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5674
  · exact u5675

def r19121 : Route 9 := (fun mask => (mask,id))

def c19121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19121 : Upper (D 6) (R 6) [24,129,257,6,96,2] 13 := by
  apply FastRouting.sound _ _ [24,129,257,6,96,2] 13 (by decide) (choices 1) [4,32] r19121 c19121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5676
  · exact u5677

def b19122 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 131 261 14 112 96 102 166 294), lower := (rows 25 131 261 14 112 96 64 128 256), losses := [] }

theorem u19122 : Upper (D 6) (R 6) [24,129,257,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19123 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 131 261 42 52 34 68 196 324), lower := (rows 25 131 261 42 52 34 64 128 256), losses := [] }

theorem u19123 : Upper (D 6) (R 6) [24,129,257,34,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19124_4 : Upper (D 6) (R 6) [24,129,257,34,36,64,4] 13 :=
  permutation_upper _ _ _ [24,129,257,34,36,64,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5678

def r19124 : Route 9 := (fun mask => (mask,id))

def c19124 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19124 : Upper (D 6) (R 6) [24,129,257,34,36,64] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,36,64] 13 (by decide) (choices 1) [2,4] r19124 c19124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5678
  · exact m19124_4

def r19125 : Route 9 := (fun mask => (mask,id))

def c19125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19125 : Upper (D 6) (R 6) [24,129,257,34,66,4] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,66,4] 13 (by decide) (choices 1) [4,32] r19125 c19125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5679
  · exact u5680

def b19126 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 25 131 261 42 82 96 100 164 292), lower := (rows 25 131 261 42 82 96 64 128 256), losses := [] }

theorem u19126 : Upper (D 6) (R 6) [24,129,257,34,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19127 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 131 261 42 84 34 100 228 356), lower := (rows 25 131 261 42 84 34 64 128 256), losses := [] }

theorem u19127 : Upper (D 6) (R 6) [24,129,257,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19128 : Route 9 := (fun mask => (mask,id))

def c19128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19128 : Upper (D 6) (R 6) [24,129,257,34,68,4] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,68,4] 13 (by decide) (choices 1) [2,32] r19128 c19128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5682
  · exact u5683

theorem m19129_2 : Upper (D 6) (R 6) [24,129,257,34,68,64,2] 13 :=
  permutation_upper _ _ _ [24,129,257,34,68,4,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5683

theorem m19129_4 : Upper (D 6) (R 6) [24,129,257,34,68,64,4] 13 :=
  permutation_upper _ _ _ [24,129,257,34,68,2,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5681

def r19129 : Route 9 := (fun mask => (mask,id))

def c19129 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19129 : Upper (D 6) (R 6) [24,129,257,34,68,64] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,68,64] 13 (by decide) (choices 1) [2,4,32] r19129 c19129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19129_2
  · exact m19129_4
  · exact u5684

def b19130 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 131 261 42 112 34 68 196 324), lower := (rows 25 131 261 42 112 34 64 128 256), losses := [] }

theorem u19130 : Upper (D 6) (R 6) [24,129,257,34,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19131 : Route 9 := (fun mask => (mask,id))

def c19131 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19131 : Upper (D 6) (R 6) [24,129,257,34,96,4] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,96,4] 13 (by decide) (choices 1) [2,4] r19131 c19131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5685
  · exact u5686

def b19132 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 131 261 42 112 96 70 134 262), lower := (rows 25 131 261 42 112 96 64 128 256), losses := [] }

theorem u19132 : Upper (D 6) (R 6) [24,129,257,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19133 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 131 262 13 50 36 96 224 352), lower := (rows 25 131 262 13 50 36 64 128 256), losses := [] }

theorem u19133 : Upper (D 6) (R 6) [24,129,258,5,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19134 : Route 9 := (fun mask => (mask,id))

def c19134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19134 : Upper (D 6) (R 6) [24,129,258,5,34,64] 13 := by
  apply FastRouting.sound _ _ [24,129,258,5,34,64] 13 (by decide) (choices 1) [4,32] r19134 c19134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5687
  · exact u5688

def r19135 : Route 9 := (fun mask => (mask,id))

def c19135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19135 : Upper (D 6) (R 6) [24,129,258,5,96,2] 13 := by
  apply FastRouting.sound _ _ [24,129,258,5,96,2] 13 (by decide) (choices 1) [4,32] r19135 c19135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5689
  · exact u5690

theorem m19136_2 : Upper (D 6) (R 6) [24,129,258,5,96,4,2] 13 :=
  permutation_upper _ _ _ [24,129,258,5,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5689

def r19136 : Route 9 := (fun mask => (mask,id))

def c19136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19136 : Upper (D 6) (R 6) [24,129,258,5,96,4] 13 := by
  apply FastRouting.sound _ _ [24,129,258,5,96,4] 13 (by decide) (choices 1) [2,32] r19136 c19136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m19136_2
  · exact u5691

def b19137 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 131 262 13 112 96 102 166 294), lower := (rows 25 131 262 13 112 96 64 128 256), losses := [] }

theorem u19137 : Upper (D 6) (R 6) [24,129,258,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19138 : Route 9 := (fun mask => (mask,id))

def c19138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19138 : Upper (D 6) (R 6) [24,129,258,33,66,4] 13 := by
  apply FastRouting.sound _ _ [24,129,258,33,66,4] 13 (by decide) (choices 1) [4,32] r19138 c19138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5692
  · exact u5693

def b19139 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 131 262 41 82 96 100 164 292), lower := (rows 25 131 262 41 82 96 64 128 256), losses := [] }

theorem u19139 : Upper (D 6) (R 6) [24,129,258,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19139
end Delivery.IrregularNine14.P06
