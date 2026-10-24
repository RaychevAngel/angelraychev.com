import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0103
import IrregularNine14P06C0104

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21060 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 336, targets := 4 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(4,2)], upper := (rows 35 74 133 28 273 36 98 226 354), lower := (rows 35 74 133 28 273 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 43 165 60 273 36 0 128 256) }] }

theorem u21060 : Upper (D 6) (R 6) [34,72,129,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21061 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 28 273 96 102 166 294), lower := (rows 35 74 133 28 273 96 64 128 256), losses := [] }

theorem u21061 : Upper (D 6) (R 6) [34,72,129,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21062 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 74 133 28 274 33 100 228 356), lower := (rows 35 74 133 28 274 33 64 128 256), losses := [] }

theorem u21062 : Upper (D 6) (R 6) [34,72,129,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21063 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 196, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(0,6),(2,1),(4,2)], upper := (rows 35 74 133 28 274 36 97 225 353), lower := (rows 35 74 133 28 274 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 43 165 60 275 36 0 128 256) }] }

theorem u21063 : Upper (D 6) (R 6) [34,72,129,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21064 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 28 274 96 101 165 293), lower := (rows 35 74 133 28 274 96 64 128 256), losses := [] }

theorem u21064 : Upper (D 6) (R 6) [34,72,129,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21065 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 74 133 28 304 33 70 198 326), lower := (rows 35 74 133 28 304 33 64 128 256), losses := [] }

theorem u21065 : Upper (D 6) (R 6) [34,72,129,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21066 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 28 304 34 69 197 325), lower := (rows 35 74 133 28 304 34 64 128 256), losses := [] }

theorem u21066 : Upper (D 6) (R 6) [34,72,129,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21067 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,6),(2,5),(4,2)], upper := (rows 35 74 133 28 304 36 67 195 323), lower := (rows 35 74 133 28 304 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 43 165 60 304 36 0 128 256) }] }

theorem u21067 : Upper (D 6) (R 6) [34,72,129,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21068 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 28 304 96 71 135 263), lower := (rows 35 74 133 28 304 96 64 128 256), losses := [] }

theorem u21068 : Upper (D 6) (R 6) [34,72,129,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21069 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 74 133 28 336 33 102 166 294), lower := (rows 35 74 133 28 336 33 64 128 256), losses := [] }

theorem u21069 : Upper (D 6) (R 6) [34,72,129,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21070 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 28 336 34 101 165 293), lower := (rows 35 74 133 28 336 34 64 128 256), losses := [] }

theorem u21070 : Upper (D 6) (R 6) [34,72,129,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21071 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 336, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 35 74 133 28 336 36 99 163 291), lower := (rows 35 74 133 28 336 36 64 128 256), losses := [] }

theorem u21071 : Upper (D 6) (R 6) [34,72,129,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21072 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 133 44 84 33 338 402 274), lower := (rows 35 74 133 44 84 33 64 128 256), losses := [] }

theorem u21072 : Upper (D 6) (R 6) [34,72,129,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21073 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 44 84 34 337 401 273), lower := (rows 35 74 133 44 84 34 64 128 256), losses := [] }

theorem u21073 : Upper (D 6) (R 6) [34,72,129,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21074 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 133 44 84 48 323 387 259), lower := (rows 35 74 133 44 84 48 64 128 256), losses := [] }

theorem u21074 : Upper (D 6) (R 6) [34,72,129,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21074 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21075 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 133 44 84 288 83 147 275), lower := (rows 35 74 133 44 84 288 64 128 256), losses := [] }

theorem u21075 : Upper (D 6) (R 6) [34,72,129,36,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21075 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21076 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 133 44 276 33 82 210 338), lower := (rows 35 74 133 44 276 33 64 128 256), losses := [] }

theorem u21076 : Upper (D 6) (R 6) [34,72,129,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21077 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 44 276 34 81 209 337), lower := (rows 35 74 133 44 276 34 64 128 256), losses := [] }

theorem u21077 : Upper (D 6) (R 6) [34,72,129,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21078 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 74 133 44 276 48 67 195 323), lower := (rows 35 74 133 44 276 48 64 128 256), losses := [] }

theorem u21078 : Upper (D 6) (R 6) [34,72,129,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21078 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21079 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 44 276 96 83 147 275), lower := (rows 35 74 133 44 276 96 64 128 256), losses := [] }

theorem u21079 : Upper (D 6) (R 6) [34,72,129,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21080 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 133 44 336 33 86 150 278), lower := (rows 35 74 133 44 336 33 64 128 256), losses := [] }

theorem u21080 : Upper (D 6) (R 6) [34,72,129,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21081 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 44 336 34 85 149 277), lower := (rows 35 74 133 44 336 34 64 128 256), losses := [] }

theorem u21081 : Upper (D 6) (R 6) [34,72,129,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21082 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 133 44 336 36 83 147 275), lower := (rows 35 74 133 44 336 36 64 128 256), losses := [] }

theorem u21082 : Upper (D 6) (R 6) [34,72,129,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21083 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 133 44 336 48 71 135 263), lower := (rows 35 74 133 44 336 48 64 128 256), losses := [] }

theorem u21083 : Upper (D 6) (R 6) [34,72,129,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21083 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21084 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 133 56 276 33 70 198 326), lower := (rows 35 74 133 56 276 33 64 128 256), losses := [] }

theorem u21084 : Upper (D 6) (R 6) [34,72,129,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21085 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 56 276 34 69 197 325), lower := (rows 35 74 133 56 276 34 64 128 256), losses := [] }

theorem u21085 : Upper (D 6) (R 6) [34,72,129,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21086 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 133 56 276 36 67 195 323), lower := (rows 35 74 133 56 276 36 64 128 256), losses := [] }

theorem u21086 : Upper (D 6) (R 6) [34,72,129,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21087 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 56 276 96 71 135 263), lower := (rows 35 74 133 56 276 96 64 128 256), losses := [] }

theorem u21087 : Upper (D 6) (R 6) [34,72,129,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21088 : Route 9 := (fun mask => (mask,id))

def c21088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21088 : Upper (D 6) (R 6) [34,72,129,257,6,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,257,6,4] 13 (by decide) (choices 1) [16,32] r21088 c21088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6235
  · exact u6236

def b21089 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 133 265 22 48 100 228 356), lower := (rows 35 74 133 265 22 48 64 128 256), losses := [] }

theorem u21089 : Upper (D 6) (R 6) [34,72,129,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21089 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21090 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 265 22 96 116 180 308), lower := (rows 35 74 133 265 22 96 64 128 256), losses := [] }

theorem u21090 : Upper (D 6) (R 6) [34,72,129,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21091 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 265 52 34 84 212 340), lower := (rows 35 74 133 265 52 34 64 128 256), losses := [] }

theorem u21091 : Upper (D 6) (R 6) [34,72,129,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21092 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 74 133 265 52 36 82 210 338), lower := (rows 35 74 133 265 52 36 64 128 256), losses := [] }

theorem u21092 : Upper (D 6) (R 6) [34,72,129,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21093 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 265 52 48 70 198 326), lower := (rows 35 74 133 265 52 48 64 128 256), losses := [] }

theorem u21093 : Upper (D 6) (R 6) [34,72,129,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21093 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21094 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 265 52 96 86 150 278), lower := (rows 35 74 133 265 52 96 64 128 256), losses := [] }

theorem u21094 : Upper (D 6) (R 6) [34,72,129,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21095 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 265 84 34 116 180 308), lower := (rows 35 74 133 265 84 34 64 128 256), losses := [] }

theorem u21095 : Upper (D 6) (R 6) [34,72,129,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21096 : Route 9 := (fun mask => (mask,id))

def c21096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21096 : Upper (D 6) (R 6) [34,72,129,257,68,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,257,68,4] 13 (by decide) (choices 1) [2,16,32] r21096 c21096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6237
  · exact u6238
  · exact u6239

def b21097 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 133 265 84 48 102 166 294), lower := (rows 35 74 133 265 84 48 64 128 256), losses := [] }

theorem u21097 : Upper (D 6) (R 6) [34,72,129,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21097 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21098 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 265 112 34 84 148 276), lower := (rows 35 74 133 265 112 34 64 128 256), losses := [] }

theorem u21098 : Upper (D 6) (R 6) [34,72,129,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21099 : Route 9 := (fun mask => (mask,id))

def c21099 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21099 : Upper (D 6) (R 6) [34,72,129,257,96,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,257,96,4] 13 (by decide) (choices 1) [2,4,16] r21099 c21099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6240
  · exact u6241
  · exact u6242

def b21100 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 265 112 48 70 134 262), lower := (rows 35 74 133 265 112 48 64 128 256), losses := [] }

theorem u21100 : Upper (D 6) (R 6) [34,72,129,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21100 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21101 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 133 266 52 33 84 212 340), lower := (rows 35 74 133 266 52 33 64 128 256), losses := [] }

theorem u21101 : Upper (D 6) (R 6) [34,72,129,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21102 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 133 266 52 36 81 209 337), lower := (rows 35 74 133 266 52 36 64 128 256), losses := [] }

theorem u21102 : Upper (D 6) (R 6) [34,72,129,258,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21103 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 266 52 48 69 197 325), lower := (rows 35 74 133 266 52 48 64 128 256), losses := [] }

theorem u21103 : Upper (D 6) (R 6) [34,72,129,258,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21103 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21104 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 266 52 96 85 149 277), lower := (rows 35 74 133 266 52 96 64 128 256), losses := [] }

theorem u21104 : Upper (D 6) (R 6) [34,72,129,258,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21105 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 133 266 84 33 116 180 308), lower := (rows 35 74 133 266 84 33 64 128 256), losses := [] }

theorem u21105 : Upper (D 6) (R 6) [34,72,129,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21106 : Route 9 := (fun mask => (mask,id))

def c21106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21106 : Upper (D 6) (R 6) [34,72,129,258,68,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,258,68,4] 13 (by decide) (choices 1) [1,16,32] r21106 c21106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6243
  · exact u6244
  · exact u6245

def b21107 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 133 266 84 48 101 165 293), lower := (rows 35 74 133 266 84 48 64 128 256), losses := [] }

theorem u21107 : Upper (D 6) (R 6) [34,72,129,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21107 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21108 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 133 266 112 33 84 148 276), lower := (rows 35 74 133 266 112 33 64 128 256), losses := [] }

theorem u21108 : Upper (D 6) (R 6) [34,72,129,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21109 : Route 9 := (fun mask => (mask,id))

def c21109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21109 : Upper (D 6) (R 6) [34,72,129,258,96,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,258,96,4] 13 (by decide) (choices 1) [1,4,16] r21109 c21109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6246
  · exact u6247
  · exact u6248

def b21110 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 266 112 48 69 133 261), lower := (rows 35 74 133 266 112 48 64 128 256), losses := [] }

theorem u21110 : Upper (D 6) (R 6) [34,72,129,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21110 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21111 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,1)], upper := (rows 35 74 133 268 22 33 112 240 368), lower := (rows 35 74 133 268 22 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 80 144 272), good := (rows 33 72 165 300 508 33 64 128 256) }] }

theorem u21111 : Upper (D 6) (R 6) [34,72,129,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21112 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 133 268 22 48 97 225 353), lower := (rows 35 74 133 268 22 48 64 128 256), losses := [] }

theorem u21112 : Upper (D 6) (R 6) [34,72,129,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21112 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21113 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 268 22 96 113 177 305), lower := (rows 35 74 133 268 22 96 64 128 256), losses := [] }

theorem u21113 : Upper (D 6) (R 6) [34,72,129,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21114 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 133 268 52 33 82 210 338), lower := (rows 35 74 133 268 52 33 64 128 256), losses := [] }

theorem u21114 : Upper (D 6) (R 6) [34,72,129,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21115 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 268 52 34 81 209 337), lower := (rows 35 74 133 268 52 34 64 128 256), losses := [] }

theorem u21115 : Upper (D 6) (R 6) [34,72,129,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21116 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 268 52 48 67 195 323), lower := (rows 35 74 133 268 52 48 64 128 256), losses := [] }

theorem u21116 : Upper (D 6) (R 6) [34,72,129,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21116 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21117 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 268 52 96 83 147 275), lower := (rows 35 74 133 268 52 96 64 128 256), losses := [] }

theorem u21117 : Upper (D 6) (R 6) [34,72,129,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21118 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 268 81 34 116 180 308), lower := (rows 35 74 133 268 81 34 64 128 256), losses := [] }

theorem u21118 : Upper (D 6) (R 6) [34,72,129,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21119 : Route 9 := (fun mask => (mask,id))

def c21119 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21119 : Upper (D 6) (R 6) [34,72,129,260,65,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,260,65,4] 13 (by decide) (choices 1) [2,16,32] r21119 c21119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6249
  · exact u6250
  · exact u6251

#print axioms u21119
end Delivery.IrregularNine14.P06
