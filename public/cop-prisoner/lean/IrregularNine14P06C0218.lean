import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0043

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13080 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,6),(2,5)], upper := (rows 11 38 69 152 112 288 71 135 263), lower := (rows 11 38 69 152 112 288 64 128 256), losses := [] }

theorem u13080 : Upper (D 6) (R 6) [10,36,65,144,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13080 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13081 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 34, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 38 69 152 273 34 100 228 356), lower := (rows 11 38 69 152 273 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 17 32 66 130 258), good := (rows 477 484 93 152 285 480 64 128 256) }] }

theorem u13081 : Upper (D 6) (R 6) [10,36,65,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13082 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 152 273 36 98 226 354), lower := (rows 11 38 69 152 273 36 64 128 256), losses := [] }

theorem u13082 : Upper (D 6) (R 6) [10,36,65,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13083 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 152 273 96 102 166 294), lower := (rows 11 38 69 152 273 96 64 128 256), losses := [] }

theorem u13083 : Upper (D 6) (R 6) [10,36,65,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13084 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 38 69 152 274 33 100 228 356), lower := (rows 11 38 69 152 274 33 64 128 256), losses := [] }

theorem u13084 : Upper (D 6) (R 6) [10,36,65,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13085 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 152 274 36 97 225 353), lower := (rows 11 38 69 152 274 36 64 128 256), losses := [] }

theorem u13085 : Upper (D 6) (R 6) [10,36,65,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13086 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 152 274 96 101 165 293), lower := (rows 11 38 69 152 274 96 64 128 256), losses := [] }

theorem u13086 : Upper (D 6) (R 6) [10,36,65,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13087 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 69 152 276 33 98 226 354), lower := (rows 11 38 69 152 276 33 64 128 256), losses := [] }

theorem u13087 : Upper (D 6) (R 6) [10,36,65,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13088 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,2)], upper := (rows 11 38 69 152 276 34 97 225 353), lower := (rows 11 38 69 152 276 34 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 35 69 133 261), good := (rows 491 482 481 152 472 34 64 128 256) }] }

theorem u13088 : Upper (D 6) (R 6) [10,36,65,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13089 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 152 276 96 99 163 291), lower := (rows 11 38 69 152 276 96 64 128 256), losses := [] }

theorem u13089 : Upper (D 6) (R 6) [10,36,65,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13090 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 38 69 152 304 33 70 198 326), lower := (rows 11 38 69 152 304 33 64 128 256), losses := [] }

theorem u13090 : Upper (D 6) (R 6) [10,36,65,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13091 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 68, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 69 152 304 34 69 197 325), lower := (rows 11 38 69 152 304 34 64 128 256), losses := [] }

theorem u13091 : Upper (D 6) (R 6) [10,36,65,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13092 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 152 304 36 67 195 323), lower := (rows 11 38 69 152 304 36 64 128 256), losses := [] }

theorem u13092 : Upper (D 6) (R 6) [10,36,65,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13093 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 152 304 96 71 135 263), lower := (rows 11 38 69 152 304 96 64 128 256), losses := [] }

theorem u13093 : Upper (D 6) (R 6) [10,36,65,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13094 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 69 152 336 33 102 166 294), lower := (rows 11 38 69 152 336 33 64 128 256), losses := [] }

theorem u13094 : Upper (D 6) (R 6) [10,36,65,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13095 : Route 9 := (fun mask => (mask,id))

def c13095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13095 : Upper (D 6) (R 6) [10,36,65,144,320,2] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144,320,2] 13 (by decide) (choices 1) [1,4,32] r13095 c13095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2611
  · exact u2612
  · exact u2613

def b13096 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 152 336 36 99 163 291), lower := (rows 11 38 69 152 336 36 64 128 256), losses := [] }

theorem u13096 : Upper (D 6) (R 6) [10,36,65,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13097 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 69 168 82 33 340 404 276), lower := (rows 11 38 69 168 82 33 64 128 256), losses := [] }

theorem u13097 : Upper (D 6) (R 6) [10,36,65,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13098 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 168 82 36 337 401 273), lower := (rows 11 38 69 168 82 36 64 128 256), losses := [] }

theorem u13098 : Upper (D 6) (R 6) [10,36,65,160,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13099 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 69 168 82 48 325 389 261), lower := (rows 11 38 69 168 82 48 64 128 256), losses := [] }

theorem u13099 : Upper (D 6) (R 6) [10,36,65,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13099 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13100 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 69 168 82 288 85 149 277), lower := (rows 11 38 69 168 82 288 64 128 256), losses := [] }

theorem u13100 : Upper (D 6) (R 6) [10,36,65,160,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13100 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13101 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 69 168 273 34 84 212 340), lower := (rows 11 38 69 168 273 34 64 128 256), losses := [] }

theorem u13101 : Upper (D 6) (R 6) [10,36,65,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13102 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 168 273 36 82 210 338), lower := (rows 11 38 69 168 273 36 64 128 256), losses := [] }

theorem u13102 : Upper (D 6) (R 6) [10,36,65,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13103 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 69 168 273 48 70 198 326), lower := (rows 11 38 69 168 273 48 64 128 256), losses := [] }

theorem u13103 : Upper (D 6) (R 6) [10,36,65,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13103 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13104 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 168 273 96 86 150 278), lower := (rows 11 38 69 168 273 96 64 128 256), losses := [] }

theorem u13104 : Upper (D 6) (R 6) [10,36,65,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13105 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 69 168 274 33 84 212 340), lower := (rows 11 38 69 168 274 33 64 128 256), losses := [] }

theorem u13105 : Upper (D 6) (R 6) [10,36,65,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13106 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 168 274 36 81 209 337), lower := (rows 11 38 69 168 274 36 64 128 256), losses := [] }

theorem u13106 : Upper (D 6) (R 6) [10,36,65,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13107 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 69 168 274 48 69 197 325), lower := (rows 11 38 69 168 274 48 64 128 256), losses := [] }

theorem u13107 : Upper (D 6) (R 6) [10,36,65,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13107 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13108 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 168 274 96 85 149 277), lower := (rows 11 38 69 168 274 96 64 128 256), losses := [] }

theorem u13108 : Upper (D 6) (R 6) [10,36,65,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13109 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 69 168 276 33 82 210 338), lower := (rows 11 38 69 168 276 33 64 128 256), losses := [] }

theorem u13109 : Upper (D 6) (R 6) [10,36,65,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13110 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 69 168 276 34 81 209 337), lower := (rows 11 38 69 168 276 34 64 128 256), losses := [] }

theorem u13110 : Upper (D 6) (R 6) [10,36,65,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13111 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 69 168 276 48 67 195 323), lower := (rows 11 38 69 168 276 48 64 128 256), losses := [] }

theorem u13111 : Upper (D 6) (R 6) [10,36,65,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13111 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13112 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 168 276 96 83 147 275), lower := (rows 11 38 69 168 276 96 64 128 256), losses := [] }

theorem u13112 : Upper (D 6) (R 6) [10,36,65,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13113 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 69 168 336 33 86 150 278), lower := (rows 11 38 69 168 336 33 64 128 256), losses := [] }

theorem u13113 : Upper (D 6) (R 6) [10,36,65,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13114 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 69 168 336 34 85 149 277), lower := (rows 11 38 69 168 336 34 64 128 256), losses := [] }

theorem u13114 : Upper (D 6) (R 6) [10,36,65,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13115 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 168 336 36 83 147 275), lower := (rows 11 38 69 168 336 36 64 128 256), losses := [] }

theorem u13115 : Upper (D 6) (R 6) [10,36,65,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13116 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 69 168 336 48 71 135 263), lower := (rows 11 38 69 168 336 48 64 128 256), losses := [] }

theorem u13116 : Upper (D 6) (R 6) [10,36,65,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13116 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13117 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 69 200 49 34 340 404 276), lower := (rows 11 38 69 200 49 34 64 128 256), losses := [] }

theorem u13117 : Upper (D 6) (R 6) [10,36,65,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13118 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 200 49 36 338 402 274), lower := (rows 11 38 69 200 49 36 64 128 256), losses := [] }

theorem u13118 : Upper (D 6) (R 6) [10,36,65,192,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13119 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 69 200 49 48 326 390 262), lower := (rows 11 38 69 200 49 48 64 128 256), losses := [] }

theorem u13119 : Upper (D 6) (R 6) [10,36,65,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13119 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13120 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 11 38 69 200 49 288 86 150 278), lower := (rows 11 38 69 200 49 288 64 128 256), losses := [] }

theorem u13120 : Upper (D 6) (R 6) [10,36,65,192,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13120 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13121 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 306, targets := 64 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 38 69 200 273 34 116 180 308), lower := (rows 11 38 69 200 273 34 64 128 256), losses := [] }

theorem u13121 : Upper (D 6) (R 6) [10,36,65,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13122 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 200 273 36 114 178 306), lower := (rows 11 38 69 200 273 36 64 128 256), losses := [] }

theorem u13122 : Upper (D 6) (R 6) [10,36,65,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13123 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 11 38 69 200 273 48 102 166 294), lower := (rows 11 38 69 200 273 48 64 128 256), losses := [] }

theorem u13123 : Upper (D 6) (R 6) [10,36,65,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13123 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13124 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 69 200 274 33 116 180 308), lower := (rows 11 38 69 200 274 33 64 128 256), losses := [] }

theorem u13124 : Upper (D 6) (R 6) [10,36,65,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13125 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 200 274 36 113 177 305), lower := (rows 11 38 69 200 274 36 64 128 256), losses := [] }

theorem u13125 : Upper (D 6) (R 6) [10,36,65,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13126 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 11 38 69 200 274 48 101 165 293), lower := (rows 11 38 69 200 274 48 64 128 256), losses := [] }

theorem u13126 : Upper (D 6) (R 6) [10,36,65,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13126 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13127 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 69 200 276 33 114 178 306), lower := (rows 11 38 69 200 276 33 64 128 256), losses := [] }

theorem u13127 : Upper (D 6) (R 6) [10,36,65,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13128 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 306, targets := 64 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 38 69 200 276 34 113 177 305), lower := (rows 11 38 69 200 276 34 64 128 256), losses := [] }

theorem u13128 : Upper (D 6) (R 6) [10,36,65,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13129 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 69 200 276 48 99 163 291), lower := (rows 11 38 69 200 276 48 64 128 256), losses := [] }

theorem u13129 : Upper (D 6) (R 6) [10,36,65,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13129 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13130 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 69 200 304 33 86 150 278), lower := (rows 11 38 69 200 304 33 64 128 256), losses := [] }

theorem u13130 : Upper (D 6) (R 6) [10,36,65,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13131 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 306, targets := 64 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 38 69 200 304 34 85 149 277), lower := (rows 11 38 69 200 304 34 64 128 256), losses := [] }

theorem u13131 : Upper (D 6) (R 6) [10,36,65,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13132 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 200 304 36 83 147 275), lower := (rows 11 38 69 200 304 36 64 128 256), losses := [] }

theorem u13132 : Upper (D 6) (R 6) [10,36,65,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13133 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 69 200 304 48 71 135 263), lower := (rows 11 38 69 200 304 48 64 128 256), losses := [] }

theorem u13133 : Upper (D 6) (R 6) [10,36,65,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13133 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13134 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 69 392 49 34 84 212 340), lower := (rows 11 38 69 392 49 34 64 128 256), losses := [] }

theorem u13134 : Upper (D 6) (R 6) [10,36,65,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13135 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 392 49 36 82 210 338), lower := (rows 11 38 69 392 49 36 64 128 256), losses := [] }

theorem u13135 : Upper (D 6) (R 6) [10,36,65,384,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13136 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 69 392 49 48 70 198 326), lower := (rows 11 38 69 392 49 48 64 128 256), losses := [] }

theorem u13136 : Upper (D 6) (R 6) [10,36,65,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13136 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13137 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 392 49 96 86 150 278), lower := (rows 11 38 69 392 49 96 64 128 256), losses := [] }

theorem u13137 : Upper (D 6) (R 6) [10,36,65,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13138 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 69 392 82 33 116 180 308), lower := (rows 11 38 69 392 82 33 64 128 256), losses := [] }

theorem u13138 : Upper (D 6) (R 6) [10,36,65,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13139 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 392 82 36 113 177 305), lower := (rows 11 38 69 392 82 36 64 128 256), losses := [] }

theorem u13139 : Upper (D 6) (R 6) [10,36,65,384,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13139
end Delivery.IrregularNine14.P06
