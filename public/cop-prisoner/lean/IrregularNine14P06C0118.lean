import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008
import IrregularNine14P06C0009

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7080 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 300, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 134 76 296 81 33 66 148 276), lower := (rows 35 134 76 296 81 33 66 128 256), losses := [] }

theorem u7080 : Upper (D 6) (R 6) [34,132,72,288,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7081 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 134 76 296 81 33 68 146 274), lower := (rows 35 134 76 296 81 33 68 128 256), losses := [] }

theorem u7081 : Upper (D 6) (R 6) [34,132,72,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7082 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 76 296 81 33 80 134 262), lower := (rows 35 134 76 296 81 33 80 128 256), losses := [] }

theorem u7082 : Upper (D 6) (R 6) [34,132,72,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7082 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7083 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 76 296 81 48 65 134 262), lower := (rows 35 134 76 296 81 48 65 128 256), losses := [] }

theorem u7083 : Upper (D 6) (R 6) [34,132,72,288,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7083 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7084 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 76 296 81 48 66 133 261), lower := (rows 35 134 76 296 81 48 66 128 256), losses := [] }

theorem u7084 : Upper (D 6) (R 6) [34,132,72,288,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7084 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7085 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 76 296 81 48 68 131 259), lower := (rows 35 134 76 296 81 48 68 128 256), losses := [] }

theorem u7085 : Upper (D 6) (R 6) [34,132,72,288,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7085 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7086 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 146, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 76 296 82 33 65 148 276), lower := (rows 35 134 76 296 82 33 65 128 256), losses := [] }

theorem u7086 : Upper (D 6) (R 6) [34,132,72,288,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7087 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 76 296 82 33 68 145 273), lower := (rows 35 134 76 296 82 33 68 128 256), losses := [] }

theorem u7087 : Upper (D 6) (R 6) [34,132,72,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7088 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 76 296 82 33 80 133 261), lower := (rows 35 134 76 296 82 33 80 128 256), losses := [] }

theorem u7088 : Upper (D 6) (R 6) [34,132,72,288,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7088 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7089 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 100 25 82 288 65 140 268), lower := (rows 35 134 100 25 82 288 65 128 256), losses := [] }

theorem u7089 : Upper (D 6) (R 6) [34,132,96,17,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7089 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7090 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 100 25 82 288 68 137 265), lower := (rows 35 134 100 25 82 288 68 128 256), losses := [] }

theorem u7090 : Upper (D 6) (R 6) [34,132,96,17,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7090 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7091 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 }], pairs := [(3,2)], upper := (rows 35 134 100 25 82 288 72 133 261), lower := (rows 35 134 100 25 82 288 72 128 256), losses := [] }

theorem u7091 : Upper (D 6) (R 6) [34,132,96,17,66,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7091 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7092 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 134 100 25 276 33 66 200 328), lower := (rows 35 134 100 25 276 33 66 128 256), losses := [] }

theorem u7092 : Upper (D 6) (R 6) [34,132,96,17,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7093 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 100 25 276 33 72 194 322), lower := (rows 35 134 100 25 276 33 72 128 256), losses := [] }

theorem u7093 : Upper (D 6) (R 6) [34,132,96,17,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7093 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7094 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 100 25 276 40 65 194 322), lower := (rows 35 134 100 25 276 40 65 128 256), losses := [] }

theorem u7094 : Upper (D 6) (R 6) [34,132,96,17,260,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7094 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7095 : Route 9 := (fun mask => (mask,id))

def c7095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7095 : Upper (D 6) (R 6) [34,132,96,17,260,8,2] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,260,8,2] 13 (by decide) (choices 1) [1,64] r7095 c7095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u539
  · exact u540

def b7096 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 134 100 25 336 33 66 140 268), lower := (rows 35 134 100 25 336 33 66 128 256), losses := [] }

theorem u7096 : Upper (D 6) (R 6) [34,132,96,17,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7097 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 134 100 25 336 33 68 138 266), lower := (rows 35 134 100 25 336 33 68 128 256), losses := [] }

theorem u7097 : Upper (D 6) (R 6) [34,132,96,17,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7098 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 100 25 336 33 72 134 262), lower := (rows 35 134 100 25 336 33 72 128 256), losses := [] }

theorem u7098 : Upper (D 6) (R 6) [34,132,96,17,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7098 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7099 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 100 26 81 288 65 140 268), lower := (rows 35 134 100 26 81 288 65 128 256), losses := [] }

theorem u7099 : Upper (D 6) (R 6) [34,132,96,18,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7099 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7100 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 100 26 81 288 68 137 265), lower := (rows 35 134 100 26 81 288 68 128 256), losses := [] }

theorem u7100 : Upper (D 6) (R 6) [34,132,96,18,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7100 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7101 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 }], pairs := [(3,2)], upper := (rows 35 134 100 26 81 288 72 133 261), lower := (rows 35 134 100 26 81 288 72 128 256), losses := [] }

theorem u7101 : Upper (D 6) (R 6) [34,132,96,18,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7101 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7102 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 100 26 276 33 65 200 328), lower := (rows 35 134 100 26 276 33 65 128 256), losses := [] }

theorem u7102 : Upper (D 6) (R 6) [34,132,96,18,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7103 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 100 26 276 33 72 193 321), lower := (rows 35 134 100 26 276 33 72 128 256), losses := [] }

theorem u7103 : Upper (D 6) (R 6) [34,132,96,18,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7103 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7104 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 100 26 336 33 65 140 268), lower := (rows 35 134 100 26 336 33 65 128 256), losses := [] }

theorem u7104 : Upper (D 6) (R 6) [34,132,96,18,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7105 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 134 100 26 336 33 68 137 265), lower := (rows 35 134 100 26 336 33 68 128 256), losses := [] }

theorem u7105 : Upper (D 6) (R 6) [34,132,96,18,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7106 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 26 336 33 72 133 261), lower := (rows 35 134 100 26 336 33 72 128 256), losses := [] }

theorem u7106 : Upper (D 6) (R 6) [34,132,96,18,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7106 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7107 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 100 28 274 33 65 200 328), lower := (rows 35 134 100 28 274 33 65 128 256), losses := [] }

theorem u7107 : Upper (D 6) (R 6) [34,132,96,20,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7108 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 100 28 274 33 72 193 321), lower := (rows 35 134 100 28 274 33 72 128 256), losses := [] }

theorem u7108 : Upper (D 6) (R 6) [34,132,96,20,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7108 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7109 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 100 28 280 33 65 194 322), lower := (rows 35 134 100 28 280 33 65 128 256), losses := [] }

theorem u7109 : Upper (D 6) (R 6) [34,132,96,20,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7110 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 134 100 28 280 33 66 193 321), lower := (rows 35 134 100 28 280 33 66 128 256), losses := [] }

theorem u7110 : Upper (D 6) (R 6) [34,132,96,20,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7111 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 100 73 273 48 66 140 268), lower := (rows 35 134 100 73 273 48 66 128 256), losses := [] }

theorem u7111 : Upper (D 6) (R 6) [34,132,96,65,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7111 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7112 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 100 73 273 48 68 138 266), lower := (rows 35 134 100 73 273 48 68 128 256), losses := [] }

theorem u7112 : Upper (D 6) (R 6) [34,132,96,65,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7112 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7113 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6)], upper := (rows 35 134 100 73 273 48 72 134 262), lower := (rows 35 134 100 73 273 48 72 128 256), losses := [] }

theorem u7113 : Upper (D 6) (R 6) [34,132,96,65,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7113 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7114 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 100 74 273 33 68 152 280), lower := (rows 35 134 100 74 273 33 68 128 256), losses := [] }

theorem u7114 : Upper (D 6) (R 6) [34,132,96,66,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7115 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 74 273 33 72 148 276), lower := (rows 35 134 100 74 273 33 72 128 256), losses := [] }

theorem u7115 : Upper (D 6) (R 6) [34,132,96,66,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7115 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7116 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 138, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 100 74 273 33 80 140 268), lower := (rows 35 134 100 74 273 33 80 128 256), losses := [] }

theorem u7116 : Upper (D 6) (R 6) [34,132,96,66,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7116 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7117 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 138, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 100 74 273 48 65 140 268), lower := (rows 35 134 100 74 273 48 65 128 256), losses := [] }

theorem u7117 : Upper (D 6) (R 6) [34,132,96,66,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7117 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7118 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 305, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 100 74 273 48 68 137 265), lower := (rows 35 134 100 74 273 48 68 128 256), losses := [] }

theorem u7118 : Upper (D 6) (R 6) [34,132,96,66,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7118 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7119 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 35 134 100 74 273 48 72 133 261), lower := (rows 35 134 100 74 273 48 72 128 256), losses := [] }

theorem u7119 : Upper (D 6) (R 6) [34,132,96,66,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7119 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7120 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 100 74 276 33 65 152 280), lower := (rows 35 134 100 74 276 33 65 128 256), losses := [] }

theorem u7120 : Upper (D 6) (R 6) [34,132,96,66,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7121 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 74 276 33 72 145 273), lower := (rows 35 134 100 74 276 33 72 128 256), losses := [] }

theorem u7121 : Upper (D 6) (R 6) [34,132,96,66,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7121 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7122 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 100 74 276 33 80 137 265), lower := (rows 35 134 100 74 276 33 80 128 256), losses := [] }

theorem u7122 : Upper (D 6) (R 6) [34,132,96,66,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7122 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7123 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 100 74 280 33 65 148 276), lower := (rows 35 134 100 74 280 33 65 128 256), losses := [] }

theorem u7123 : Upper (D 6) (R 6) [34,132,96,66,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7124 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 100 74 280 33 68 145 273), lower := (rows 35 134 100 74 280 33 68 128 256), losses := [] }

theorem u7124 : Upper (D 6) (R 6) [34,132,96,66,264,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7125 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 74 280 33 80 133 261), lower := (rows 35 134 100 74 280 33 80 128 256), losses := [] }

theorem u7125 : Upper (D 6) (R 6) [34,132,96,66,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7125 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7126 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 100 88 274 33 65 140 268), lower := (rows 35 134 100 88 274 33 65 128 256), losses := [] }

theorem u7126 : Upper (D 6) (R 6) [34,132,96,80,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7127 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 134 100 88 274 33 68 137 265), lower := (rows 35 134 100 88 274 33 68 128 256), losses := [] }

theorem u7127 : Upper (D 6) (R 6) [34,132,96,80,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7128 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 88 274 33 72 133 261), lower := (rows 35 134 100 88 274 33 72 128 256), losses := [] }

theorem u7128 : Upper (D 6) (R 6) [34,132,96,80,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7128 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7129 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 100 88 276 33 65 138 266), lower := (rows 35 134 100 88 276 33 65 128 256), losses := [] }

theorem u7129 : Upper (D 6) (R 6) [34,132,96,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7130 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 134 100 88 276 33 66 137 265), lower := (rows 35 134 100 88 276 33 66 128 256), losses := [] }

theorem u7130 : Upper (D 6) (R 6) [34,132,96,80,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7131 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 100 88 276 33 72 131 259), lower := (rows 35 134 100 88 276 33 72 128 256), losses := [] }

theorem u7131 : Upper (D 6) (R 6) [34,132,96,80,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7131 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7132 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 112, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 35 134 261 25 52 96 66 200 328), lower := (rows 35 134 261 25 52 96 66 128 256), losses := [] }

theorem u7132 : Upper (D 6) (R 6) [34,132,257,17,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7133 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 35 134 261 25 52 96 72 194 322), lower := (rows 35 134 261 25 52 96 72 128 256), losses := [] }

theorem u7133 : Upper (D 6) (R 6) [34,132,257,17,36,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7133 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7134 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 97, targets := 4 },{ cop := 1, region := 80, targets := 32 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 134 261 25 84 96 66 168 296), lower := (rows 35 134 261 25 84 96 66 128 256), losses := [] }

theorem u7134 : Upper (D 6) (R 6) [34,132,257,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7135 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 261 25 84 96 72 162 290), lower := (rows 35 134 261 25 84 96 72 128 256), losses := [] }

theorem u7135 : Upper (D 6) (R 6) [34,132,257,17,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7135 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7136 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 261 25 84 96 96 138 266), lower := (rows 35 134 261 25 84 96 96 128 256), losses := [] }

theorem u7136 : Upper (D 6) (R 6) [34,132,257,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7137 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 2, region := 112, targets := 2 }], pairs := [(0,2),(1,5),(4,1)], upper := (rows 35 134 261 26 52 96 65 200 328), lower := (rows 35 134 261 26 52 96 65 128 256), losses := [{ target := 5, region := (rows 1 18 4 24 16 0 69 144 272), good := (rows 67 198 325 410 478 64 65 128 256) }] }

theorem u7137 : Upper (D 6) (R 6) [34,132,257,18,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7138 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 134 261 26 52 96 72 193 321), lower := (rows 35 134 261 26 52 96 72 128 256), losses := [] }

theorem u7138 : Upper (D 6) (R 6) [34,132,257,18,36,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7138 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7139 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 80, targets := 2 },{ cop := 2, region := 80, targets := 32 }], pairs := [(0,2),(4,1),(4,5)], upper := (rows 35 134 261 26 81 96 68 168 296), lower := (rows 35 134 261 26 81 96 68 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 112 64 136 264), good := (rows 35 130 257 443 113 96 96 128 256) }] }

theorem u7139 : Upper (D 6) (R 6) [34,132,257,18,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7139
end Delivery.IrregularNine14.P06
