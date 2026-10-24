import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0118

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23100 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 280 112 34 69 133 261), lower := (rows 35 134 76 280 112 34 64 128 256), losses := [] }

theorem u23100 : Upper (D 6) (R 6) [34,132,72,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23101 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 134 76 280 112 36 67 131 259), lower := (rows 35 134 76 280 112 36 64 128 256), losses := [] }

theorem u23101 : Upper (D 6) (R 6) [34,132,72,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23102 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 134 76 296 21 33 82 210 338), lower := (rows 35 134 76 296 21 33 64 128 256), losses := [] }

theorem u23102 : Upper (D 6) (R 6) [34,132,72,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23103 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 296 21 34 81 209 337), lower := (rows 35 134 76 296 21 34 64 128 256), losses := [] }

theorem u23103 : Upper (D 6) (R 6) [34,132,72,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23104 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 134 76 296 21 48 67 195 323), lower := (rows 35 134 76 296 21 48 64 128 256), losses := [] }

theorem u23104 : Upper (D 6) (R 6) [34,132,72,288,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23104 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23105 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 130, targets := 32 },{ cop := 4, region := 130, targets := 64 }], pairs := [(0,2),(1,5),(1,6)], upper := (rows 35 134 76 296 21 96 83 147 275), lower := (rows 35 134 76 296 21 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 100 64 128 256), good := (rows 35 163 104 296 49 96 96 128 256) }] }

theorem u23105 : Upper (D 6) (R 6) [34,132,72,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23106 : Route 9 := (fun mask => (mask,id))

def c23106 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23106 : Upper (D 6) (R 6) [34,132,72,288,65,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,288,65,1] 13 (by decide) (choices 1) [2,4,16] r23106 c23106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7080
  · exact u7081
  · exact u7082

def b23107 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 296 81 34 85 149 277), lower := (rows 35 134 76 296 81 34 64 128 256), losses := [] }

theorem u23107 : Upper (D 6) (R 6) [34,132,72,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23108 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 134 76 296 81 36 83 147 275), lower := (rows 35 134 76 296 81 36 64 128 256), losses := [] }

theorem u23108 : Upper (D 6) (R 6) [34,132,72,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23109 : Route 9 := (fun mask => (mask,id))

def c23109 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23109 : Upper (D 6) (R 6) [34,132,72,288,65,16] 13 := by
  apply FastRouting.sound _ _ [34,132,72,288,65,16] 13 (by decide) (choices 1) [1,2,4] r23109 c23109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7083
  · exact u7084
  · exact u7085

def r23110 : Route 9 := (fun mask => (mask,id))

def c23110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23110 : Upper (D 6) (R 6) [34,132,72,288,66,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,288,66,1] 13 (by decide) (choices 1) [1,4,16] r23110 c23110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7086
  · exact u7087
  · exact u7088

def b23111 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 134 76 296 82 36 81 145 273), lower := (rows 35 134 76 296 82 36 64 128 256), losses := [] }

theorem u23111 : Upper (D 6) (R 6) [34,132,72,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23112 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 76 296 82 48 69 133 261), lower := (rows 35 134 76 296 82 48 64 128 256), losses := [] }

theorem u23112 : Upper (D 6) (R 6) [34,132,72,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23112 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23113 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 13 81 34 344 408 280), lower := (rows 35 134 100 13 81 34 64 128 256), losses := [] }

theorem u23113 : Upper (D 6) (R 6) [34,132,96,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23114 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 100 13 81 40 338 402 274), lower := (rows 35 134 100 13 81 40 64 128 256), losses := [] }

theorem u23114 : Upper (D 6) (R 6) [34,132,96,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23114 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23115 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 13 81 48 330 394 266), lower := (rows 35 134 100 13 81 48 64 128 256), losses := [] }

theorem u23115 : Upper (D 6) (R 6) [34,132,96,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23115 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23116 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 134 100 13 81 288 90 154 282), lower := (rows 35 134 100 13 81 288 64 128 256), losses := [] }

theorem u23116 : Upper (D 6) (R 6) [34,132,96,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23116 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23117 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 100 13 82 33 344 408 280), lower := (rows 35 134 100 13 82 33 64 128 256), losses := [] }

theorem u23117 : Upper (D 6) (R 6) [34,132,96,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23118 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 100 13 82 40 337 401 273), lower := (rows 35 134 100 13 82 40 64 128 256), losses := [] }

theorem u23118 : Upper (D 6) (R 6) [34,132,96,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23118 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23119 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 13 82 48 329 393 265), lower := (rows 35 134 100 13 82 48 64 128 256), losses := [] }

theorem u23119 : Upper (D 6) (R 6) [34,132,96,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23119 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23120 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 134 100 13 82 288 89 153 281), lower := (rows 35 134 100 13 82 288 64 128 256), losses := [] }

theorem u23120 : Upper (D 6) (R 6) [34,132,96,5,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23120 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23121 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 100 13 88 33 338 402 274), lower := (rows 35 134 100 13 88 33 64 128 256), losses := [] }

theorem u23121 : Upper (D 6) (R 6) [34,132,96,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23122 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 13 88 34 337 401 273), lower := (rows 35 134 100 13 88 34 64 128 256), losses := [] }

theorem u23122 : Upper (D 6) (R 6) [34,132,96,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23123 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 13 88 48 323 387 259), lower := (rows 35 134 100 13 88 48 64 128 256), losses := [] }

theorem u23123 : Upper (D 6) (R 6) [34,132,96,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23123 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23124 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 134 100 13 88 288 83 147 275), lower := (rows 35 134 100 13 88 288 64 128 256), losses := [] }

theorem u23124 : Upper (D 6) (R 6) [34,132,96,5,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23124 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23125 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 13 273 34 88 216 344), lower := (rows 35 134 100 13 273 34 64 128 256), losses := [] }

theorem u23125 : Upper (D 6) (R 6) [34,132,96,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23126 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 100 13 273 40 82 210 338), lower := (rows 35 134 100 13 273 40 64 128 256), losses := [] }

theorem u23126 : Upper (D 6) (R 6) [34,132,96,5,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23126 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23127 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 134 100 13 273 48 74 202 330), lower := (rows 35 134 100 13 273 48 64 128 256), losses := [] }

theorem u23127 : Upper (D 6) (R 6) [34,132,96,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23127 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23128 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 13 273 96 90 154 282), lower := (rows 35 134 100 13 273 96 64 128 256), losses := [] }

theorem u23128 : Upper (D 6) (R 6) [34,132,96,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23129 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 100 13 274 33 88 216 344), lower := (rows 35 134 100 13 274 33 64 128 256), losses := [] }

theorem u23129 : Upper (D 6) (R 6) [34,132,96,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23130 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 100 13 274 40 81 209 337), lower := (rows 35 134 100 13 274 40 64 128 256), losses := [] }

theorem u23130 : Upper (D 6) (R 6) [34,132,96,5,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23130 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23131 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 100 13 274 48 73 201 329), lower := (rows 35 134 100 13 274 48 64 128 256), losses := [] }

theorem u23131 : Upper (D 6) (R 6) [34,132,96,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23131 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23132 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 13 274 96 89 153 281), lower := (rows 35 134 100 13 274 96 64 128 256), losses := [] }

theorem u23132 : Upper (D 6) (R 6) [34,132,96,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23133 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 100 13 280 33 82 210 338), lower := (rows 35 134 100 13 280 33 64 128 256), losses := [] }

theorem u23133 : Upper (D 6) (R 6) [34,132,96,5,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23134 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 13 280 34 81 209 337), lower := (rows 35 134 100 13 280 34 64 128 256), losses := [] }

theorem u23134 : Upper (D 6) (R 6) [34,132,96,5,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23135 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 134 100 13 280 48 67 195 323), lower := (rows 35 134 100 13 280 48 64 128 256), losses := [] }

theorem u23135 : Upper (D 6) (R 6) [34,132,96,5,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23135 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23136 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 13 280 96 83 147 275), lower := (rows 35 134 100 13 280 96 64 128 256), losses := [] }

theorem u23136 : Upper (D 6) (R 6) [34,132,96,5,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23137 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 100 13 336 33 90 154 282), lower := (rows 35 134 100 13 336 33 64 128 256), losses := [] }

theorem u23137 : Upper (D 6) (R 6) [34,132,96,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23138 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 13 336 34 89 153 281), lower := (rows 35 134 100 13 336 34 64 128 256), losses := [] }

theorem u23138 : Upper (D 6) (R 6) [34,132,96,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23139 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 100 13 336 40 83 147 275), lower := (rows 35 134 100 13 336 40 64 128 256), losses := [] }

theorem u23139 : Upper (D 6) (R 6) [34,132,96,5,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23139 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23140 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 13 336 48 75 139 267), lower := (rows 35 134 100 13 336 48 64 128 256), losses := [] }

theorem u23140 : Upper (D 6) (R 6) [34,132,96,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23140 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23141 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 100 25 28 33 322 450 322), lower := (rows 35 134 100 25 28 33 64 128 256), losses := [] }

theorem u23141 : Upper (D 6) (R 6) [34,132,96,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23142 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 25 28 34 321 449 321), lower := (rows 35 134 100 25 28 34 64 128 256), losses := [] }

theorem u23142 : Upper (D 6) (R 6) [34,132,96,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23143 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 25 28 96 323 387 259), lower := (rows 35 134 100 25 28 96 64 128 256), losses := [] }

theorem u23143 : Upper (D 6) (R 6) [34,132,96,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23144 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(1,5)], upper := (rows 35 134 100 25 28 288 67 195 323), lower := (rows 35 134 100 25 28 288 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 73 137 265), good := (rows 451 134 68 475 478 256 64 128 256) }] }

theorem u23144 : Upper (D 6) (R 6) [34,132,96,17,12,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23144 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23145 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 100 25 82 33 332 396 268), lower := (rows 35 134 100 25 82 33 64 128 256), losses := [] }

theorem u23145 : Upper (D 6) (R 6) [34,132,96,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23146 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 25 82 36 329 393 265), lower := (rows 35 134 100 25 82 36 64 128 256), losses := [] }

theorem u23146 : Upper (D 6) (R 6) [34,132,96,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23147 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 100 25 82 40 325 389 261), lower := (rows 35 134 100 25 82 40 64 128 256), losses := [] }

theorem u23147 : Upper (D 6) (R 6) [34,132,96,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23147 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23148 : Route 9 := (fun mask => (mask,id))

def c23148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23148 : Upper (D 6) (R 6) [34,132,96,17,66,256] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,66,256] 13 (by decide) (choices 1) [1,4,8] r23148 c23148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7089
  · exact u7090
  · exact u7091

def b23149 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,0),(2,0)], upper := (rows 35 134 100 25 88 33 326 390 262), lower := (rows 35 134 100 25 88 33 64 128 256), losses := [] }

theorem u23149 : Upper (D 6) (R 6) [34,132,96,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23150 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 25 88 34 325 389 261), lower := (rows 35 134 100 25 88 34 64 128 256), losses := [] }

theorem u23150 : Upper (D 6) (R 6) [34,132,96,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23151 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 25 88 36 323 387 259), lower := (rows 35 134 100 25 88 36 64 128 256), losses := [] }

theorem u23151 : Upper (D 6) (R 6) [34,132,96,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23152 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 25 88 288 71 135 263), lower := (rows 35 134 100 25 88 288 64 128 256), losses := [] }

theorem u23152 : Upper (D 6) (R 6) [34,132,96,17,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23152 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23153 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 100 25 274 33 76 204 332), lower := (rows 35 134 100 25 274 33 64 128 256), losses := [] }

theorem u23153 : Upper (D 6) (R 6) [34,132,96,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23154 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 25 274 36 73 201 329), lower := (rows 35 134 100 25 274 36 64 128 256), losses := [] }

theorem u23154 : Upper (D 6) (R 6) [34,132,96,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23155 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 100 25 274 40 69 197 325), lower := (rows 35 134 100 25 274 40 64 128 256), losses := [] }

theorem u23155 : Upper (D 6) (R 6) [34,132,96,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23155 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23156 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 25 274 96 77 141 269), lower := (rows 35 134 100 25 274 96 64 128 256), losses := [] }

theorem u23156 : Upper (D 6) (R 6) [34,132,96,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23157 : Route 9 := (fun mask => (mask,id))

def c23157 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23157 : Upper (D 6) (R 6) [34,132,96,17,260,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,260,1] 13 (by decide) (choices 1) [2,8] r23157 c23157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7092
  · exact u7093

def b23158 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 25 276 34 73 201 329), lower := (rows 35 134 100 25 276 34 64 128 256), losses := [] }

theorem u23158 : Upper (D 6) (R 6) [34,132,96,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23159 : Route 9 := (fun mask => (mask,id))

def c23159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23159 : Upper (D 6) (R 6) [34,132,96,17,260,8] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,260,8] 13 (by decide) (choices 1) [1,2] r23159 c23159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7094
  · exact u7095

#print axioms u23159
end Delivery.IrregularNine14.P06
