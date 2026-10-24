import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0100

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20100 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 152 273 96 71 135 263), lower := (rows 35 70 44 152 273 96 64 128 256), losses := [] }

theorem u20100 : Upper (D 6) (R 6) [34,68,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20101 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 44 152 274 33 69 197 325), lower := (rows 35 70 44 152 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 128 256), good := (rows 35 39 44 189 307 33 0 128 256) }] }

theorem u20101 : Upper (D 6) (R 6) [34,68,40,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20102 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 152 274 36 65 193 321), lower := (rows 35 70 44 152 274 36 64 128 256), losses := [] }

theorem u20102 : Upper (D 6) (R 6) [34,68,40,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20103 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 152 274 96 69 133 261), lower := (rows 35 70 44 152 274 96 64 128 256), losses := [] }

theorem u20103 : Upper (D 6) (R 6) [34,68,40,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20104 : Route 9 := (fun mask => (mask,id))

def c20104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20104 : Upper (D 6) (R 6) [34,68,40,144,260,1] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,260,1] 13 (by decide) (choices 1) [1,2] r20104 c20104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6000
  · exact u6001

def b20105 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 152 276 34 65 193 321), lower := (rows 35 70 44 152 276 34 64 128 256), losses := [] }

theorem u20105 : Upper (D 6) (R 6) [34,68,40,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20106 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 152 276 96 67 131 259), lower := (rows 35 70 44 152 276 96 64 128 256), losses := [] }

theorem u20106 : Upper (D 6) (R 6) [34,68,40,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20107 : Route 9 := (fun mask => (mask,id))

def c20107 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20107 : Upper (D 6) (R 6) [34,68,40,144,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,320,1] 13 (by decide) (choices 1) [1,2,4] r20107 c20107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6002
  · exact u6003
  · exact u6004

def b20108 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 152 336 34 69 133 261), lower := (rows 35 70 44 152 336 34 64 128 256), losses := [] }

theorem u20108 : Upper (D 6) (R 6) [34,68,40,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20109 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 152 336 36 67 131 259), lower := (rows 35 70 44 152 336 36 64 128 256), losses := [] }

theorem u20109 : Upper (D 6) (R 6) [34,68,40,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20110 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 44 200 273 33 86 150 278), lower := (rows 35 70 44 200 273 33 64 128 256), losses := [] }

theorem u20110 : Upper (D 6) (R 6) [34,68,40,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20111 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 200 273 34 85 149 277), lower := (rows 35 70 44 200 273 34 64 128 256), losses := [] }

theorem u20111 : Upper (D 6) (R 6) [34,68,40,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20112 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 200 273 36 83 147 275), lower := (rows 35 70 44 200 273 36 64 128 256), losses := [] }

theorem u20112 : Upper (D 6) (R 6) [34,68,40,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20113 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 200 273 48 71 135 263), lower := (rows 35 70 44 200 273 48 64 128 256), losses := [] }

theorem u20113 : Upper (D 6) (R 6) [34,68,40,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20113 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20114 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 44 200 274 33 85 149 277), lower := (rows 35 70 44 200 274 33 64 128 256), losses := [] }

theorem u20114 : Upper (D 6) (R 6) [34,68,40,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20115 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 200 274 36 81 145 273), lower := (rows 35 70 44 200 274 36 64 128 256), losses := [] }

theorem u20115 : Upper (D 6) (R 6) [34,68,40,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20116 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 44 200 274 48 69 133 261), lower := (rows 35 70 44 200 274 48 64 128 256), losses := [] }

theorem u20116 : Upper (D 6) (R 6) [34,68,40,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20116 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20117 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 44 200 276 33 83 147 275), lower := (rows 35 70 44 200 276 33 64 128 256), losses := [] }

theorem u20117 : Upper (D 6) (R 6) [34,68,40,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20118 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 200 276 34 81 145 273), lower := (rows 35 70 44 200 276 34 64 128 256), losses := [] }

theorem u20118 : Upper (D 6) (R 6) [34,68,40,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20119 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 200, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 200 276 48 67 131 259), lower := (rows 35 70 44 200 276 48 64 128 256), losses := [] }

theorem u20119 : Upper (D 6) (R 6) [34,68,40,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20119 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20120 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 44 392 21 33 82 210 338), lower := (rows 35 70 44 392 21 33 64 128 256), losses := [] }

theorem u20120 : Upper (D 6) (R 6) [34,68,40,384,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20121 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 392 21 34 81 209 337), lower := (rows 35 70 44 392 21 34 64 128 256), losses := [] }

theorem u20121 : Upper (D 6) (R 6) [34,68,40,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20122 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 456, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 392 21 48 67 195 323), lower := (rows 35 70 44 392 21 48 64 128 256), losses := [] }

theorem u20122 : Upper (D 6) (R 6) [34,68,40,384,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20122 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20123 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 392 21 96 83 147 275), lower := (rows 35 70 44 392 21 96 64 128 256), losses := [] }

theorem u20123 : Upper (D 6) (R 6) [34,68,40,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20124 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 44 392 81 33 86 150 278), lower := (rows 35 70 44 392 81 33 64 128 256), losses := [] }

theorem u20124 : Upper (D 6) (R 6) [34,68,40,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20125 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 392 81 34 85 149 277), lower := (rows 35 70 44 392 81 34 64 128 256), losses := [] }

theorem u20125 : Upper (D 6) (R 6) [34,68,40,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20126 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 392 81 36 83 147 275), lower := (rows 35 70 44 392 81 36 64 128 256), losses := [] }

theorem u20126 : Upper (D 6) (R 6) [34,68,40,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20127 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 392 81 48 71 135 263), lower := (rows 35 70 44 392 81 48 64 128 256), losses := [] }

theorem u20127 : Upper (D 6) (R 6) [34,68,40,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20127 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20128 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 52 34 328 456 328), lower := (rows 35 70 133 25 52 34 64 128 256), losses := [] }

theorem u20128 : Upper (D 6) (R 6) [34,68,129,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20129 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 35 70 133 25 52 40 322 450 322), lower := (rows 35 70 133 25 52 40 64 128 256), losses := [] }

theorem u20129 : Upper (D 6) (R 6) [34,68,129,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20129 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20130 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 52 96 330 394 266), lower := (rows 35 70 133 25 52 96 64 128 256), losses := [] }

theorem u20130 : Upper (D 6) (R 6) [34,68,129,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20131 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 25 52 288 74 202 330), lower := (rows 35 70 133 25 52 288 64 128 256), losses := [] }

theorem u20131 : Upper (D 6) (R 6) [34,68,129,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20131 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20132 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 112 34 332 396 268), lower := (rows 35 70 133 25 112 34 64 128 256), losses := [] }

theorem u20132 : Upper (D 6) (R 6) [34,68,129,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20133 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 70 133 25 112 36 330 394 266), lower := (rows 35 70 133 25 112 36 64 128 256), losses := [] }

theorem u20133 : Upper (D 6) (R 6) [34,68,129,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20134 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 133 25 112 40 326 390 262), lower := (rows 35 70 133 25 112 40 64 128 256), losses := [] }

theorem u20134 : Upper (D 6) (R 6) [34,68,129,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20134 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20135 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 25 112 288 78 142 270), lower := (rows 35 70 133 25 112 288 64 128 256), losses := [] }

theorem u20135 : Upper (D 6) (R 6) [34,68,129,17,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20135 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20136 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 25 274 36 104 232 360), lower := (rows 35 70 133 25 274 36 64 128 256), losses := [] }

theorem u20136 : Upper (D 6) (R 6) [34,68,129,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20137 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 70 133 25 274 40 100 228 356), lower := (rows 35 70 133 25 274 40 64 128 256), losses := [] }

theorem u20137 : Upper (D 6) (R 6) [34,68,129,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20137 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20138 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 274 96 108 172 300), lower := (rows 35 70 133 25 274 96 64 128 256), losses := [] }

theorem u20138 : Upper (D 6) (R 6) [34,68,129,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20139 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 276 34 104 232 360), lower := (rows 35 70 133 25 276 34 64 128 256), losses := [] }

theorem u20139 : Upper (D 6) (R 6) [34,68,129,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20140 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(4,0)], upper := (rows 35 70 133 25 276 40 98 226 354), lower := (rows 35 70 133 25 276 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 40 65 129 257), good := (rows 482 86 470 504 278 40 64 128 256) }] }

theorem u20140 : Upper (D 6) (R 6) [34,68,129,17,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20140 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20141 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 276 96 106 170 298), lower := (rows 35 70 133 25 276 96 64 128 256), losses := [] }

theorem u20141 : Upper (D 6) (R 6) [34,68,129,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20142 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 280 34 100 228 356), lower := (rows 35 70 133 25 280 34 64 128 256), losses := [] }

theorem u20142 : Upper (D 6) (R 6) [34,68,129,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20143 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 25 280 36 98 226 354), lower := (rows 35 70 133 25 280 36 64 128 256), losses := [] }

theorem u20143 : Upper (D 6) (R 6) [34,68,129,17,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20144 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 280 96 102 166 294), lower := (rows 35 70 133 25 280 96 64 128 256), losses := [] }

theorem u20144 : Upper (D 6) (R 6) [34,68,129,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20145 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 304 34 76 204 332), lower := (rows 35 70 133 25 304 34 64 128 256), losses := [] }

theorem u20145 : Upper (D 6) (R 6) [34,68,129,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20146 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 70 133 25 304 36 74 202 330), lower := (rows 35 70 133 25 304 36 64 128 256), losses := [] }

theorem u20146 : Upper (D 6) (R 6) [34,68,129,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20147 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 25 304 40 70 198 326), lower := (rows 35 70 133 25 304 40 64 128 256), losses := [] }

theorem u20147 : Upper (D 6) (R 6) [34,68,129,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20147 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20148 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 304 96 78 142 270), lower := (rows 35 70 133 25 304 96 64 128 256), losses := [] }

theorem u20148 : Upper (D 6) (R 6) [34,68,129,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20149 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 336 34 108 172 300), lower := (rows 35 70 133 25 336 34 64 128 256), losses := [] }

theorem u20149 : Upper (D 6) (R 6) [34,68,129,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20150 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 25 336 36 106 170 298), lower := (rows 35 70 133 25 336 36 64 128 256), losses := [] }

theorem u20150 : Upper (D 6) (R 6) [34,68,129,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20151 : Route 9 := (fun mask => (mask,id))

def c20151 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20151 : Upper (D 6) (R 6) [34,68,129,17,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,320,8] 13 (by decide) (choices 1) [2,4,32] r20151 c20151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6005
  · exact u6006
  · exact u6007

def b20152 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 133 26 52 33 328 456 328), lower := (rows 35 70 133 26 52 33 64 128 256), losses := [] }

theorem u20152 : Upper (D 6) (R 6) [34,68,129,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20153 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 133 26 52 40 321 449 321), lower := (rows 35 70 133 26 52 40 64 128 256), losses := [] }

theorem u20153 : Upper (D 6) (R 6) [34,68,129,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20153 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20154 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 52 96 329 393 265), lower := (rows 35 70 133 26 52 96 64 128 256), losses := [] }

theorem u20154 : Upper (D 6) (R 6) [34,68,129,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20155 : Route 9 := (fun mask => (mask,id))

def c20155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20155 : Upper (D 6) (R 6) [34,68,129,18,36,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,36,256] 13 (by decide) (choices 1) [1,8] r20155 c20155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6008
  · exact u6009

def b20156 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 26 81 36 360 424 296), lower := (rows 35 70 133 26 81 36 64 128 256), losses := [] }

theorem u20156 : Upper (D 6) (R 6) [34,68,129,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20157 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 133 26 81 40 356 420 292), lower := (rows 35 70 133 26 81 40 64 128 256), losses := [] }

theorem u20157 : Upper (D 6) (R 6) [34,68,129,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20157 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20158 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 26 81 288 108 172 300), lower := (rows 35 70 133 26 81 288 64 128 256), losses := [] }

theorem u20158 : Upper (D 6) (R 6) [34,68,129,18,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20158 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20159 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 133 26 112 33 332 396 268), lower := (rows 35 70 133 26 112 33 64 128 256), losses := [] }

theorem u20159 : Upper (D 6) (R 6) [34,68,129,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20159
end Delivery.IrregularNine14.P06
