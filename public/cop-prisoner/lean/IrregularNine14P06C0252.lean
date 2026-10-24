import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0057
import IrregularNine14P06C0058

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15120 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 88 273 33 70 134 262), lower := (rows 11 98 164 88 273 33 64 128 256), losses := [] }

theorem u15120 : Upper (D 6) (R 6) [10,96,160,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15121 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 88 273 34 69 133 261), lower := (rows 11 98 164 88 273 34 64 128 256), losses := [] }

theorem u15121 : Upper (D 6) (R 6) [10,96,160,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15122 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 88 273 36 71 135 263), lower := (rows 11 98 164 88 273 36 64 128 256), losses := [] }

theorem u15122 : Upper (D 6) (R 6) [10,96,160,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15123 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 88 276 33 71 135 263), lower := (rows 11 98 164 88 276 33 64 128 256), losses := [] }

theorem u15123 : Upper (D 6) (R 6) [10,96,160,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15124 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 88 276 34 69 133 261), lower := (rows 11 98 164 88 276 34 64 128 256), losses := [] }

theorem u15124 : Upper (D 6) (R 6) [10,96,160,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15125 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 88 276 36 67 131 259), lower := (rows 11 98 164 88 276 36 64 128 256), losses := [] }

theorem u15125 : Upper (D 6) (R 6) [10,96,160,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15126 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 328, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 98 164 265 21 34 84 212 340), lower := (rows 11 98 164 265 21 34 64 128 256), losses := [] }

theorem u15126 : Upper (D 6) (R 6) [10,96,160,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15127 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 265 21 36 82 210 338), lower := (rows 11 98 164 265 21 36 64 128 256), losses := [] }

theorem u15127 : Upper (D 6) (R 6) [10,96,160,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15128 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 164 265 21 48 70 198 326), lower := (rows 11 98 164 265 21 48 64 128 256), losses := [] }

theorem u15128 : Upper (D 6) (R 6) [10,96,160,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15128 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15129 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 265 21 96 86 150 278), lower := (rows 11 98 164 265 21 96 64 128 256), losses := [] }

theorem u15129 : Upper (D 6) (R 6) [10,96,160,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15130 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 164 265 22 33 84 212 340), lower := (rows 11 98 164 265 22 33 64 128 256), losses := [] }

theorem u15130 : Upper (D 6) (R 6) [10,96,160,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15131 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 164 265 22 36 81 209 337), lower := (rows 11 98 164 265 22 36 64 128 256), losses := [] }

theorem u15131 : Upper (D 6) (R 6) [10,96,160,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15132 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 98 164 265 22 48 69 197 325), lower := (rows 11 98 164 265 22 48 64 128 256), losses := [] }

theorem u15132 : Upper (D 6) (R 6) [10,96,160,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15132 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15133 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 265 22 96 85 149 277), lower := (rows 11 98 164 265 22 96 64 128 256), losses := [] }

theorem u15133 : Upper (D 6) (R 6) [10,96,160,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15134 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 164 265 81 34 84 148 276), lower := (rows 11 98 164 265 81 34 64 128 256), losses := [] }

theorem u15134 : Upper (D 6) (R 6) [10,96,160,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15135 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 265 81 36 86 150 278), lower := (rows 11 98 164 265 81 36 64 128 256), losses := [] }

theorem u15135 : Upper (D 6) (R 6) [10,96,160,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15136 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 265 81 48 70 134 262), lower := (rows 11 98 164 265 81 48 64 128 256), losses := [] }

theorem u15136 : Upper (D 6) (R 6) [10,96,160,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15136 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15137 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 164 265 84 33 86 150 278), lower := (rows 11 98 164 265 84 33 64 128 256), losses := [] }

theorem u15137 : Upper (D 6) (R 6) [10,96,160,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15138 : Route 9 := (fun mask => (mask,id))

def c15138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15138 : Upper (D 6) (R 6) [10,96,160,257,68,2] 13 := by
  apply FastRouting.sound _ _ [10,96,160,257,68,2] 13 (by decide) (choices 1) [1,4,16] r15138 c15138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3470
  · exact u3471
  · exact u3472

def b15139 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 265 84 36 83 147 275), lower := (rows 11 98 164 265 84 36 64 128 256), losses := [] }

theorem u15139 : Upper (D 6) (R 6) [10,96,160,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15140 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 265 84 48 71 135 263), lower := (rows 11 98 164 265 84 48 64 128 256), losses := [] }

theorem u15140 : Upper (D 6) (R 6) [10,96,160,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15140 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15141 : Route 9 := (fun mask => (mask,id))

def c15141 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15141 : Upper (D 6) (R 6) [10,96,160,260,5,1] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,5,1] 13 (by decide) (choices 1) [2,16] r15141 c15141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3473
  · exact u3474

def b15142 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 328, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 11 98 164 268 21 34 81 209 337), lower := (rows 11 98 164 268 21 34 64 128 256), losses := [] }

theorem u15142 : Upper (D 6) (R 6) [10,96,160,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15143 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(3,5)], upper := (rows 11 98 164 268 21 48 67 195 323), lower := (rows 11 98 164 268 21 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 65 129 257), good := (rows 459 66 132 268 477 24 64 128 256) }] }

theorem u15143 : Upper (D 6) (R 6) [10,96,160,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15143 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15144 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 268 21 96 83 147 275), lower := (rows 11 98 164 268 21 96 64 128 256), losses := [] }

theorem u15144 : Upper (D 6) (R 6) [10,96,160,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15145 : Route 9 := (fun mask => (mask,id))

def c15145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15145 : Upper (D 6) (R 6) [10,96,160,260,6,1] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,6,1] 13 (by decide) (choices 1) [1,16] r15145 c15145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3475
  · exact u3476

def b15146 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 98 164 268 22 48 65 193 321), lower := (rows 11 98 164 268 22 48 64 128 256), losses := [] }

theorem u15146 : Upper (D 6) (R 6) [10,96,160,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15146 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15147 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 268 22 96 81 145 273), lower := (rows 11 98 164 268 22 96 64 128 256), losses := [] }

theorem u15147 : Upper (D 6) (R 6) [10,96,160,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15148 : Route 9 := (fun mask => (mask,id))

def c15148 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15148 : Upper (D 6) (R 6) [10,96,160,260,65,1] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,65,1] 13 (by decide) (choices 1) [2,4,16] r15148 c15148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3477
  · exact u3478
  · exact u3479

def b15149 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(2,6)], upper := (rows 11 98 164 268 81 34 85 149 277), lower := (rows 11 98 164 268 81 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 144 272), good := (rows 43 34 164 268 445 34 0 128 256) }] }

theorem u15149 : Upper (D 6) (R 6) [10,96,160,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15150 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 268 81 36 83 147 275), lower := (rows 11 98 164 268 81 36 64 128 256), losses := [] }

theorem u15150 : Upper (D 6) (R 6) [10,96,160,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15151 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 268 81 48 71 135 263), lower := (rows 11 98 164 268 81 48 64 128 256), losses := [] }

theorem u15151 : Upper (D 6) (R 6) [10,96,160,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15151 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15152 : Route 9 := (fun mask => (mask,id))

def c15152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15152 : Upper (D 6) (R 6) [10,96,160,260,68,1] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,68,1] 13 (by decide) (choices 1) [1,2,16] r15152 c15152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3480
  · exact u3481
  · exact u3482

def r15153 : Route 9 := (fun mask => (mask,id))

def c15153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15153 : Upper (D 6) (R 6) [10,96,160,260,68,2] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260,68,2] 13 (by decide) (choices 1) [1,16] r15153 c15153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3483
  · exact u3484

def b15154 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 268 84 48 67 131 259), lower := (rows 11 98 164 268 84 48 64 128 256), losses := [] }

theorem u15154 : Upper (D 6) (R 6) [10,96,160,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15154 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15155 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 98 164 280 21 33 70 198 326), lower := (rows 11 98 164 280 21 33 64 128 256), losses := [{ target := 0, region := (rows 0 38 38 24 16 32 119 183 311), good := (rows 462 486 486 472 478 486 64 128 256) }] }

theorem u15155 : Upper (D 6) (R 6) [10,96,160,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15156 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 328, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 11 98 164 280 21 34 69 197 325), lower := (rows 11 98 164 280 21 34 64 128 256), losses := [] }

theorem u15156 : Upper (D 6) (R 6) [10,96,160,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15157 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 280 21 36 67 195 323), lower := (rows 11 98 164 280 21 36 64 128 256), losses := [] }

theorem u15157 : Upper (D 6) (R 6) [10,96,160,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15158 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 280 21 96 71 135 263), lower := (rows 11 98 164 280 21 96 64 128 256), losses := [] }

theorem u15158 : Upper (D 6) (R 6) [10,96,160,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15159 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 0, region := 164, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 98 164 280 81 33 70 134 262), lower := (rows 11 98 164 280 81 33 64 128 256), losses := [] }

theorem u15159 : Upper (D 6) (R 6) [10,96,160,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15160 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 0, region := 164, targets := 64 }], pairs := [(1,0),(1,2),(2,6)], upper := (rows 11 98 164 280 81 34 69 133 261), lower := (rows 11 98 164 280 81 34 64 128 256), losses := [] }

theorem u15160 : Upper (D 6) (R 6) [10,96,160,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15161 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 280 81 36 71 135 263), lower := (rows 11 98 164 280 81 36 64 128 256), losses := [] }

theorem u15161 : Upper (D 6) (R 6) [10,96,160,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15162 : Route 9 := (fun mask => (mask,id))

def c15162 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15162 : Upper (D 6) (R 6) [10,96,160,272,68,1] 13 := by
  apply FastRouting.sound _ _ [10,96,160,272,68,1] 13 (by decide) (choices 1) [1,2,4] r15162 c15162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3485
  · exact u3486
  · exact u3487

def b15163 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 0, region := 164, targets := 64 }], pairs := [(1,0),(1,2),(2,6)], upper := (rows 11 98 164 280 84 34 69 133 261), lower := (rows 11 98 164 280 84 34 64 128 256), losses := [] }

theorem u15163 : Upper (D 6) (R 6) [10,96,160,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15164 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 280 84 36 67 131 259), lower := (rows 11 98 164 280 84 36 64 128 256), losses := [] }

theorem u15164 : Upper (D 6) (R 6) [10,96,160,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15165 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 180, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 328 21 33 86 150 278), lower := (rows 11 98 164 328 21 33 64 128 256), losses := [] }

theorem u15165 : Upper (D 6) (R 6) [10,96,160,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15166 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 180, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 328 21 34 85 149 277), lower := (rows 11 98 164 328 21 34 64 128 256), losses := [] }

theorem u15166 : Upper (D 6) (R 6) [10,96,160,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15167 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 328 21 36 83 147 275), lower := (rows 11 98 164 328 21 36 64 128 256), losses := [] }

theorem u15167 : Upper (D 6) (R 6) [10,96,160,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15168 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 164 328 21 48 71 135 263), lower := (rows 11 98 164 328 21 48 64 128 256), losses := [] }

theorem u15168 : Upper (D 6) (R 6) [10,96,160,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15168 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15169 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 98 388 13 49 34 84 212 340), lower := (rows 11 98 388 13 49 34 64 128 256), losses := [] }

theorem u15169 : Upper (D 6) (R 6) [10,96,384,5,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15170 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 98 388 13 49 36 82 210 338), lower := (rows 11 98 388 13 49 36 64 128 256), losses := [] }

theorem u15170 : Upper (D 6) (R 6) [10,96,384,5,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15171 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 98 388 13 49 48 70 198 326), lower := (rows 11 98 388 13 49 48 64 128 256), losses := [] }

theorem u15171 : Upper (D 6) (R 6) [10,96,384,5,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15171 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15172 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 388 13 49 96 86 150 278), lower := (rows 11 98 388 13 49 96 64 128 256), losses := [] }

theorem u15172 : Upper (D 6) (R 6) [10,96,384,5,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15173 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 388 13 52 33 82 210 338), lower := (rows 11 98 388 13 52 33 64 128 256), losses := [] }

theorem u15173 : Upper (D 6) (R 6) [10,96,384,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15174 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 98 388 13 52 34 81 209 337), lower := (rows 11 98 388 13 52 34 64 128 256), losses := [{ target := 0, region := (rows 0 66 4 8 24 99 64 128 256), good := (rows 58 98 388 60 52 34 98 128 256) }] }

theorem u15174 : Upper (D 6) (R 6) [10,96,384,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15175 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 98 388 13 52 48 67 195 323), lower := (rows 11 98 388 13 52 48 64 128 256), losses := [] }

theorem u15175 : Upper (D 6) (R 6) [10,96,384,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15175 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15176 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 388 13 52 96 83 147 275), lower := (rows 11 98 388 13 52 96 64 128 256), losses := [] }

theorem u15176 : Upper (D 6) (R 6) [10,96,384,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15177 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 388 25 52 33 70 198 326), lower := (rows 11 98 388 25 52 33 64 128 256), losses := [] }

theorem u15177 : Upper (D 6) (R 6) [10,96,384,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15178 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 98 388 25 52 34 69 197 325), lower := (rows 11 98 388 25 52 34 64 128 256), losses := [] }

theorem u15178 : Upper (D 6) (R 6) [10,96,384,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15179 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 98 388 25 52 36 67 195 323), lower := (rows 11 98 388 25 52 36 64 128 256), losses := [] }

theorem u15179 : Upper (D 6) (R 6) [10,96,384,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15179
end Delivery.IrregularNine14.P06
