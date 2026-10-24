import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0104

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21120 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 133 268 81 48 102 166 294), lower := (rows 35 74 133 268 81 48 64 128 256), losses := [] }

theorem u21120 : Upper (D 6) (R 6) [34,72,129,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21120 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21121 : Route 9 := (fun mask => (mask,id))

def c21121 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21121 : Upper (D 6) (R 6) [34,72,129,260,68,1] 13 := by
  apply FastRouting.sound _ _ [34,72,129,260,68,1] 13 (by decide) (choices 1) [2,16,32] r21121 c21121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6252
  · exact u6253
  · exact u6254

def b21122 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 268 84 34 113 177 305), lower := (rows 35 74 133 268 84 34 64 128 256), losses := [] }

theorem u21122 : Upper (D 6) (R 6) [34,72,129,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21123 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 133 268 84 48 99 163 291), lower := (rows 35 74 133 268 84 48 64 128 256), losses := [] }

theorem u21123 : Upper (D 6) (R 6) [34,72,129,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21123 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21124 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 133 268 112 33 86 150 278), lower := (rows 35 74 133 268 112 33 64 128 256), losses := [] }

theorem u21124 : Upper (D 6) (R 6) [34,72,129,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21125 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 268 112 34 85 149 277), lower := (rows 35 74 133 268 112 34 64 128 256), losses := [] }

theorem u21125 : Upper (D 6) (R 6) [34,72,129,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21126 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 80, targets := 4 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 74 133 268 112 36 83 147 275), lower := (rows 35 74 133 268 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 44 64 128 256), good := (rows 50 122 164 300 112 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 18 44 64 128 256), good := (rows 49 120 165 300 112 36 64 128 256) }] }

theorem u21126 : Upper (D 6) (R 6) [34,72,129,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21127 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 268 112 48 71 135 263), lower := (rows 35 74 133 268 112 48 64 128 256), losses := [] }

theorem u21127 : Upper (D 6) (R 6) [34,72,129,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21127 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21128 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 74 133 280 22 33 100 228 356), lower := (rows 35 74 133 280 22 33 64 128 256), losses := [] }

theorem u21128 : Upper (D 6) (R 6) [34,72,129,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21129 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 196, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 74 133 280 22 36 97 225 353), lower := (rows 35 74 133 280 22 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 24 16 53 69 133 261), good := (rows 485 72 485 312 508 484 64 128 256) }] }

theorem u21129 : Upper (D 6) (R 6) [34,72,129,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21130 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 280 22 96 101 165 293), lower := (rows 35 74 133 280 22 96 64 128 256), losses := [] }

theorem u21130 : Upper (D 6) (R 6) [34,72,129,272,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21131 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 133 280 52 33 70 198 326), lower := (rows 35 74 133 280 52 33 64 128 256), losses := [] }

theorem u21131 : Upper (D 6) (R 6) [34,72,129,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21132 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 280 52 34 69 197 325), lower := (rows 35 74 133 280 52 34 64 128 256), losses := [] }

theorem u21132 : Upper (D 6) (R 6) [34,72,129,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21133 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 74 133 280 52 36 67 195 323), lower := (rows 35 74 133 280 52 36 64 128 256), losses := [] }

theorem u21133 : Upper (D 6) (R 6) [34,72,129,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21134 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 280 52 96 71 135 263), lower := (rows 35 74 133 280 52 96 64 128 256), losses := [] }

theorem u21134 : Upper (D 6) (R 6) [34,72,129,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21135 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 74 133 280 84 33 102 166 294), lower := (rows 35 74 133 280 84 33 64 128 256), losses := [] }

theorem u21135 : Upper (D 6) (R 6) [34,72,129,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21136 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 280 84 34 101 165 293), lower := (rows 35 74 133 280 84 34 64 128 256), losses := [] }

theorem u21136 : Upper (D 6) (R 6) [34,72,129,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21137 : Route 9 := (fun mask => (mask,id))

def c21137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21137 : Upper (D 6) (R 6) [34,72,129,272,68,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,272,68,4] 13 (by decide) (choices 1) [1,2,32] r21137 c21137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6255
  · exact u6256
  · exact u6257

def b21138 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 133 296 22 33 84 212 340), lower := (rows 35 74 133 296 22 33 64 128 256), losses := [] }

theorem u21138 : Upper (D 6) (R 6) [34,72,129,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21139 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 133 296 22 36 81 209 337), lower := (rows 35 74 133 296 22 36 64 128 256), losses := [] }

theorem u21139 : Upper (D 6) (R 6) [34,72,129,288,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21140 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 133 296 22 48 69 197 325), lower := (rows 35 74 133 296 22 48 64 128 256), losses := [] }

theorem u21140 : Upper (D 6) (R 6) [34,72,129,288,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21140 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21141 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 296 22 96 85 149 277), lower := (rows 35 74 133 296 22 96 64 128 256), losses := [] }

theorem u21141 : Upper (D 6) (R 6) [34,72,129,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21142 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 296 81 34 84 148 276), lower := (rows 35 74 133 296 81 34 64 128 256), losses := [] }

theorem u21142 : Upper (D 6) (R 6) [34,72,129,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21143 : Route 9 := (fun mask => (mask,id))

def c21143 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21143 : Upper (D 6) (R 6) [34,72,129,288,65,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,288,65,4] 13 (by decide) (choices 1) [2,4,16] r21143 c21143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6258
  · exact u6259
  · exact u6260

def b21144 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 133 296 81 48 70 134 262), lower := (rows 35 74 133 296 81 48 64 128 256), losses := [] }

theorem u21144 : Upper (D 6) (R 6) [34,72,129,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21144 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21145 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 133 296 84 33 86 150 278), lower := (rows 35 74 133 296 84 33 64 128 256), losses := [] }

theorem u21145 : Upper (D 6) (R 6) [34,72,129,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21146 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 296 84 34 85 149 277), lower := (rows 35 74 133 296 84 34 64 128 256), losses := [] }

theorem u21146 : Upper (D 6) (R 6) [34,72,129,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21147 : Route 9 := (fun mask => (mask,id))

def c21147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21147 : Upper (D 6) (R 6) [34,72,129,288,68,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,288,68,4] 13 (by decide) (choices 1) [1,2,16] r21147 c21147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6261
  · exact u6262
  · exact u6263

def b21148 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 133 296 84 48 71 135 263), lower := (rows 35 74 133 296 84 48 64 128 256), losses := [] }

theorem u21148 : Upper (D 6) (R 6) [34,72,129,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21148 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21149 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 74 134 13 52 33 336 464 336), lower := (rows 35 74 134 13 52 33 64 128 256), losses := [] }

theorem u21149 : Upper (D 6) (R 6) [34,72,130,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21150 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 134 13 52 48 321 449 321), lower := (rows 35 74 134 13 52 48 64 128 256), losses := [] }

theorem u21150 : Upper (D 6) (R 6) [34,72,130,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21150 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21151 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 13 52 96 337 401 273), lower := (rows 35 74 134 13 52 96 64 128 256), losses := [] }

theorem u21151 : Upper (D 6) (R 6) [34,72,130,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21152 : Route 9 := (fun mask => (mask,id))

def c21152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21152 : Upper (D 6) (R 6) [34,72,130,5,36,256] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,36,256] 13 (by decide) (choices 1) [1,16] r21152 c21152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6264
  · exact u6265

def b21153 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 13 81 36 368 432 304), lower := (rows 35 74 134 13 81 36 64 128 256), losses := [] }

theorem u21153 : Upper (D 6) (R 6) [34,72,130,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21154 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 134 13 81 48 356 420 292), lower := (rows 35 74 134 13 81 48 64 128 256), losses := [] }

theorem u21154 : Upper (D 6) (R 6) [34,72,130,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21154 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21155 : Route 9 := (fun mask => (mask,id))

def c21155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21155 : Upper (D 6) (R 6) [34,72,130,5,65,256] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,65,256] 13 (by decide) (choices 1) [4,16,32] r21155 c21155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6266
  · exact u6267
  · exact u6268

def b21156 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 13 84 33 368 432 304), lower := (rows 35 74 134 13 84 33 64 128 256), losses := [] }

theorem u21156 : Upper (D 6) (R 6) [34,72,130,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21157 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 134 13 84 48 353 417 289), lower := (rows 35 74 134 13 84 48 64 128 256), losses := [] }

theorem u21157 : Upper (D 6) (R 6) [34,72,130,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21157 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21158 : Route 9 := (fun mask => (mask,id))

def c21158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21158 : Upper (D 6) (R 6) [34,72,130,5,68,256] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,68,256] 13 (by decide) (choices 1) [1,16,32] r21158 c21158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6269
  · exact u6270
  · exact u6271

def b21159 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 13 112 33 340 404 276), lower := (rows 35 74 134 13 112 33 64 128 256), losses := [] }

theorem u21159 : Upper (D 6) (R 6) [34,72,130,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21160 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 13 112 36 337 401 273), lower := (rows 35 74 134 13 112 36 64 128 256), losses := [] }

theorem u21160 : Upper (D 6) (R 6) [34,72,130,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21161 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 134 13 112 48 325 389 261), lower := (rows 35 74 134 13 112 48 64 128 256), losses := [] }

theorem u21161 : Upper (D 6) (R 6) [34,72,130,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21161 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21162 : Route 9 := (fun mask => (mask,id))

def c21162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21162 : Upper (D 6) (R 6) [34,72,130,5,96,256] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,96,256] 13 (by decide) (choices 1) [1,4,16] r21162 c21162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6272
  · exact u6273
  · exact u6274

def b21163 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 13 273 36 112 240 368), lower := (rows 35 74 134 13 273 36 64 128 256), losses := [] }

theorem u21163 : Upper (D 6) (R 6) [34,72,130,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21164 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 196, targets := 1 },{ cop := 3, region := 368, targets := 2 }], pairs := [(2,0),(4,1)], upper := (rows 35 74 134 13 273 48 100 228 356), lower := (rows 35 74 134 13 273 48 64 128 256), losses := [] }

theorem u21164 : Upper (D 6) (R 6) [34,72,130,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21164 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21165 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 13 273 96 116 180 308), lower := (rows 35 74 134 13 273 96 64 128 256), losses := [] }

theorem u21165 : Upper (D 6) (R 6) [34,72,130,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21166 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 13 276 33 112 240 368), lower := (rows 35 74 134 13 276 33 64 128 256), losses := [] }

theorem u21166 : Upper (D 6) (R 6) [34,72,130,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21167 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 368, targets := 2 }], pairs := [(1,2),(4,1)], upper := (rows 35 74 134 13 276 48 97 225 353), lower := (rows 35 74 134 13 276 48 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 48 65 129 257), good := (rows 483 74 130 459 304 48 64 128 256) }] }

theorem u21167 : Upper (D 6) (R 6) [34,72,130,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21167 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21168 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 13 276 96 113 177 305), lower := (rows 35 74 134 13 276 96 64 128 256), losses := [] }

theorem u21168 : Upper (D 6) (R 6) [34,72,130,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21169 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 13 304 33 84 212 340), lower := (rows 35 74 134 13 304 33 64 128 256), losses := [] }

theorem u21169 : Upper (D 6) (R 6) [34,72,130,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21170 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 13 304 36 81 209 337), lower := (rows 35 74 134 13 304 36 64 128 256), losses := [] }

theorem u21170 : Upper (D 6) (R 6) [34,72,130,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21171 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 74 134 13 304 48 69 197 325), lower := (rows 35 74 134 13 304 48 64 128 256), losses := [] }

theorem u21171 : Upper (D 6) (R 6) [34,72,130,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21171 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21172 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 13 304 96 85 149 277), lower := (rows 35 74 134 13 304 96 64 128 256), losses := [] }

theorem u21172 : Upper (D 6) (R 6) [34,72,130,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21173 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 13 336 33 116 180 308), lower := (rows 35 74 134 13 336 33 64 128 256), losses := [] }

theorem u21173 : Upper (D 6) (R 6) [34,72,130,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21174 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 13 336 36 113 177 305), lower := (rows 35 74 134 13 336 36 64 128 256), losses := [] }

theorem u21174 : Upper (D 6) (R 6) [34,72,130,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21175 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 134 13 336 48 101 165 293), lower := (rows 35 74 134 13 336 48 64 128 256), losses := [] }

theorem u21175 : Upper (D 6) (R 6) [34,72,130,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21175 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21176 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 74 134 25 52 33 324 452 324), lower := (rows 35 74 134 25 52 33 64 128 256), losses := [] }

theorem u21176 : Upper (D 6) (R 6) [34,72,130,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21177 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 74 134 25 52 36 321 449 321), lower := (rows 35 74 134 25 52 36 64 128 256), losses := [] }

theorem u21177 : Upper (D 6) (R 6) [34,72,130,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21178 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 25 52 96 325 389 261), lower := (rows 35 74 134 25 52 96 64 128 256), losses := [] }

theorem u21178 : Upper (D 6) (R 6) [34,72,130,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21179 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 134 25 52 288 69 197 325), lower := (rows 35 74 134 25 52 288 64 128 256), losses := [] }

theorem u21179 : Upper (D 6) (R 6) [34,72,130,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21179 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21179
end Delivery.IrregularNine14.P06
