import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0422
import IrregularNine14P06C0423

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39120 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 76 56 84 39 71 135 263), lower := (rows 35 386 76 56 84 32 64 128 256), losses := [] }

theorem u39120 : Upper (D 6) (R 6) [34,384,72,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39121 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 100 11 21 124 92 220 348), lower := (rows 35 386 100 11 21 32 64 128 256), losses := [] }

theorem u39121 : Upper (D 6) (R 6) [34,384,96,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39122 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 100 11 25 116 84 212 340), lower := (rows 35 386 100 11 25 32 64 128 256), losses := [] }

theorem u39122 : Upper (D 6) (R 6) [34,384,96,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39123 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 100 11 28 117 85 213 341), lower := (rows 35 386 100 11 28 32 64 128 256), losses := [] }

theorem u39123 : Upper (D 6) (R 6) [34,384,96,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39124 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 100 11 81 60 92 156 284), lower := (rows 35 386 100 11 81 32 64 128 256), losses := [] }

theorem u39124 : Upper (D 6) (R 6) [34,384,96,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39125 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 100 11 88 53 85 149 277), lower := (rows 35 386 100 11 88 32 64 128 256), losses := [] }

theorem u39125 : Upper (D 6) (R 6) [34,384,96,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39126 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 66 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 35 386 100 13 21 122 90 218 346), lower := (rows 35 386 100 13 21 32 64 128 256), losses := [] }

theorem u39126 : Upper (D 6) (R 6) [34,384,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39127 : Route 9 := (fun mask => (mask,id))

def c39127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39127 : Upper (D 6) (R 6) [34,384,96,5,6] 13 := by
  apply FastRouting.sound _ _ [34,384,96,5,6] 13 (by decide) (choices 1) [1,8,16,64] r39127 c39127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25340
  · exact u25341
  · exact u25342
  · exact u25343

def b39128 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 386 100 13 25 118 86 214 342), lower := (rows 35 386 100 13 25 32 64 128 256), losses := [] }

theorem u39128 : Upper (D 6) (R 6) [34,384,96,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39129 : Route 9 := (fun mask => (mask,id))

def c39129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39129 : Upper (D 6) (R 6) [34,384,96,5,10] 13 := by
  apply FastRouting.sound _ _ [34,384,96,5,10] 13 (by decide) (choices 1) [1,4,16,64] r39129 c39129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25344
  · exact u25345
  · exact u25346
  · exact u25347

def b39130 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 386 100 13 28 115 83 211 339), lower := (rows 35 386 100 13 28 32 64 128 256), losses := [] }

theorem u39130 : Upper (D 6) (R 6) [34,384,96,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39131 : Route 9 := (fun mask => (mask,id))

def c39131 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39131 : Upper (D 6) (R 6) [34,384,96,5,65] 13 := by
  apply FastRouting.sound _ _ [34,384,96,5,65] 13 (by decide) (choices 1) [2,4,8,16] r39131 c39131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25348
  · exact u25349
  · exact u25350
  · exact u25351

def r39132 : Route 9 := (fun mask => (mask,id))

def c39132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39132 : Upper (D 6) (R 6) [34,384,96,5,66] 13 := by
  apply FastRouting.sound _ _ [34,384,96,5,66] 13 (by decide) (choices 1) [1,4,8,16] r39132 c39132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25352
  · exact u25353
  · exact u25354
  · exact u25355

def b39133 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 100 13 84 59 91 155 283), lower := (rows 35 386 100 13 84 32 64 128 256), losses := [] }

theorem u39133 : Upper (D 6) (R 6) [34,384,96,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39134 : Route 9 := (fun mask => (mask,id))

def c39134 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39134 : Upper (D 6) (R 6) [34,384,96,5,72] 13 := by
  apply FastRouting.sound _ _ [34,384,96,5,72] 13 (by decide) (choices 1) [1,2,4,16] r39134 c39134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25356
  · exact u25357
  · exact u25358
  · exact u25359

def r39135 : Route 9 := (fun mask => (mask,id))

def c39135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39135 : Upper (D 6) (R 6) [34,384,96,6,9] 13 := by
  apply FastRouting.sound _ _ [34,384,96,6,9] 13 (by decide) (choices 1) [1,4,16,64] r39135 c39135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25360
  · exact u25361
  · exact u25362
  · exact u25363

def b39136 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 100 14 28 113 81 209 337), lower := (rows 35 386 100 14 28 32 64 128 256), losses := [] }

theorem u39136 : Upper (D 6) (R 6) [34,384,96,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39137 : Route 9 := (fun mask => (mask,id))

def c39137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39137 : Upper (D 6) (R 6) [34,384,96,6,65] 13 := by
  apply FastRouting.sound _ _ [34,384,96,6,65] 13 (by decide) (choices 1) [1,4,8,16] r39137 c39137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25364
  · exact u25365
  · exact u25366
  · exact u25367

def b39138 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 100 14 84 57 89 153 281), lower := (rows 35 386 100 14 84 32 64 128 256), losses := [] }

theorem u39138 : Upper (D 6) (R 6) [34,384,96,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39139 : Route 9 := (fun mask => (mask,id))

def c39139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39139 : Upper (D 6) (R 6) [34,384,96,6,72] 13 := by
  apply FastRouting.sound _ _ [34,384,96,6,72] 13 (by decide) (choices 1) [1,4,16] r39139 c39139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25368
  · exact u25369
  · exact u25370

def b39140 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 386 100 25 25 102 70 198 326), lower := (rows 35 386 100 25 25 32 64 128 256), losses := [] }

theorem u39140 : Upper (D 6) (R 6) [34,384,96,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39141 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 100 25 26 101 69 197 325), lower := (rows 35 386 100 25 26 32 64 128 256), losses := [] }

theorem u39141 : Upper (D 6) (R 6) [34,384,96,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39142 : Route 9 := (fun mask => (mask,id))

def c39142 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39142 : Upper (D 6) (R 6) [34,384,96,17,12] 13 := by
  apply FastRouting.sound _ _ [34,384,96,17,12] 13 (by decide) (choices 1) [1,2,4,64] r39142 c39142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25371
  · exact u25372
  · exact u25373
  · exact u25374

def b39143 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 386 100 25 81 46 78 142 270), lower := (rows 35 386 100 25 81 32 64 128 256), losses := [] }

theorem u39143 : Upper (D 6) (R 6) [34,384,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39144 : Route 9 := (fun mask => (mask,id))

def c39144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39144 : Upper (D 6) (R 6) [34,384,96,17,66] 13 := by
  apply FastRouting.sound _ _ [34,384,96,17,66] 13 (by decide) (choices 1) [1,4,8] r39144 c39144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25375
  · exact u25376
  · exact u25377

def b39145 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 100 25 84 47 79 143 271), lower := (rows 35 386 100 25 84 32 64 128 256), losses := [] }

theorem u39145 : Upper (D 6) (R 6) [34,384,96,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39146 : Route 9 := (fun mask => (mask,id))

def c39146 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39146 : Upper (D 6) (R 6) [34,384,96,17,72] 13 := by
  apply FastRouting.sound _ _ [34,384,96,17,72] 13 (by decide) (choices 1) [1,2,4] r39146 c39146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25378
  · exact u25379
  · exact u25380

def r39147 : Route 9 := (fun mask => (mask,id))

def c39147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39147 : Upper (D 6) (R 6) [34,384,96,18,12] 13 := by
  apply FastRouting.sound _ _ [34,384,96,18,12] 13 (by decide) (choices 1) [1,4,64] r39147 c39147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25381
  · exact u25382
  · exact u25383

def r39148 : Route 9 := (fun mask => (mask,id))

def c39148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39148 : Upper (D 6) (R 6) [34,384,96,18,65] 13 := by
  apply FastRouting.sound _ _ [34,384,96,18,65] 13 (by decide) (choices 1) [1,4,8] r39148 c39148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25384
  · exact u25385
  · exact u25386

def b39149 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 100 26 84 45 77 141 269), lower := (rows 35 386 100 26 84 32 64 128 256), losses := [] }

theorem u39149 : Upper (D 6) (R 6) [34,384,96,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39150 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 386 100 26 88 37 69 133 261), lower := (rows 35 386 100 26 88 32 64 128 256), losses := [] }

theorem u39150 : Upper (D 6) (R 6) [34,384,96,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39151 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 100 28 28 99 67 195 323), lower := (rows 35 386 100 28 28 32 64 128 256), losses := [] }

theorem u39151 : Upper (D 6) (R 6) [34,384,96,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39152 : Route 9 := (fun mask => (mask,id))

def c39152 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39152 : Upper (D 6) (R 6) [34,384,96,20,65] 13 := by
  apply FastRouting.sound _ _ [34,384,96,20,65] 13 (by decide) (choices 1) [1,2,4,8] r39152 c39152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25387
  · exact u25388
  · exact u25389
  · exact u25390

def r39153 : Route 9 := (fun mask => (mask,id))

def c39153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39153 : Upper (D 6) (R 6) [34,384,96,20,66] 13 := by
  apply FastRouting.sound _ _ [34,384,96,20,66] 13 (by decide) (choices 1) [1,4,8] r39153 c39153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25391
  · exact u25392
  · exact u25393

def b39154 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 100 28 84 43 75 139 267), lower := (rows 35 386 100 28 84 32 64 128 256), losses := [] }

theorem u39154 : Upper (D 6) (R 6) [34,384,96,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39155 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 100 28 88 39 71 135 263), lower := (rows 35 386 100 28 88 32 64 128 256), losses := [] }

theorem u39155 : Upper (D 6) (R 6) [34,384,96,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39156 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 18, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 133 14 19 356 324 452 324), lower := (rows 41 50 133 14 19 32 64 128 256), losses := [] }

theorem u39156 : Upper (D 6) (R 6) [40,48,129,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39157 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 50 133 14 21 354 322 450 322), lower := (rows 41 50 133 14 21 32 64 128 256), losses := [] }

theorem u39157 : Upper (D 6) (R 6) [40,48,129,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39158 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 50 133 14 22 353 321 449 321), lower := (rows 41 50 133 14 22 32 64 128 256), losses := [] }

theorem u39158 : Upper (D 6) (R 6) [40,48,129,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39159 : Route 9 := (fun mask => (mask,id))

def c39159 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39159 : Upper (D 6) (R 6) [40,48,129,6,65] 13 := by
  apply FastRouting.sound _ _ [40,48,129,6,65] 13 (by decide) (choices 1) [2,4,64,256] r39159 c39159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25394
  · exact u25395
  · exact u25396
  · exact u25397

def b39160 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 485, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 133 14 82 357 325 453 325), lower := (rows 41 50 133 14 82 32 64 128 256), losses := [] }

theorem u39160 : Upper (D 6) (R 6) [40,48,129,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39161 : Route 9 := (fun mask => (mask,id))

def c39161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39161 : Upper (D 6) (R 6) [40,48,129,6,68] 13 := by
  apply FastRouting.sound _ _ [40,48,129,6,68] 13 (by decide) (choices 1) [1,2,64,256] r39161 c39161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25398
  · exact u25399
  · exact u25400
  · exact u25401

def r39162 : Route 9 := (fun mask => (mask,id))

def c39162 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39162 : Upper (D 6) (R 6) [40,48,129,6,257] 13 := by
  apply FastRouting.sound _ _ [40,48,129,6,257] 13 (by decide) (choices 1) [2,4,64] r39162 c39162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25402
  · exact u25403
  · exact u25404

def b39163 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 133 14 274 101 69 197 325), lower := (rows 41 50 133 14 274 32 64 128 256), losses := [] }

theorem u39163 : Upper (D 6) (R 6) [40,48,129,6,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39164 : Route 9 := (fun mask => (mask,id))

def c39164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39164 : Upper (D 6) (R 6) [40,48,129,6,260] 13 := by
  apply FastRouting.sound _ _ [40,48,129,6,260] 13 (by decide) (choices 1) [1,2,64] r39164 c39164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25405
  · exact u25406
  · exact u25407

def r39165 : Route 9 := (fun mask => (mask,id))

def c39165 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39165 : Upper (D 6) (R 6) [40,48,129,6,320] 13 := by
  apply FastRouting.sound _ _ [40,48,129,6,320] 13 (by decide) (choices 1) [1,2,4,64] r39165 c39165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25408
  · exact u25409
  · exact u25410
  · exact u25411

def r39166 : Route 9 := (fun mask => (mask,id))

def c39166 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39166 : Upper (D 6) (R 6) [40,48,129,65,6] 13 := by
  apply FastRouting.sound _ _ [40,48,129,65,6] 13 (by decide) (choices 1) [2,4,64,256] r39166 c39166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25412
  · exact u25413
  · exact u25414
  · exact u25415

def b39167 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 50 133 73 82 294 326 390 262), lower := (rows 41 50 133 73 82 32 64 128 256), losses := [{ target := 1, region := (rows 3 0 4 24 16 32 64 128 256), good := (rows 41 57 133 73 89 32 64 128 256) }] }

theorem u39167 : Upper (D 6) (R 6) [40,48,129,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39168 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 50 133 73 84 294 326 390 262), lower := (rows 41 50 133 73 84 32 64 128 256), losses := [] }

theorem u39168 : Upper (D 6) (R 6) [40,48,129,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39169 : Route 9 := (fun mask => (mask,id))

def c39169 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39169 : Upper (D 6) (R 6) [40,48,129,65,258] 13 := by
  apply FastRouting.sound _ _ [40,48,129,65,258] 13 (by decide) (choices 1) [2,4,64] r39169 c39169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25416
  · exact u25417
  · exact u25418

def r39170 : Route 9 := (fun mask => (mask,id))

def c39170 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39170 : Upper (D 6) (R 6) [40,48,129,65,260] 13 := by
  apply FastRouting.sound _ _ [40,48,129,65,260] 13 (by decide) (choices 1) [2,4,64] r39170 c39170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25419
  · exact u25420
  · exact u25421

def r39171 : Route 9 := (fun mask => (mask,id))

def c39171 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39171 : Upper (D 6) (R 6) [40,48,129,65,320] 13 := by
  apply FastRouting.sound _ _ [40,48,129,65,320] 13 (by decide) (choices 1) [2,4] r39171 c39171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25422
  · exact u25423

def b39172 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 18, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 133 74 19 356 324 452 324), lower := (rows 41 50 133 74 19 32 64 128 256), losses := [] }

theorem u39172 : Upper (D 6) (R 6) [40,48,129,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39173 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 50 133 74 21 358 326 454 326), lower := (rows 41 50 133 74 21 32 64 128 256), losses := [] }

theorem u39173 : Upper (D 6) (R 6) [40,48,129,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39174 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 421, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 133 74 22 357 325 453 325), lower := (rows 41 50 133 74 22 32 64 128 256), losses := [] }

theorem u39174 : Upper (D 6) (R 6) [40,48,129,66,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39175 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 50 133 74 81 294 326 390 262), lower := (rows 41 50 133 74 81 32 64 128 256), losses := [] }

theorem u39175 : Upper (D 6) (R 6) [40,48,129,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39176 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 50 133 74 82 293 325 389 261), lower := (rows 41 50 133 74 82 32 64 128 256), losses := [] }

theorem u39176 : Upper (D 6) (R 6) [40,48,129,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39177 : Route 9 := (fun mask => (mask,id))

def c39177 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39177 : Upper (D 6) (R 6) [40,48,129,66,68] 13 := by
  apply FastRouting.sound _ _ [40,48,129,66,68] 13 (by decide) (choices 1) [1,2,4,256] r39177 c39177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25424
  · exact u25425
  · exact u25426
  · exact u25427

def r39178 : Route 9 := (fun mask => (mask,id))

def c39178 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39178 : Upper (D 6) (R 6) [40,48,129,66,257] 13 := by
  apply FastRouting.sound _ _ [40,48,129,66,257] 13 (by decide) (choices 1) [2,4,64] r39178 c39178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25428
  · exact u25429
  · exact u25430

def b39179 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 133 74 274 101 69 197 325), lower := (rows 41 50 133 74 274 32 64 128 256), losses := [] }

theorem u39179 : Upper (D 6) (R 6) [40,48,129,66,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39179
end Delivery.IrregularNine14.P06
