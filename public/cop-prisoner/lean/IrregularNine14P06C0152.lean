import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0014

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9120 : Route 9 := (fun mask => (mask,id))

def c9120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9120 : Upper (D 6) (R 6) [6,9,160,96,68,256] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,68,256] 13 (by decide) (choices 1) [1,2,16] r9120 c9120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u853
  · exact u854
  · exact u855

def b9121 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 336, targets := 34 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 11 164 104 273 34 84 212 340), lower := (rows 7 11 164 104 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 42 164 104 508 34 64 128 256) }] }

theorem u9121 : Upper (D 6) (R 6) [6,9,160,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9122 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 104 273 36 82 210 338), lower := (rows 7 11 164 104 273 36 64 128 256), losses := [] }

theorem u9122 : Upper (D 6) (R 6) [6,9,160,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9123 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,5)], upper := (rows 7 11 164 104 273 48 70 198 326), lower := (rows 7 11 164 104 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 48 65 129 257), good := (rows 454 458 164 104 508 60 64 128 256) }] }

theorem u9123 : Upper (D 6) (R 6) [6,9,160,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9123 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9124 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 104 273 96 86 150 278), lower := (rows 7 11 164 104 273 96 64 128 256), losses := [] }

theorem u9124 : Upper (D 6) (R 6) [6,9,160,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9125 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 104 274 33 84 212 340), lower := (rows 7 11 164 104 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 19 32 99 163 291), good := (rows 478 478 492 492 466 508 64 128 256) }] }

theorem u9125 : Upper (D 6) (R 6) [6,9,160,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9126 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 104 274 36 81 209 337), lower := (rows 7 11 164 104 274 36 64 128 256), losses := [] }

theorem u9126 : Upper (D 6) (R 6) [6,9,160,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9127 : Route 9 := (fun mask => (mask,id))

def c9127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9127 : Upper (D 6) (R 6) [6,9,160,96,258,16] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,258,16] 13 (by decide) (choices 1) [1,4] r9127 c9127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u856
  · exact u857

def b9128 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 104 274 96 85 149 277), lower := (rows 7 11 164 104 274 96 64 128 256), losses := [] }

theorem u9128 : Upper (D 6) (R 6) [6,9,160,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9129 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 104 276 33 82 210 338), lower := (rows 7 11 164 104 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 49 32 67 131 259), good := (rows 470 474 188 124 276 508 64 128 256) }] }

theorem u9129 : Upper (D 6) (R 6) [6,9,160,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9130 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 34 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 164 104 276 34 81 209 337), lower := (rows 7 11 164 104 276 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 40 49 32 67 131 259), good := (rows 469 473 188 124 276 508 64 128 256) }] }

theorem u9130 : Upper (D 6) (R 6) [6,9,160,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9131 : Route 9 := (fun mask => (mask,id))

def c9131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9131 : Upper (D 6) (R 6) [6,9,160,96,260,16] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,260,16] 13 (by decide) (choices 1) [1,2] r9131 c9131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u858
  · exact u859

def b9132 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 104 276 96 83 147 275), lower := (rows 7 11 164 104 276 96 64 128 256), losses := [] }

theorem u9132 : Upper (D 6) (R 6) [6,9,160,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9133 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 104 336 33 86 150 278), lower := (rows 7 11 164 104 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 51 32 65 129 257), good := (rows 470 474 188 124 336 508 64 128 256) }] }

theorem u9133 : Upper (D 6) (R 6) [6,9,160,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9134 : Route 9 := (fun mask => (mask,id))

def c9134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9134 : Upper (D 6) (R 6) [6,9,160,96,320,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,320,2] 13 (by decide) (choices 1) [1,4,16] r9134 c9134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u860
  · exact u861
  · exact u862

def b9135 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 104 336 36 83 147 275), lower := (rows 7 11 164 104 336 36 64 128 256), losses := [] }

theorem u9135 : Upper (D 6) (R 6) [6,9,160,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9136 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 104 336 48 71 135 263), lower := (rows 7 11 164 104 336 48 64 128 256), losses := [] }

theorem u9136 : Upper (D 6) (R 6) [6,9,160,96,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9136 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9137 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 266 84 33 112 240 368), lower := (rows 7 11 164 266 84 33 64 128 256), losses := [] }

theorem u9137 : Upper (D 6) (R 6) [6,9,160,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9138 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 164 266 84 48 97 225 353), lower := (rows 7 11 164 266 84 48 64 128 256), losses := [] }

theorem u9138 : Upper (D 6) (R 6) [6,9,160,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9138 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9139 : Route 9 := (fun mask => (mask,id))

def c9139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9139 : Upper (D 6) (R 6) [6,9,160,258,68,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,258,68,64] 13 (by decide) (choices 1) [1,16,32] r9139 c9139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u863
  · exact u864
  · exact u865

def b9140 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 266 112 33 84 212 340), lower := (rows 7 11 164 266 112 33 64 128 256), losses := [] }

theorem u9140 : Upper (D 6) (R 6) [6,9,160,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9141 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 266 112 36 81 209 337), lower := (rows 7 11 164 266 112 36 64 128 256), losses := [] }

theorem u9141 : Upper (D 6) (R 6) [6,9,160,258,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9142 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 164 266 112 48 69 197 325), lower := (rows 7 11 164 266 112 48 64 128 256), losses := [] }

theorem u9142 : Upper (D 6) (R 6) [6,9,160,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9142 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9143 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 266 112 96 85 149 277), lower := (rows 7 11 164 266 112 96 64 128 256), losses := [] }

theorem u9143 : Upper (D 6) (R 6) [6,9,160,258,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9144 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 280 50 33 68 196 324), lower := (rows 7 11 164 280 50 33 64 128 256), losses := [] }

theorem u9144 : Upper (D 6) (R 6) [6,9,160,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9145 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 280 50 36 65 193 321), lower := (rows 7 11 164 280 50 36 64 128 256), losses := [] }

theorem u9145 : Upper (D 6) (R 6) [6,9,160,272,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9146 : Route 9 := (fun mask => (mask,id))

def c9146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9146 : Upper (D 6) (R 6) [6,9,160,272,34,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,34,64] 13 (by decide) (choices 1) [1,4] r9146 c9146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u866
  · exact u867

def b9147 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 280 81 34 100 228 356), lower := (rows 7 11 164 280 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 119 183 311), good := (rows 486 494 484 476 508 486 64 128 256) }] }

theorem u9147 : Upper (D 6) (R 6) [6,9,160,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9148 : PairBound 9 := { available := 98, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 280 81 36 98 226 354), lower := (rows 7 11 164 280 81 36 64 128 256), losses := [] }

theorem u9148 : Upper (D 6) (R 6) [6,9,160,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9149 : Route 9 := (fun mask => (mask,id))

def c9149 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9149 : Upper (D 6) (R 6) [6,9,160,272,65,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,65,64] 13 (by decide) (choices 1) [2,4,32] r9149 c9149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u868
  · exact u869
  · exact u870

def b9150 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 280 82 33 100 228 356), lower := (rows 7 11 164 280 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 17 32 100 164 292), good := (rows 478 26 492 280 82 508 64 128 256) }] }

theorem u9150 : Upper (D 6) (R 6) [6,9,160,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9151 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 280 82 36 97 225 353), lower := (rows 7 11 164 280 82 36 64 128 256), losses := [] }

theorem u9151 : Upper (D 6) (R 6) [6,9,160,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9152 : Route 9 := (fun mask => (mask,id))

def c9152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9152 : Upper (D 6) (R 6) [6,9,160,272,66,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,66,64] 13 (by decide) (choices 1) [1,4,32] r9152 c9152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u871
  · exact u872
  · exact u873

def r9153 : Route 9 := (fun mask => (mask,id))

def c9153 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9153 : Upper (D 6) (R 6) [6,9,160,272,68,1] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,68,1] 13 (by decide) (choices 1) [2,32] r9153 c9153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u874
  · exact u875

def r9154 : Route 9 := (fun mask => (mask,id))

def c9154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9154 : Upper (D 6) (R 6) [6,9,160,272,68,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,68,2] 13 (by decide) (choices 1) [1,32] r9154 c9154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u876
  · exact u877

def r9155 : Route 9 := (fun mask => (mask,id))

def c9155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9155 : Upper (D 6) (R 6) [6,9,160,272,68,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,68,64] 13 (by decide) (choices 1) [1,2,32] r9155 c9155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u878
  · exact u879
  · exact u880

def b9156 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 164 280 112 33 70 198 326), lower := (rows 7 11 164 280 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 48 32 65 129 257), good := (rows 454 458 188 280 124 508 64 128 256) }] }

theorem u9156 : Upper (D 6) (R 6) [6,9,160,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9157 : Route 9 := (fun mask => (mask,id))

def c9157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9157 : Upper (D 6) (R 6) [6,9,160,272,96,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,96,2] 13 (by decide) (choices 1) [1,4] r9157 c9157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u881
  · exact u882

def b9158 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 280 112 36 67 195 323), lower := (rows 7 11 164 280 112 36 64 128 256), losses := [] }

theorem u9158 : Upper (D 6) (R 6) [6,9,160,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9159 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 280 112 96 71 135 263), lower := (rows 7 11 164 280 112 96 64 128 256), losses := [] }

theorem u9159 : Upper (D 6) (R 6) [6,9,160,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9160 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 11 164 296 81 34 84 212 340), lower := (rows 7 11 164 296 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 42 164 296 508 34 64 128 256) }] }

theorem u9160 : Upper (D 6) (R 6) [6,9,160,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9161 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 296 81 36 82 210 338), lower := (rows 7 11 164 296 81 36 64 128 256), losses := [] }

theorem u9161 : Upper (D 6) (R 6) [6,9,160,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9162 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 80, targets := 32 }], pairs := [(2,0),(4,5)], upper := (rows 7 11 164 296 81 48 70 198 326), lower := (rows 7 11 164 296 81 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 48 65 129 257), good := (rows 454 458 164 296 508 60 64 128 256) }] }

theorem u9162 : Upper (D 6) (R 6) [6,9,160,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9162 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9163 : Route 9 := (fun mask => (mask,id))

def c9163 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9163 : Upper (D 6) (R 6) [6,9,160,288,65,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,65,64] 13 (by decide) (choices 1) [2,4,16] r9163 c9163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u883
  · exact u884
  · exact u885

def b9164 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 296 82 33 84 212 340), lower := (rows 7 11 164 296 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 19 32 99 163 291), good := (rows 478 478 492 492 466 508 64 128 256) }] }

theorem u9164 : Upper (D 6) (R 6) [6,9,160,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9165 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 296 82 36 81 209 337), lower := (rows 7 11 164 296 82 36 64 128 256), losses := [] }

theorem u9165 : Upper (D 6) (R 6) [6,9,160,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9166 : Route 9 := (fun mask => (mask,id))

def c9166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9166 : Upper (D 6) (R 6) [6,9,160,288,66,16] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,66,16] 13 (by decide) (choices 1) [1,4] r9166 c9166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u886
  · exact u887

def r9167 : Route 9 := (fun mask => (mask,id))

def c9167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9167 : Upper (D 6) (R 6) [6,9,160,288,66,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,66,64] 13 (by decide) (choices 1) [1,4,16] r9167 c9167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u888
  · exact u889
  · exact u890

def b9168 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 296 84 33 82 210 338), lower := (rows 7 11 164 296 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 49 32 67 131 259), good := (rows 470 474 188 316 84 508 64 128 256) }] }

theorem u9168 : Upper (D 6) (R 6) [6,9,160,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9169 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 164 296 84 34 81 209 337), lower := (rows 7 11 164 296 84 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 40 49 32 67 131 259), good := (rows 469 473 188 316 84 508 64 128 256) }] }

theorem u9169 : Upper (D 6) (R 6) [6,9,160,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9170 : Route 9 := (fun mask => (mask,id))

def c9170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9170 : Upper (D 6) (R 6) [6,9,160,288,68,16] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,68,16] 13 (by decide) (choices 1) [1,2] r9170 c9170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u891
  · exact u892

def r9171 : Route 9 := (fun mask => (mask,id))

def c9171 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9171 : Upper (D 6) (R 6) [6,9,160,288,68,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,68,64] 13 (by decide) (choices 1) [1,2,16] r9171 c9171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u893
  · exact u894
  · exact u895

def b9172 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 328 49 34 84 212 340), lower := (rows 7 11 164 328 49 34 64 128 256), losses := [] }

theorem u9172 : Upper (D 6) (R 6) [6,9,160,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9173 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 11 164 328 49 36 82 210 338), lower := (rows 7 11 164 328 49 36 64 128 256), losses := [] }

theorem u9173 : Upper (D 6) (R 6) [6,9,160,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9174 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 11 164 328 49 48 70 198 326), lower := (rows 7 11 164 328 49 48 64 128 256), losses := [] }

theorem u9174 : Upper (D 6) (R 6) [6,9,160,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9174 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9175 : Route 9 := (fun mask => (mask,id))

def c9175 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9175 : Upper (D 6) (R 6) [6,9,160,320,33,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,33,64] 13 (by decide) (choices 1) [2,4,16] r9175 c9175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u896
  · exact u897
  · exact u898

def b9176 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 328 50 33 84 212 340), lower := (rows 7 11 164 328 50 33 64 128 256), losses := [] }

theorem u9176 : Upper (D 6) (R 6) [6,9,160,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9177 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 328 50 36 81 209 337), lower := (rows 7 11 164 328 50 36 64 128 256), losses := [] }

theorem u9177 : Upper (D 6) (R 6) [6,9,160,320,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9178 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 164 328 50 48 69 197 325), lower := (rows 7 11 164 328 50 48 64 128 256), losses := [] }

theorem u9178 : Upper (D 6) (R 6) [6,9,160,320,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9178 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9179 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 133, targets := 64 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 7 11 164 328 50 96 85 149 277), lower := (rows 7 11 164 328 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 104 64 128 256), good := (rows 22 58 164 360 50 96 96 128 256) }] }

theorem u9179 : Upper (D 6) (R 6) [6,9,160,320,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9179
end Delivery.IrregularNine14.P06
