import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0029

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13200 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 84 328 49 34 193 129 385), lower := (rows 7 42 84 328 49 34 64 128 256), losses := [] }

theorem u13200 : Upper (D 7) (R 7) [6,40,80,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13201 : Route 9 := (fun mask => (mask,id))

def c13201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13201 : Upper (D 7) (R 7) [6,40,80,320,33,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,33,128] 13 (by decide) (choices 1) [1,2,128] r13201 c13201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1753
  · exact u1754
  · exact u1755

def r13202 : Route 9 := (fun mask => (mask,id))

def c13202 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13202 : Upper (D 7) (R 7) [6,40,80,320,129,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,129,1] 13 (by decide) (choices 1) [2,32,128] r13202 c13202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1756
  · exact u1757
  · exact u1758

def b13203 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 84 328 145 34 225 161 417), lower := (rows 7 42 84 328 145 34 64 128 256), losses := [] }

theorem u13203 : Upper (D 7) (R 7) [6,40,80,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13204 : Route 9 := (fun mask => (mask,id))

def c13204 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13204 : Upper (D 7) (R 7) [6,40,80,320,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,129,128] 13 (by decide) (choices 1) [1,2,32] r13204 c13204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1759
  · exact u1760
  · exact u1761

def r13205 : Route 9 := (fun mask => (mask,id))

def c13205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13205 : Upper (D 7) (R 7) [6,40,80,320,130,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,130,1] 13 (by decide) (choices 1) [1,32,128] r13205 c13205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1762
  · exact u1763
  · exact u1764

def r13206 : Route 9 := (fun mask => (mask,id))

def c13206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13206 : Upper (D 7) (R 7) [6,40,80,320,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,130,128] 13 (by decide) (choices 1) [1,32] r13206 c13206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1765
  · exact u1766

def r13207 : Route 9 := (fun mask => (mask,id))

def c13207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13207 : Upper (D 7) (R 7) [6,40,80,320,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,160,1] 13 (by decide) (choices 1) [1,2,128] r13207 c13207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1767
  · exact u1768
  · exact u1769

def b13208 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 456, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 42 84 328 176 34 193 129 385), lower := (rows 7 42 84 328 176 34 64 128 256), losses := [] }

theorem u13208 : Upper (D 7) (R 7) [6,40,80,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13209 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 84 328 176 160 67 131 259), lower := (rows 7 42 84 328 176 160 64 128 256), losses := [] }

theorem u13209 : Upper (D 7) (R 7) [6,40,80,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13210 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 7 42 84 392 49 33 194 194 450), lower := (rows 7 42 84 392 49 33 64 128 256), losses := [] }

theorem u13210 : Upper (D 7) (R 7) [6,40,80,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13211 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 42 84 392 49 34 193 193 449), lower := (rows 7 42 84 392 49 34 64 128 256), losses := [] }

theorem u13211 : Upper (D 7) (R 7) [6,40,80,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13212 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 394, targets := 64 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,6),(3,5),(3,6),(4,1)], upper := (rows 7 42 84 392 49 96 195 131 387), lower := (rows 7 42 84 392 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 100 64 128 256), good := (rows 53 40 116 392 49 96 96 128 256) }] }

theorem u13212 : Upper (D 7) (R 7) [6,40,80,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13213 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 392 49 160 67 195 323), lower := (rows 7 42 84 392 49 160 64 128 256), losses := [] }

theorem u13213 : Upper (D 7) (R 7) [6,40,80,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13214 : Route 9 := (fun mask => (mask,id))

def c13214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13214 : Upper (D 7) (R 7) [6,40,80,384,129,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,129,1] 13 (by decide) (choices 1) [2,32] r13214 c13214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1770
  · exact u1771

def b13215 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,7)], upper := (rows 7 42 84 392 145 34 97 225 353), lower := (rows 7 42 84 392 145 34 64 128 256), losses := [{ target := 7, region := (rows 1 10 20 8 16 43 81 0 273), good := (rows 359 42 340 298 373 34 64 0 256) }] }

theorem u13215 : Upper (D 7) (R 7) [6,40,80,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13216 : Route 9 := (fun mask => (mask,id))

def c13216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13216 : Upper (D 7) (R 7) [6,40,80,384,129,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,129,64] 13 (by decide) (choices 1) [1,2,32] r13216 c13216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1772
  · exact u1773
  · exact u1774

def r13217 : Route 9 := (fun mask => (mask,id))

def c13217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13217 : Upper (D 7) (R 7) [6,40,80,384,130,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,130,1] 13 (by decide) (choices 1) [1,32] r13217 c13217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1775
  · exact u1776

def r13218 : Route 9 := (fun mask => (mask,id))

def c13218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13218 : Upper (D 7) (R 7) [6,40,80,384,130,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,130,64] 13 (by decide) (choices 1) [1,32] r13218 c13218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1777
  · exact u1778

def r13219 : Route 9 := (fun mask => (mask,id))

def c13219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13219 : Upper (D 7) (R 7) [6,40,80,384,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160,1] 13 (by decide) (choices 1) [1,2] r13219 c13219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1779
  · exact u1780

def b13220 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 42 84 392 176 34 65 193 321), lower := (rows 7 42 84 392 176 34 64 128 256), losses := [] }

theorem u13220 : Upper (D 7) (R 7) [6,40,80,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13221 : Route 9 := (fun mask => (mask,id))

def c13221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13221 : Upper (D 7) (R 7) [6,40,80,384,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160,64] 13 (by decide) (choices 1) [1,2] r13221 c13221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1781
  · exact u1782

def b13222 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 25 146 33 448 448 448), lower := (rows 7 42 100 25 146 33 64 128 256), losses := [] }

theorem u13222 : Upper (D 7) (R 7) [6,40,96,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13223 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 25 146 96 449 385 385), lower := (rows 7 42 100 25 146 96 64 128 256), losses := [] }

theorem u13223 : Upper (D 7) (R 7) [6,40,96,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13224 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 25 146 160 321 449 321), lower := (rows 7 42 100 25 146 160 64 128 256), losses := [] }

theorem u13224 : Upper (D 7) (R 7) [6,40,96,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13225 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 100 25 146 288 193 193 449), lower := (rows 7 42 100 25 146 288 64 128 256), losses := [] }

theorem u13225 : Upper (D 7) (R 7) [6,40,96,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13225 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13226 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 100 25 208 33 450 386 386), lower := (rows 7 42 100 25 208 33 64 128 256), losses := [] }

theorem u13226 : Upper (D 7) (R 7) [6,40,96,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13227 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 25 208 34 449 385 385), lower := (rows 7 42 100 25 208 34 64 128 256), losses := [] }

theorem u13227 : Upper (D 7) (R 7) [6,40,96,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13228 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 25 208 160 323 387 259), lower := (rows 7 42 100 25 208 160 64 128 256), losses := [] }

theorem u13228 : Upper (D 7) (R 7) [6,40,96,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13229 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 7 42 100 25 208 288 195 131 387), lower := (rows 7 42 100 25 208 288 64 128 256), losses := [] }

theorem u13229 : Upper (D 7) (R 7) [6,40,96,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13229 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13230 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 25 274 33 192 192 448), lower := (rows 7 42 100 25 274 33 64 128 256), losses := [] }

theorem u13230 : Upper (D 7) (R 7) [6,40,96,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13231 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 25 274 96 193 129 385), lower := (rows 7 42 100 25 274 96 64 128 256), losses := [] }

theorem u13231 : Upper (D 7) (R 7) [6,40,96,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13232 : Route 9 := (fun mask => (mask,id))

def c13232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13232 : Upper (D 7) (R 7) [6,40,96,17,258,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,258,128] 13 (by decide) (choices 1) [1,128] r13232 c13232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1783
  · exact u1784

def b13233 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 100 25 336 33 194 130 386), lower := (rows 7 42 100 25 336 33 64 128 256), losses := [] }

theorem u13233 : Upper (D 7) (R 7) [6,40,96,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13234 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 25 336 34 193 129 385), lower := (rows 7 42 100 25 336 34 64 128 256), losses := [] }

theorem u13234 : Upper (D 7) (R 7) [6,40,96,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13235 : Route 9 := (fun mask => (mask,id))

def c13235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13235 : Upper (D 7) (R 7) [6,40,96,17,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,320,128] 13 (by decide) (choices 1) [1,2,128] r13235 c13235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1785
  · exact u1786
  · exact u1787

def b13236 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 25 400 33 194 194 450), lower := (rows 7 42 100 25 400 33 64 128 256), losses := [] }

theorem u13236 : Upper (D 7) (R 7) [6,40,96,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13237 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 25 400 34 193 193 449), lower := (rows 7 42 100 25 400 34 64 128 256), losses := [] }

theorem u13237 : Upper (D 7) (R 7) [6,40,96,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13238 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 25 400 96 195 131 387), lower := (rows 7 42 100 25 400 96 64 128 256), losses := [] }

theorem u13238 : Upper (D 7) (R 7) [6,40,96,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13239 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 25 400 160 67 195 323), lower := (rows 7 42 100 25 400 160 64 128 256), losses := [] }

theorem u13239 : Upper (D 7) (R 7) [6,40,96,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13240 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 88 145 33 450 386 386), lower := (rows 7 42 100 88 145 33 64 128 256), losses := [] }

theorem u13240 : Upper (D 7) (R 7) [6,40,96,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13241 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 88 145 34 449 385 385), lower := (rows 7 42 100 88 145 34 64 128 256), losses := [] }

theorem u13241 : Upper (D 7) (R 7) [6,40,96,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13242 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 88 145 160 323 387 259), lower := (rows 7 42 100 88 145 160 64 128 256), losses := [] }

theorem u13242 : Upper (D 7) (R 7) [6,40,96,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13243 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 42 100 88 145 288 195 131 387), lower := (rows 7 42 100 88 145 288 64 128 256), losses := [] }

theorem u13243 : Upper (D 7) (R 7) [6,40,96,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13243 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13244 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 88 273 33 194 130 386), lower := (rows 7 42 100 88 273 33 64 128 256), losses := [] }

theorem u13244 : Upper (D 7) (R 7) [6,40,96,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13245 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 88 273 34 193 129 385), lower := (rows 7 42 100 88 273 34 64 128 256), losses := [] }

theorem u13245 : Upper (D 7) (R 7) [6,40,96,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13246 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,6),(3,5),(4,5),(4,6)], upper := (rows 7 42 100 88 273 160 195 131 387), lower := (rows 7 42 100 88 273 160 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 17 177 0 129 257), good := (rows 439 42 36 58 433 160 0 160 256) }] }

theorem u13246 : Upper (D 7) (R 7) [6,40,96,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13247 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 88 400 33 195 131 387), lower := (rows 7 42 100 88 400 33 64 128 256), losses := [] }

theorem u13247 : Upper (D 7) (R 7) [6,40,96,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13248 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 88 400 34 193 129 385), lower := (rows 7 42 100 88 400 34 64 128 256), losses := [] }

theorem u13248 : Upper (D 7) (R 7) [6,40,96,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13249 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 88 400 160 67 131 259), lower := (rows 7 42 100 88 400 160 64 128 256), losses := [] }

theorem u13249 : Upper (D 7) (R 7) [6,40,96,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13250 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 137 82 33 464 400 400), lower := (rows 7 42 100 137 82 33 64 128 256), losses := [] }

theorem u13250 : Upper (D 7) (R 7) [6,40,96,129,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13251 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 137 82 48 449 385 385), lower := (rows 7 42 100 137 82 48 64 128 256), losses := [] }

theorem u13251 : Upper (D 7) (R 7) [6,40,96,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13251 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13252 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 137 82 160 337 401 273), lower := (rows 7 42 100 137 82 160 64 128 256), losses := [] }

theorem u13252 : Upper (D 7) (R 7) [6,40,96,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13253 : Route 9 := (fun mask => (mask,id))

def c13253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13253 : Upper (D 7) (R 7) [6,40,96,129,66,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,66,256] 13 (by decide) (choices 1) [1,16,128] r13253 c13253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1788
  · exact u1789
  · exact u1790

def b13254 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 137 208 33 338 402 274), lower := (rows 7 42 100 137 208 33 64 128 256), losses := [] }

theorem u13254 : Upper (D 7) (R 7) [6,40,96,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13255 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 137 208 34 337 401 273), lower := (rows 7 42 100 137 208 34 64 128 256), losses := [] }

theorem u13255 : Upper (D 7) (R 7) [6,40,96,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13256 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 137 208 48 323 387 259), lower := (rows 7 42 100 137 208 48 64 128 256), losses := [] }

theorem u13256 : Upper (D 7) (R 7) [6,40,96,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13256 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13257 : Route 9 := (fun mask => (mask,id))

def c13257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13257 : Upper (D 7) (R 7) [6,40,96,129,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,192,256] 13 (by decide) (choices 1) [1,2,16] r13257 c13257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1791
  · exact u1792
  · exact u1793

def b13258 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 137 273 34 208 208 464), lower := (rows 7 42 100 137 273 34 64 128 256), losses := [] }

theorem u13258 : Upper (D 7) (R 7) [6,40,96,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13259 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 137 273 48 194 194 450), lower := (rows 7 42 100 137 273 48 64 128 256), losses := [] }

theorem u13259 : Upper (D 7) (R 7) [6,40,96,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13259 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13259
end Delivery.IrregularNine14.P07
