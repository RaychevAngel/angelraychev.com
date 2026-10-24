import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0030
import IrregularNine14P07C0031

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13320 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 280 145 96 195 131 387), lower := (rows 7 42 100 280 145 96 64 128 256), losses := [] }

theorem u13320 : Upper (D 7) (R 7) [6,40,96,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13321 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 280 145 160 67 195 323), lower := (rows 7 42 100 280 145 160 64 128 256), losses := [] }

theorem u13321 : Upper (D 7) (R 7) [6,40,96,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13322 : Route 9 := (fun mask => (mask,id))

def c13322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13322 : Upper (D 7) (R 7) [6,40,96,272,130,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,130,1] 13 (by decide) (choices 1) [1,128] r13322 c13322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1808
  · exact u1809

def b13323 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 280 146 96 193 129 385), lower := (rows 7 42 100 280 146 96 64 128 256), losses := [] }

theorem u13323 : Upper (D 7) (R 7) [6,40,96,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13324 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 280 146 160 65 193 321), lower := (rows 7 42 100 280 146 160 64 128 256), losses := [] }

theorem u13324 : Upper (D 7) (R 7) [6,40,96,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13325 : Route 9 := (fun mask => (mask,id))

def c13325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13325 : Upper (D 7) (R 7) [6,40,96,272,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,192,1] 13 (by decide) (choices 1) [1,2,128] r13325 c13325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1810
  · exact u1811
  · exact u1812

def b13326 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 280 208 34 193 129 385), lower := (rows 7 42 100 280 208 34 64 128 256), losses := [] }

theorem u13326 : Upper (D 7) (R 7) [6,40,96,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13327 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 280 208 160 67 131 259), lower := (rows 7 42 100 280 208 160 64 128 256), losses := [] }

theorem u13327 : Upper (D 7) (R 7) [6,40,96,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13328 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 328 145 33 210 146 402), lower := (rows 7 42 100 328 145 33 64 128 256), losses := [] }

theorem u13328 : Upper (D 7) (R 7) [6,40,96,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13329 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 328 145 34 209 145 401), lower := (rows 7 42 100 328 145 34 64 128 256), losses := [] }

theorem u13329 : Upper (D 7) (R 7) [6,40,96,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13330 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 42 100 328 145 48 195 131 387), lower := (rows 7 42 100 328 145 48 64 128 256), losses := [] }

theorem u13330 : Upper (D 7) (R 7) [6,40,96,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13330 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13331 : Route 9 := (fun mask => (mask,id))

def c13331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13331 : Upper (D 7) (R 7) [6,40,96,320,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,320,129,128] 13 (by decide) (choices 1) [1,2,16] r13331 c13331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1813
  · exact u1814
  · exact u1815

def b13332 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 328 146 33 209 145 401), lower := (rows 7 42 100 328 146 33 64 128 256), losses := [] }

theorem u13332 : Upper (D 7) (R 7) [6,40,96,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13333 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 42 100 328 146 48 193 129 385), lower := (rows 7 42 100 328 146 48 64 128 256), losses := [] }

theorem u13333 : Upper (D 7) (R 7) [6,40,96,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13333 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13334 : Route 9 := (fun mask => (mask,id))

def c13334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13334 : Upper (D 7) (R 7) [6,40,96,320,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,320,130,128] 13 (by decide) (choices 1) [1,16] r13334 c13334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1816
  · exact u1817

def b13335 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 392 82 33 209 145 401), lower := (rows 7 42 100 392 82 33 64 128 256), losses := [] }

theorem u13335 : Upper (D 7) (R 7) [6,40,96,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13336 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 392 82 48 193 129 385), lower := (rows 7 42 100 392 82 48 64 128 256), losses := [] }

theorem u13336 : Upper (D 7) (R 7) [6,40,96,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13336 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13337 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 392 82 160 81 145 273), lower := (rows 7 42 100 392 82 160 64 128 256), losses := [] }

theorem u13337 : Upper (D 7) (R 7) [6,40,96,384,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13338 : Route 9 := (fun mask => (mask,id))

def c13338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13338 : Upper (D 7) (R 7) [6,40,96,384,129,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,129,1] 13 (by decide) (choices 1) [2,16] r13338 c13338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1818
  · exact u1819

def b13339 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 392 145 34 81 209 337), lower := (rows 7 42 100 392 145 34 64 128 256), losses := [] }

theorem u13339 : Upper (D 7) (R 7) [6,40,96,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13340 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 42 100 392 145 48 67 195 323), lower := (rows 7 42 100 392 145 48 64 128 256), losses := [] }

theorem u13340 : Upper (D 7) (R 7) [6,40,96,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13341 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 392 145 96 83 147 275), lower := (rows 7 42 100 392 145 96 64 128 256), losses := [] }

theorem u13341 : Upper (D 7) (R 7) [6,40,96,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13342 : Route 9 := (fun mask => (mask,id))

def c13342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13342 : Upper (D 7) (R 7) [6,40,96,384,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,192,1] 13 (by decide) (choices 1) [1,2,16] r13342 c13342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1820
  · exact u1821
  · exact u1822

def b13343 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 392 208 34 81 145 273), lower := (rows 7 42 100 392 208 34 64 128 256), losses := [] }

theorem u13343 : Upper (D 7) (R 7) [6,40,96,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13344 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 392 208 48 67 131 259), lower := (rows 7 42 100 392 208 48 64 128 256), losses := [] }

theorem u13344 : Upper (D 7) (R 7) [6,40,96,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13344 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13345 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 25 82 33 480 416 416), lower := (rows 7 42 196 25 82 33 64 128 256), losses := [] }

theorem u13345 : Upper (D 7) (R 7) [6,40,192,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13346 : Route 9 := (fun mask => (mask,id))

def c13346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u13346 : Upper (D 7) (R 7) [6,40,192,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,66,128] 13 (by decide) (choices 1) [1,32,256] r13346 c13346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1823
  · exact u1824
  · exact u1825

def r13347 : Route 9 := (fun mask => (mask,id))

def c13347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13347 : Upper (D 7) (R 7) [6,40,192,17,66,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,66,256] 13 (by decide) (choices 1) [1,32,128] r13347 c13347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1826
  · exact u1827
  · exact u1828

def b13348 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 25 112 33 450 386 386), lower := (rows 7 42 196 25 112 33 64 128 256), losses := [] }

theorem u13348 : Upper (D 7) (R 7) [6,40,192,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13349 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 25 112 34 449 385 385), lower := (rows 7 42 196 25 112 34 64 128 256), losses := [] }

theorem u13349 : Upper (D 7) (R 7) [6,40,192,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13350 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 2, region := 48, targets := 3 }], pairs := [(0,5),(2,5),(4,0),(4,1)], upper := (rows 7 42 196 25 112 160 323 387 259), lower := (rows 7 42 196 25 112 160 64 128 256), losses := [] }

theorem u13350 : Upper (D 7) (R 7) [6,40,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13351 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(2,5)], upper := (rows 7 42 196 25 112 288 195 131 387), lower := (rows 7 42 196 25 112 288 64 128 256), losses := [] }

theorem u13351 : Upper (D 7) (R 7) [6,40,192,17,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13351 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13352 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 196 25 274 33 224 224 480), lower := (rows 7 42 196 25 274 33 64 128 256), losses := [] }

theorem u13352 : Upper (D 7) (R 7) [6,40,192,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13353 : Route 9 := (fun mask => (mask,id))

def c13353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13353 : Upper (D 7) (R 7) [6,40,192,17,258,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,258,64] 13 (by decide) (choices 1) [1,32,128] r13353 c13353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1829
  · exact u1830
  · exact u1831

def b13354 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,0),(2,5),(4,0)], upper := (rows 7 42 196 25 304 33 194 194 450), lower := (rows 7 42 196 25 304 33 64 128 256), losses := [] }

theorem u13354 : Upper (D 7) (R 7) [6,40,192,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13355 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 196 25 304 34 193 193 449), lower := (rows 7 42 196 25 304 34 64 128 256), losses := [] }

theorem u13355 : Upper (D 7) (R 7) [6,40,192,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13356 : Route 9 := (fun mask => (mask,id))

def c13356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13356 : Upper (D 7) (R 7) [6,40,192,17,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,288,64] 13 (by decide) (choices 1) [1,2,128] r13356 c13356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1832
  · exact u1833
  · exact u1834

def b13357 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 196 25 336 33 226 162 418), lower := (rows 7 42 196 25 336 33 64 128 256), losses := [] }

theorem u13357 : Upper (D 7) (R 7) [6,40,192,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13358 : Route 9 := (fun mask => (mask,id))

def c13358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13358 : Upper (D 7) (R 7) [6,40,192,17,320,2] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320,2] 13 (by decide) (choices 1) [1,32,128] r13358 c13358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1835
  · exact u1836
  · exact u1837

def r13359 : Route 9 := (fun mask => (mask,id))

def c13359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13359 : Upper (D 7) (R 7) [6,40,192,17,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320,128] 13 (by decide) (choices 1) [1,2,32] r13359 c13359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1838
  · exact u1839
  · exact u1840

def b13360 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 42 196 26 273 33 224 224 480), lower := (rows 7 42 196 26 273 33 64 128 256), losses := [] }

theorem u13360 : Upper (D 7) (R 7) [6,40,192,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13361 : Route 9 := (fun mask => (mask,id))

def c13361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13361 : Upper (D 7) (R 7) [6,40,192,18,257,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,257,64] 13 (by decide) (choices 1) [1,32,128] r13361 c13361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1841
  · exact u1842
  · exact u1843

def r13362 : Route 9 := (fun mask => (mask,id))

def c13362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13362 : Upper (D 7) (R 7) [6,40,192,18,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,320,1] 13 (by decide) (choices 1) [1,32,128] r13362 c13362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1844
  · exact u1845
  · exact u1846

def r13363 : Route 9 := (fun mask => (mask,id))

def c13363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13363 : Upper (D 7) (R 7) [6,40,192,18,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,320,128] 13 (by decide) (choices 1) [1,32] r13363 c13363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1847
  · exact u1848

def b13364 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 73 49 34 464 400 400), lower := (rows 7 42 196 73 49 34 64 128 256), losses := [] }

theorem u13364 : Upper (D 7) (R 7) [6,40,192,65,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13365 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 73 49 48 450 386 386), lower := (rows 7 42 196 73 49 48 64 128 256), losses := [] }

theorem u13365 : Upper (D 7) (R 7) [6,40,192,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13365 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13366 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 330, targets := 128 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 7 42 196 73 49 160 338 402 274), lower := (rows 7 42 196 73 49 160 64 128 256), losses := [] }

theorem u13366 : Upper (D 7) (R 7) [6,40,192,65,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13367 : Route 9 := (fun mask => (mask,id))

def c13367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13367 : Upper (D 7) (R 7) [6,40,192,65,33,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,33,256] 13 (by decide) (choices 1) [2,16,128] r13367 c13367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1849
  · exact u1850
  · exact u1851

def b13368 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 196 73 146 33 368 432 304), lower := (rows 7 42 196 73 146 33 64 128 256), losses := [] }

theorem u13368 : Upper (D 7) (R 7) [6,40,192,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13369 : Route 9 := (fun mask => (mask,id))

def c13369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u13369 : Upper (D 7) (R 7) [6,40,192,65,130,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,130,16] 13 (by decide) (choices 1) [1,32,256] r13369 c13369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1852
  · exact u1853
  · exact u1854

def r13370 : Route 9 := (fun mask => (mask,id))

def c13370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13370 : Upper (D 7) (R 7) [6,40,192,65,130,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,130,256] 13 (by decide) (choices 1) [1,16,32] r13370 c13370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1855
  · exact u1856
  · exact u1857

def b13371 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 196 73 176 33 338 402 274), lower := (rows 7 42 196 73 176 33 64 128 256), losses := [] }

theorem u13371 : Upper (D 7) (R 7) [6,40,192,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13372 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 7 42 196 73 176 34 337 401 273), lower := (rows 7 42 196 73 176 34 64 128 256), losses := [] }

theorem u13372 : Upper (D 7) (R 7) [6,40,192,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13373 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 73 176 48 323 387 259), lower := (rows 7 42 196 73 176 48 64 128 256), losses := [] }

theorem u13373 : Upper (D 7) (R 7) [6,40,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13373 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13374 : Route 9 := (fun mask => (mask,id))

def c13374 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13374 : Upper (D 7) (R 7) [6,40,192,65,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,160,256] 13 (by decide) (choices 1) [1,2,16] r13374 c13374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1858
  · exact u1859
  · exact u1860

def b13375 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 7 42 196 73 273 34 240 176 432), lower := (rows 7 42 196 73 273 34 64 128 256), losses := [] }

theorem u13375 : Upper (D 7) (R 7) [6,40,192,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13376 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 7 42 196 73 273 48 226 162 418), lower := (rows 7 42 196 73 273 48 64 128 256), losses := [] }

theorem u13376 : Upper (D 7) (R 7) [6,40,192,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13376 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13377 : Route 9 := (fun mask => (mask,id))

def c13377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13377 : Upper (D 7) (R 7) [6,40,192,65,257,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,257,128] 13 (by decide) (choices 1) [2,16,32] r13377 c13377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1861
  · exact u1862
  · exact u1863

def b13378 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 196 73 274 33 240 176 432), lower := (rows 7 42 196 73 274 33 64 128 256), losses := [] }

theorem u13378 : Upper (D 7) (R 7) [6,40,192,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13379 : Route 9 := (fun mask => (mask,id))

def c13379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13379 : Upper (D 7) (R 7) [6,40,192,65,258,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,258,16] 13 (by decide) (choices 1) [1,32,128] r13379 c13379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1864
  · exact u1865
  · exact u1866

#print axioms u13379
end Delivery.IrregularNine14.P07
