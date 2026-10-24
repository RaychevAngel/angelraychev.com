import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0314
import IrregularNine14P07C0315

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34260 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 14 25 112 417 449 385 385), lower := (rows 35 70 14 25 112 32 64 128 256), losses := [] }

theorem u34260 : Upper (D 7) (R 7) [34,68,10,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34261 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 14 25 145 480 480 480 480), lower := (rows 35 70 14 25 145 32 64 128 256), losses := [] }

theorem u34261 : Upper (D 7) (R 7) [34,68,10,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34262 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 14 25 176 481 449 449 449), lower := (rows 35 70 14 25 176 32 64 128 256), losses := [] }

theorem u34262 : Upper (D 7) (R 7) [34,68,10,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34263 : Route 9 := (fun mask => (mask,id))

def c34263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34263 : Upper (D 7) (R 7) [34,68,10,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,10,17,192] 13 (by decide) (choices 1) [1,128,256] r34263 c34263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18845
  · exact u18846
  · exact u18847

def b34264 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 14 25 273 224 224 224 480), lower := (rows 35 70 14 25 273 32 64 128 256), losses := [] }

theorem u34264 : Upper (D 7) (R 7) [34,68,10,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34265 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 14 25 304 225 193 193 449), lower := (rows 35 70 14 25 304 32 64 128 256), losses := [] }

theorem u34265 : Upper (D 7) (R 7) [34,68,10,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34266 : Route 9 := (fun mask => (mask,id))

def c34266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34266 : Upper (D 7) (R 7) [34,68,10,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,10,17,320] 13 (by decide) (choices 1) [1,128] r34266 c34266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18848
  · exact u18849

def r34267 : Route 9 := (fun mask => (mask,id))

def c34267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34267 : Upper (D 7) (R 7) [34,68,10,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,10,17,384] 13 (by decide) (choices 1) [1,64,128] r34267 c34267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18850
  · exact u18851
  · exact u18852

def b34268 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,5)], upper := (rows 35 70 14 56 81 417 449 385 385), lower := (rows 35 70 14 56 81 32 64 128 256), losses := [] }

theorem u34268 : Upper (D 7) (R 7) [34,68,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34269 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 35 70 14 56 145 481 449 449 449), lower := (rows 35 70 14 56 145 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 17 0 81 145 273), good := (rows 467 70 14 478 465 0 64 128 256) }] }

theorem u34269 : Upper (D 7) (R 7) [34,68,10,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34270 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,5)], upper := (rows 35 70 14 56 208 417 449 385 385), lower := (rows 35 70 14 56 208 32 64 128 256), losses := [] }

theorem u34270 : Upper (D 7) (R 7) [34,68,10,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34271 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 35 70 14 56 273 225 193 193 449), lower := (rows 35 70 14 56 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 17 0 81 145 273), good := (rows 467 70 14 478 465 0 64 128 256) }] }

theorem u34271 : Upper (D 7) (R 7) [34,68,10,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34272 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,5)], upper := (rows 35 70 14 56 336 161 193 129 385), lower := (rows 35 70 14 56 336 32 64 128 256), losses := [] }

theorem u34272 : Upper (D 7) (R 7) [34,68,10,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34273 : Route 9 := (fun mask => (mask,id))

def c34273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34273 : Upper (D 7) (R 7) [34,68,10,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,10,48,384] 13 (by decide) (choices 1) [1,64,128] r34273 c34273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18853
  · exact u18854
  · exact u18855

def b34274 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 472, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 70 14 137 49 496 464 464 464), lower := (rows 35 70 14 137 49 32 64 128 256), losses := [] }

theorem u34274 : Upper (D 7) (R 7) [34,68,10,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34275 : Route 9 := (fun mask => (mask,id))

def c34275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u34275 : Upper (D 7) (R 7) [34,68,10,129,65] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,65] 13 (by decide) (choices 1) [16,128,256] r34275 c34275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18856
  · exact u18857
  · exact u18858

def r34276 : Route 9 := (fun mask => (mask,id))

def c34276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u34276 : Upper (D 7) (R 7) [34,68,10,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,96] 13 (by decide) (choices 1) [1,16,128,256] r34276 c34276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18859
  · exact u18860
  · exact u18861
  · exact u18862

def b34277 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 16, targets := 96 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 14 137 145 368 368 496 368), lower := (rows 35 70 14 137 145 32 64 128 256), losses := [] }

theorem u34277 : Upper (D 7) (R 7) [34,68,10,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34278 : Route 9 := (fun mask => (mask,id))

def c34278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34278 : Upper (D 7) (R 7) [34,68,10,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,160] 13 (by decide) (choices 1) [1,16,64,256] r34278 c34278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18863
  · exact u18864
  · exact u18865
  · exact u18866

def r34279 : Route 9 := (fun mask => (mask,id))

def c34279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34279 : Upper (D 7) (R 7) [34,68,10,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,192] 13 (by decide) (choices 1) [1,16,256] r34279 c34279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18867
  · exact u18868
  · exact u18869

def r34280 : Route 9 := (fun mask => (mask,id))

def c34280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34280 : Upper (D 7) (R 7) [34,68,10,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,257] 13 (by decide) (choices 1) [16,64,128] r34280 c34280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18870
  · exact u18871
  · exact u18872

def r34281 : Route 9 := (fun mask => (mask,id))

def c34281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34281 : Upper (D 7) (R 7) [34,68,10,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,288] 13 (by decide) (choices 1) [1,16,64,128] r34281 c34281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18873
  · exact u18874
  · exact u18875
  · exact u18876

def r34282 : Route 9 := (fun mask => (mask,id))

def c34282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34282 : Upper (D 7) (R 7) [34,68,10,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,320] 13 (by decide) (choices 1) [1,16,128] r34282 c34282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18877
  · exact u18878
  · exact u18879

def r34283 : Route 9 := (fun mask => (mask,id))

def c34283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34283 : Upper (D 7) (R 7) [34,68,10,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,384] 13 (by decide) (choices 1) [1,16,64] r34283 c34283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18880
  · exact u18881
  · exact u18882

def b34284 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 472, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 70 14 152 49 481 449 449 449), lower := (rows 35 70 14 152 49 32 64 128 256), losses := [] }

theorem u34284 : Upper (D 7) (R 7) [34,68,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34285 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 417, targets := 64 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 35 70 14 152 81 417 481 417 417), lower := (rows 35 70 14 152 81 32 64 128 256), losses := [] }

theorem u34285 : Upper (D 7) (R 7) [34,68,10,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34286 : Route 9 := (fun mask => (mask,id))

def c34286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34286 : Upper (D 7) (R 7) [34,68,10,144,96] 13 := by
  apply FastRouting.sound _ _ [34,68,10,144,96] 13 (by decide) (choices 1) [1,128,256] r34286 c34286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18883
  · exact u18884
  · exact u18885

def b34287 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 14 152 145 353 353 481 353), lower := (rows 35 70 14 152 145 32 64 128 256), losses := [] }

theorem u34287 : Upper (D 7) (R 7) [34,68,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34288 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 14 152 176 353 321 449 321), lower := (rows 35 70 14 152 176 32 64 128 256), losses := [] }

theorem u34288 : Upper (D 7) (R 7) [34,68,10,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34289 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 14, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 14 152 208 289 353 417 289), lower := (rows 35 70 14 152 208 32 64 128 256), losses := [] }

theorem u34289 : Upper (D 7) (R 7) [34,68,10,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34290 : Route 9 := (fun mask => (mask,id))

def c34290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34290 : Upper (D 7) (R 7) [34,68,10,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,10,144,257] 13 (by decide) (choices 1) [1,64,128] r34290 c34290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18886
  · exact u18887
  · exact u18888

def r34291 : Route 9 := (fun mask => (mask,id))

def c34291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34291 : Upper (D 7) (R 7) [34,68,10,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,10,144,288] 13 (by decide) (choices 1) [1,64,128] r34291 c34291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18889
  · exact u18890
  · exact u18891

def r34292 : Route 9 := (fun mask => (mask,id))

def c34292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34292 : Upper (D 7) (R 7) [34,68,10,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,10,144,320] 13 (by decide) (choices 1) [1,128] r34292 c34292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18892
  · exact u18893

def b34293 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 14 152 400 97 97 225 353), lower := (rows 35 70 14 152 400 32 64 128 256), losses := [] }

theorem u34293 : Upper (D 7) (R 7) [34,68,10,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34294 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(3,1),(3,6),(4,1),(4,5)], upper := (rows 35 70 14 168 81 433 465 401 401), lower := (rows 35 70 14 168 81 32 64 128 256), losses := [] }

theorem u34294 : Upper (D 7) (R 7) [34,68,10,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34295 : Route 9 := (fun mask => (mask,id))

def c34295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34295 : Upper (D 7) (R 7) [34,68,10,160,129] 13 := by
  apply FastRouting.sound _ _ [34,68,10,160,129] 13 (by decide) (choices 1) [1,16,64,256] r34295 c34295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18894
  · exact u18895
  · exact u18896
  · exact u18897

def r34296 : Route 9 := (fun mask => (mask,id))

def c34296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34296 : Upper (D 7) (R 7) [34,68,10,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,10,160,192] 13 (by decide) (choices 1) [1,16,256] r34296 c34296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18898
  · exact u18899
  · exact u18900

def r34297 : Route 9 := (fun mask => (mask,id))

def c34297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34297 : Upper (D 7) (R 7) [34,68,10,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,10,160,257] 13 (by decide) (choices 1) [1,16,64,128] r34297 c34297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18901
  · exact u18902
  · exact u18903
  · exact u18904

def r34298 : Route 9 := (fun mask => (mask,id))

def c34298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34298 : Upper (D 7) (R 7) [34,68,10,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,10,160,320] 13 (by decide) (choices 1) [1,16,128] r34298 c34298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18905
  · exact u18906
  · exact u18907

def r34299 : Route 9 := (fun mask => (mask,id))

def c34299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34299 : Upper (D 7) (R 7) [34,68,10,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,10,160,384] 13 (by decide) (choices 1) [1,16,64] r34299 c34299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18908
  · exact u18909
  · exact u18910

def b34300 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 472, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 70 14 265 49 240 208 208 464), lower := (rows 35 70 14 265 49 32 64 128 256), losses := [] }

theorem u34300 : Upper (D 7) (R 7) [34,68,10,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34301 : Route 9 := (fun mask => (mask,id))

def c34301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34301 : Upper (D 7) (R 7) [34,68,10,257,65] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,65] 13 (by decide) (choices 1) [16,128] r34301 c34301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18911
  · exact u18912

def r34302 : Route 9 := (fun mask => (mask,id))

def c34302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34302 : Upper (D 7) (R 7) [34,68,10,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,96] 13 (by decide) (choices 1) [1,16,128] r34302 c34302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18913
  · exact u18914
  · exact u18915

def r34303 : Route 9 := (fun mask => (mask,id))

def c34303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34303 : Upper (D 7) (R 7) [34,68,10,257,129] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,129] 13 (by decide) (choices 1) [16,64,128] r34303 c34303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18916
  · exact u18917
  · exact u18918

def r34304 : Route 9 := (fun mask => (mask,id))

def c34304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34304 : Upper (D 7) (R 7) [34,68,10,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,160] 13 (by decide) (choices 1) [1,16,64,128] r34304 c34304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18919
  · exact u18920
  · exact u18921
  · exact u18922

def r34305 : Route 9 := (fun mask => (mask,id))

def c34305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34305 : Upper (D 7) (R 7) [34,68,10,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,192] 13 (by decide) (choices 1) [1,16,128] r34305 c34305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18923
  · exact u18924
  · exact u18925

def b34306 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 472, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 70 14 280 49 225 193 193 449), lower := (rows 35 70 14 280 49 32 64 128 256), losses := [] }

theorem u34306 : Upper (D 7) (R 7) [34,68,10,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34307 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 161, targets := 64 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 35 70 14 280 81 161 225 161 417), lower := (rows 35 70 14 280 81 32 64 128 256), losses := [] }

theorem u34307 : Upper (D 7) (R 7) [34,68,10,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34308 : Route 9 := (fun mask => (mask,id))

def c34308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34308 : Upper (D 7) (R 7) [34,68,10,272,96] 13 := by
  apply FastRouting.sound _ _ [34,68,10,272,96] 13 (by decide) (choices 1) [1,128] r34308 c34308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18926
  · exact u18927

def r34309 : Route 9 := (fun mask => (mask,id))

def c34309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34309 : Upper (D 7) (R 7) [34,68,10,272,129] 13 := by
  apply FastRouting.sound _ _ [34,68,10,272,129] 13 (by decide) (choices 1) [1,64,128] r34309 c34309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18928
  · exact u18929
  · exact u18930

def r34310 : Route 9 := (fun mask => (mask,id))

def c34310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34310 : Upper (D 7) (R 7) [34,68,10,272,160] 13 := by
  apply FastRouting.sound _ _ [34,68,10,272,160] 13 (by decide) (choices 1) [1,64,128] r34310 c34310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18931
  · exact u18932
  · exact u18933

def r34311 : Route 9 := (fun mask => (mask,id))

def c34311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34311 : Upper (D 7) (R 7) [34,68,10,272,192] 13 := by
  apply FastRouting.sound _ _ [34,68,10,272,192] 13 (by decide) (choices 1) [1,128] r34311 c34311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18934
  · exact u18935

def b34312 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(3,1),(3,6),(4,1),(4,5)], upper := (rows 35 70 14 296 81 177 209 145 401), lower := (rows 35 70 14 296 81 32 64 128 256), losses := [] }

theorem u34312 : Upper (D 7) (R 7) [34,68,10,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34313 : Route 9 := (fun mask => (mask,id))

def c34313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34313 : Upper (D 7) (R 7) [34,68,10,288,129] 13 := by
  apply FastRouting.sound _ _ [34,68,10,288,129] 13 (by decide) (choices 1) [1,16,64,128] r34313 c34313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18936
  · exact u18937
  · exact u18938
  · exact u18939

def r34314 : Route 9 := (fun mask => (mask,id))

def c34314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34314 : Upper (D 7) (R 7) [34,68,10,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,10,288,192] 13 (by decide) (choices 1) [1,16,128] r34314 c34314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18940
  · exact u18941
  · exact u18942

def b34315 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 472, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 70 14 392 49 241 209 209 465), lower := (rows 35 70 14 392 49 32 64 128 256), losses := [] }

theorem u34315 : Upper (D 7) (R 7) [34,68,10,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34316 : Route 9 := (fun mask => (mask,id))

def c34316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34316 : Upper (D 7) (R 7) [34,68,10,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384,65] 13 (by decide) (choices 1) [1,16,128] r34316 c34316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18943
  · exact u18944
  · exact u18945

def r34317 : Route 9 := (fun mask => (mask,id))

def c34317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34317 : Upper (D 7) (R 7) [34,68,10,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384,96] 13 (by decide) (choices 1) [1,16,128] r34317 c34317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18946
  · exact u18947
  · exact u18948

def r34318 : Route 9 := (fun mask => (mask,id))

def c34318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34318 : Upper (D 7) (R 7) [34,68,10,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384,129] 13 (by decide) (choices 1) [1,16,64] r34318 c34318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18949
  · exact u18950
  · exact u18951

def r34319 : Route 9 := (fun mask => (mask,id))

def c34319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34319 : Upper (D 7) (R 7) [34,68,10,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384,160] 13 (by decide) (choices 1) [1,16,64] r34319 c34319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18952
  · exact u18953
  · exact u18954

#print axioms u34319
end Delivery.IrregularNine14.P07
