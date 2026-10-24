import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0088

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19320 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 152 280 34 97 225 353), lower := (rows 35 70 133 152 280 34 64 128 256), losses := [] }

theorem u19320 : Upper (D 7) (R 7) [34,68,129,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19321 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 152 280 96 99 163 291), lower := (rows 35 70 133 152 280 96 64 128 256), losses := [] }

theorem u19321 : Upper (D 7) (R 7) [34,68,129,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19322 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 152 304 33 74 202 330), lower := (rows 35 70 133 152 304 33 64 128 256), losses := [] }

theorem u19322 : Upper (D 7) (R 7) [34,68,129,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19323 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 152 304 34 73 201 329), lower := (rows 35 70 133 152 304 34 64 128 256), losses := [] }

theorem u19323 : Upper (D 7) (R 7) [34,68,129,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19324 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,5),(2,5),(4,7)], upper := (rows 35 70 133 152 304 40 67 195 323), lower := (rows 35 70 133 152 304 40 64 128 256), losses := [] }

theorem u19324 : Upper (D 7) (R 7) [34,68,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19324 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19325 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 152 304 96 75 139 267), lower := (rows 35 70 133 152 304 96 64 128 256), losses := [] }

theorem u19325 : Upper (D 7) (R 7) [34,68,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19326 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 152 336 33 106 170 298), lower := (rows 35 70 133 152 336 33 64 128 256), losses := [] }

theorem u19326 : Upper (D 7) (R 7) [34,68,129,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19327 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 152 336 34 105 169 297), lower := (rows 35 70 133 152 336 34 64 128 256), losses := [] }

theorem u19327 : Upper (D 7) (R 7) [34,68,129,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19328 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 132, targets := 64 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,7),(2,6),(4,7)], upper := (rows 35 70 133 152 336 40 99 163 291), lower := (rows 35 70 133 152 336 40 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 21 40 65 0 257), good := (rows 371 86 343 56 336 40 64 0 256) }] }

theorem u19328 : Upper (D 7) (R 7) [34,68,129,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19328 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19329 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 168 273 34 88 216 344), lower := (rows 35 70 133 168 273 34 64 128 256), losses := [] }

theorem u19329 : Upper (D 7) (R 7) [34,68,129,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19330 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 168 273 40 82 210 338), lower := (rows 35 70 133 168 273 40 64 128 256), losses := [] }

theorem u19330 : Upper (D 7) (R 7) [34,68,129,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19330 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19331 : Route 9 := (fun mask => (mask,id))

def c19331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19331 : Upper (D 7) (R 7) [34,68,129,160,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,257,16] 13 (by decide) (choices 1) [2,8] r19331 c19331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5287
  · exact u5288

def b19332 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 168 273 96 90 154 282), lower := (rows 35 70 133 168 273 96 64 128 256), losses := [] }

theorem u19332 : Upper (D 7) (R 7) [34,68,129,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19333 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 168 274 33 88 216 344), lower := (rows 35 70 133 168 274 33 64 128 256), losses := [] }

theorem u19333 : Upper (D 7) (R 7) [34,68,129,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19334 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 168 274 40 81 209 337), lower := (rows 35 70 133 168 274 40 64 128 256), losses := [] }

theorem u19334 : Upper (D 7) (R 7) [34,68,129,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19334 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19335 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 133 168 274 48 73 201 329), lower := (rows 35 70 133 168 274 48 64 128 256), losses := [] }

theorem u19335 : Upper (D 7) (R 7) [34,68,129,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19335 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19336 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 168 274 96 89 153 281), lower := (rows 35 70 133 168 274 96 64 128 256), losses := [] }

theorem u19336 : Upper (D 7) (R 7) [34,68,129,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19337 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 168 280 33 82 210 338), lower := (rows 35 70 133 168 280 33 64 128 256), losses := [] }

theorem u19337 : Upper (D 7) (R 7) [34,68,129,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19338 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 168 280 34 81 209 337), lower := (rows 35 70 133 168 280 34 64 128 256), losses := [] }

theorem u19338 : Upper (D 7) (R 7) [34,68,129,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19339 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 70 133 168 280 48 67 195 323), lower := (rows 35 70 133 168 280 48 64 128 256), losses := [] }

theorem u19339 : Upper (D 7) (R 7) [34,68,129,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19339 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19340 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 168 280 96 83 147 275), lower := (rows 35 70 133 168 280 96 64 128 256), losses := [] }

theorem u19340 : Upper (D 7) (R 7) [34,68,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19341 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 168 336 33 90 154 282), lower := (rows 35 70 133 168 336 33 64 128 256), losses := [] }

theorem u19341 : Upper (D 7) (R 7) [34,68,129,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19342 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 168 336 34 89 153 281), lower := (rows 35 70 133 168 336 34 64 128 256), losses := [] }

theorem u19342 : Upper (D 7) (R 7) [34,68,129,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19343 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 168 336 40 83 147 275), lower := (rows 35 70 133 168 336 40 64 128 256), losses := [] }

theorem u19343 : Upper (D 7) (R 7) [34,68,129,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19343 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19344 : Route 9 := (fun mask => (mask,id))

def c19344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19344 : Upper (D 7) (R 7) [34,68,129,160,320,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,320,16] 13 (by decide) (choices 1) [1,2,8] r19344 c19344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5289
  · exact u5290
  · exact u5291

def b19345 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 200 273 34 120 184 312), lower := (rows 35 70 133 200 273 34 64 128 256), losses := [] }

theorem u19345 : Upper (D 7) (R 7) [34,68,129,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19346 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(2,6),(4,6),(4,7)], upper := (rows 35 70 133 200 273 40 114 178 306), lower := (rows 35 70 133 200 273 40 64 128 256), losses := [] }

theorem u19346 : Upper (D 7) (R 7) [34,68,129,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19346 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19347 : Route 9 := (fun mask => (mask,id))

def c19347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19347 : Upper (D 7) (R 7) [34,68,129,192,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,257,16] 13 (by decide) (choices 1) [2,8,32] r19347 c19347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5292
  · exact u5293
  · exact u5294

def b19348 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 200 274 33 120 184 312), lower := (rows 35 70 133 200 274 33 64 128 256), losses := [] }

theorem u19348 : Upper (D 7) (R 7) [34,68,129,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19349 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(2,6),(4,6),(4,7)], upper := (rows 35 70 133 200 274 40 113 177 305), lower := (rows 35 70 133 200 274 40 64 128 256), losses := [] }

theorem u19349 : Upper (D 7) (R 7) [34,68,129,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19349 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19350 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 133 200 274 48 105 169 297), lower := (rows 35 70 133 200 274 48 64 128 256), losses := [] }

theorem u19350 : Upper (D 7) (R 7) [34,68,129,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19350 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19351 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 200 280 33 114 178 306), lower := (rows 35 70 133 200 280 33 64 128 256), losses := [] }

theorem u19351 : Upper (D 7) (R 7) [34,68,129,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19352 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 200 280 34 113 177 305), lower := (rows 35 70 133 200 280 34 64 128 256), losses := [] }

theorem u19352 : Upper (D 7) (R 7) [34,68,129,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19353 : Route 9 := (fun mask => (mask,id))

def c19353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19353 : Upper (D 7) (R 7) [34,68,129,192,264,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,264,16] 13 (by decide) (choices 1) [1,2,32] r19353 c19353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5295
  · exact u5296
  · exact u5297

def b19354 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 200 304 33 90 154 282), lower := (rows 35 70 133 200 304 33 64 128 256), losses := [] }

theorem u19354 : Upper (D 7) (R 7) [34,68,129,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19355 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 200 304 34 89 153 281), lower := (rows 35 70 133 200 304 34 64 128 256), losses := [] }

theorem u19355 : Upper (D 7) (R 7) [34,68,129,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19356 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(2,6),(4,6),(4,7)], upper := (rows 35 70 133 200 304 40 83 147 275), lower := (rows 35 70 133 200 304 40 64 128 256), losses := [] }

theorem u19356 : Upper (D 7) (R 7) [34,68,129,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19356 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19357 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 133 200 304 48 75 139 267), lower := (rows 35 70 133 200 304 48 64 128 256), losses := [] }

theorem u19357 : Upper (D 7) (R 7) [34,68,129,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19357 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19358 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 198, targets := 1 },{ cop := 0, region := 472, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 70 134 25 280 33 224 224 480), lower := (rows 35 70 134 25 280 33 64 128 256), losses := [] }

theorem u19358 : Upper (D 7) (R 7) [34,68,130,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19359 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 25 280 96 225 161 417), lower := (rows 35 70 134 25 280 96 64 128 256), losses := [] }

theorem u19359 : Upper (D 7) (R 7) [34,68,130,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19360 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 25 280 160 97 225 353), lower := (rows 35 70 134 25 280 160 64 128 256), losses := [] }

theorem u19360 : Upper (D 7) (R 7) [34,68,130,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19361 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 25 336 33 232 168 424), lower := (rows 35 70 134 25 336 33 64 128 256), losses := [] }

theorem u19361 : Upper (D 7) (R 7) [34,68,130,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19362 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 25 336 40 225 161 417), lower := (rows 35 70 134 25 336 40 64 128 256), losses := [] }

theorem u19362 : Upper (D 7) (R 7) [34,68,130,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19362 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19363 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 25 336 160 105 169 297), lower := (rows 35 70 134 25 336 160 64 128 256), losses := [] }

theorem u19363 : Upper (D 7) (R 7) [34,68,130,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19364 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 25 400 33 104 232 360), lower := (rows 35 70 134 25 400 33 64 128 256), losses := [] }

theorem u19364 : Upper (D 7) (R 7) [34,68,130,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19365 : Route 9 := (fun mask => (mask,id))

def c19365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19365 : Upper (D 7) (R 7) [34,68,130,17,384,8] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,384,8] 13 (by decide) (choices 1) [1,32] r19365 c19365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5298
  · exact u5299

def b19366 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 25 400 96 105 169 297), lower := (rows 35 70 134 25 400 96 64 128 256), losses := [] }

theorem u19366 : Upper (D 7) (R 7) [34,68,130,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19367 : PairBound 9 := { available := 392, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 56 81 33 456 392 392), lower := (rows 35 70 134 56 81 33 64 128 256), losses := [] }

theorem u19367 : Upper (D 7) (R 7) [34,68,130,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19368 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 134 56 81 40 449 385 385), lower := (rows 35 70 134 56 81 40 64 128 256), losses := [] }

theorem u19368 : Upper (D 7) (R 7) [34,68,130,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19368 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19369 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 56 81 160 329 393 265), lower := (rows 35 70 134 56 81 160 64 128 256), losses := [] }

theorem u19369 : Upper (D 7) (R 7) [34,68,130,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19370 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 4, region := 424, targets := 64 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 70 134 56 81 288 201 137 393), lower := (rows 35 70 134 56 81 288 64 128 256), losses := [] }

theorem u19370 : Upper (D 7) (R 7) [34,68,130,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19370 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19371 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 56 145 33 328 456 328), lower := (rows 35 70 134 56 145 33 64 128 256), losses := [] }

theorem u19371 : Upper (D 7) (R 7) [34,68,130,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19372 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 134 56 145 40 321 449 321), lower := (rows 35 70 134 56 145 40 64 128 256), losses := [] }

theorem u19372 : Upper (D 7) (R 7) [34,68,130,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19372 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19373 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 56 145 96 329 393 265), lower := (rows 35 70 134 56 145 96 64 128 256), losses := [] }

theorem u19373 : Upper (D 7) (R 7) [34,68,130,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19374 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 4, region := 360, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 134 56 145 288 73 201 329), lower := (rows 35 70 134 56 145 288 64 128 256), losses := [] }

theorem u19374 : Upper (D 7) (R 7) [34,68,130,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19374 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19375 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 56 273 33 200 200 456), lower := (rows 35 70 134 56 273 33 64 128 256), losses := [] }

theorem u19375 : Upper (D 7) (R 7) [34,68,130,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19376 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 134 56 273 40 193 193 449), lower := (rows 35 70 134 56 273 40 64 128 256), losses := [] }

theorem u19376 : Upper (D 7) (R 7) [34,68,130,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19376 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19377 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 56 273 96 201 137 393), lower := (rows 35 70 134 56 273 96 64 128 256), losses := [] }

theorem u19377 : Upper (D 7) (R 7) [34,68,130,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19378 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 56 273 160 73 201 329), lower := (rows 35 70 134 56 273 160 64 128 256), losses := [] }

theorem u19378 : Upper (D 7) (R 7) [34,68,130,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19379 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 56 336 33 201 137 393), lower := (rows 35 70 134 56 336 33 64 128 256), losses := [] }

theorem u19379 : Upper (D 7) (R 7) [34,68,130,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19379
end Delivery.IrregularNine14.P07
