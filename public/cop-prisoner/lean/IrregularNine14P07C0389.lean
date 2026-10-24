import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0123

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r23340 : Route 9 := (fun mask => (mask,id))

def c23340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23340 : Upper (D 7) (R 7) [36,72,130,288,65,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288,65,16] 13 (by decide) (choices 1) [1,2,128] r23340 c23340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7385
  · exact u7386
  · exact u7387

def b23341 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 296 81 160 83 147 275), lower := (rows 37 74 134 296 81 160 64 128 256), losses := [] }

theorem u23341 : Upper (D 7) (R 7) [36,72,130,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23342 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 134 296 145 33 82 210 338), lower := (rows 37 74 134 296 145 33 64 128 256), losses := [] }

theorem u23342 : Upper (D 7) (R 7) [36,72,130,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23343 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 74 134 296 145 34 81 209 337), lower := (rows 37 74 134 296 145 34 64 128 256), losses := [] }

theorem u23343 : Upper (D 7) (R 7) [36,72,130,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23344 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 134 296 145 48 67 195 323), lower := (rows 37 74 134 296 145 48 64 128 256), losses := [] }

theorem u23344 : Upper (D 7) (R 7) [36,72,130,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23344 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23345 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 74 134 296 145 96 83 147 275), lower := (rows 37 74 134 296 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 20 98 64 128 256), good := (rows 53 104 181 296 145 96 96 128 256) }] }

theorem u23345 : Upper (D 7) (R 7) [36,72,130,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23346 : Route 9 := (fun mask => (mask,id))

def c23346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23346 : Upper (D 7) (R 7) [36,72,130,288,192,1] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288,192,1] 13 (by decide) (choices 1) [1,2,16] r23346 c23346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7388
  · exact u7389
  · exact u7390

def b23347 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 134 296 208 34 81 145 273), lower := (rows 37 74 134 296 208 34 64 128 256), losses := [] }

theorem u23347 : Upper (D 7) (R 7) [36,72,130,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23348 : Route 9 := (fun mask => (mask,id))

def c23348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23348 : Upper (D 7) (R 7) [36,72,130,288,192,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288,192,16] 13 (by decide) (choices 1) [1,2] r23348 c23348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7391
  · exact u7392

def b23349 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 74 134 392 19 33 112 240 368), lower := (rows 37 74 134 392 19 33 64 128 256), losses := [] }

theorem u23349 : Upper (D 7) (R 7) [36,72,130,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23350 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 74 134 392 19 48 97 225 353), lower := (rows 37 74 134 392 19 48 64 128 256), losses := [] }

theorem u23350 : Upper (D 7) (R 7) [36,72,130,384,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23350 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23351 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(0,7),(3,1),(4,7)], upper := (rows 37 74 134 392 19 96 113 177 305), lower := (rows 37 74 134 392 19 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 114 80 144 272), good := (rows 37 104 165 392 505 96 96 128 256) }] }

theorem u23351 : Upper (D 7) (R 7) [36,72,130,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23352 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 74 134 392 50 33 81 209 337), lower := (rows 37 74 134 392 50 33 64 128 256), losses := [] }

theorem u23352 : Upper (D 7) (R 7) [36,72,130,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23353 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 392 50 48 65 193 321), lower := (rows 37 74 134 392 50 48 64 128 256), losses := [] }

theorem u23353 : Upper (D 7) (R 7) [36,72,130,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23353 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23354 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 134 392 50 96 81 145 273), lower := (rows 37 74 134 392 50 96 64 128 256), losses := [] }

theorem u23354 : Upper (D 7) (R 7) [36,72,130,384,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23355 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,7)], upper := (rows 37 74 134 392 81 33 114 178 306), lower := (rows 37 74 134 392 81 33 64 128 256), losses := [] }

theorem u23355 : Upper (D 7) (R 7) [36,72,130,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23356 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 37 74 134 392 81 34 113 177 305), lower := (rows 37 74 134 392 81 34 64 128 256), losses := [] }

theorem u23356 : Upper (D 7) (R 7) [36,72,130,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23357 : Route 9 := (fun mask => (mask,id))

def c23357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23357 : Upper (D 7) (R 7) [36,72,130,384,65,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,384,65,16] 13 (by decide) (choices 1) [1,2,32] r23357 c23357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7393
  · exact u7394
  · exact u7395

def b23358 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,7)], upper := (rows 37 74 134 392 112 33 83 147 275), lower := (rows 37 74 134 392 112 33 64 128 256), losses := [] }

theorem u23358 : Upper (D 7) (R 7) [36,72,130,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23359 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 74 134 392 112 34 81 145 273), lower := (rows 37 74 134 392 112 34 64 128 256), losses := [] }

theorem u23359 : Upper (D 7) (R 7) [36,72,130,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23360 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 392 112 48 67 131 259), lower := (rows 37 74 134 392 112 48 64 128 256), losses := [] }

theorem u23360 : Upper (D 7) (R 7) [36,72,130,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23360 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23361 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 148 168 19 33 322 450 322), lower := (rows 37 74 148 168 19 33 64 128 256), losses := [] }

theorem u23361 : Upper (D 7) (R 7) [36,72,144,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23362 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 452, targets := 34 },{ cop := 0, region := 456, targets := 2 }], pairs := [(2,1),(2,5),(3,0),(3,1)], upper := (rows 37 74 148 168 19 34 321 449 321), lower := (rows 37 74 148 168 19 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 50 64 128 256), good := (rows 44 106 188 168 50 34 64 128 256) }] }

theorem u23362 : Upper (D 7) (R 7) [36,72,144,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23363 : Route 9 := (fun mask => (mask,id))

def c23363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23363 : Upper (D 7) (R 7) [36,72,144,160,3,64] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,3,64] 13 (by decide) (choices 1) [1,2,256] r23363 c23363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7396
  · exact u7397
  · exact u7398

def r23364 : Route 9 := (fun mask => (mask,id))

def c23364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23364 : Upper (D 7) (R 7) [36,72,144,160,3,256] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,3,256] 13 (by decide) (choices 1) [1,2] r23364 c23364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7399
  · exact u7400

def b23365 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 148 168 81 33 322 386 258), lower := (rows 37 74 148 168 81 33 64 128 256), losses := [] }

theorem u23365 : Upper (D 7) (R 7) [36,72,144,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23366 : Route 9 := (fun mask => (mask,id))

def c23366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23366 : Upper (D 7) (R 7) [36,72,144,160,65,2] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,65,2] 13 (by decide) (choices 1) [1,2,256] r23366 c23366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7401
  · exact u7402
  · exact u7403

def r23367 : Route 9 := (fun mask => (mask,id))

def c23367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23367 : Upper (D 7) (R 7) [36,72,144,160,65,256] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,65,256] 13 (by decide) (choices 1) [1,2] r23367 c23367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7404
  · exact u7405

def b23368 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 148 168 273 33 66 194 322), lower := (rows 37 74 148 168 273 33 64 128 256), losses := [] }

theorem u23368 : Upper (D 7) (R 7) [36,72,144,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23369 : Route 9 := (fun mask => (mask,id))

def c23369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23369 : Upper (D 7) (R 7) [36,72,144,160,257,2] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,257,2] 13 (by decide) (choices 1) [1,2] r23369 c23369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7406
  · exact u7407

def r23370 : Route 9 := (fun mask => (mask,id))

def c23370 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23370 : Upper (D 7) (R 7) [36,72,144,160,257,64] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,257,64] 13 (by decide) (choices 1) [1,2] r23370 c23370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7408
  · exact u7409

def b23371 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 148 168 274 33 67 195 323), lower := (rows 37 74 148 168 274 33 64 128 256), losses := [] }

theorem u23371 : Upper (D 7) (R 7) [36,72,144,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23372 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,0),(3,1),(3,6)], upper := (rows 37 74 148 168 274 34 65 193 321), lower := (rows 37 74 148 168 274 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 50 64 128 256), good := (rows 44 106 188 168 306 34 64 128 256) },{ target := 6, region := (rows 5 2 4 12 16 50 0 128 256), good := (rows 45 42 189 168 306 34 0 128 256) }] }

theorem u23372 : Upper (D 7) (R 7) [36,72,144,160,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23373 : Route 9 := (fun mask => (mask,id))

def c23373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23373 : Upper (D 7) (R 7) [36,72,144,160,258,64] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,258,64] 13 (by decide) (choices 1) [1,2] r23373 c23373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7410
  · exact u7411

def b23374 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 148 168 336 33 67 131 259), lower := (rows 37 74 148 168 336 33 64 128 256), losses := [] }

theorem u23374 : Upper (D 7) (R 7) [36,72,144,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23375 : Route 9 := (fun mask => (mask,id))

def c23375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23375 : Upper (D 7) (R 7) [36,72,144,160,320,2] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,320,2] 13 (by decide) (choices 1) [1,2] r23375 c23375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7412
  · exact u7413

def b23376 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 456, targets := 2 },{ cop := 3, region := 226, targets := 1 },{ cop := 4, region := 228, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(3,1)], upper := (rows 37 74 148 265 19 34 224 224 480), lower := (rows 37 74 148 265 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 32 97 161 289), good := (rows 493 72 156 457 477 480 64 128 256) }] }

theorem u23376 : Upper (D 7) (R 7) [36,72,144,257,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23377 : Route 9 := (fun mask => (mask,id))

def c23377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23377 : Upper (D 7) (R 7) [36,72,144,257,3,64] 13 := by
  apply FastRouting.sound _ _ [36,72,144,257,3,64] 13 (by decide) (choices 1) [2,32,128] r23377 c23377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7414
  · exact u7415
  · exact u7416

def b23378 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 265 19 160 98 226 354), lower := (rows 37 74 148 265 19 160 64 128 256), losses := [] }

theorem u23378 : Upper (D 7) (R 7) [36,72,144,257,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23379 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 148 265 50 33 194 194 450), lower := (rows 37 74 148 265 50 33 64 128 256), losses := [] }

theorem u23379 : Upper (D 7) (R 7) [36,72,144,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23380 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 74 148 265 50 34 193 193 449), lower := (rows 37 74 148 265 50 34 64 128 256), losses := [] }

theorem u23380 : Upper (D 7) (R 7) [36,72,144,257,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23381 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(3,6)], upper := (rows 37 74 148 265 50 96 195 131 387), lower := (rows 37 74 148 265 50 96 64 128 256), losses := [] }

theorem u23381 : Upper (D 7) (R 7) [36,72,144,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23382 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 330, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 265 50 160 67 195 323), lower := (rows 37 74 148 265 50 160 64 128 256), losses := [] }

theorem u23382 : Upper (D 7) (R 7) [36,72,144,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23383 : Route 9 := (fun mask => (mask,id))

def c23383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23383 : Upper (D 7) (R 7) [36,72,144,257,65,2] 13 := by
  apply FastRouting.sound _ _ [36,72,144,257,65,2] 13 (by decide) (choices 1) [2,32,128] r23383 c23383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7417
  · exact u7418
  · exact u7419

def b23384 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 265 81 160 98 162 290), lower := (rows 37 74 148 265 81 160 64 128 256), losses := [] }

theorem u23384 : Upper (D 7) (R 7) [36,72,144,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23385 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 148 265 112 33 194 130 386), lower := (rows 37 74 148 265 112 33 64 128 256), losses := [] }

theorem u23385 : Upper (D 7) (R 7) [36,72,144,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23386 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 1, region := 48, targets := 129 }], pairs := [(1,5),(3,5),(4,0),(4,7)], upper := (rows 37 74 148 265 112 34 195 131 387), lower := (rows 37 74 148 265 112 34 64 128 256), losses := [] }

theorem u23386 : Upper (D 7) (R 7) [36,72,144,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23387 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 330, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 265 112 160 67 131 259), lower := (rows 37 74 148 265 112 160 64 128 256), losses := [] }

theorem u23387 : Upper (D 7) (R 7) [36,72,144,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23388 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 37 74 148 266 19 33 224 224 480), lower := (rows 37 74 148 266 19 33 64 128 256), losses := [] }

theorem u23388 : Upper (D 7) (R 7) [36,72,144,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23389 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(2,1),(2,6),(3,6)], upper := (rows 37 74 148 266 19 96 225 161 417), lower := (rows 37 74 148 266 19 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 32 0 129 257), good := (rows 421 10 156 266 415 32 0 128 256) }] }

theorem u23389 : Upper (D 7) (R 7) [36,72,144,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23390 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 266 19 160 97 225 353), lower := (rows 37 74 148 266 19 160 64 128 256), losses := [] }

theorem u23390 : Upper (D 7) (R 7) [36,72,144,258,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23391 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 148 266 81 33 226 162 418), lower := (rows 37 74 148 266 81 33 64 128 256), losses := [] }

theorem u23391 : Upper (D 7) (R 7) [36,72,144,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23392 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 213, targets := 2 }], pairs := [(0,1),(2,1),(2,6),(4,1)], upper := (rows 37 74 148 266 81 34 225 161 417), lower := (rows 37 74 148 266 81 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 8 16 42 0 129 257), good := (rows 421 42 148 298 405 34 0 128 256) }] }

theorem u23392 : Upper (D 7) (R 7) [36,72,144,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23393 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 266 81 160 99 163 291), lower := (rows 37 74 148 266 81 160 64 128 256), losses := [] }

theorem u23393 : Upper (D 7) (R 7) [36,72,144,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23394 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 148 266 112 33 195 131 387), lower := (rows 37 74 148 266 112 33 64 128 256), losses := [] }

theorem u23394 : Upper (D 7) (R 7) [36,72,144,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23395 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 74 148 266 112 34 193 129 385), lower := (rows 37 74 148 266 112 34 64 128 256), losses := [] }

theorem u23395 : Upper (D 7) (R 7) [36,72,144,258,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23396 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 330, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 74 148 266 112 160 67 131 259), lower := (rows 37 74 148 266 112 160 64 128 256), losses := [] }

theorem u23396 : Upper (D 7) (R 7) [36,72,144,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23397 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 148 296 19 33 194 194 450), lower := (rows 37 74 148 296 19 33 64 128 256), losses := [] }

theorem u23397 : Upper (D 7) (R 7) [36,72,144,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23398 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 196, targets := 34 },{ cop := 0, region := 456, targets := 2 }], pairs := [(0,6),(2,1),(2,5),(3,1)], upper := (rows 37 74 148 296 19 34 193 193 449), lower := (rows 37 74 148 296 19 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 50 0 128 256), good := (rows 37 42 181 296 51 34 0 128 256) }] }

theorem u23398 : Upper (D 7) (R 7) [36,72,144,288,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23399 : Route 9 := (fun mask => (mask,id))

def c23399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23399 : Upper (D 7) (R 7) [36,72,144,288,3,64] 13 := by
  apply FastRouting.sound _ _ [36,72,144,288,3,64] 13 (by decide) (choices 1) [1,2,128] r23399 c23399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7420
  · exact u7421
  · exact u7422

#print axioms u23399
end Delivery.IrregularNine14.P07
