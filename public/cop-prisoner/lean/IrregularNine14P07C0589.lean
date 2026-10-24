import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0340
import IrregularNine14P07C0341

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35340 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 14 268 208 49 113 177 305), lower := (rows 35 194 14 268 208 32 64 128 256), losses := [] }

theorem u35340 : Upper (D 7) (R 7) [34,192,10,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35341 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 14 280 49 229 197 197 453), lower := (rows 35 194 14 280 49 32 64 128 256), losses := [] }

theorem u35341 : Upper (D 7) (R 7) [34,192,10,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35342 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35342 : Upper (D 7) (R 7) [34,192,10,272,36] 13 := by
  apply FastRouting.sound _ _ [34,192,10,272,36] 13 (by decide) (choices 1) [1,64] r35342 c35342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20426
  · exact u20427

def r35343 : Route 9 := (fun mask => (mask,id))

def c35343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35343 : Upper (D 7) (R 7) [34,192,10,272,65] 13 := by
  apply FastRouting.sound _ _ [34,192,10,272,65] 13 (by decide) (choices 1) [1,4,128] r35343 c35343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20428
  · exact u20429
  · exact u20430

def r35344 : Route 9 := (fun mask => (mask,id))

def c35344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35344 : Upper (D 7) (R 7) [34,192,10,272,68] 13 := by
  apply FastRouting.sound _ _ [34,192,10,272,68] 13 (by decide) (choices 1) [1,128] r35344 c35344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20431
  · exact u20432

def r35345 : Route 9 := (fun mask => (mask,id))

def c35345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35345 : Upper (D 7) (R 7) [34,192,10,272,96] 13 := by
  apply FastRouting.sound _ _ [34,192,10,272,96] 13 (by decide) (choices 1) [1,4,128] r35345 c35345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20433
  · exact u20434
  · exact u20435

def b35346 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 14 280 208 37 101 165 293), lower := (rows 35 194 14 280 208 32 64 128 256), losses := [] }

theorem u35346 : Upper (D 7) (R 7) [34,192,10,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35347 : Route 9 := (fun mask => (mask,id))

def c35347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35347 : Upper (D 7) (R 7) [34,192,10,288,65] 13 := by
  apply FastRouting.sound _ _ [34,192,10,288,65] 13 (by decide) (choices 1) [1,4,16,128] r35347 c35347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20436
  · exact u20437
  · exact u20438
  · exact u20439

def r35348 : Route 9 := (fun mask => (mask,id))

def c35348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35348 : Upper (D 7) (R 7) [34,192,10,288,68] 13 := by
  apply FastRouting.sound _ _ [34,192,10,288,68] 13 (by decide) (choices 1) [1,16,128] r35348 c35348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20440
  · exact u20441
  · exact u20442

def b35349 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 14 296 208 53 85 149 277), lower := (rows 35 194 14 296 208 32 64 128 256), losses := [] }

theorem u35349 : Upper (D 7) (R 7) [34,192,10,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35350 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 14 328 49 181 213 149 405), lower := (rows 35 194 14 328 49 32 64 128 256), losses := [] }

theorem u35350 : Upper (D 7) (R 7) [34,192,10,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35351 : Route 9 := (fun mask => (mask,id))

def c35351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35351 : Upper (D 7) (R 7) [34,192,10,320,36] 13 := by
  apply FastRouting.sound _ _ [34,192,10,320,36] 13 (by decide) (choices 1) [1,16,128] r35351 c35351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20443
  · exact u20444
  · exact u20445

def r35352 : Route 9 := (fun mask => (mask,id))

def c35352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35352 : Upper (D 7) (R 7) [34,192,10,320,129] 13 := by
  apply FastRouting.sound _ _ [34,192,10,320,129] 13 (by decide) (choices 1) [1,4,16] r35352 c35352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20446
  · exact u20447
  · exact u20448

def r35353 : Route 9 := (fun mask => (mask,id))

def c35353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35353 : Upper (D 7) (R 7) [34,192,10,320,132] 13 := by
  apply FastRouting.sound _ _ [34,192,10,320,132] 13 (by decide) (choices 1) [1,16] r35353 c35353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20449
  · exact u20450

def r35354 : Route 9 := (fun mask => (mask,id))

def c35354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35354 : Upper (D 7) (R 7) [34,192,10,320,160] 13 := by
  apply FastRouting.sound _ _ [34,192,10,320,160] 13 (by decide) (choices 1) [1,4,16] r35354 c35354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20451
  · exact u20452
  · exact u20453

def b35355 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 194 28 41 81 422 454 390 390), lower := (rows 35 194 28 41 81 32 64 128 256), losses := [] }

theorem u35355 : Upper (D 7) (R 7) [34,192,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35356 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 194 28 41 84 419 451 387 387), lower := (rows 35 194 28 41 84 32 64 128 256), losses := [] }

theorem u35356 : Upper (D 7) (R 7) [34,192,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35357 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 194 28 41 273 230 198 198 454), lower := (rows 35 194 28 41 273 32 64 128 256), losses := [] }

theorem u35357 : Upper (D 7) (R 7) [34,192,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35358 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 194 28 41 274 229 197 197 453), lower := (rows 35 194 28 41 274 32 64 128 256), losses := [] }

theorem u35358 : Upper (D 7) (R 7) [34,192,24,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35359 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 194 28 41 276 227 195 195 451), lower := (rows 35 194 28 41 276 32 64 128 256), losses := [] }

theorem u35359 : Upper (D 7) (R 7) [34,192,24,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35360 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 194 28 41 336 167 199 135 391), lower := (rows 35 194 28 41 336 32 64 128 256), losses := [] }

theorem u35360 : Upper (D 7) (R 7) [34,192,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35361 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 194 28 42 81 421 453 389 389), lower := (rows 35 194 28 42 81 32 64 128 256), losses := [] }

theorem u35361 : Upper (D 7) (R 7) [34,192,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35362 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 297, targets := 64 },{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(3,0),(3,6)], upper := (rows 35 194 28 42 84 417 449 385 385), lower := (rows 35 194 28 42 84 32 64 128 256), losses := [] }

theorem u35362 : Upper (D 7) (R 7) [34,192,24,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35363 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 194 28 42 273 229 197 197 453), lower := (rows 35 194 28 42 273 32 64 128 256), losses := [] }

theorem u35363 : Upper (D 7) (R 7) [34,192,24,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35364 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 194 28 42 276 225 193 193 449), lower := (rows 35 194 28 42 276 32 64 128 256), losses := [] }

theorem u35364 : Upper (D 7) (R 7) [34,192,24,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35365 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 194 28 42 336 165 197 133 389), lower := (rows 35 194 28 42 336 32 64 128 256), losses := [] }

theorem u35365 : Upper (D 7) (R 7) [34,192,24,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35366 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(2,6),(4,5)], upper := (rows 35 194 28 44 81 419 451 387 387), lower := (rows 35 194 28 44 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 35 0 131 259), good := (rows 419 419 28 44 445 32 0 128 256) }] }

theorem u35366 : Upper (D 7) (R 7) [34,192,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35367 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 28 44 82 417 449 385 385), lower := (rows 35 194 28 44 82 32 64 128 256), losses := [] }

theorem u35367 : Upper (D 7) (R 7) [34,192,24,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35368 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,5),(4,0),(4,1),(4,5)], upper := (rows 35 194 28 44 208 291 323 387 259), lower := (rows 35 194 28 44 208 32 64 128 256), losses := [] }

theorem u35368 : Upper (D 7) (R 7) [34,192,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35369 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35369 : Upper (D 7) (R 7) [34,192,24,36,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,36,257] 13 (by decide) (choices 1) [1,2,64] r35369 c35369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20454
  · exact u20455
  · exact u20456

def r35370 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35370 : Upper (D 7) (R 7) [34,192,24,36,258] 13 := by
  apply FastRouting.sound _ _ [34,192,24,36,258] 13 (by decide) (choices 1) [1,64] r35370 c35370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20457
  · exact u20458

def r35371 : Route 9 := (fun mask => (mask,id))

def c35371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35371 : Upper (D 7) (R 7) [34,192,24,36,320] 13 := by
  apply FastRouting.sound _ _ [34,192,24,36,320] 13 (by decide) (choices 1) [1,2,128] r35371 c35371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20459
  · exact u20460
  · exact u20461

def r35372 : Route 9 := (fun mask => (mask,id))

def c35372 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35372 : Upper (D 7) (R 7) [34,192,24,65,129] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,129] 13 (by decide) (choices 1) [2,4,256] r35372 c35372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20462
  · exact u20463
  · exact u20464

def b35373 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 35 194 28 73 146 293 357 421 293), lower := (rows 35 194 28 73 146 32 64 128 256), losses := [] }

theorem u35373 : Upper (D 7) (R 7) [34,192,24,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35374 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 297, targets := 128 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(2,6),(3,7)], upper := (rows 35 194 28 73 148 291 355 419 291), lower := (rows 35 194 28 73 148 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 24 35 0 131 259), good := (rows 419 419 28 445 148 32 0 128 256) }] }

theorem u35374 : Upper (D 7) (R 7) [34,192,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35375 : Route 9 := (fun mask => (mask,id))

def c35375 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35375 : Upper (D 7) (R 7) [34,192,24,65,160] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,160] 13 (by decide) (choices 1) [1,2,4,256] r35375 c35375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20465
  · exact u20466
  · exact u20467
  · exact u20468

def r35376 : Route 9 := (fun mask => (mask,id))

def c35376 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35376 : Upper (D 7) (R 7) [34,192,24,65,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,257] 13 (by decide) (choices 1) [2,4,128] r35376 c35376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20469
  · exact u20470
  · exact u20471

def r35377 : Route 9 := (fun mask => (mask,id))

def c35377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35377 : Upper (D 7) (R 7) [34,192,24,65,258] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,258] 13 (by decide) (choices 1) [1,4,128] r35377 c35377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20472
  · exact u20473
  · exact u20474

def r35378 : Route 9 := (fun mask => (mask,id))

def c35378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35378 : Upper (D 7) (R 7) [34,192,24,65,260] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,260] 13 (by decide) (choices 1) [1,2,128] r35378 c35378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20475
  · exact u20476
  · exact u20477

def r35379 : Route 9 := (fun mask => (mask,id))

def c35379 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35379 : Upper (D 7) (R 7) [34,192,24,65,288] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,288] 13 (by decide) (choices 1) [1,2,4,128] r35379 c35379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20478
  · exact u20479
  · exact u20480
  · exact u20481

def r35380 : Route 9 := (fun mask => (mask,id))

def c35380 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35380 : Upper (D 7) (R 7) [34,192,24,65,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,384] 13 (by decide) (choices 1) [1,2,4] r35380 c35380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20482
  · exact u20483
  · exact u20484

def b35381 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 28, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 28 74 148 289 353 417 289), lower := (rows 35 194 28 74 148 32 64 128 256), losses := [] }

theorem u35381 : Upper (D 7) (R 7) [34,192,24,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35382 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 28 74 176 293 325 389 261), lower := (rows 35 194 28 74 176 32 64 128 256), losses := [] }

theorem u35382 : Upper (D 7) (R 7) [34,192,24,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35383 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 28 74 273 165 229 165 421), lower := (rows 35 194 28 74 273 32 64 128 256), losses := [] }

theorem u35383 : Upper (D 7) (R 7) [34,192,24,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35384 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 28 74 276 161 225 161 417), lower := (rows 35 194 28 74 276 32 64 128 256), losses := [] }

theorem u35384 : Upper (D 7) (R 7) [34,192,24,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35385 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 28 74 304 165 197 133 389), lower := (rows 35 194 28 74 304 32 64 128 256), losses := [] }

theorem u35385 : Upper (D 7) (R 7) [34,192,24,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35386 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 28 74 400 37 101 165 293), lower := (rows 35 194 28 74 400 32 64 128 256), losses := [] }

theorem u35386 : Upper (D 7) (R 7) [34,192,24,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35387 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,6)], upper := (rows 35 194 28 76 176 291 323 387 259), lower := (rows 35 194 28 76 176 32 64 128 256), losses := [] }

theorem u35387 : Upper (D 7) (R 7) [34,192,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35388 : Route 9 := (fun mask => (mask,id))

def c35388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35388 : Upper (D 7) (R 7) [34,192,24,68,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,257] 13 (by decide) (choices 1) [1,2,128] r35388 c35388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20485
  · exact u20486
  · exact u20487

def r35389 : Route 9 := (fun mask => (mask,id))

def c35389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35389 : Upper (D 7) (R 7) [34,192,24,68,258] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,258] 13 (by decide) (choices 1) [1,128] r35389 c35389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20488
  · exact u20489

def r35390 : Route 9 := (fun mask => (mask,id))

def c35390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35390 : Upper (D 7) (R 7) [34,192,24,68,288] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,288] 13 (by decide) (choices 1) [1,2,128] r35390 c35390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20490
  · exact u20491
  · exact u20492

def r35391 : Route 9 := (fun mask => (mask,id))

def c35391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35391 : Upper (D 7) (R 7) [34,192,24,68,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,384] 13 (by decide) (choices 1) [1,2] r35391 c35391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20493
  · exact u20494

def r35392 : Route 9 := (fun mask => (mask,id))

def c35392 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35392 : Upper (D 7) (R 7) [34,192,24,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,257] 13 (by decide) (choices 1) [1,2,4,128] r35392 c35392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20495
  · exact u20496
  · exact u20497
  · exact u20498

def r35393 : Route 9 := (fun mask => (mask,id))

def c35393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35393 : Upper (D 7) (R 7) [34,192,24,96,258] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,258] 13 (by decide) (choices 1) [1,4,128] r35393 c35393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20499
  · exact u20500
  · exact u20501

def r35394 : Route 9 := (fun mask => (mask,id))

def c35394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35394 : Upper (D 7) (R 7) [34,192,24,96,260] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,260] 13 (by decide) (choices 1) [1,2,128] r35394 c35394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20502
  · exact u20503
  · exact u20504

def r35395 : Route 9 := (fun mask => (mask,id))

def c35395 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35395 : Upper (D 7) (R 7) [34,192,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,384] 13 (by decide) (choices 1) [1,2,4] r35395 c35395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20505
  · exact u20506
  · exact u20507

def b35396 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 28 200 273 39 103 167 295), lower := (rows 35 194 28 200 273 32 64 128 256), losses := [] }

theorem u35396 : Upper (D 7) (R 7) [34,192,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35397 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 28 200 274 37 101 165 293), lower := (rows 35 194 28 200 274 32 64 128 256), losses := [] }

theorem u35397 : Upper (D 7) (R 7) [34,192,24,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35398 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 28 200 276 35 99 163 291), lower := (rows 35 194 28 200 276 32 64 128 256), losses := [] }

theorem u35398 : Upper (D 7) (R 7) [34,192,24,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35399 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 28 200 304 39 71 135 263), lower := (rows 35 194 28 200 304 32 64 128 256), losses := [] }

theorem u35399 : Upper (D 7) (R 7) [34,192,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u35399
end Delivery.IrregularNine14.P07
