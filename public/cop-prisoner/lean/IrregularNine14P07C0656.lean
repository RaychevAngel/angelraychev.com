import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0455
import IrregularNine14P07C0456
import IrregularNine14P07C0457

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39360 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 14 56 82 161 193 129 385), lower := (rows 37 322 14 56 82 32 64 128 256), losses := [] }

theorem u39360 : Upper (D 7) (R 7) [36,320,10,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39361 : Route 9 := (fun mask => (mask,id))

def c39361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39361 : Upper (D 7) (R 7) [36,320,10,48,129] 13 := by
  apply FastRouting.sound _ _ [36,320,10,48,129] 13 (by decide) (choices 1) [1,2,64,128] r39361 c39361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27306
  · exact u27307
  · exact u27308
  · exact u27309

def r39362 : Route 9 := (fun mask => (mask,id))

def c39362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39362 : Upper (D 7) (R 7) [36,320,10,48,130] 13 := by
  apply FastRouting.sound _ _ [36,320,10,48,130] 13 (by decide) (choices 1) [1,64,128] r39362 c39362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27310
  · exact u27311
  · exact u27312

def r39363 : Route 9 := (fun mask => (mask,id))

def c39363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39363 : Upper (D 7) (R 7) [36,320,10,48,192] 13 := by
  apply FastRouting.sound _ _ [36,320,10,48,192] 13 (by decide) (choices 1) [1,2,128] r39363 c39363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27313
  · exact u27314
  · exact u27315

def b39364 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,6),(1,0),(3,1),(4,6)], upper := (rows 37 322 14 73 19 176 240 176 432), lower := (rows 37 322 14 73 19 32 64 128 256), losses := [] }

theorem u39364 : Upper (D 7) (R 7) [36,320,10,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39365 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 14 73 49 178 210 146 402), lower := (rows 37 322 14 73 49 32 64 128 256), losses := [] }

theorem u39365 : Upper (D 7) (R 7) [36,320,10,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39366 : Route 9 := (fun mask => (mask,id))

def c39366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39366 : Upper (D 7) (R 7) [36,320,10,65,34] 13 := by
  apply FastRouting.sound _ _ [36,320,10,65,34] 13 (by decide) (choices 1) [1,16,128] r39366 c39366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27316
  · exact u27317
  · exact u27318

def r39367 : Route 9 := (fun mask => (mask,id))

def c39367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39367 : Upper (D 7) (R 7) [36,320,10,65,129] 13 := by
  apply FastRouting.sound _ _ [36,320,10,65,129] 13 (by decide) (choices 1) [2,16,128] r39367 c39367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27319
  · exact u27320
  · exact u27321

def r39368 : Route 9 := (fun mask => (mask,id))

def c39368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39368 : Upper (D 7) (R 7) [36,320,10,65,130] 13 := by
  apply FastRouting.sound _ _ [36,320,10,65,130] 13 (by decide) (choices 1) [1,16,128] r39368 c39368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27322
  · exact u27323
  · exact u27324

def r39369 : Route 9 := (fun mask => (mask,id))

def c39369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39369 : Upper (D 7) (R 7) [36,320,10,65,160] 13 := by
  apply FastRouting.sound _ _ [36,320,10,65,160] 13 (by decide) (choices 1) [1,2,16,128] r39369 c39369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27325
  · exact u27326
  · exact u27327
  · exact u27328

def b39370 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 2, region := 161, targets := 2 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(0,6),(3,1),(4,6)], upper := (rows 37 322 14 88 19 161 225 161 417), lower := (rows 37 322 14 88 19 32 64 128 256), losses := [] }

theorem u39370 : Upper (D 7) (R 7) [36,320,10,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39371 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 14 88 49 163 195 131 387), lower := (rows 37 322 14 88 49 32 64 128 256), losses := [] }

theorem u39371 : Upper (D 7) (R 7) [36,320,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39372 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 450, targets := 32 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(1,5),(4,6)], upper := (rows 37 322 14 88 50 161 193 129 385), lower := (rows 37 322 14 88 50 32 64 128 256), losses := [] }

theorem u39372 : Upper (D 7) (R 7) [36,320,10,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39373 : Route 9 := (fun mask => (mask,id))

def c39373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39373 : Upper (D 7) (R 7) [36,320,10,80,129] 13 := by
  apply FastRouting.sound _ _ [36,320,10,80,129] 13 (by decide) (choices 1) [1,2,128] r39373 c39373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27329
  · exact u27330
  · exact u27331

def r39374 : Route 9 := (fun mask => (mask,id))

def c39374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39374 : Upper (D 7) (R 7) [36,320,10,80,130] 13 := by
  apply FastRouting.sound _ _ [36,320,10,80,130] 13 (by decide) (choices 1) [1,128] r39374 c39374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27332
  · exact u27333

def r39375 : Route 9 := (fun mask => (mask,id))

def c39375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39375 : Upper (D 7) (R 7) [36,320,10,80,160] 13 := by
  apply FastRouting.sound _ _ [36,320,10,80,160] 13 (by decide) (choices 1) [1,2,128] r39375 c39375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27334
  · exact u27335
  · exact u27336

def r39376 : Route 9 := (fun mask => (mask,id))

def c39376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39376 : Upper (D 7) (R 7) [36,320,10,129,3] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,3] 13 (by decide) (choices 1) [16,64,128] r39376 c39376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27337
  · exact u27338
  · exact u27339

def b39377 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 14 137 49 242 210 210 466), lower := (rows 37 322 14 137 49 32 64 128 256), losses := [] }

theorem u39377 : Upper (D 7) (R 7) [36,320,10,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39378 : Route 9 := (fun mask => (mask,id))

def c39378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39378 : Upper (D 7) (R 7) [36,320,10,129,34] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,34] 13 (by decide) (choices 1) [1,16,64,128] r39378 c39378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27340
  · exact u27341
  · exact u27342
  · exact u27343

def r39379 : Route 9 := (fun mask => (mask,id))

def c39379 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39379 : Upper (D 7) (R 7) [36,320,10,129,65] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,65] 13 (by decide) (choices 1) [2,16,128] r39379 c39379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27344
  · exact u27345
  · exact u27346

def b39380 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 14 137 82 177 241 177 433), lower := (rows 37 322 14 137 82 32 64 128 256), losses := [] }

theorem u39380 : Upper (D 7) (R 7) [36,320,10,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39381 : Route 9 := (fun mask => (mask,id))

def c39381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39381 : Upper (D 7) (R 7) [36,320,10,129,96] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,96] 13 (by decide) (choices 1) [1,2,16,128] r39381 c39381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27347
  · exact u27348
  · exact u27349
  · exact u27350

def b39382 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 322 14 137 145 114 114 242 370), lower := (rows 37 322 14 137 145 32 64 128 256), losses := [] }

theorem u39382 : Upper (D 7) (R 7) [36,320,10,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39383 : Route 9 := (fun mask => (mask,id))

def c39383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39383 : Upper (D 7) (R 7) [36,320,10,129,130] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,130] 13 (by decide) (choices 1) [1,16,64] r39383 c39383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27351
  · exact u27352
  · exact u27353

def r39384 : Route 9 := (fun mask => (mask,id))

def c39384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39384 : Upper (D 7) (R 7) [36,320,10,129,160] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,160] 13 (by decide) (choices 1) [1,2,16,64] r39384 c39384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27354
  · exact u27355
  · exact u27356
  · exact u27357

def r39385 : Route 9 := (fun mask => (mask,id))

def c39385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39385 : Upper (D 7) (R 7) [36,320,10,129,192] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,192] 13 (by decide) (choices 1) [1,2,16] r39385 c39385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27358
  · exact u27359
  · exact u27360

def r39386 : Route 9 := (fun mask => (mask,id))

def c39386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39386 : Upper (D 7) (R 7) [36,320,10,144,3] 13 := by
  apply FastRouting.sound _ _ [36,320,10,144,3] 13 (by decide) (choices 1) [1,64,128] r39386 c39386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27361
  · exact u27362
  · exact u27363

def b39387 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 14 152 49 227 195 195 451), lower := (rows 37 322 14 152 49 32 64 128 256), losses := [] }

theorem u39387 : Upper (D 7) (R 7) [36,320,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39388 : Route 9 := (fun mask => (mask,id))

def c39388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39388 : Upper (D 7) (R 7) [36,320,10,144,34] 13 := by
  apply FastRouting.sound _ _ [36,320,10,144,34] 13 (by decide) (choices 1) [1,64,128] r39388 c39388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27364
  · exact u27365
  · exact u27366

def r39389 : Route 9 := (fun mask => (mask,id))

def c39389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39389 : Upper (D 7) (R 7) [36,320,10,144,65] 13 := by
  apply FastRouting.sound _ _ [36,320,10,144,65] 13 (by decide) (choices 1) [1,2,128] r39389 c39389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27367
  · exact u27368
  · exact u27369

def b39390 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 14 152 82 161 225 161 417), lower := (rows 37 322 14 152 82 32 64 128 256), losses := [] }

theorem u39390 : Upper (D 7) (R 7) [36,320,10,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39391 : Route 9 := (fun mask => (mask,id))

def c39391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39391 : Upper (D 7) (R 7) [36,320,10,144,96] 13 := by
  apply FastRouting.sound _ _ [36,320,10,144,96] 13 (by decide) (choices 1) [1,2,128] r39391 c39391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27370
  · exact u27371
  · exact u27372

def b39392 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 14 152 145 99 99 227 355), lower := (rows 37 322 14 152 145 32 64 128 256), losses := [] }

theorem u39392 : Upper (D 7) (R 7) [36,320,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39393 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 37 322 14 152 146 97 97 225 353), lower := (rows 37 322 14 152 146 32 64 128 256), losses := [] }

theorem u39393 : Upper (D 7) (R 7) [36,320,10,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39394 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 14 152 176 99 67 195 323), lower := (rows 37 322 14 152 176 32 64 128 256), losses := [] }

theorem u39394 : Upper (D 7) (R 7) [36,320,10,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39395 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 14 152 208 35 99 163 291), lower := (rows 37 322 14 152 208 32 64 128 256), losses := [] }

theorem u39395 : Upper (D 7) (R 7) [36,320,10,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39396 : Route 9 := (fun mask => (mask,id))

def c39396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39396 : Upper (D 7) (R 7) [36,320,10,160,3] 13 := by
  apply FastRouting.sound _ _ [36,320,10,160,3] 13 (by decide) (choices 1) [1,16,64,128] r39396 c39396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27373
  · exact u27374
  · exact u27375
  · exact u27376

def r39397 : Route 9 := (fun mask => (mask,id))

def c39397 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39397 : Upper (D 7) (R 7) [36,320,10,160,65] 13 := by
  apply FastRouting.sound _ _ [36,320,10,160,65] 13 (by decide) (choices 1) [1,2,16,128] r39397 c39397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27377
  · exact u27378
  · exact u27379
  · exact u27380

def b39398 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 14 168 82 177 209 145 401), lower := (rows 37 322 14 168 82 32 64 128 256), losses := [] }

theorem u39398 : Upper (D 7) (R 7) [36,320,10,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39399 : Route 9 := (fun mask => (mask,id))

def c39399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39399 : Upper (D 7) (R 7) [36,320,10,160,129] 13 := by
  apply FastRouting.sound _ _ [36,320,10,160,129] 13 (by decide) (choices 1) [1,2,16,64] r39399 c39399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27381
  · exact u27382
  · exact u27383
  · exact u27384

def r39400 : Route 9 := (fun mask => (mask,id))

def c39400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39400 : Upper (D 7) (R 7) [36,320,10,160,130] 13 := by
  apply FastRouting.sound _ _ [36,320,10,160,130] 13 (by decide) (choices 1) [1,16,64] r39400 c39400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27385
  · exact u27386
  · exact u27387

def r39401 : Route 9 := (fun mask => (mask,id))

def c39401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39401 : Upper (D 7) (R 7) [36,320,10,160,192] 13 := by
  apply FastRouting.sound _ _ [36,320,10,160,192] 13 (by decide) (choices 1) [1,2,16] r39401 c39401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27388
  · exact u27389
  · exact u27390

def r39402 : Route 9 := (fun mask => (mask,id))

def c39402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39402 : Upper (D 7) (R 7) [36,320,10,192,3] 13 := by
  apply FastRouting.sound _ _ [36,320,10,192,3] 13 (by decide) (choices 1) [1,16,128] r39402 c39402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27391
  · exact u27392
  · exact u27393

def b39403 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 14 200 49 179 211 147 403), lower := (rows 37 322 14 200 49 32 64 128 256), losses := [] }

theorem u39403 : Upper (D 7) (R 7) [36,320,10,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39404 : Route 9 := (fun mask => (mask,id))

def c39404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39404 : Upper (D 7) (R 7) [36,320,10,192,34] 13 := by
  apply FastRouting.sound _ _ [36,320,10,192,34] 13 (by decide) (choices 1) [1,16,128] r39404 c39404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27394
  · exact u27395
  · exact u27396

def r39405 : Route 9 := (fun mask => (mask,id))

def c39405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39405 : Upper (D 7) (R 7) [36,320,10,192,129] 13 := by
  apply FastRouting.sound _ _ [36,320,10,192,129] 13 (by decide) (choices 1) [1,2,16] r39405 c39405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27397
  · exact u27398
  · exact u27399

def r39406 : Route 9 := (fun mask => (mask,id))

def c39406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39406 : Upper (D 7) (R 7) [36,320,10,192,130] 13 := by
  apply FastRouting.sound _ _ [36,320,10,192,130] 13 (by decide) (choices 1) [1,16] r39406 c39406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27400
  · exact u27401

def r39407 : Route 9 := (fun mask => (mask,id))

def c39407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39407 : Upper (D 7) (R 7) [36,320,10,192,160] 13 := by
  apply FastRouting.sound _ _ [36,320,10,192,160] 13 (by decide) (choices 1) [1,2,16] r39407 c39407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27402
  · exact u27403
  · exact u27404

def b39408 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 20, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(4,5)], upper := (rows 37 322 28 11 19 224 224 224 480), lower := (rows 37 322 28 11 19 32 64 128 256), losses := [] }

theorem u39408 : Upper (D 7) (R 7) [36,320,24,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39409 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 28 11 49 226 194 194 450), lower := (rows 37 322 28 11 49 32 64 128 256), losses := [] }

theorem u39409 : Upper (D 7) (R 7) [36,320,24,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39410 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 28 11 50 225 193 193 449), lower := (rows 37 322 28 11 50 32 64 128 256), losses := [] }

theorem u39410 : Upper (D 7) (R 7) [36,320,24,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39411 : Route 9 := (fun mask => (mask,id))

def c39411 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39411 : Upper (D 7) (R 7) [36,320,24,3,65] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,65] 13 (by decide) (choices 1) [2,128] r39411 c39411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27405
  · exact u27406

def b39412 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 28 11 82 161 225 161 417), lower := (rows 37 322 28 11 82 32 64 128 256), losses := [] }

theorem u39412 : Upper (D 7) (R 7) [36,320,24,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39413 : Route 9 := (fun mask => (mask,id))

def c39413 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39413 : Upper (D 7) (R 7) [36,320,24,3,96] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,96] 13 (by decide) (choices 1) [1,2,128] r39413 c39413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27407
  · exact u27408
  · exact u27409

def r39414 : Route 9 := (fun mask => (mask,id))

def c39414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39414 : Upper (D 7) (R 7) [36,320,24,3,129] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,129] 13 (by decide) (choices 1) [2,64,128] r39414 c39414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27410
  · exact u27411
  · exact u27412

def r39415 : Route 9 := (fun mask => (mask,id))

def c39415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39415 : Upper (D 7) (R 7) [36,320,24,3,130] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,130] 13 (by decide) (choices 1) [1,64,128] r39415 c39415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27413
  · exact u27414
  · exact u27415

def r39416 : Route 9 := (fun mask => (mask,id))

def c39416 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39416 : Upper (D 7) (R 7) [36,320,24,3,160] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,160] 13 (by decide) (choices 1) [1,2,64,128] r39416 c39416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27416
  · exact u27417
  · exact u27418
  · exact u27419

def r39417 : Route 9 := (fun mask => (mask,id))

def c39417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39417 : Upper (D 7) (R 7) [36,320,24,3,192] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3,192] 13 (by decide) (choices 1) [1,2,128] r39417 c39417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27420
  · exact u27421
  · exact u27422

def b39418 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 28 41 81 162 194 130 386), lower := (rows 37 322 28 41 81 32 64 128 256), losses := [] }

theorem u39418 : Upper (D 7) (R 7) [36,320,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39419 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 28 41 145 226 194 194 450), lower := (rows 37 322 28 41 145 32 64 128 256), losses := [] }

theorem u39419 : Upper (D 7) (R 7) [36,320,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39419
end Delivery.IrregularNine14.P07
