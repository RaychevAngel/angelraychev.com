import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0271
import IrregularNine14P06C0272
import IrregularNine14P06C0273

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33300 : Route 9 := (fun mask => (mask,id))

def c33300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33300 : Upper (D 6) (R 6) [10,132,48,320,5] 13 := by
  apply FastRouting.sound _ _ [10,132,48,320,5] 13 (by decide) (choices 1) [1,2,64] r33300 c33300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16299
  · exact u16300
  · exact u16301

def b33301 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 52 328 22 97 97 225 353), lower := (rows 11 134 52 328 22 32 64 128 256), losses := [] }

theorem u33301 : Upper (D 6) (R 6) [10,132,48,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33302 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 328 49 103 71 199 327), lower := (rows 11 134 52 328 49 32 64 128 256), losses := [] }

theorem u33302 : Upper (D 6) (R 6) [10,132,48,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33303 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 328 50 101 69 197 325), lower := (rows 11 134 52 328 50 32 64 128 256), losses := [] }

theorem u33303 : Upper (D 6) (R 6) [10,132,48,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33304 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 328 52 99 67 195 323), lower := (rows 11 134 52 328 52 32 64 128 256), losses := [] }

theorem u33304 : Upper (D 6) (R 6) [10,132,48,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33305 : Route 9 := (fun mask => (mask,id))

def c33305 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33305 : Upper (D 6) (R 6) [10,132,48,320,65] 13 := by
  apply FastRouting.sound _ _ [10,132,48,320,65] 13 (by decide) (choices 1) [1,2,4] r33305 c33305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16302
  · exact u16303
  · exact u16304

def r33306 : Route 9 := (fun mask => (mask,id))

def c33306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33306 : Upper (D 6) (R 6) [10,132,48,320,66] 13 := by
  apply FastRouting.sound _ _ [10,132,48,320,66] 13 (by decide) (choices 1) [1,4] r33306 c33306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16305
  · exact u16306

def r33307 : Route 9 := (fun mask => (mask,id))

def c33307 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33307 : Upper (D 6) (R 6) [10,132,48,320,68] 13 := by
  apply FastRouting.sound _ _ [10,132,48,320,68] 13 (by decide) (choices 1) [1,2] r33307 c33307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16307
  · exact u16308

def b33308 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 328 112 39 71 135 263), lower := (rows 11 134 52 328 112 32 64 128 256), losses := [] }

theorem u33308 : Upper (D 6) (R 6) [10,132,48,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33309 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 100 25 19 356 356 484 356), lower := (rows 11 134 100 25 19 32 64 128 256), losses := [] }

theorem u33309 : Upper (D 6) (R 6) [10,132,96,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33310 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 100 25 21 354 354 482 354), lower := (rows 11 134 100 25 21 32 64 128 256), losses := [] }

theorem u33310 : Upper (D 6) (R 6) [10,132,96,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33311 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 100 25 22 353 353 481 353), lower := (rows 11 134 100 25 22 32 64 128 256), losses := [] }

theorem u33311 : Upper (D 6) (R 6) [10,132,96,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33312 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 134 100 25 49 358 326 454 326), lower := (rows 11 134 100 25 49 32 64 128 256), losses := [] }

theorem u33312 : Upper (D 6) (R 6) [10,132,96,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33313 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 100 25 50 357 325 453 325), lower := (rows 11 134 100 25 50 32 64 128 256), losses := [] }

theorem u33313 : Upper (D 6) (R 6) [10,132,96,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33314 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 100 25 52 355 323 451 323), lower := (rows 11 134 100 25 52 32 64 128 256), losses := [] }

theorem u33314 : Upper (D 6) (R 6) [10,132,96,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33315 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 134 100 25 112 295 327 391 263), lower := (rows 11 134 100 25 112 32 64 128 256), losses := [] }

theorem u33315 : Upper (D 6) (R 6) [10,132,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33316 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 134 100 25 273 102 102 230 358), lower := (rows 11 134 100 25 273 32 64 128 256), losses := [] }

theorem u33316 : Upper (D 6) (R 6) [10,132,96,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33317 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 100 25 274 101 101 229 357), lower := (rows 11 134 100 25 274 32 64 128 256), losses := [] }

theorem u33317 : Upper (D 6) (R 6) [10,132,96,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33318 : Route 9 := (fun mask => (mask,id))

def c33318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33318 : Upper (D 6) (R 6) [10,132,96,17,260] 13 := by
  apply FastRouting.sound _ _ [10,132,96,17,260] 13 (by decide) (choices 1) [1,2,64] r33318 c33318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16309
  · exact u16310
  · exact u16311

def r33319 : Route 9 := (fun mask => (mask,id))

def c33319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33319 : Upper (D 6) (R 6) [10,132,96,17,288] 13 := by
  apply FastRouting.sound _ _ [10,132,96,17,288] 13 (by decide) (choices 1) [1,2,4,64] r33319 c33319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16312
  · exact u16313
  · exact u16314
  · exact u16315

def b33320 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 100 28 19 353 353 481 353), lower := (rows 11 134 100 28 19 32 64 128 256), losses := [] }

theorem u33320 : Upper (D 6) (R 6) [10,132,96,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33321 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 451, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 100 28 49 355 323 451 323), lower := (rows 11 134 100 28 49 32 64 128 256), losses := [] }

theorem u33321 : Upper (D 6) (R 6) [10,132,96,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33322 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 451, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 11 134 100 28 50 353 321 449 321), lower := (rows 11 134 100 28 50 32 64 128 256), losses := [] }

theorem u33322 : Upper (D 6) (R 6) [10,132,96,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33323 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 134 100 28 112 291 323 387 259), lower := (rows 11 134 100 28 112 32 64 128 256), losses := [] }

theorem u33323 : Upper (D 6) (R 6) [10,132,96,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33324 : Route 9 := (fun mask => (mask,id))

def c33324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33324 : Upper (D 6) (R 6) [10,132,96,20,257] 13 := by
  apply FastRouting.sound _ _ [10,132,96,20,257] 13 (by decide) (choices 1) [1,2,64] r33324 c33324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16316
  · exact u16317
  · exact u16318

def r33325 : Route 9 := (fun mask => (mask,id))

def c33325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33325 : Upper (D 6) (R 6) [10,132,96,20,258] 13 := by
  apply FastRouting.sound _ _ [10,132,96,20,258] 13 (by decide) (choices 1) [1,64] r33325 c33325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16319
  · exact u16320

def b33326 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 100 28 304 99 67 195 323), lower := (rows 11 134 100 28 304 32 64 128 256), losses := [] }

theorem u33326 : Upper (D 6) (R 6) [10,132,96,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33327 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 100 41 19 372 340 468 340), lower := (rows 11 134 100 41 19 32 64 128 256), losses := [] }

theorem u33327 : Upper (D 6) (R 6) [10,132,96,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33328 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 134 100 41 21 370 338 466 338), lower := (rows 11 134 100 41 21 32 64 128 256), losses := [] }

theorem u33328 : Upper (D 6) (R 6) [10,132,96,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33329 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 100 41 22 369 337 465 337), lower := (rows 11 134 100 41 22 32 64 128 256), losses := [] }

theorem u33329 : Upper (D 6) (R 6) [10,132,96,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33330 : Route 9 := (fun mask => (mask,id))

def c33330 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33330 : Upper (D 6) (R 6) [10,132,96,33,65] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,65] 13 (by decide) (choices 1) [2,4,16,256] r33330 c33330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16321
  · exact u16322
  · exact u16323
  · exact u16324

def r33331 : Route 9 := (fun mask => (mask,id))

def c33331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33331 : Upper (D 6) (R 6) [10,132,96,33,66] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,66] 13 (by decide) (choices 1) [1,4,16,256] r33331 c33331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16325
  · exact u16326
  · exact u16327
  · exact u16328

def b33332 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 134 100 41 84 307 339 403 275), lower := (rows 11 134 100 41 84 32 64 128 256), losses := [] }

theorem u33332 : Upper (D 6) (R 6) [10,132,96,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33333 : Route 9 := (fun mask => (mask,id))

def c33333 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33333 : Upper (D 6) (R 6) [10,132,96,33,257] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,257] 13 (by decide) (choices 1) [2,4,16,64] r33333 c33333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16329
  · exact u16330
  · exact u16331
  · exact u16332

def r33334 : Route 9 := (fun mask => (mask,id))

def c33334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33334 : Upper (D 6) (R 6) [10,132,96,33,258] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,258] 13 (by decide) (choices 1) [1,4,16,64] r33334 c33334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16333
  · exact u16334
  · exact u16335
  · exact u16336

def r33335 : Route 9 := (fun mask => (mask,id))

def c33335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33335 : Upper (D 6) (R 6) [10,132,96,33,260] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,260] 13 (by decide) (choices 1) [1,2,16,64] r33335 c33335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16337
  · exact u16338
  · exact u16339
  · exact u16340

def r33336 : Route 9 := (fun mask => (mask,id))

def c33336 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33336 : Upper (D 6) (R 6) [10,132,96,33,320] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,320] 13 (by decide) (choices 1) [1,2,4,16] r33336 c33336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16341
  · exact u16342
  · exact u16343
  · exact u16344

def b33337 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 100 56 19 357 325 453 325), lower := (rows 11 134 100 56 19 32 64 128 256), losses := [] }

theorem u33337 : Upper (D 6) (R 6) [10,132,96,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33338 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 450, targets := 32 }], pairs := [(0,5),(1,5),(3,2)], upper := (rows 11 134 100 56 21 355 323 451 323), lower := (rows 11 134 100 56 21 32 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 33 65 129 257), good := (rows 491 130 96 56 505 32 64 128 256) },{ target := 5, region := (rows 9 18 4 8 16 0 89 153 281), good := (rows 459 134 68 475 471 0 64 128 256) }] }

theorem u33338 : Upper (D 6) (R 6) [10,132,96,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33339 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 100 56 22 353 321 449 321), lower := (rows 11 134 100 56 22 32 64 128 256), losses := [] }

theorem u33339 : Upper (D 6) (R 6) [10,132,96,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33340 : Route 9 := (fun mask => (mask,id))

def c33340 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33340 : Upper (D 6) (R 6) [10,132,96,48,65] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,65] 13 (by decide) (choices 1) [1,2,4,256] r33340 c33340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16345
  · exact u16346
  · exact u16347
  · exact u16348

def r33341 : Route 9 := (fun mask => (mask,id))

def c33341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33341 : Upper (D 6) (R 6) [10,132,96,48,66] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,66] 13 (by decide) (choices 1) [1,4,256] r33341 c33341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16349
  · exact u16350
  · exact u16351

def b33342 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 134 100 56 84 291 323 387 259), lower := (rows 11 134 100 56 84 32 64 128 256), losses := [] }

theorem u33342 : Upper (D 6) (R 6) [10,132,96,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33343 : Route 9 := (fun mask => (mask,id))

def c33343 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33343 : Upper (D 6) (R 6) [10,132,96,48,257] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,257] 13 (by decide) (choices 1) [1,2,4,64] r33343 c33343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16352
  · exact u16353
  · exact u16354
  · exact u16355

def r33344 : Route 9 := (fun mask => (mask,id))

def c33344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33344 : Upper (D 6) (R 6) [10,132,96,48,258] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,258] 13 (by decide) (choices 1) [1,4,64] r33344 c33344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16356
  · exact u16357
  · exact u16358

def r33345 : Route 9 := (fun mask => (mask,id))

def c33345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33345 : Upper (D 6) (R 6) [10,132,96,48,260] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,260] 13 (by decide) (choices 1) [1,2,64] r33345 c33345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16359
  · exact u16360
  · exact u16361

def r33346 : Route 9 := (fun mask => (mask,id))

def c33346 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33346 : Upper (D 6) (R 6) [10,132,96,48,320] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,320] 13 (by decide) (choices 1) [1,2,4] r33346 c33346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16362
  · exact u16363
  · exact u16364

def b33347 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 100 265 19 116 116 244 372), lower := (rows 11 134 100 265 19 32 64 128 256), losses := [] }

theorem u33347 : Upper (D 6) (R 6) [10,132,96,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33348 : Route 9 := (fun mask => (mask,id))

def c33348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33348 : Upper (D 6) (R 6) [10,132,96,257,5] 13 := by
  apply FastRouting.sound _ _ [10,132,96,257,5] 13 (by decide) (choices 1) [2,16,64] r33348 c33348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16365
  · exact u16366
  · exact u16367

def b33349 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 100 265 22 113 113 241 369), lower := (rows 11 134 100 265 22 32 64 128 256), losses := [] }

theorem u33349 : Upper (D 6) (R 6) [10,132,96,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33350 : Route 9 := (fun mask => (mask,id))

def c33350 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33350 : Upper (D 6) (R 6) [10,132,96,257,33] 13 := by
  apply FastRouting.sound _ _ [10,132,96,257,33] 13 (by decide) (choices 1) [2,4,16,64] r33350 c33350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16368
  · exact u16369
  · exact u16370
  · exact u16371

def r33351 : Route 9 := (fun mask => (mask,id))

def c33351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33351 : Upper (D 6) (R 6) [10,132,96,257,34] 13 := by
  apply FastRouting.sound _ _ [10,132,96,257,34] 13 (by decide) (choices 1) [1,4,16,64] r33351 c33351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16372
  · exact u16373
  · exact u16374
  · exact u16375

def b33352 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 100 265 52 115 83 211 339), lower := (rows 11 134 100 265 52 32 64 128 256), losses := [] }

theorem u33352 : Upper (D 6) (R 6) [10,132,96,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33353 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 134 100 265 112 55 87 151 279), lower := (rows 11 134 100 265 112 32 64 128 256), losses := [] }

theorem u33353 : Upper (D 6) (R 6) [10,132,96,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33354 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 134 100 268 19 113 113 241 369), lower := (rows 11 134 100 268 19 32 64 128 256), losses := [] }

theorem u33354 : Upper (D 6) (R 6) [10,132,96,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33355 : Route 9 := (fun mask => (mask,id))

def c33355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33355 : Upper (D 6) (R 6) [10,132,96,260,33] 13 := by
  apply FastRouting.sound _ _ [10,132,96,260,33] 13 (by decide) (choices 1) [1,2,16,64] r33355 c33355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16376
  · exact u16377
  · exact u16378
  · exact u16379

def r33356 : Route 9 := (fun mask => (mask,id))

def c33356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33356 : Upper (D 6) (R 6) [10,132,96,260,34] 13 := by
  apply FastRouting.sound _ _ [10,132,96,260,34] 13 (by decide) (choices 1) [1,16,64] r33356 c33356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16380
  · exact u16381
  · exact u16382

def b33357 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 134 100 268 112 51 83 147 275), lower := (rows 11 134 100 268 112 32 64 128 256), losses := [] }

theorem u33357 : Upper (D 6) (R 6) [10,132,96,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33358 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 100 280 19 101 101 229 357), lower := (rows 11 134 100 280 19 32 64 128 256), losses := [] }

theorem u33358 : Upper (D 6) (R 6) [10,132,96,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33359 : Route 9 := (fun mask => (mask,id))

def c33359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33359 : Upper (D 6) (R 6) [10,132,96,272,5] 13 := by
  apply FastRouting.sound _ _ [10,132,96,272,5] 13 (by decide) (choices 1) [1,2,64] r33359 c33359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16383
  · exact u16384
  · exact u16385

#print axioms u33359
end Delivery.IrregularNine14.P06
