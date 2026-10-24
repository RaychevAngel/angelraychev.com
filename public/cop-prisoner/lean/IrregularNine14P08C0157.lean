import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0039
import IrregularNine14P08C0040

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9420 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 104 400 53 85 149 277), lower := (rows 35 194 44 104 400 32 64 128 256), losses := [] }

theorem u9420 : Upper (D 8) (R 8) [34,192,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9421 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 44 200 273 53 117 181 309), lower := (rows 35 194 44 200 273 32 64 128 256), losses := [] }

theorem u9421 : Upper (D 8) (R 8) [34,192,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9422 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 44 200 276 49 113 177 305), lower := (rows 35 194 44 200 276 32 64 128 256), losses := [] }

theorem u9422 : Upper (D 8) (R 8) [34,192,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9423 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 44 200 304 53 85 149 277), lower := (rows 35 194 44 200 304 32 64 128 256), losses := [] }

theorem u9423 : Upper (D 8) (R 8) [34,192,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9424 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 265 81 180 244 180 436), lower := (rows 35 194 44 265 81 32 64 128 256), losses := [] }

theorem u9424 : Upper (D 8) (R 8) [34,192,40,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9425 : Route 9 := (fun mask => (mask,id))

def c9425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9425 : Upper (D 8) (R 8) [34,192,40,257,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,68] 13 (by decide) (choices 1) [1,16,128] r9425 c9425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2383
  · exact u2384
  · exact u2385

def r9426 : Route 9 := (fun mask => (mask,id))

def c9426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9426 : Upper (D 8) (R 8) [34,192,40,257,96] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,96] 13 (by decide) (choices 1) [1,4,16,128] r9426 c9426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2386
  · exact u2387
  · exact u2388
  · exact u2389

def b9427 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 44 265 208 53 117 181 309), lower := (rows 35 194 44 265 208 32 64 128 256), losses := [] }

theorem u9427 : Upper (D 8) (R 8) [34,192,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9428 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 268 81 177 241 177 433), lower := (rows 35 194 44 268 81 32 64 128 256), losses := [] }

theorem u9428 : Upper (D 8) (R 8) [34,192,40,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9429 : Route 9 := (fun mask => (mask,id))

def c9429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9429 : Upper (D 8) (R 8) [34,192,40,260,96] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260,96] 13 (by decide) (choices 1) [1,16,128] r9429 c9429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2390
  · exact u2391
  · exact u2392

def b9430 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 44 268 208 49 113 177 305), lower := (rows 35 194 44 268 208 32 64 128 256), losses := [] }

theorem u9430 : Upper (D 8) (R 8) [34,192,40,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9431 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 280 81 165 229 165 421), lower := (rows 35 194 44 280 81 32 64 128 256), losses := [] }

theorem u9431 : Upper (D 8) (R 8) [34,192,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9432 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 280 84 161 225 161 417), lower := (rows 35 194 44 280 84 32 64 128 256), losses := [] }

theorem u9432 : Upper (D 8) (R 8) [34,192,40,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9433 : Route 9 := (fun mask => (mask,id))

def c9433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9433 : Upper (D 8) (R 8) [34,192,40,272,96] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,96] 13 (by decide) (choices 1) [1,4,128] r9433 c9433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2393
  · exact u2394
  · exact u2395

def b9434 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 44 280 208 37 101 165 293), lower := (rows 35 194 44 280 208 32 64 128 256), losses := [] }

theorem u9434 : Upper (D 8) (R 8) [34,192,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9435 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 296 84 177 209 145 401), lower := (rows 35 194 44 296 84 32 64 128 256), losses := [] }

theorem u9435 : Upper (D 8) (R 8) [34,192,40,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9436 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 328 145 53 117 181 309), lower := (rows 35 194 44 328 145 32 64 128 256), losses := [] }

theorem u9436 : Upper (D 8) (R 8) [34,192,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9437 : Route 9 := (fun mask => (mask,id))

def c9437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9437 : Upper (D 8) (R 8) [34,192,40,320,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,132] 13 (by decide) (choices 1) [1,16] r9437 c9437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2396
  · exact u2397

def r9438 : Route 9 := (fun mask => (mask,id))

def c9438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9438 : Upper (D 8) (R 8) [34,192,40,320,160] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,160] 13 (by decide) (choices 1) [1,4,16] r9438 c9438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2398
  · exact u2399
  · exact u2400

def b9439 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 140 273 56 120 184 312), lower := (rows 35 194 69 140 273 32 64 128 256), losses := [] }

theorem u9439 : Upper (D 8) (R 8) [34,192,65,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9440 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 140 280 49 113 177 305), lower := (rows 35 194 69 140 280 32 64 128 256), losses := [] }

theorem u9440 : Upper (D 8) (R 8) [34,192,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9441 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 140 304 57 121 185 313), lower := (rows 35 194 69 140 304 32 64 128 256), losses := [] }

theorem u9441 : Upper (D 8) (R 8) [34,192,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9442 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 152 273 44 108 172 300), lower := (rows 35 194 69 152 273 32 64 128 256), losses := [] }

theorem u9442 : Upper (D 8) (R 8) [34,192,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9443 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 152 276 41 105 169 297), lower := (rows 35 194 69 152 276 32 64 128 256), losses := [] }

theorem u9443 : Upper (D 8) (R 8) [34,192,65,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9444 : PairBound 9 := { available := 45, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 152 304 45 109 173 301), lower := (rows 35 194 69 152 304 32 64 128 256), losses := [] }

theorem u9444 : Upper (D 8) (R 8) [34,192,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9445 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 168 273 60 124 188 316), lower := (rows 35 194 69 168 273 32 64 128 256), losses := [] }

theorem u9445 : Upper (D 8) (R 8) [34,192,65,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9446 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 168 276 57 121 185 313), lower := (rows 35 194 69 168 276 32 64 128 256), losses := [] }

theorem u9446 : Upper (D 8) (R 8) [34,192,65,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9447 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 168 280 53 117 181 309), lower := (rows 35 194 69 168 280 32 64 128 256), losses := [] }

theorem u9447 : Upper (D 8) (R 8) [34,192,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9448 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 168 304 61 93 157 285), lower := (rows 35 194 69 168 304 32 64 128 256), losses := [] }

theorem u9448 : Upper (D 8) (R 8) [34,192,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9449 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 76 140 273 49 113 177 305), lower := (rows 35 194 76 140 273 32 64 128 256), losses := [] }

theorem u9449 : Upper (D 8) (R 8) [34,192,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9450 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 76 140 304 49 113 177 305), lower := (rows 35 194 76 140 304 32 64 128 256), losses := [] }

theorem u9450 : Upper (D 8) (R 8) [34,192,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9451 : Route 9 := (fun mask => (mask,id))

def c9451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9451 : Upper (D 8) (R 8) [34,192,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257] 13 (by decide) (choices 1) [1,4] r9451 c9451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2401
  · exact u2402

def b9452 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 152 276 33 97 161 289), lower := (rows 35 194 76 152 276 32 64 128 256), losses := [] }

theorem u9452 : Upper (D 8) (R 8) [34,192,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9453 : Route 9 := (fun mask => (mask,id))

def c9453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9453 : Upper (D 8) (R 8) [34,192,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,288] 13 (by decide) (choices 1) [1,4] r9453 c9453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2403
  · exact u2404

def r9454 : Route 9 := (fun mask => (mask,id))

def c9454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9454 : Upper (D 8) (R 8) [34,192,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257] 13 (by decide) (choices 1) [1,4,16] r9454 c9454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2405
  · exact u2406
  · exact u2407

def r9455 : Route 9 := (fun mask => (mask,id))

def c9455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9455 : Upper (D 8) (R 8) [34,192,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260] 13 (by decide) (choices 1) [1,16] r9455 c9455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2408
  · exact u2409

def r9456 : Route 9 := (fun mask => (mask,id))

def c9456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9456 : Upper (D 8) (R 8) [34,192,72,160,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,288] 13 (by decide) (choices 1) [1,4,16] r9456 c9456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2410
  · exact u2411
  · exact u2412

def r9457 : Route 9 := (fun mask => (mask,id))

def c9457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9457 : Upper (D 8) (R 8) [34,192,72,257,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160] 13 (by decide) (choices 1) [1,4,16] r9457 c9457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2413
  · exact u2414
  · exact u2415

def b9458 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 268 176 49 113 177 305), lower := (rows 35 194 76 268 176 32 64 128 256), losses := [] }

theorem u9458 : Upper (D 8) (R 8) [34,192,72,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9459 : Route 9 := (fun mask => (mask,id))

def c9459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9459 : Upper (D 8) (R 8) [34,192,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160] 13 (by decide) (choices 1) [1,4] r9459 c9459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2416
  · exact u2417

def r9460 : Route 9 := (fun mask => (mask,id))

def c9460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9460 : Upper (D 8) (R 8) [34,192,72,288,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,160] 13 (by decide) (choices 1) [1,4,16] r9460 c9460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2418
  · exact u2419
  · exact u2420

theorem m9461_8 : Upper (D 8) (R 8) [34,192,96,160,257,8] 13 :=
  permutation_upper _ _ _ [34,192,96,160,257,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2422

def r9461 : Route 9 := (fun mask => (mask,id))

def c9461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9461 : Upper (D 8) (R 8) [34,192,96,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,96,160,257] 13 (by decide) (choices 1) [1,4,8,16] r9461 c9461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2421
  · exact u2422
  · exact m9461_8
  · exact u2423

def r9462 : Route 9 := (fun mask => (mask,id))

def c9462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9462 : Upper (D 8) (R 8) [34,192,96,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,160,260] 13 (by decide) (choices 1) [1,8,16] r9462 c9462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2424
  · exact u2425
  · exact u2426

def b9463 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 28 112 224 224 224 480), lower := (rows 35 259 13 28 112 32 64 128 256), losses := [] }

theorem u9463 : Upper (D 8) (R 8) [34,257,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9464 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 28 208 224 224 224 480), lower := (rows 35 259 13 28 208 32 64 128 256), losses := [] }

theorem u9464 : Upper (D 8) (R 8) [34,257,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9465 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 13 44 112 240 208 208 464), lower := (rows 35 259 13 44 112 32 64 128 256), losses := [] }

theorem u9465 : Upper (D 8) (R 8) [34,257,9,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9466 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 13 44 208 240 240 240 496), lower := (rows 35 259 13 44 208 32 64 128 256), losses := [] }

theorem u9466 : Upper (D 8) (R 8) [34,257,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9467 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 56 84 224 224 224 480), lower := (rows 35 259 13 56 84 32 64 128 256), losses := [] }

theorem u9467 : Upper (D 8) (R 8) [34,257,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9468 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 56 208 228 228 228 484), lower := (rows 35 259 13 56 208 32 64 128 256), losses := [] }

theorem u9468 : Upper (D 8) (R 8) [34,257,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9469 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 76 112 176 240 176 432), lower := (rows 35 259 13 76 112 32 64 128 256), losses := [] }

theorem u9469 : Upper (D 8) (R 8) [34,257,9,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9470 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 76 176 240 240 240 496), lower := (rows 35 259 13 76 176 32 64 128 256), losses := [] }

theorem u9470 : Upper (D 8) (R 8) [34,257,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9471 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 76 208 176 240 176 432), lower := (rows 35 259 13 76 208 32 64 128 256), losses := [] }

theorem u9471 : Upper (D 8) (R 8) [34,257,9,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9472 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 88 52 224 224 224 480), lower := (rows 35 259 13 88 52 32 64 128 256), losses := [] }

theorem u9472 : Upper (D 8) (R 8) [34,257,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9473 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 88 148 224 224 224 480), lower := (rows 35 259 13 88 148 32 64 128 256), losses := [] }

theorem u9473 : Upper (D 8) (R 8) [34,257,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9474 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 88 176 228 228 228 484), lower := (rows 35 259 13 88 176 32 64 128 256), losses := [] }

theorem u9474 : Upper (D 8) (R 8) [34,257,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9475 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 104 52 240 208 208 464), lower := (rows 35 259 13 104 52 32 64 128 256), losses := [] }

theorem u9475 : Upper (D 8) (R 8) [34,257,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9476 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 104 84 176 240 176 432), lower := (rows 35 259 13 104 84 32 64 128 256), losses := [] }

theorem u9476 : Upper (D 8) (R 8) [34,257,9,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9477 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 104 148 240 240 240 496), lower := (rows 35 259 13 104 148 32 64 128 256), losses := [] }

theorem u9477 : Upper (D 8) (R 8) [34,257,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9478 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 104 176 244 212 212 468), lower := (rows 35 259 13 104 176 32 64 128 256), losses := [] }

theorem u9478 : Upper (D 8) (R 8) [34,257,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9479 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 104 208 180 244 180 436), lower := (rows 35 259 13 104 208 32 64 128 256), losses := [] }

theorem u9479 : Upper (D 8) (R 8) [34,257,9,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9479
end Delivery.IrregularNine14.P08
