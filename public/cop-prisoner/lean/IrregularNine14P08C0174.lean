import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0048

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10440 : PairBound 9 := { available := 344, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 140 176 376 344 472 344), lower := (rows 67 35 37 140 176 32 64 128 256), losses := [] }

theorem u10440 : Upper (D 8) (R 8) [66,33,33,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10441 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 140 208 312 376 440 312), lower := (rows 67 35 37 140 208 32 64 128 256), losses := [] }

theorem u10441 : Upper (D 8) (R 8) [66,33,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10442 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 140 280 240 240 240 496), lower := (rows 67 35 37 140 280 32 64 128 256), losses := [] }

theorem u10442 : Upper (D 8) (R 8) [66,33,33,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10443 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 140 304 248 216 216 472), lower := (rows 67 35 37 140 304 32 64 128 256), losses := [] }

theorem u10443 : Upper (D 8) (R 8) [66,33,33,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10444 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 140 336 184 248 184 440), lower := (rows 67 35 37 140 336 32 64 128 256), losses := [] }

theorem u10444 : Upper (D 8) (R 8) [66,33,33,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10445 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 140 400 120 120 248 376), lower := (rows 67 35 37 140 400 32 64 128 256), losses := [] }

theorem u10445 : Upper (D 8) (R 8) [66,33,33,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10446 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 152 276 232 232 232 488), lower := (rows 67 35 37 152 276 32 64 128 256), losses := [] }

theorem u10446 : Upper (D 8) (R 8) [66,33,33,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10447 : PairBound 9 := { available := 228, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 152 280 228 228 228 484), lower := (rows 67 35 37 152 280 32 64 128 256), losses := [] }

theorem u10447 : Upper (D 8) (R 8) [66,33,33,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10448 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 152 304 236 204 204 460), lower := (rows 67 35 37 152 304 32 64 128 256), losses := [] }

theorem u10448 : Upper (D 8) (R 8) [66,33,33,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10449 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 152 336 172 236 172 428), lower := (rows 67 35 37 152 336 32 64 128 256), losses := [] }

theorem u10449 : Upper (D 8) (R 8) [66,33,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10450 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 168 208 316 348 412 284), lower := (rows 67 35 37 168 208 32 64 128 256), losses := [] }

theorem u10450 : Upper (D 8) (R 8) [66,33,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10451 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 168 276 248 216 216 472), lower := (rows 67 35 37 168 276 32 64 128 256), losses := [] }

theorem u10451 : Upper (D 8) (R 8) [66,33,33,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10452 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 168 280 244 212 212 468), lower := (rows 67 35 37 168 280 32 64 128 256), losses := [] }

theorem u10452 : Upper (D 8) (R 8) [66,33,33,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10453 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 168 336 188 220 156 412), lower := (rows 67 35 37 168 336 32 64 128 256), losses := [] }

theorem u10453 : Upper (D 8) (R 8) [66,33,33,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10454 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 168 400 124 92 220 348), lower := (rows 67 35 37 168 400 32 64 128 256), losses := [] }

theorem u10454 : Upper (D 8) (R 8) [66,33,33,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10455 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 200 276 184 248 184 440), lower := (rows 67 35 37 200 276 32 64 128 256), losses := [] }

theorem u10455 : Upper (D 8) (R 8) [66,33,33,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10456 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 200 280 180 244 180 436), lower := (rows 67 35 37 200 280 32 64 128 256), losses := [] }

theorem u10456 : Upper (D 8) (R 8) [66,33,33,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10457 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 200 304 188 220 156 412), lower := (rows 67 35 37 200 304 32 64 128 256), losses := [] }

theorem u10457 : Upper (D 8) (R 8) [66,33,33,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10458 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 200 400 60 124 188 316), lower := (rows 67 35 37 200 400 32 64 128 256), losses := [] }

theorem u10458 : Upper (D 8) (R 8) [66,33,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10459 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 44 208 433 465 401 401), lower := (rows 67 35 44 44 208 32 64 128 256), losses := [] }

theorem u10459 : Upper (D 8) (R 8) [66,33,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10460 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 44 336 177 209 145 401), lower := (rows 67 35 44 44 336 32 64 128 256), losses := [] }

theorem u10460 : Upper (D 8) (R 8) [66,33,40,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10461 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 44 400 241 209 209 465), lower := (rows 67 35 44 44 400 32 64 128 256), losses := [] }

theorem u10461 : Upper (D 8) (R 8) [66,33,40,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10462 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 56 84 417 449 385 385), lower := (rows 67 35 44 56 84 32 64 128 256), losses := [] }

theorem u10462 : Upper (D 8) (R 8) [66,33,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10463 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 56 148 481 449 449 449), lower := (rows 67 35 44 56 148 32 64 128 256), losses := [] }

theorem u10463 : Upper (D 8) (R 8) [66,33,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10464 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 56 208 421 453 389 389), lower := (rows 67 35 44 56 208 32 64 128 256), losses := [] }

theorem u10464 : Upper (D 8) (R 8) [66,33,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10465 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 56 276 225 193 193 449), lower := (rows 67 35 44 56 276 32 64 128 256), losses := [] }

theorem u10465 : Upper (D 8) (R 8) [66,33,40,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10466 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 56 336 165 197 133 389), lower := (rows 67 35 44 56 336 32 64 128 256), losses := [] }

theorem u10466 : Upper (D 8) (R 8) [66,33,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10467 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 56 400 229 197 197 453), lower := (rows 67 35 44 56 400 32 64 128 256), losses := [] }

theorem u10467 : Upper (D 8) (R 8) [66,33,40,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10468 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 73 148 432 496 432 432), lower := (rows 67 35 44 73 148 32 64 128 256), losses := [] }

theorem u10468 : Upper (D 8) (R 8) [66,33,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10469 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 73 176 436 468 404 404), lower := (rows 67 35 44 73 176 32 64 128 256), losses := [] }

theorem u10469 : Upper (D 8) (R 8) [66,33,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10470 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 73 276 176 240 176 432), lower := (rows 67 35 44 73 276 32 64 128 256), losses := [] }

theorem u10470 : Upper (D 8) (R 8) [66,33,40,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10471 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 73 304 180 212 148 404), lower := (rows 67 35 44 73 304 32 64 128 256), losses := [] }

theorem u10471 : Upper (D 8) (R 8) [66,33,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10472 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 73 400 180 244 180 436), lower := (rows 67 35 44 73 400 32 64 128 256), losses := [] }

theorem u10472 : Upper (D 8) (R 8) [66,33,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10473 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 76 176 433 465 401 401), lower := (rows 67 35 44 76 176 32 64 128 256), losses := [] }

theorem u10473 : Upper (D 8) (R 8) [66,33,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10474 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 76 304 177 209 145 401), lower := (rows 67 35 44 76 304 32 64 128 256), losses := [] }

theorem u10474 : Upper (D 8) (R 8) [66,33,40,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10475 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 76 400 177 241 177 433), lower := (rows 67 35 44 76 400 32 64 128 256), losses := [] }

theorem u10475 : Upper (D 8) (R 8) [66,33,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10476 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 88 145 420 484 420 420), lower := (rows 67 35 44 88 145 32 64 128 256), losses := [] }

theorem u10476 : Upper (D 8) (R 8) [66,33,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10477 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 88 148 417 481 417 417), lower := (rows 67 35 44 88 148 32 64 128 256), losses := [] }

theorem u10477 : Upper (D 8) (R 8) [66,33,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10478 : Route 9 := (fun mask => (mask,id))

def c10478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u10478 : Upper (D 8) (R 8) [66,33,40,80,160] 13 := by
  apply FastRouting.sound _ _ [66,33,40,80,160] 13 (by decide) (choices 1) [1,4,128,256] r10478 c10478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2901
  · exact u2902
  · exact u2903
  · exact u2904

def b10479 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 88 273 164 228 164 420), lower := (rows 67 35 44 88 273 32 64 128 256), losses := [] }

theorem u10479 : Upper (D 8) (R 8) [66,33,40,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10480 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 88 276 161 225 161 417), lower := (rows 67 35 44 88 276 32 64 128 256), losses := [] }

theorem u10480 : Upper (D 8) (R 8) [66,33,40,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10481 : Route 9 := (fun mask => (mask,id))

def c10481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10481 : Upper (D 8) (R 8) [66,33,40,80,288] 13 := by
  apply FastRouting.sound _ _ [66,33,40,80,288] 13 (by decide) (choices 1) [1,4,128] r10481 c10481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2905
  · exact u2906
  · exact u2907

def r10482 : Route 9 := (fun mask => (mask,id))

def c10482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10482 : Upper (D 8) (R 8) [66,33,40,80,384] 13 := by
  apply FastRouting.sound _ _ [66,33,40,80,384] 13 (by decide) (choices 1) [1,4,128] r10482 c10482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2908
  · exact u2909
  · exact u2910

def b10483 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 104 148 433 465 401 401), lower := (rows 67 35 44 104 148 32 64 128 256), losses := [] }

theorem u10483 : Upper (D 8) (R 8) [66,33,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10484 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 104 276 177 209 145 401), lower := (rows 67 35 44 104 276 32 64 128 256), losses := [] }

theorem u10484 : Upper (D 8) (R 8) [66,33,40,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10485 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 104 400 181 213 149 405), lower := (rows 67 35 44 104 400 32 64 128 256), losses := [] }

theorem u10485 : Upper (D 8) (R 8) [66,33,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10486 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 84 432 496 432 432), lower := (rows 67 35 44 137 84 32 64 128 256), losses := [] }

theorem u10486 : Upper (D 8) (R 8) [66,33,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10487 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 148 368 368 496 368), lower := (rows 67 35 44 137 148 32 64 128 256), losses := [] }

theorem u10487 : Upper (D 8) (R 8) [66,33,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10488 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 176 372 340 468 340), lower := (rows 67 35 44 137 176 32 64 128 256), losses := [] }

theorem u10488 : Upper (D 8) (R 8) [66,33,40,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10489 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 208 308 372 436 308), lower := (rows 67 35 44 137 208 32 64 128 256), losses := [] }

theorem u10489 : Upper (D 8) (R 8) [66,33,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10490 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 276 240 240 240 496), lower := (rows 67 35 44 137 276 32 64 128 256), losses := [] }

theorem u10490 : Upper (D 8) (R 8) [66,33,40,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10491 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 304 244 212 212 468), lower := (rows 67 35 44 137 304 32 64 128 256), losses := [] }

theorem u10491 : Upper (D 8) (R 8) [66,33,40,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10492 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 336 180 244 180 436), lower := (rows 67 35 44 137 336 32 64 128 256), losses := [] }

theorem u10492 : Upper (D 8) (R 8) [66,33,40,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10493 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 400 116 116 244 372), lower := (rows 67 35 44 137 400 32 64 128 256), losses := [] }

theorem u10493 : Upper (D 8) (R 8) [66,33,40,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10494 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 140 81 432 496 432 432), lower := (rows 67 35 44 140 81 32 64 128 256), losses := [] }

theorem u10494 : Upper (D 8) (R 8) [66,33,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10495 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 140 112 433 465 401 401), lower := (rows 67 35 44 140 112 32 64 128 256), losses := [] }

theorem u10495 : Upper (D 8) (R 8) [66,33,40,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10496 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 140 145 368 368 496 368), lower := (rows 67 35 44 140 145 32 64 128 256), losses := [] }

theorem u10496 : Upper (D 8) (R 8) [66,33,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10497 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 140 176 369 337 465 337), lower := (rows 67 35 44 140 176 32 64 128 256), losses := [] }

theorem u10497 : Upper (D 8) (R 8) [66,33,40,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10498 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 140 208 305 369 433 305), lower := (rows 67 35 44 140 208 32 64 128 256), losses := [] }

theorem u10498 : Upper (D 8) (R 8) [66,33,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10499 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 140 273 240 240 240 496), lower := (rows 67 35 44 140 273 32 64 128 256), losses := [] }

theorem u10499 : Upper (D 8) (R 8) [66,33,40,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10499
end Delivery.IrregularNine14.P08
