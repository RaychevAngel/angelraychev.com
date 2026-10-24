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

def b10380 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 73 176 420 484 420 420), lower := (rows 67 35 28 73 176 32 64 128 256), losses := [] }

theorem u10380 : Upper (D 8) (R 8) [66,33,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10381 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 73 276 160 224 160 416), lower := (rows 67 35 28 73 276 32 64 128 256), losses := [] }

theorem u10381 : Upper (D 8) (R 8) [66,33,24,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10382 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 73 304 164 228 164 420), lower := (rows 67 35 28 73 304 32 64 128 256), losses := [] }

theorem u10382 : Upper (D 8) (R 8) [66,33,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10383 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 73 400 164 228 164 420), lower := (rows 67 35 28 73 400 32 64 128 256), losses := [] }

theorem u10383 : Upper (D 8) (R 8) [66,33,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10384 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 76 176 417 481 417 417), lower := (rows 67 35 28 76 176 32 64 128 256), losses := [] }

theorem u10384 : Upper (D 8) (R 8) [66,33,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10385 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 76 304 161 225 161 417), lower := (rows 67 35 28 76 304 32 64 128 256), losses := [] }

theorem u10385 : Upper (D 8) (R 8) [66,33,24,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10386 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 76 400 161 225 161 417), lower := (rows 67 35 28 76 400 32 64 128 256), losses := [] }

theorem u10386 : Upper (D 8) (R 8) [66,33,24,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10387 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 104 148 417 481 417 417), lower := (rows 67 35 28 104 148 32 64 128 256), losses := [] }

theorem u10387 : Upper (D 8) (R 8) [66,33,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10388 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 104 176 421 453 389 389), lower := (rows 67 35 28 104 176 32 64 128 256), losses := [] }

theorem u10388 : Upper (D 8) (R 8) [66,33,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10389 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 104 276 161 225 161 417), lower := (rows 67 35 28 104 276 32 64 128 256), losses := [] }

theorem u10389 : Upper (D 8) (R 8) [66,33,24,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10390 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 104 304 165 197 133 389), lower := (rows 67 35 28 104 304 32 64 128 256), losses := [] }

theorem u10390 : Upper (D 8) (R 8) [66,33,24,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10391 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 104 400 165 229 165 421), lower := (rows 67 35 28 104 400 32 64 128 256), losses := [] }

theorem u10391 : Upper (D 8) (R 8) [66,33,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10392 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 67 35 28 137 148 352 352 480 352), lower := (rows 67 35 28 137 148 32 64 128 256), losses := [] }

theorem u10392 : Upper (D 8) (R 8) [66,33,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10393 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 137 176 356 356 484 356), lower := (rows 67 35 28 137 176 32 64 128 256), losses := [] }

theorem u10393 : Upper (D 8) (R 8) [66,33,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10394 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 137 208 292 356 420 292), lower := (rows 67 35 28 137 208 32 64 128 256), losses := [] }

theorem u10394 : Upper (D 8) (R 8) [66,33,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10395 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 137 276 224 224 224 480), lower := (rows 67 35 28 137 276 32 64 128 256), losses := [] }

theorem u10395 : Upper (D 8) (R 8) [66,33,24,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10396 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 137 304 228 228 228 484), lower := (rows 67 35 28 137 304 32 64 128 256), losses := [] }

theorem u10396 : Upper (D 8) (R 8) [66,33,24,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10397 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 137 336 164 228 164 420), lower := (rows 67 35 28 137 336 32 64 128 256), losses := [] }

theorem u10397 : Upper (D 8) (R 8) [66,33,24,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10398 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 137 400 100 100 228 356), lower := (rows 67 35 28 137 400 32 64 128 256), losses := [] }

theorem u10398 : Upper (D 8) (R 8) [66,33,24,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10399 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 140 176 353 353 481 353), lower := (rows 67 35 28 140 176 32 64 128 256), losses := [] }

theorem u10399 : Upper (D 8) (R 8) [66,33,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10400 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 140 208 289 353 417 289), lower := (rows 67 35 28 140 208 32 64 128 256), losses := [] }

theorem u10400 : Upper (D 8) (R 8) [66,33,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10401 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 140 273 224 224 224 480), lower := (rows 67 35 28 140 273 32 64 128 256), losses := [] }

theorem u10401 : Upper (D 8) (R 8) [66,33,24,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10402 : Route 9 := (fun mask => (mask,id))

def c10402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10402 : Upper (D 8) (R 8) [66,33,24,132,288] 13 := by
  apply FastRouting.sound _ _ [66,33,24,132,288] 13 (by decide) (choices 1) [1,64,128] r10402 c10402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2885
  · exact u2886
  · exact u2887

def b10403 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 140 336 161 225 161 417), lower := (rows 67 35 28 140 336 32 64 128 256), losses := [] }

theorem u10403 : Upper (D 8) (R 8) [66,33,24,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10404 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 140 400 97 97 225 353), lower := (rows 67 35 28 140 400 32 64 128 256), losses := [] }

theorem u10404 : Upper (D 8) (R 8) [66,33,24,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10405 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 168 176 357 325 453 325), lower := (rows 67 35 28 168 176 32 64 128 256), losses := [] }

theorem u10405 : Upper (D 8) (R 8) [66,33,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10406 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 168 208 293 357 421 293), lower := (rows 67 35 28 168 208 32 64 128 256), losses := [] }

theorem u10406 : Upper (D 8) (R 8) [66,33,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10407 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 168 273 228 228 228 484), lower := (rows 67 35 28 168 273 32 64 128 256), losses := [] }

theorem u10407 : Upper (D 8) (R 8) [66,33,24,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10408 : Route 9 := (fun mask => (mask,id))

def c10408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10408 : Upper (D 8) (R 8) [66,33,24,160,260] 13 := by
  apply FastRouting.sound _ _ [66,33,24,160,260] 13 (by decide) (choices 1) [1,64,128] r10408 c10408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2888
  · exact u2889
  · exact u2890

def r10409 : Route 9 := (fun mask => (mask,id))

def c10409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10409 : Upper (D 8) (R 8) [66,33,24,160,288] 13 := by
  apply FastRouting.sound _ _ [66,33,24,160,288] 13 (by decide) (choices 1) [1,4,64,128] r10409 c10409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2891
  · exact u2892
  · exact u2893
  · exact u2894

def r10410 : Route 9 := (fun mask => (mask,id))

def c10410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10410 : Upper (D 8) (R 8) [66,33,24,160,320] 13 := by
  apply FastRouting.sound _ _ [66,33,24,160,320] 13 (by decide) (choices 1) [1,4,128] r10410 c10410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2895
  · exact u2896
  · exact u2897

def b10411 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 168 400 101 101 229 357), lower := (rows 67 35 28 168 400 32 64 128 256), losses := [] }

theorem u10411 : Upper (D 8) (R 8) [66,33,24,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10412 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 200 273 164 228 164 420), lower := (rows 67 35 28 200 273 32 64 128 256), losses := [] }

theorem u10412 : Upper (D 8) (R 8) [66,33,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10413 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 200 276 161 225 161 417), lower := (rows 67 35 28 200 276 32 64 128 256), losses := [] }

theorem u10413 : Upper (D 8) (R 8) [66,33,24,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10414 : Route 9 := (fun mask => (mask,id))

def c10414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10414 : Upper (D 8) (R 8) [66,33,24,192,288] 13 := by
  apply FastRouting.sound _ _ [66,33,24,192,288] 13 (by decide) (choices 1) [1,4,128] r10414 c10414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2898
  · exact u2899
  · exact u2900

def b10415 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 200 400 37 101 165 293), lower := (rows 67 35 28 200 400 32 64 128 256), losses := [] }

theorem u10415 : Upper (D 8) (R 8) [66,33,24,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10416 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 44 88 432 464 400 400), lower := (rows 67 35 37 44 88 32 64 128 256), losses := [] }

theorem u10416 : Upper (D 8) (R 8) [66,33,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10417 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 44 152 496 464 464 464), lower := (rows 67 35 37 44 152 32 64 128 256), losses := [] }

theorem u10417 : Upper (D 8) (R 8) [66,33,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10418 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 44 208 440 472 408 408), lower := (rows 67 35 37 44 208 32 64 128 256), losses := [] }

theorem u10418 : Upper (D 8) (R 8) [66,33,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10419 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 44 280 240 208 208 464), lower := (rows 67 35 37 44 280 32 64 128 256), losses := [] }

theorem u10419 : Upper (D 8) (R 8) [66,33,33,36,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10420 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 44 336 184 216 152 408), lower := (rows 67 35 37 44 336 32 64 128 256), losses := [] }

theorem u10420 : Upper (D 8) (R 8) [66,33,33,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10421 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 44 400 248 216 216 472), lower := (rows 67 35 37 44 400 32 64 128 256), losses := [] }

theorem u10421 : Upper (D 8) (R 8) [66,33,33,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10422 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 56 84 424 456 392 392), lower := (rows 67 35 37 56 84 32 64 128 256), losses := [] }

theorem u10422 : Upper (D 8) (R 8) [66,33,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10423 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 56 148 488 456 456 456), lower := (rows 67 35 37 56 148 32 64 128 256), losses := [] }

theorem u10423 : Upper (D 8) (R 8) [66,33,33,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10424 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 56 152 484 452 452 452), lower := (rows 67 35 37 56 152 32 64 128 256), losses := [] }

theorem u10424 : Upper (D 8) (R 8) [66,33,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10425 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 56 208 428 460 396 396), lower := (rows 67 35 37 56 208 32 64 128 256), losses := [] }

theorem u10425 : Upper (D 8) (R 8) [66,33,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10426 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 56 276 232 200 200 456), lower := (rows 67 35 37 56 276 32 64 128 256), losses := [] }

theorem u10426 : Upper (D 8) (R 8) [66,33,33,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10427 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 56 280 228 196 196 452), lower := (rows 67 35 37 56 280 32 64 128 256), losses := [] }

theorem u10427 : Upper (D 8) (R 8) [66,33,33,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10428 : PairBound 9 := { available := 140, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 56 336 172 204 140 396), lower := (rows 67 35 37 56 336 32 64 128 256), losses := [] }

theorem u10428 : Upper (D 8) (R 8) [66,33,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10429 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 56 400 236 204 204 460), lower := (rows 67 35 37 56 400 32 64 128 256), losses := [] }

theorem u10429 : Upper (D 8) (R 8) [66,33,33,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10430 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 76 152 432 496 432 432), lower := (rows 67 35 37 76 152 32 64 128 256), losses := [] }

theorem u10430 : Upper (D 8) (R 8) [66,33,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10431 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 76 176 440 472 408 408), lower := (rows 67 35 37 76 176 32 64 128 256), losses := [] }

theorem u10431 : Upper (D 8) (R 8) [66,33,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10432 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 76 280 176 240 176 432), lower := (rows 67 35 37 76 280 32 64 128 256), losses := [] }

theorem u10432 : Upper (D 8) (R 8) [66,33,33,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10433 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 76 304 184 216 152 408), lower := (rows 67 35 37 76 304 32 64 128 256), losses := [] }

theorem u10433 : Upper (D 8) (R 8) [66,33,33,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10434 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 76 400 184 248 184 440), lower := (rows 67 35 37 76 400 32 64 128 256), losses := [] }

theorem u10434 : Upper (D 8) (R 8) [66,33,33,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10435 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 88 148 424 488 424 424), lower := (rows 67 35 37 88 148 32 64 128 256), losses := [] }

theorem u10435 : Upper (D 8) (R 8) [66,33,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10436 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 88 176 428 460 396 396), lower := (rows 67 35 37 88 176 32 64 128 256), losses := [] }

theorem u10436 : Upper (D 8) (R 8) [66,33,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10437 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 88 276 168 232 168 424), lower := (rows 67 35 37 88 276 32 64 128 256), losses := [] }

theorem u10437 : Upper (D 8) (R 8) [66,33,33,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10438 : PairBound 9 := { available := 140, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 88 304 172 204 140 396), lower := (rows 67 35 37 88 304 32 64 128 256), losses := [] }

theorem u10438 : Upper (D 8) (R 8) [66,33,33,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10439 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 88 400 172 236 172 428), lower := (rows 67 35 37 88 400 32 64 128 256), losses := [] }

theorem u10439 : Upper (D 8) (R 8) [66,33,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10439
end Delivery.IrregularNine14.P08
