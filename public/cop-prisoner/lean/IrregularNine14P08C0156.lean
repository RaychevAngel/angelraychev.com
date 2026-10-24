import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0039

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9360 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 76 304 161 225 161 417), lower := (rows 35 194 28 76 304 32 64 128 256), losses := [] }

theorem u9360 : Upper (D 8) (R 8) [34,192,24,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9361 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 76 400 33 97 161 289), lower := (rows 35 194 28 76 400 32 64 128 256), losses := [] }

theorem u9361 : Upper (D 8) (R 8) [34,192,24,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9362 : Route 9 := (fun mask => (mask,id))

def c9362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u9362 : Upper (D 8) (R 8) [34,192,24,96,160] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,160] 13 (by decide) (choices 1) [1,4,256] r9362 c9362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2361
  · exact u2362
  · exact u2363

def r9363 : Route 9 := (fun mask => (mask,id))

def c9363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9363 : Upper (D 8) (R 8) [34,192,24,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,257] 13 (by decide) (choices 1) [1,4,128] r9363 c9363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2364
  · exact u2365
  · exact u2366

def b9364 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 104 276 161 225 161 417), lower := (rows 35 194 28 104 276 32 64 128 256), losses := [] }

theorem u9364 : Upper (D 8) (R 8) [34,192,24,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9365 : Route 9 := (fun mask => (mask,id))

def c9365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9365 : Upper (D 8) (R 8) [34,192,24,96,288] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,288] 13 (by decide) (choices 1) [1,4,128] r9365 c9365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2367
  · exact u2368
  · exact u2369

def r9366 : Route 9 := (fun mask => (mask,id))

def c9366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9366 : Upper (D 8) (R 8) [34,192,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,384] 13 (by decide) (choices 1) [1,4] r9366 c9366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2370
  · exact u2371

def b9367 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 28 200 273 37 101 165 293), lower := (rows 35 194 28 200 273 32 64 128 256), losses := [] }

theorem u9367 : Upper (D 8) (R 8) [34,192,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9368 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 28 200 276 33 97 161 289), lower := (rows 35 194 28 200 276 32 64 128 256), losses := [] }

theorem u9368 : Upper (D 8) (R 8) [34,192,24,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9369 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 28 200 304 37 101 165 293), lower := (rows 35 194 28 200 304 32 64 128 256), losses := [] }

theorem u9369 : Upper (D 8) (R 8) [34,192,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9370 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 44 88 433 465 401 401), lower := (rows 35 194 37 44 88 32 64 128 256), losses := [] }

theorem u9370 : Upper (D 8) (R 8) [34,192,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9371 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 44 273 248 216 216 472), lower := (rows 35 194 37 44 273 32 64 128 256), losses := [] }

theorem u9371 : Upper (D 8) (R 8) [34,192,33,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9372 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 44 280 241 209 209 465), lower := (rows 35 194 37 44 280 32 64 128 256), losses := [] }

theorem u9372 : Upper (D 8) (R 8) [34,192,33,36,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9373 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 44 336 185 217 153 409), lower := (rows 35 194 37 44 336 32 64 128 256), losses := [] }

theorem u9373 : Upper (D 8) (R 8) [34,192,33,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9374 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 56 84 425 457 393 393), lower := (rows 35 194 37 56 84 32 64 128 256), losses := [] }

theorem u9374 : Upper (D 8) (R 8) [34,192,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9375 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 56 273 236 204 204 460), lower := (rows 35 194 37 56 273 32 64 128 256), losses := [] }

theorem u9375 : Upper (D 8) (R 8) [34,192,33,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9376 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 56 276 233 201 201 457), lower := (rows 35 194 37 56 276 32 64 128 256), losses := [] }

theorem u9376 : Upper (D 8) (R 8) [34,192,33,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9377 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 56 280 229 197 197 453), lower := (rows 35 194 37 56 280 32 64 128 256), losses := [] }

theorem u9377 : Upper (D 8) (R 8) [34,192,33,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9378 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 56 336 173 205 141 397), lower := (rows 35 194 37 56 336 32 64 128 256), losses := [] }

theorem u9378 : Upper (D 8) (R 8) [34,192,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9379 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 76 152 305 369 433 305), lower := (rows 35 194 37 76 152 32 64 128 256), losses := [] }

theorem u9379 : Upper (D 8) (R 8) [34,192,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9380 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 76 176 313 345 409 281), lower := (rows 35 194 37 76 176 32 64 128 256), losses := [] }

theorem u9380 : Upper (D 8) (R 8) [34,192,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9381 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 76 273 184 248 184 440), lower := (rows 35 194 37 76 273 32 64 128 256), losses := [] }

theorem u9381 : Upper (D 8) (R 8) [34,192,33,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9382 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 76 280 177 241 177 433), lower := (rows 35 194 37 76 280 32 64 128 256), losses := [] }

theorem u9382 : Upper (D 8) (R 8) [34,192,33,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9383 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 76 304 185 217 153 409), lower := (rows 35 194 37 76 304 32 64 128 256), losses := [] }

theorem u9383 : Upper (D 8) (R 8) [34,192,33,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9384 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 76 400 57 121 185 313), lower := (rows 35 194 37 76 400 32 64 128 256), losses := [] }

theorem u9384 : Upper (D 8) (R 8) [34,192,33,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9385 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 88 176 301 333 397 269), lower := (rows 35 194 37 88 176 32 64 128 256), losses := [] }

theorem u9385 : Upper (D 8) (R 8) [34,192,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9386 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 88 273 172 236 172 428), lower := (rows 35 194 37 88 273 32 64 128 256), losses := [] }

theorem u9386 : Upper (D 8) (R 8) [34,192,33,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9387 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 88 276 169 233 169 425), lower := (rows 35 194 37 88 276 32 64 128 256), losses := [] }

theorem u9387 : Upper (D 8) (R 8) [34,192,33,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9388 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 88 304 173 205 141 397), lower := (rows 35 194 37 88 304 32 64 128 256), losses := [] }

theorem u9388 : Upper (D 8) (R 8) [34,192,33,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9389 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 88 400 45 109 173 301), lower := (rows 35 194 37 88 400 32 64 128 256), losses := [] }

theorem u9389 : Upper (D 8) (R 8) [34,192,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9390 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 104 273 188 220 156 412), lower := (rows 35 194 37 104 273 32 64 128 256), losses := [] }

theorem u9390 : Upper (D 8) (R 8) [34,192,33,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9391 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 104 276 185 217 153 409), lower := (rows 35 194 37 104 276 32 64 128 256), losses := [] }

theorem u9391 : Upper (D 8) (R 8) [34,192,33,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9392 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 104 280 181 213 149 405), lower := (rows 35 194 37 104 280 32 64 128 256), losses := [] }

theorem u9392 : Upper (D 8) (R 8) [34,192,33,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9393 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 104 400 61 93 157 285), lower := (rows 35 194 37 104 400 32 64 128 256), losses := [] }

theorem u9393 : Upper (D 8) (R 8) [34,192,33,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9394 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 44 273 241 209 209 465), lower := (rows 35 194 44 44 273 32 64 128 256), losses := [] }

theorem u9394 : Upper (D 8) (R 8) [34,192,40,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9395 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 44 336 177 209 145 401), lower := (rows 35 194 44 44 336 32 64 128 256), losses := [] }

theorem u9395 : Upper (D 8) (R 8) [34,192,40,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9396 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 56 84 417 449 385 385), lower := (rows 35 194 44 56 84 32 64 128 256), losses := [] }

theorem u9396 : Upper (D 8) (R 8) [34,192,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9397 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 56 273 229 197 197 453), lower := (rows 35 194 44 56 273 32 64 128 256), losses := [] }

theorem u9397 : Upper (D 8) (R 8) [34,192,40,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9398 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 56 276 225 193 193 449), lower := (rows 35 194 44 56 276 32 64 128 256), losses := [] }

theorem u9398 : Upper (D 8) (R 8) [34,192,40,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9399 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 56 336 165 197 133 389), lower := (rows 35 194 44 56 336 32 64 128 256), losses := [] }

theorem u9399 : Upper (D 8) (R 8) [34,192,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9400 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 148 305 369 433 305), lower := (rows 35 194 44 73 148 32 64 128 256), losses := [] }

theorem u9400 : Upper (D 8) (R 8) [34,192,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9401 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 176 309 341 405 277), lower := (rows 35 194 44 73 176 32 64 128 256), losses := [] }

theorem u9401 : Upper (D 8) (R 8) [34,192,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9402 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 273 180 244 180 436), lower := (rows 35 194 44 73 273 32 64 128 256), losses := [] }

theorem u9402 : Upper (D 8) (R 8) [34,192,40,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9403 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 276 177 241 177 433), lower := (rows 35 194 44 73 276 32 64 128 256), losses := [] }

theorem u9403 : Upper (D 8) (R 8) [34,192,40,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9404 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 304 181 213 149 405), lower := (rows 35 194 44 73 304 32 64 128 256), losses := [] }

theorem u9404 : Upper (D 8) (R 8) [34,192,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9405 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 400 53 117 181 309), lower := (rows 35 194 44 73 400 32 64 128 256), losses := [] }

theorem u9405 : Upper (D 8) (R 8) [34,192,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9406 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 76 176 305 337 401 273), lower := (rows 35 194 44 76 176 32 64 128 256), losses := [] }

theorem u9406 : Upper (D 8) (R 8) [34,192,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9407 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 76 273 177 241 177 433), lower := (rows 35 194 44 76 273 32 64 128 256), losses := [] }

theorem u9407 : Upper (D 8) (R 8) [34,192,40,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9408 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 76 304 177 209 145 401), lower := (rows 35 194 44 76 304 32 64 128 256), losses := [] }

theorem u9408 : Upper (D 8) (R 8) [34,192,40,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9409 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 76 400 49 113 177 305), lower := (rows 35 194 44 76 400 32 64 128 256), losses := [] }

theorem u9409 : Upper (D 8) (R 8) [34,192,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9410 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 88 145 293 357 421 293), lower := (rows 35 194 44 88 145 32 64 128 256), losses := [] }

theorem u9410 : Upper (D 8) (R 8) [34,192,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9411 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 88 148 289 353 417 289), lower := (rows 35 194 44 88 148 32 64 128 256), losses := [] }

theorem u9411 : Upper (D 8) (R 8) [34,192,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9412 : Route 9 := (fun mask => (mask,id))

def c9412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u9412 : Upper (D 8) (R 8) [34,192,40,80,160] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,160] 13 (by decide) (choices 1) [1,4,256] r9412 c9412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2372
  · exact u2373
  · exact u2374

def r9413 : Route 9 := (fun mask => (mask,id))

def c9413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9413 : Upper (D 8) (R 8) [34,192,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,257] 13 (by decide) (choices 1) [1,4,128] r9413 c9413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2375
  · exact u2376
  · exact u2377

def b9414 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 88 276 161 225 161 417), lower := (rows 35 194 44 88 276 32 64 128 256), losses := [] }

theorem u9414 : Upper (D 8) (R 8) [34,192,40,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9415 : Route 9 := (fun mask => (mask,id))

def c9415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9415 : Upper (D 8) (R 8) [34,192,40,80,288] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,288] 13 (by decide) (choices 1) [1,4,128] r9415 c9415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2378
  · exact u2379
  · exact u2380

def r9416 : Route 9 := (fun mask => (mask,id))

def c9416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9416 : Upper (D 8) (R 8) [34,192,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,384] 13 (by decide) (choices 1) [1,4] r9416 c9416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2381
  · exact u2382

def b9417 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 104 148 305 337 401 273), lower := (rows 35 194 44 104 148 32 64 128 256), losses := [] }

theorem u9417 : Upper (D 8) (R 8) [34,192,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9418 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 104 273 181 213 149 405), lower := (rows 35 194 44 104 273 32 64 128 256), losses := [] }

theorem u9418 : Upper (D 8) (R 8) [34,192,40,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9419 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 44 104 276 177 209 145 401), lower := (rows 35 194 44 104 276 32 64 128 256), losses := [] }

theorem u9419 : Upper (D 8) (R 8) [34,192,40,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9419
end Delivery.IrregularNine14.P08
