import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0002

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2400 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 26 145 96 192 168 296), lower := (rows 7 98 261 26 145 96 192 128 256), losses := [] }

theorem u2400 : Upper (D 7) (R 7) [6,96,257,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2401 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 82, targets := 1 },{ cop := 3, region := 82, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 261 41 88 160 66 144 400), lower := (rows 7 98 261 41 88 160 66 128 256), losses := [] }

theorem u2401 : Upper (D 7) (R 7) [6,96,257,33,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2402 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 261 41 88 160 80 130 386), lower := (rows 7 98 261 41 88 160 80 128 256), losses := [] }

theorem u2402 : Upper (D 7) (R 7) [6,96,257,33,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2402 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2403 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 261 41 88 160 192 146 274), lower := (rows 7 98 261 41 88 160 192 128 256), losses := [] }

theorem u2403 : Upper (D 7) (R 7) [6,96,257,33,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2404 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 261 41 146 160 72 208 336), lower := (rows 7 98 261 41 146 160 72 128 256), losses := [] }

theorem u2404 : Upper (D 7) (R 7) [6,96,257,33,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2404 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2405 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 261 41 146 160 80 200 328), lower := (rows 7 98 261 41 146 160 80 128 256), losses := [] }

theorem u2405 : Upper (D 7) (R 7) [6,96,257,33,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2405 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2406 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 210, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(4,0)], upper := (rows 7 98 261 41 152 160 66 208 336), lower := (rows 7 98 261 41 152 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 24 0 67 136 264), good := (rows 71 66 325 477 412 128 66 128 256) }] }

theorem u2406 : Upper (D 7) (R 7) [6,96,257,33,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2407 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 261 41 152 160 80 194 322), lower := (rows 7 98 261 41 152 160 80 128 256), losses := [] }

theorem u2407 : Upper (D 7) (R 7) [6,96,257,33,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2407 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2408 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 210, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(4,0)], upper := (rows 7 98 261 41 208 160 66 152 280), lower := (rows 7 98 261 41 208 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 24 0 67 136 264), good := (rows 71 66 325 477 208 128 66 128 256) }] }

theorem u2408 : Upper (D 7) (R 7) [6,96,257,33,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2409 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 261 41 208 160 72 146 274), lower := (rows 7 98 261 41 208 160 72 128 256), losses := [] }

theorem u2409 : Upper (D 7) (R 7) [6,96,257,33,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2409 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2410 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 261 41 208 160 80 138 266), lower := (rows 7 98 261 41 208 160 80 128 256), losses := [] }

theorem u2410 : Upper (D 7) (R 7) [6,96,257,33,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2410 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2411 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 261 56 146 33 72 192 448), lower := (rows 7 98 261 56 146 33 72 128 256), losses := [] }

theorem u2411 : Upper (D 7) (R 7) [6,96,257,48,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2411 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2412 : Route 9 := (fun mask => (mask,id))

def c2412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2412 : Upper (D 7) (R 7) [6,96,257,48,130,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,130,1,128] 13 (by decide) (choices 1) [8,64] r2412 c2412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u152
  · exact u153

def b2413 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 98 261 56 208 33 66 136 392), lower := (rows 7 98 261 56 208 33 66 128 256), losses := [] }

theorem u2413 : Upper (D 7) (R 7) [6,96,257,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2414 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 261 56 208 33 72 130 386), lower := (rows 7 98 261 56 208 33 72 128 256), losses := [] }

theorem u2414 : Upper (D 7) (R 7) [6,96,257,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2414 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2415 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 261 56 208 33 192 138 266), lower := (rows 7 98 261 56 208 33 192 128 256), losses := [] }

theorem u2415 : Upper (D 7) (R 7) [6,96,257,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2416 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 98 261 137 146 40 80 224 352), lower := (rows 7 98 261 137 146 40 80 128 256), losses := [] }

theorem u2416 : Upper (D 7) (R 7) [6,96,257,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2416 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2417 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 261 137 146 40 96 208 336), lower := (rows 7 98 261 137 146 40 96 128 256), losses := [] }

theorem u2417 : Upper (D 7) (R 7) [6,96,257,129,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2417 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2418 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 261 137 146 48 96 200 328), lower := (rows 7 98 261 137 146 48 96 128 256), losses := [] }

theorem u2418 : Upper (D 7) (R 7) [6,96,257,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2418 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2419 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 261 138 176 33 72 208 336), lower := (rows 7 98 261 138 176 33 72 128 256), losses := [] }

theorem u2419 : Upper (D 7) (R 7) [6,96,257,130,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2419 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2420 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 261 138 176 33 80 200 328), lower := (rows 7 98 261 138 176 33 80 128 256), losses := [] }

theorem u2420 : Upper (D 7) (R 7) [6,96,257,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2420 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2421 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 98 261 168 208 33 66 152 280), lower := (rows 7 98 261 168 208 33 66 128 256), losses := [] }

theorem u2421 : Upper (D 7) (R 7) [6,96,257,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2422 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 261 168 208 33 72 146 274), lower := (rows 7 98 261 168 208 33 72 128 256), losses := [] }

theorem u2422 : Upper (D 7) (R 7) [6,96,257,160,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2422 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2423 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 261 168 208 33 80 138 266), lower := (rows 7 98 261 168 208 33 80 128 256), losses := [] }

theorem u2423 : Upper (D 7) (R 7) [6,96,257,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2423 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2424 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 261 168 208 34 72 145 273), lower := (rows 7 98 261 168 208 34 72 128 256), losses := [] }

theorem u2424 : Upper (D 7) (R 7) [6,96,257,160,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2424 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2425 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 261 168 208 34 80 137 265), lower := (rows 7 98 261 168 208 34 80 128 256), losses := [] }

theorem u2425 : Upper (D 7) (R 7) [6,96,257,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2425 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2426 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 268 25 146 33 96 192 448), lower := (rows 7 98 268 25 146 33 96 128 256), losses := [] }

theorem u2426 : Upper (D 7) (R 7) [6,96,264,17,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2427 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 210, targets := 1 },{ cop := 3, region := 484, targets := 2 }], pairs := [(0,7),(1,0),(2,1),(4,0)], upper := (rows 7 98 268 25 146 33 192 224 352), lower := (rows 7 98 268 25 146 33 192 128 256), losses := [{ target := 7, region := (rows 17 2 20 24 16 57 64 0 258), good := (rows 295 354 300 61 319 33 64 0 256) }] }

theorem u2427 : Upper (D 7) (R 7) [6,96,264,17,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2428 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 25 146 96 192 161 289), lower := (rows 7 98 268 25 146 96 192 128 256), losses := [] }

theorem u2428 : Upper (D 7) (R 7) [6,96,264,17,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2429 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(4,1)], upper := (rows 7 98 268 26 145 33 192 224 352), lower := (rows 7 98 268 26 145 33 192 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 16 32 251 162 290), good := (rows 454 482 332 478 208 482 192 192 256) },{ target := 1, region := (rows 1 0 12 8 49 49 255 187 315), good := (rows 501 496 460 508 497 497 192 192 256) }] }

theorem u2429 : Upper (D 7) (R 7) [6,96,264,18,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2430 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 26 145 96 192 161 289), lower := (rows 7 98 268 26 145 96 192 128 256), losses := [] }

theorem u2430 : Upper (D 7) (R 7) [6,96,264,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2431 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 268 26 176 33 65 192 448), lower := (rows 7 98 268 26 176 33 65 128 256), losses := [] }

theorem u2431 : Upper (D 7) (R 7) [6,96,264,18,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2432 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 4, region := 74, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,0)], upper := (rows 7 98 268 26 176 33 192 193 321), lower := (rows 7 98 268 26 176 33 192 128 256), losses := [] }

theorem u2432 : Upper (D 7) (R 7) [6,96,264,18,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2433 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 7 98 268 41 81 160 66 144 400), lower := (rows 7 98 268 41 81 160 66 128 256), losses := [] }

theorem u2433 : Upper (D 7) (R 7) [6,96,264,33,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2434 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 268 41 81 160 80 130 386), lower := (rows 7 98 268 41 81 160 80 128 256), losses := [] }

theorem u2434 : Upper (D 7) (R 7) [6,96,264,33,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2434 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 268 41 81 160 192 146 274), lower := (rows 7 98 268 41 81 160 192 128 256), losses := [] }

theorem u2435 : Upper (D 7) (R 7) [6,96,264,33,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2436 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 178, targets := 1 },{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 7 98 268 41 146 160 65 208 336), lower := (rows 7 98 268 41 146 160 65 128 256), losses := [] }

theorem u2436 : Upper (D 7) (R 7) [6,96,264,33,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2437 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 268 41 146 160 80 193 321), lower := (rows 7 98 268 41 146 160 80 128 256), losses := [] }

theorem u2437 : Upper (D 7) (R 7) [6,96,264,33,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2437 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2438 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 178, targets := 1 },{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 7 98 268 41 208 160 65 146 274), lower := (rows 7 98 268 41 208 160 65 128 256), losses := [] }

theorem u2438 : Upper (D 7) (R 7) [6,96,264,33,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2439 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 0, region := 208, targets := 32 },{ cop := 5, region := 82, targets := 1 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 7 98 268 41 208 160 66 145 273), lower := (rows 7 98 268 41 208 160 66 128 256), losses := [] }

theorem u2439 : Upper (D 7) (R 7) [6,96,264,33,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 268 41 208 160 80 131 259), lower := (rows 7 98 268 41 208 160 80 128 256), losses := [] }

theorem u2440 : Upper (D 7) (R 7) [6,96,264,33,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2440 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2441 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 98 268 56 81 160 65 130 386), lower := (rows 7 98 268 56 81 160 65 128 256), losses := [] }

theorem u2441 : Upper (D 7) (R 7) [6,96,264,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2442 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 7 98 268 56 81 160 66 129 385), lower := (rows 7 98 268 56 81 160 66 128 256), losses := [] }

theorem u2442 : Upper (D 7) (R 7) [6,96,264,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2443 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 268 56 81 160 192 131 259), lower := (rows 7 98 268 56 81 160 192 128 256), losses := [] }

theorem u2443 : Upper (D 7) (R 7) [6,96,264,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2444 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 268 56 146 33 65 192 448), lower := (rows 7 98 268 56 146 33 65 128 256), losses := [] }

theorem u2444 : Upper (D 7) (R 7) [6,96,264,48,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2445 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(2,1),(2,5),(4,5)], upper := (rows 7 98 268 56 146 33 192 193 321), lower := (rows 7 98 268 56 146 33 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 32 208 128 256), good := (rows 6 98 270 122 210 32 192 192 256) },{ target := 1, region := (rows 1 0 12 8 16 33 251 161 289), good := (rows 485 480 332 508 208 481 192 192 256) },{ target := 5, region := (rows 1 2 12 8 19 0 251 161 289), good := (rows 471 466 332 476 210 465 192 192 256) }] }

theorem u2445 : Upper (D 7) (R 7) [6,96,264,48,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2446 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 268 56 208 33 65 130 386), lower := (rows 7 98 268 56 208 33 65 128 256), losses := [] }

theorem u2446 : Upper (D 7) (R 7) [6,96,264,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2447 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,5)], upper := (rows 7 98 268 56 208 33 66 129 385), lower := (rows 7 98 268 56 208 33 66 128 256), losses := [] }

theorem u2447 : Upper (D 7) (R 7) [6,96,264,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2448 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 268 56 208 33 192 131 259), lower := (rows 7 98 268 56 208 33 192 128 256), losses := [] }

theorem u2448 : Upper (D 7) (R 7) [6,96,264,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2449 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 98 268 137 146 33 80 224 352), lower := (rows 7 98 268 137 146 33 80 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 16 41 80 130 258), good := (rows 429 480 300 173 464 45 80 128 256) }] }

theorem u2449 : Upper (D 7) (R 7) [6,96,264,129,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2449 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2450 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 268 137 146 33 96 208 336), lower := (rows 7 98 268 137 146 33 96 128 256), losses := [] }

theorem u2450 : Upper (D 7) (R 7) [6,96,264,129,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2451 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 268 137 146 48 96 193 321), lower := (rows 7 98 268 137 146 48 96 128 256), losses := [] }

theorem u2451 : Upper (D 7) (R 7) [6,96,264,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2451 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2452 : Route 9 := (fun mask => (mask,id))

def c2452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2452 : Upper (D 7) (R 7) [6,96,264,130,33,128,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,130,33,128,1] 13 (by decide) (choices 1) [16,64] r2452 c2452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u154
  · exact u155

def b2453 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 268 138 49 160 80 193 321), lower := (rows 7 98 268 138 49 160 80 128 256), losses := [] }

theorem u2453 : Upper (D 7) (R 7) [6,96,264,130,33,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2453 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2454 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 396, targets := 1 },{ cop := 0, region := 240, targets := 2 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 7 98 268 138 145 33 80 224 352), lower := (rows 7 98 268 138 145 33 80 128 256), losses := [] }

theorem u2454 : Upper (D 7) (R 7) [6,96,264,130,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2454 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2455 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 268 138 145 33 96 208 336), lower := (rows 7 98 268 138 145 33 96 128 256), losses := [] }

theorem u2455 : Upper (D 7) (R 7) [6,96,264,130,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2456 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 268 138 145 48 96 193 321), lower := (rows 7 98 268 138 145 48 96 128 256), losses := [] }

theorem u2456 : Upper (D 7) (R 7) [6,96,264,130,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2456 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2457 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 268 138 176 33 65 208 336), lower := (rows 7 98 268 138 176 33 65 128 256), losses := [] }

theorem u2457 : Upper (D 7) (R 7) [6,96,264,130,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2458 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 268 138 176 33 80 193 321), lower := (rows 7 98 268 138 176 33 80 128 256), losses := [] }

theorem u2458 : Upper (D 7) (R 7) [6,96,264,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2458 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2459 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 7 98 268 168 81 33 66 144 400), lower := (rows 7 98 268 168 81 33 66 128 256), losses := [] }

theorem u2459 : Upper (D 7) (R 7) [6,96,264,160,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2459
end Delivery.IrregularNine14.P07
