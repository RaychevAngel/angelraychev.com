import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0002

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2460 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 337, targets := 128 },{ cop := 6, region := 169, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,8),(4,7)], upper := (rows 97 14 22 137 273 160 320 224 352), lower := (rows 97 14 22 137 273 160 320 128 256), losses := [{ target := 7, region := (rows 33 10 14 8 57 32 377 0 289), good := (rows 369 94 86 351 337 369 320 0 320) }] }

theorem u2460 : Upper (D 9) (R 9) [96,12,18,129,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2461 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 169, targets := 256 },{ cop := 0, region := 400, targets := 1 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(3,8),(4,0)], upper := (rows 97 14 22 137 400 33 320 224 352), lower := (rows 97 14 22 137 400 33 320 128 256), losses := [{ target := 0, region := (rows 0 10 14 8 57 32 377 161 289), good := (rows 496 94 86 478 464 496 320 128 320) }] }

theorem u2461 : Upper (D 9) (R 9) [96,12,18,129,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2461 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2462 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 22 137 400 96 320 161 289), lower := (rows 97 14 22 137 400 96 320 128 256), losses := [] }

theorem u2462 : Upper (D 9) (R 9) [96,12,18,129,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2462 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2463 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,5)], upper := (rows 97 14 22 168 208 33 320 385 257), lower := (rows 97 14 22 168 208 33 320 128 256), losses := [] }

theorem u2463 : Upper (D 9) (R 9) [96,12,18,160,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2463 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2464 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 14 22 168 208 288 320 129 257), lower := (rows 97 14 22 168 208 288 320 128 256), losses := [] }

theorem u2464 : Upper (D 9) (R 9) [96,12,18,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2464 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2465 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(3,5),(4,0),(4,5)], upper := (rows 97 14 38 137 208 288 65 400 272), lower := (rows 97 14 38 137 208 288 65 128 256), losses := [] }

theorem u2465 : Upper (D 9) (R 9) [96,12,34,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2465 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2466 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 7, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 14 38 137 208 288 80 385 257), lower := (rows 97 14 38 137 208 288 80 128 256), losses := [] }

theorem u2466 : Upper (D 9) (R 9) [96,12,34,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2466 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2467 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 152, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 14 38 137 208 288 320 145 273), lower := (rows 97 14 38 137 208 288 320 128 256), losses := [] }

theorem u2467 : Upper (D 9) (R 9) [96,12,34,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2467 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2468 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 97 14 38 137 273 48 192 448 320), lower := (rows 97 14 38 137 273 48 192 128 256), losses := [] }

theorem u2468 : Upper (D 9) (R 9) [96,12,34,129,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2468 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2469 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 14 38 137 273 48 320 192 448), lower := (rows 97 14 38 137 273 48 320 128 256), losses := [] }

theorem u2469 : Upper (D 9) (R 9) [96,12,34,129,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2469 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2470 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 14 38 137 273 288 80 192 448), lower := (rows 97 14 38 137 273 288 80 128 256), losses := [] }

theorem u2470 : Upper (D 9) (R 9) [96,12,34,129,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2470 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2471 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 6, region := 305, targets := 128 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,7),(3,5),(3,8),(4,5),(4,7)], upper := (rows 97 14 38 137 273 288 192 208 336), lower := (rows 97 14 38 137 273 288 192 128 256), losses := [] }

theorem u2471 : Upper (D 9) (R 9) [96,12,34,129,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2471 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2472 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(3,5),(4,0),(4,5)], upper := (rows 97 14 38 137 336 288 65 144 400), lower := (rows 97 14 38 137 336 288 65 128 256), losses := [] }

theorem u2472 : Upper (D 9) (R 9) [96,12,34,129,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2472 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2473 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 14 38 137 336 288 80 129 385), lower := (rows 97 14 38 137 336 288 80 128 256), losses := [] }

theorem u2473 : Upper (D 9) (R 9) [96,12,34,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2473 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2474 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5),(4,7)], upper := (rows 97 14 38 137 336 288 192 145 273), lower := (rows 97 14 38 137 336 288 192 128 256), losses := [{ target := 7, region := (rows 81 10 14 8 81 379 64 0 345), good := (rows 369 302 38 319 369 288 369 0 288) }] }

theorem u2474 : Upper (D 9) (R 9) [96,12,34,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2474 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2475 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 38 137 400 48 65 448 320), lower := (rows 97 14 38 137 400 48 65 128 256), losses := [] }

theorem u2475 : Upper (D 9) (R 9) [96,12,34,129,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2475 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 14 38 137 400 48 320 193 321), lower := (rows 97 14 38 137 400 48 320 128 256), losses := [] }

theorem u2476 : Upper (D 9) (R 9) [96,12,34,129,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2476 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2477 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(3,5),(4,0),(4,5)], upper := (rows 97 14 38 137 400 288 65 208 336), lower := (rows 97 14 38 137 400 288 65 128 256), losses := [] }

theorem u2477 : Upper (D 9) (R 9) [96,12,34,129,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2477 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2478 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 14 38 137 400 288 80 193 321), lower := (rows 97 14 38 137 400 288 80 128 256), losses := [] }

theorem u2478 : Upper (D 9) (R 9) [96,12,34,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2478 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2479 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,6)], upper := (rows 97 14 38 200 145 288 65 400 272), lower := (rows 97 14 38 200 145 288 65 128 256), losses := [] }

theorem u2479 : Upper (D 9) (R 9) [96,12,34,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2479 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2480 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 97 14 38 200 145 288 80 385 257), lower := (rows 97 14 38 200 145 288 80 128 256), losses := [] }

theorem u2480 : Upper (D 9) (R 9) [96,12,34,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2480 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2481 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 152, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 14 38 200 145 288 320 145 273), lower := (rows 97 14 38 200 145 288 320 128 256), losses := [] }

theorem u2481 : Upper (D 9) (R 9) [96,12,34,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2481 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2482 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,6)], upper := (rows 97 14 38 200 273 288 65 144 400), lower := (rows 97 14 38 200 273 288 65 128 256), losses := [] }

theorem u2482 : Upper (D 9) (R 9) [96,12,34,192,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2482 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2483 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 14 38 200 273 288 80 129 385), lower := (rows 97 14 38 200 273 288 80 128 256), losses := [] }

theorem u2483 : Upper (D 9) (R 9) [96,12,34,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2483 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2484 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 97 14 38 200 273 288 192 145 273), lower := (rows 97 14 38 200 273 288 192 128 256), losses := [] }

theorem u2484 : Upper (D 9) (R 9) [96,12,34,192,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2484 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2485 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,6)], upper := (rows 97 14 38 200 400 288 65 145 273), lower := (rows 97 14 38 200 400 288 65 128 256), losses := [] }

theorem u2485 : Upper (D 9) (R 9) [96,12,34,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2485 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2486 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 289, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 14 38 200 400 288 80 129 257), lower := (rows 97 14 38 200 400 288 80 128 256), losses := [] }

theorem u2486 : Upper (D 9) (R 9) [96,12,34,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2486 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2487 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 65, targets := 384 },{ cop := 4, region := 420, targets := 65 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,7),(0,8),(2,0),(2,6),(3,5)], upper := (rows 97 14 52 137 82 288 65 384 384), lower := (rows 97 14 52 137 82 288 65 128 256), losses := [] }

theorem u2487 : Upper (D 9) (R 9) [96,12,48,129,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2487 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2488 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 293, targets := 128 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 392, targets := 64 }], pairs := [(0,7),(2,7),(3,5),(3,6),(4,0)], upper := (rows 97 14 52 137 82 288 192 385 257), lower := (rows 97 14 52 137 82 288 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 288 200 128 256), good := (rows 96 94 52 200 82 288 192 192 288) }] }

theorem u2488 : Upper (D 9) (R 9) [96,12,48,129,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2488 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2489 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 14 52 137 82 288 320 129 385), lower := (rows 97 14 52 137 82 288 320 128 256), losses := [] }

theorem u2489 : Upper (D 9) (R 9) [96,12,48,129,66,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2489 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2490 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 392, targets := 32 },{ cop := 2, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(2,7),(3,5)], upper := (rows 97 14 52 137 146 288 65 448 320), lower := (rows 97 14 52 137 146 288 65 128 256), losses := [{ target := 0, region := (rows 0 10 14 8 24 361 64 193 321), good := (rows 480 62 52 446 150 288 480 128 288) }] }

theorem u2490 : Upper (D 9) (R 9) [96,12,48,129,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2490 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2491 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 14 52 137 146 288 320 193 321), lower := (rows 97 14 52 137 146 288 320 128 256), losses := [] }

theorem u2491 : Upper (D 9) (R 9) [96,12,48,129,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2491 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2492 : Route 9 := (fun mask => (mask,id))

def c2492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 8 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | _ => 0)

theorem u2492 : Upper (D 9) (R 9) [96,12,48,129,192,256,1] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,192,256,1] 13 (by decide) (choices 1) [256] r2492 c2492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u146

def b2493 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 4, region := 293, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 14 52 137 208 288 66 385 257), lower := (rows 97 14 52 137 208 288 66 128 256), losses := [] }

theorem u2493 : Upper (D 9) (R 9) [96,12,48,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2493 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2494 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 14 52 137 208 288 320 131 259), lower := (rows 97 14 52 137 208 288 320 128 256), losses := [] }

theorem u2494 : Upper (D 9) (R 9) [96,12,48,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2494 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2495 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 276, targets := 128 }], pairs := [(2,7),(3,5),(4,5),(4,7)], upper := (rows 97 14 52 137 273 34 192 448 320), lower := (rows 97 14 52 137 273 34 192 128 256), losses := [] }

theorem u2495 : Upper (D 9) (R 9) [96,12,48,129,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2495 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2496 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 136, targets := 256 }], pairs := [(1,5),(3,5),(3,8),(4,5)], upper := (rows 97 14 52 137 273 34 320 192 448), lower := (rows 97 14 52 137 273 34 320 128 256), losses := [{ target := 5, region := (rows 1 6 4 25 25 0 511 511 511), good := (rows 473 478 478 473 473 450 448 448 448) }] }

theorem u2496 : Upper (D 9) (R 9) [96,12,48,129,257,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2496 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2497 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 276, targets := 128 }], pairs := [(2,7),(3,5),(4,5),(4,7)], upper := (rows 97 14 52 137 273 160 66 448 320), lower := (rows 97 14 52 137 273 160 66 128 256), losses := [] }

theorem u2497 : Upper (D 9) (R 9) [96,12,48,129,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2497 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2498 : Route 9 := (fun mask => (mask,id))

def c2498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2498 : Upper (D 9) (R 9) [96,12,48,129,257,128,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,257,128,256] 13 (by decide) (choices 1) [2,64] r2498 c2498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u147
  · exact u148

def b2499 : PairBound 9 := { available := 320, camps := [{ cop := 5, region := 73, targets := 256 },{ cop := 0, region := 392, targets := 32 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(3,5),(3,8)], upper := (rows 97 14 52 137 274 160 65 448 320), lower := (rows 97 14 52 137 274 160 65 128 256), losses := [{ target := 0, region := (rows 0 10 14 8 24 233 64 193 321), good := (rows 480 62 52 446 278 160 480 160 256) }] }

theorem u2499 : Upper (D 9) (R 9) [96,12,48,129,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2499 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2500 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 169, targets := 256 },{ cop := 0, region := 136, targets := 32 },{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(3,8),(4,5)], upper := (rows 97 14 52 137 274 160 320 193 321), lower := (rows 97 14 52 137 274 160 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 18 0 347 137 265), good := (rows 457 478 84 457 338 128 320 128 320) }] }

theorem u2500 : Upper (D 9) (R 9) [96,12,48,129,258,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2500 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2501 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 404, targets := 1 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 97 14 52 137 336 34 65 384 384), lower := (rows 97 14 52 137 336 34 65 128 256), losses := [] }

theorem u2501 : Upper (D 9) (R 9) [96,12,48,129,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2501 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2502 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 276, targets := 128 }], pairs := [(2,7),(3,5),(4,5),(4,7)], upper := (rows 97 14 52 137 336 34 192 385 257), lower := (rows 97 14 52 137 336 34 192 128 256), losses := [] }

theorem u2502 : Upper (D 9) (R 9) [96,12,48,129,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2502 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2503 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 52 137 336 34 320 129 385), lower := (rows 97 14 52 137 336 34 320 128 256), losses := [] }

theorem u2503 : Upper (D 9) (R 9) [96,12,48,129,320,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2503 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2504 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 65, targets := 384 },{ cop := 5, region := 73, targets := 256 }], pairs := [(0,7),(0,8),(3,8),(4,5),(4,7)], upper := (rows 97 14 52 137 336 160 65 386 258), lower := (rows 97 14 52 137 336 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 18 0 73 130 258), good := (rows 65 478 20 201 336 128 65 128 256) },{ target := 7, region := (rows 37 2 4 8 18 32 111 0 258), good := (rows 97 351 117 73 336 97 65 0 256) }] }

theorem u2504 : Upper (D 9) (R 9) [96,12,48,129,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2504 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2505 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 276, targets := 128 }], pairs := [(2,7),(3,5),(4,5),(4,7)], upper := (rows 97 14 52 137 336 160 66 385 257), lower := (rows 97 14 52 137 336 160 66 128 256), losses := [] }

theorem u2505 : Upper (D 9) (R 9) [96,12,48,129,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2505 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2506 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 14 52 137 336 160 320 131 259), lower := (rows 97 14 52 137 336 160 320 128 256), losses := [] }

theorem u2506 : Upper (D 9) (R 9) [96,12,48,129,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2506 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2507 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 52 137 400 33 66 448 320), lower := (rows 97 14 52 137 400 33 66 128 256), losses := [] }

theorem u2507 : Upper (D 9) (R 9) [96,12,48,129,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2507 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2508 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 101, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(4,0),(4,5)], upper := (rows 97 14 52 137 400 33 320 194 322), lower := (rows 97 14 52 137 400 33 320 128 256), losses := [] }

theorem u2508 : Upper (D 9) (R 9) [96,12,48,129,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2508 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2509 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 52 137 400 34 65 448 320), lower := (rows 97 14 52 137 400 34 65 128 256), losses := [] }

theorem u2509 : Upper (D 9) (R 9) [96,12,48,129,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2509 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2510 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 136, targets := 256 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(3,5),(3,8),(4,5)], upper := (rows 97 14 52 137 400 34 320 193 321), lower := (rows 97 14 52 137 400 34 320 128 256), losses := [] }

theorem u2510 : Upper (D 9) (R 9) [96,12,48,129,384,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2510 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2511 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 293, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 2, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,6),(2,7),(4,5)], upper := (rows 97 14 52 138 208 288 65 385 257), lower := (rows 97 14 52 138 208 288 65 128 256), losses := [{ target := 6, region := (rows 1 22 20 24 16 369 0 193 321), good := (rows 417 14 62 138 446 288 417 128 288) }] }

theorem u2511 : Upper (D 9) (R 9) [96,12,48,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2511 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2512 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 14 52 138 208 288 320 129 257), lower := (rows 97 14 52 138 208 288 320 128 256), losses := [] }

theorem u2512 : Upper (D 9) (R 9) [96,12,48,130,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2512 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2513 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 341, targets := 128 },{ cop := 0, region := 272, targets := 32 },{ cop := 2, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(4,5),(4,7)], upper := (rows 97 14 52 138 336 160 65 385 257), lower := (rows 97 14 52 138 336 160 65 128 256), losses := [] }

theorem u2513 : Upper (D 9) (R 9) [96,12,48,130,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2513 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2514 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 52 138 336 160 320 129 257), lower := (rows 97 14 52 138 336 160 320 128 256), losses := [] }

theorem u2514 : Upper (D 9) (R 9) [96,12,48,130,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2514 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2515 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 65, targets := 384 },{ cop := 4, region := 72, targets := 288 }], pairs := [(0,7),(0,8),(1,5),(3,5),(3,8)], upper := (rows 97 14 52 200 145 288 65 386 258), lower := (rows 97 14 52 200 145 288 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 28 16 0 81 134 262), good := (rows 65 398 478 200 217 256 65 128 256) }] }

theorem u2515 : Upper (D 9) (R 9) [96,12,48,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2515 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2516 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 52 200 145 288 66 385 257), lower := (rows 97 14 52 200 145 288 66 128 256), losses := [] }

theorem u2516 : Upper (D 9) (R 9) [96,12,48,192,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2516 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2517 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 14 52 200 145 288 320 131 259), lower := (rows 97 14 52 200 145 288 320 128 256), losses := [] }

theorem u2517 : Upper (D 9) (R 9) [96,12,48,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2517 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2518 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 392, targets := 32 },{ cop := 2, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,6),(2,7),(3,5)], upper := (rows 97 14 52 200 146 288 65 385 257), lower := (rows 97 14 52 200 146 288 65 128 256), losses := [{ target := 6, region := (rows 1 10 14 8 24 361 0 193 321), good := (rows 417 62 52 446 150 288 417 128 288) }] }

theorem u2518 : Upper (D 9) (R 9) [96,12,48,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2518 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2519 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 14 52 200 146 288 320 129 257), lower := (rows 97 14 52 200 146 288 320 128 256), losses := [] }

theorem u2519 : Upper (D 9) (R 9) [96,12,48,192,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2519 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P09
