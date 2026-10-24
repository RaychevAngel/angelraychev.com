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

def b2520 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 65, targets := 384 },{ cop := 5, region := 73, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(3,5),(3,8)], upper := (rows 97 14 52 200 273 160 65 386 258), lower := (rows 97 14 52 200 273 160 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 12 16 0 81 134 262), good := (rows 65 398 478 200 337 128 65 128 256) }] }

theorem u2520 : Upper (D 9) (R 9) [96,12,48,192,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2520 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2521 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 276, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 52 200 273 160 66 385 257), lower := (rows 97 14 52 200 273 160 66 128 256), losses := [] }

theorem u2521 : Upper (D 9) (R 9) [96,12,48,192,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2521 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2522 : Route 9 := (fun mask => (mask,id))

def c2522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2522 : Upper (D 9) (R 9) [96,12,48,192,257,128,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,257,128,256] 13 (by decide) (choices 1) [1,2] r2522 c2522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u149
  · exact u150

def b2523 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 73, targets := 256 },{ cop := 0, region := 392, targets := 32 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,6),(3,5),(3,8)], upper := (rows 97 14 52 200 274 160 65 385 257), lower := (rows 97 14 52 200 274 160 65 128 256), losses := [{ target := 6, region := (rows 1 10 14 8 24 233 0 193 321), good := (rows 417 62 52 446 278 160 417 160 256) }] }

theorem u2523 : Upper (D 9) (R 9) [96,12,48,192,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2523 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2524 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 169, targets := 256 },{ cop := 0, region := 136, targets := 32 },{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(3,8),(4,7)], upper := (rows 97 14 52 200 274 160 320 129 257), lower := (rows 97 14 52 200 274 160 320 128 256), losses := [{ target := 7, region := (rows 37 2 4 8 18 32 375 0 295), good := (rows 353 351 373 72 338 353 320 0 320) }] }

theorem u2524 : Upper (D 9) (R 9) [96,12,48,192,258,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2524 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2525 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 14 52 200 400 33 65 386 258), lower := (rows 97 14 52 200 400 33 65 128 256), losses := [] }

theorem u2525 : Upper (D 9) (R 9) [96,12,48,192,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2525 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2526 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 52 200 400 33 66 385 257), lower := (rows 97 14 52 200 400 33 66 128 256), losses := [] }

theorem u2526 : Upper (D 9) (R 9) [96,12,48,192,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2526 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2527 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 33, targets := 384 },{ cop := 4, region := 72, targets := 33 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(0,8),(2,7),(3,0),(3,5)], upper := (rows 97 14 52 200 400 33 320 131 259), lower := (rows 97 14 52 200 400 33 320 128 256), losses := [] }

theorem u2527 : Upper (D 9) (R 9) [96,12,48,192,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2527 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2528 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,8)], upper := (rows 97 14 52 392 82 160 65 385 257), lower := (rows 97 14 52 392 82 160 65 128 256), losses := [] }

theorem u2528 : Upper (D 9) (R 9) [96,12,48,384,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2528 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2529 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 118, targets := 1 },{ cop := 4, region := 165, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(2,8),(4,0)], upper := (rows 97 14 52 392 82 160 320 129 257), lower := (rows 97 14 52 392 82 160 320 128 256), losses := [] }

theorem u2529 : Upper (D 9) (R 9) [96,12,48,384,66,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2529 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2530 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 65, targets := 384 }], pairs := [(0,7),(0,8),(1,5),(3,5),(4,8)], upper := (rows 97 14 52 392 145 288 65 194 322), lower := (rows 97 14 52 392 145 288 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 14 16 0 81 132 260), good := (rows 65 398 478 392 209 256 65 128 256) },{ target := 8, region := (rows 37 2 4 8 18 32 119 130 0), good := (rows 97 223 117 136 209 97 65 128 0) }] }

theorem u2530 : Upper (D 9) (R 9) [96,12,48,384,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2530 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2531 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 148, targets := 256 }], pairs := [(2,8),(3,5),(4,5),(4,8)], upper := (rows 97 14 52 392 145 288 66 193 321), lower := (rows 97 14 52 392 145 288 66 128 256), losses := [] }

theorem u2531 : Upper (D 9) (R 9) [96,12,48,384,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2531 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2532 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 394, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(3,0),(3,5)], upper := (rows 97 14 52 392 208 33 65 386 258), lower := (rows 97 14 52 392 208 33 65 128 256), losses := [] }

theorem u2532 : Upper (D 9) (R 9) [96,12,48,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2532 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2533 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 52 392 208 33 66 385 257), lower := (rows 97 14 52 392 208 33 66 128 256), losses := [] }

theorem u2533 : Upper (D 9) (R 9) [96,12,48,384,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2533 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2534 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 37, targets := 384 },{ cop := 3, region := 80, targets := 1 }], pairs := [(0,7),(0,8),(2,7),(2,8),(4,0)], upper := (rows 97 14 52 392 208 33 320 131 259), lower := (rows 97 14 52 392 208 33 320 128 256), losses := [] }

theorem u2534 : Upper (D 9) (R 9) [96,12,48,384,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2534 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2535 : Route 9 := (fun mask => (mask,id))

def c2535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2535 : Upper (D 9) (R 9) [96,12,48,384,192,256,1] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,192,256,1] 13 (by decide) (choices 1) [1,2] r2535 c2535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u151
  · exact u152

def b2536 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 118, targets := 1 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,0)], upper := (rows 97 14 52 392 208 288 66 129 257), lower := (rows 97 14 52 392 208 288 66 128 256), losses := [] }

theorem u2536 : Upper (D 9) (R 9) [96,12,48,384,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2536 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2537 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 388, targets := 32 },{ cop := 4, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(2,5),(4,7)], upper := (rows 97 14 133 152 50 288 65 448 320), lower := (rows 97 14 133 152 50 288 65 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 22 357 64 193 321), good := (rows 480 62 446 152 50 288 480 128 288) }] }

theorem u2537 : Upper (D 9) (R 9) [96,12,129,144,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2537 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 14 133 152 50 288 320 193 321), lower := (rows 97 14 133 152 50 288 320 128 256), losses := [] }

theorem u2538 : Upper (D 9) (R 9) [96,12,129,144,34,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2538 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2539 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 14 133 152 273 34 96 448 320), lower := (rows 97 14 133 152 273 34 96 128 256), losses := [] }

theorem u2539 : Upper (D 9) (R 9) [96,12,129,144,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2539 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2540 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 132, targets := 256 }], pairs := [(0,7),(2,8),(3,0),(4,7)], upper := (rows 97 14 133 152 273 34 320 224 352), lower := (rows 97 14 133 152 273 34 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 34 375 163 291), good := (rows 480 494 452 216 472 482 320 128 320) }] }

theorem u2540 : Upper (D 9) (R 9) [96,12,129,144,257,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2540 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2541 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 152 273 96 320 162 290), lower := (rows 97 14 133 152 273 96 320 128 256), losses := [] }

theorem u2541 : Upper (D 9) (R 9) [96,12,129,144,257,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2541 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2542 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 6, region := 165, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(2,8),(4,7)], upper := (rows 97 14 133 152 274 33 320 224 352), lower := (rows 97 14 133 152 274 33 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 373 161 289), good := (rows 480 94 478 216 338 480 320 128 320) }] }

theorem u2542 : Upper (D 9) (R 9) [96,12,129,144,258,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2542 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2543 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 152 274 96 320 161 289), lower := (rows 97 14 133 152 274 96 320 128 256), losses := [] }

theorem u2543 : Upper (D 9) (R 9) [96,12,129,144,258,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2543 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2544 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 14 133 152 304 33 66 448 320), lower := (rows 97 14 133 152 304 33 66 128 256), losses := [] }

theorem u2544 : Upper (D 9) (R 9) [96,12,129,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2544 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2545 : Route 9 := (fun mask => (mask,id))

def c2545 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2545 : Upper (D 9) (R 9) [96,12,129,144,288,1,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,288,1,256] 13 (by decide) (choices 1) [2,64] r2545 c2545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u153
  · exact u154

def b2546 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 14 133 152 304 34 65 448 320), lower := (rows 97 14 133 152 304 34 65 128 256), losses := [] }

theorem u2546 : Upper (D 9) (R 9) [96,12,129,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2546 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2547 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 132, targets := 32 },{ cop := 0, region := 132, targets := 256 }], pairs := [(0,7),(2,5),(2,8),(4,7)], upper := (rows 97 14 133 152 304 34 320 193 321), lower := (rows 97 14 133 152 304 34 320 128 256), losses := [] }

theorem u2547 : Upper (D 9) (R 9) [96,12,129,144,288,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2547 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2548 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 133 168 82 288 65 400 272), lower := (rows 97 14 133 168 82 288 65 128 256), losses := [] }

theorem u2548 : Upper (D 9) (R 9) [96,12,129,160,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2548 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2549 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 133 168 82 288 80 385 257), lower := (rows 97 14 133 168 82 288 80 128 256), losses := [] }

theorem u2549 : Upper (D 9) (R 9) [96,12,129,160,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2549 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2550 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 14 133 168 82 288 320 145 273), lower := (rows 97 14 133 168 82 288 320 128 256), losses := [] }

theorem u2550 : Upper (D 9) (R 9) [96,12,129,160,66,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2550 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2551 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 71, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 14 133 168 273 48 66 448 320), lower := (rows 97 14 133 168 273 48 66 128 256), losses := [] }

theorem u2551 : Upper (D 9) (R 9) [96,12,129,160,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2551 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2552 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 14 133 168 273 48 320 194 322), lower := (rows 97 14 133 168 273 48 320 128 256), losses := [] }

theorem u2552 : Upper (D 9) (R 9) [96,12,129,160,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2552 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2553 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 0, region := 404, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8)], upper := (rows 97 14 133 168 273 288 66 208 336), lower := (rows 97 14 133 168 273 288 66 128 256), losses := [] }

theorem u2553 : Upper (D 9) (R 9) [96,12,129,160,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2553 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2554 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 14 133 168 273 288 80 194 322), lower := (rows 97 14 133 168 273 288 80 128 256), losses := [] }

theorem u2554 : Upper (D 9) (R 9) [96,12,129,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2554 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2555 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 97 14 133 168 274 288 65 208 336), lower := (rows 97 14 133 168 274 288 65 128 256), losses := [] }

theorem u2555 : Upper (D 9) (R 9) [96,12,129,160,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2555 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2556 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 14 133 168 274 288 80 193 321), lower := (rows 97 14 133 168 274 288 80 128 256), losses := [] }

theorem u2556 : Upper (D 9) (R 9) [96,12,129,160,258,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2556 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2557 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 97 14 133 168 336 288 65 146 274), lower := (rows 97 14 133 168 336 288 65 128 256), losses := [] }

theorem u2557 : Upper (D 9) (R 9) [96,12,129,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2557 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2558 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 0, region := 404, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8)], upper := (rows 97 14 133 168 336 288 66 145 273), lower := (rows 97 14 133 168 336 288 66 128 256), losses := [] }

theorem u2558 : Upper (D 9) (R 9) [96,12,129,160,320,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2558 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2559 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 14 133 168 336 288 80 131 259), lower := (rows 97 14 133 168 336 288 80 128 256), losses := [] }

theorem u2559 : Upper (D 9) (R 9) [96,12,129,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2559 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2560 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 0, region := 132, targets := 256 },{ cop := 1, region := 496, targets := 1 }], pairs := [(0,7),(2,8),(3,7),(4,0)], upper := (rows 97 14 133 265 146 48 320 224 352), lower := (rows 97 14 133 265 146 48 320 128 256), losses := [] }

theorem u2560 : Upper (D 9) (R 9) [96,12,129,257,130,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2560 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2561 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 265 146 96 320 176 304), lower := (rows 97 14 133 265 146 96 320 128 256), losses := [] }

theorem u2561 : Upper (D 9) (R 9) [96,12,129,257,130,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2561 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2562 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 14 133 265 176 34 80 448 320), lower := (rows 97 14 133 265 176 34 80 128 256), losses := [] }

theorem u2562 : Upper (D 9) (R 9) [96,12,129,257,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2562 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2563 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 148, targets := 256 },{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7),(2,8),(3,7),(4,8)], upper := (rows 97 14 133 265 176 34 320 208 336), lower := (rows 97 14 133 265 176 34 320 128 256), losses := [] }

theorem u2563 : Upper (D 9) (R 9) [96,12,129,257,160,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2563 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2564 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 148, targets := 256 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,7),(2,8),(4,0),(4,8)], upper := (rows 97 14 133 265 176 288 66 208 336), lower := (rows 97 14 133 265 176 288 66 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 296 66 0 256), good := (rows 97 111 5 297 48 288 67 0 288) }] }

theorem u2564 : Upper (D 9) (R 9) [96,12,129,257,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2564 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2565 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 4, region := 65, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(3,5)], upper := (rows 97 14 133 265 176 288 80 194 322), lower := (rows 97 14 133 265 176 288 80 128 256), losses := [] }

theorem u2565 : Upper (D 9) (R 9) [96,12,129,257,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2565 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2566 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 264, targets := 128 },{ cop := 0, region := 132, targets := 256 }], pairs := [(2,8),(3,7),(4,0)], upper := (rows 97 14 133 265 400 34 80 224 352), lower := (rows 97 14 133 265 400 34 80 128 256), losses := [] }

theorem u2566 : Upper (D 9) (R 9) [96,12,129,257,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2566 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2567 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 14 133 265 400 34 96 208 336), lower := (rows 97 14 133 265 400 34 96 128 256), losses := [] }

theorem u2567 : Upper (D 9) (R 9) [96,12,129,257,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2567 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2568 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 14 133 265 400 48 96 194 322), lower := (rows 97 14 133 265 400 48 96 128 256), losses := [] }

theorem u2568 : Upper (D 9) (R 9) [96,12,129,257,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2568 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2569 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 213, targets := 256 },{ cop := 0, region := 144, targets := 1 },{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7),(0,8),(2,8),(4,0),(4,8)], upper := (rows 97 14 133 266 176 288 65 208 336), lower := (rows 97 14 133 266 176 288 65 128 256), losses := [] }

theorem u2569 : Upper (D 9) (R 9) [96,12,129,258,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2569 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2570 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 5, region := 209, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(3,5)], upper := (rows 97 14 133 266 176 288 80 193 321), lower := (rows 97 14 133 266 176 288 80 128 256), losses := [] }

theorem u2570 : Upper (D 9) (R 9) [96,12,129,258,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2570 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 165, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(2,8),(3,7)], upper := (rows 97 14 133 280 146 33 320 224 352), lower := (rows 97 14 133 280 146 33 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 365 161 289), good := (rows 480 94 478 344 146 480 320 128 320) }] }

theorem u2571 : Upper (D 9) (R 9) [96,12,129,272,130,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2571 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2572 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 280 146 96 320 161 289), lower := (rows 97 14 133 280 146 96 320 128 256), losses := [] }

theorem u2572 : Upper (D 9) (R 9) [96,12,129,272,130,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2572 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2573 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 2, region := 48, targets := 320 }], pairs := [(3,0),(4,0),(4,6),(4,8)], upper := (rows 97 14 133 280 176 33 66 448 320), lower := (rows 97 14 133 280 176 33 66 128 256), losses := [] }

theorem u2573 : Upper (D 9) (R 9) [96,12,129,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2573 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2574 : Route 9 := (fun mask => (mask,id))

def c2574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2574 : Upper (D 9) (R 9) [96,12,129,272,160,1,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,160,1,256] 13 (by decide) (choices 1) [2,64] r2574 c2574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u155
  · exact u156

def b2575 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7),(3,0),(3,7),(4,0)], upper := (rows 97 14 133 280 176 34 65 448 320), lower := (rows 97 14 133 280 176 34 65 128 256), losses := [] }

theorem u2575 : Upper (D 9) (R 9) [96,12,129,272,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2575 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2576 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 148, targets := 256 },{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7),(2,8),(3,7),(4,8)], upper := (rows 97 14 133 280 176 34 320 193 321), lower := (rows 97 14 133 280 176 34 320 128 256), losses := [] }

theorem u2576 : Upper (D 9) (R 9) [96,12,129,272,160,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2576 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2577 : Route 9 := (fun mask => (mask,id))

def c2577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2577 : Upper (D 9) (R 9) [96,12,129,272,160,256,1] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,160,256,1] 13 (by decide) (choices 1) [2,64] r2577 c2577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u157
  · exact u158

def b2578 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 148, targets := 256 },{ cop := 0, region := 132, targets := 32 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(2,5),(2,8),(4,8)], upper := (rows 97 14 133 280 176 288 66 193 321), lower := (rows 97 14 133 280 176 288 66 128 256), losses := [] }

theorem u2578 : Upper (D 9) (R 9) [96,12,129,272,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2578 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2579 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 113, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 97 14 133 296 82 33 80 384 384), lower := (rows 97 14 133 296 82 33 80 128 256), losses := [] }

theorem u2579 : Upper (D 9) (R 9) [96,12,129,288,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2579 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2579
end Delivery.IrregularNine14.P09
