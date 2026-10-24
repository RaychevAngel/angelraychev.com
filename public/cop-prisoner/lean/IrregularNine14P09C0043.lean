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

def b2580 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 297, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,0),(4,5)], upper := (rows 97 14 133 296 82 33 192 400 272), lower := (rows 97 14 133 296 82 33 192 128 256), losses := [] }

theorem u2580 : Upper (D 9) (R 9) [96,12,129,288,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2580 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2581 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 165, targets := 256 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(2,8),(4,0),(4,5)], upper := (rows 97 14 133 296 82 33 320 144 400), lower := (rows 97 14 133 296 82 33 320 128 256), losses := [] }

theorem u2581 : Upper (D 9) (R 9) [96,12,129,288,66,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2581 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2582 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 65, targets := 384 },{ cop := 4, region := 424, targets := 65 },{ cop := 5, region := 69, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(3,0),(3,6)], upper := (rows 97 14 133 296 82 160 65 400 272), lower := (rows 97 14 133 296 82 160 65 128 256), losses := [] }

theorem u2582 : Upper (D 9) (R 9) [96,12,129,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2582 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2583 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 80, targets := 417 }], pairs := [(4,0),(4,5),(4,7),(4,8)], upper := (rows 97 14 133 296 82 160 80 385 257), lower := (rows 97 14 133 296 82 160 80 128 256), losses := [] }

theorem u2583 : Upper (D 9) (R 9) [96,12,129,288,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2583 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2584 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 165, targets := 256 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(2,8),(4,0),(4,5)], upper := (rows 97 14 133 296 82 160 320 145 273), lower := (rows 97 14 133 296 82 160 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 328 128 256), good := (rows 96 126 164 360 82 160 320 160 320) },{ target := 5, region := (rows 1 2 4 8 18 0 328 128 256), good := (rows 65 94 133 328 82 128 320 128 320) }] }

theorem u2584 : Upper (D 9) (R 9) [96,12,129,288,66,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2584 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2585 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 0, region := 404, targets := 32 }], pairs := [(2,5),(3,0),(4,0),(4,5)], upper := (rows 97 14 133 296 208 34 65 400 272), lower := (rows 97 14 133 296 208 34 65 128 256), losses := [] }

theorem u2585 : Upper (D 9) (R 9) [96,12,129,288,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2585 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2586 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 14 133 296 208 34 80 385 257), lower := (rows 97 14 133 296 208 34 80 128 256), losses := [] }

theorem u2586 : Upper (D 9) (R 9) [96,12,129,288,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2586 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2587 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 148, targets := 32 },{ cop := 0, region := 148, targets := 256 }], pairs := [(2,5),(2,8),(4,5),(4,8)], upper := (rows 97 14 133 296 208 34 320 145 273), lower := (rows 97 14 133 296 208 34 320 128 256), losses := [] }

theorem u2587 : Upper (D 9) (R 9) [96,12,129,288,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2587 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2588 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7),(2,5),(4,5)], upper := (rows 97 14 133 296 273 34 80 192 448), lower := (rows 97 14 133 296 273 34 80 128 256), losses := [] }

theorem u2588 : Upper (D 9) (R 9) [96,12,129,288,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2588 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2589 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(2,5),(3,7),(4,5),(4,7)], upper := (rows 97 14 133 296 273 34 192 208 336), lower := (rows 97 14 133 296 273 34 192 128 256), losses := [] }

theorem u2589 : Upper (D 9) (R 9) [96,12,129,288,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2589 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2590 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(2,5),(3,7),(4,5),(4,7)], upper := (rows 97 14 133 296 273 160 66 208 336), lower := (rows 97 14 133 296 273 160 66 128 256), losses := [] }

theorem u2590 : Upper (D 9) (R 9) [96,12,129,288,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2590 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2591 : Route 9 := (fun mask => (mask,id))

def c2591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2591 : Upper (D 9) (R 9) [96,12,129,288,257,128,16] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,257,128,16] 13 (by decide) (choices 1) [2,64] r2591 c2591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u159
  · exact u160

def b2592 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 65, targets := 384 },{ cop := 4, region := 229, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,5),(4,7)], upper := (rows 97 14 133 296 274 160 65 208 336), lower := (rows 97 14 133 296 274 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 18 0 69 130 258), good := (rows 65 478 197 264 402 128 65 128 256) },{ target := 7, region := (rows 41 2 4 8 18 32 111 0 274), good := (rows 97 351 69 361 338 97 65 0 256) }] }

theorem u2592 : Upper (D 9) (R 9) [96,12,129,288,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2592 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2593 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 229, targets := 256 },{ cop := 0, region := 132, targets := 32 },{ cop := 0, region := 264, targets := 128 }], pairs := [(0,8),(2,5),(2,8),(3,7)], upper := (rows 97 14 133 296 274 160 80 193 321), lower := (rows 97 14 133 296 274 160 80 128 256), losses := [] }

theorem u2593 : Upper (D 9) (R 9) [96,12,129,288,258,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2593 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2594 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 0, region := 404, targets := 32 }], pairs := [(2,5),(3,0),(4,0),(4,5)], upper := (rows 97 14 133 296 336 34 65 144 400), lower := (rows 97 14 133 296 336 34 65 128 256), losses := [] }

theorem u2594 : Upper (D 9) (R 9) [96,12,129,288,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2594 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2595 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 14 133 296 336 34 80 129 385), lower := (rows 97 14 133 296 336 34 80 128 256), losses := [] }

theorem u2595 : Upper (D 9) (R 9) [96,12,129,288,320,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2595 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2596 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(2,5),(3,7),(4,5),(4,7)], upper := (rows 97 14 133 296 336 34 192 145 273), lower := (rows 97 14 133 296 336 34 192 128 256), losses := [] }

theorem u2596 : Upper (D 9) (R 9) [96,12,129,288,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2596 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2597 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 81, targets := 128 },{ cop := 5, region := 69, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,5),(4,7)], upper := (rows 97 14 133 296 336 160 65 146 274), lower := (rows 97 14 133 296 336 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 18 0 69 130 258), good := (rows 65 478 197 264 336 128 65 128 256) }] }

theorem u2597 : Upper (D 9) (R 9) [96,12,129,288,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2597 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2598 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(2,5),(3,7),(4,5),(4,7)], upper := (rows 97 14 133 296 336 160 66 145 273), lower := (rows 97 14 133 296 336 160 66 128 256), losses := [] }

theorem u2598 : Upper (D 9) (R 9) [96,12,129,288,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2598 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2599 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 8, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 14 133 296 336 160 80 131 259), lower := (rows 97 14 133 296 336 160 80 128 256), losses := [] }

theorem u2599 : Upper (D 9) (R 9) [96,12,129,288,320,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2599 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2600 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 0, region := 404, targets := 32 }], pairs := [(2,5),(3,0),(4,0),(4,5)], upper := (rows 97 14 133 296 400 33 66 208 336), lower := (rows 97 14 133 296 400 33 66 128 256), losses := [] }

theorem u2600 : Upper (D 9) (R 9) [96,12,129,288,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2600 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2601 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 14 133 296 400 33 80 194 322), lower := (rows 97 14 133 296 400 33 80 128 256), losses := [] }

theorem u2601 : Upper (D 9) (R 9) [96,12,129,288,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2601 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2602 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 0, region := 404, targets := 32 }], pairs := [(2,5),(3,0),(4,0),(4,5)], upper := (rows 97 14 133 296 400 34 65 208 336), lower := (rows 97 14 133 296 400 34 65 128 256), losses := [] }

theorem u2602 : Upper (D 9) (R 9) [96,12,129,288,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2602 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2603 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 264, targets := 128 }], pairs := [(2,5),(3,7),(4,5)], upper := (rows 97 14 133 296 400 34 80 193 321), lower := (rows 97 14 133 296 400 34 80 128 256), losses := [] }

theorem u2603 : Upper (D 9) (R 9) [96,12,129,288,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2603 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2604 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 392, targets := 1 }], pairs := [(0,7),(3,0),(4,7)], upper := (rows 97 14 133 392 273 34 80 224 352), lower := (rows 97 14 133 392 273 34 80 128 256), losses := [] }

theorem u2604 : Upper (D 9) (R 9) [96,12,129,384,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2604 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2605 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 14 133 392 273 34 96 208 336), lower := (rows 97 14 133 392 273 34 96 128 256), losses := [] }

theorem u2605 : Upper (D 9) (R 9) [96,12,129,384,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2605 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2606 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 14 133 392 273 48 96 194 322), lower := (rows 97 14 133 392 273 48 96 128 256), losses := [] }

theorem u2606 : Upper (D 9) (R 9) [96,12,129,384,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2606 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2607 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 229, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,7)], upper := (rows 97 14 133 392 274 33 80 224 352), lower := (rows 97 14 133 392 274 33 80 128 256), losses := [] }

theorem u2607 : Upper (D 9) (R 9) [96,12,129,384,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2607 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2608 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 },{ cop := 3, region := 97, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 14 133 392 274 33 96 208 336), lower := (rows 97 14 133 392 274 33 96 128 256), losses := [] }

theorem u2608 : Upper (D 9) (R 9) [96,12,129,384,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2608 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2609 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 14 133 392 304 33 66 208 336), lower := (rows 97 14 133 392 304 33 66 128 256), losses := [] }

theorem u2609 : Upper (D 9) (R 9) [96,12,129,384,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2609 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2610 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 97 14 133 392 304 33 80 194 322), lower := (rows 97 14 133 392 304 33 80 128 256), losses := [] }

theorem u2610 : Upper (D 9) (R 9) [96,12,129,384,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2610 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2611 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 177, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(3,7),(4,8)], upper := (rows 97 14 134 280 145 33 320 224 352), lower := (rows 97 14 134 280 145 33 320 128 256), losses := [{ target := 0, region := (rows 0 26 20 24 16 32 377 161 289), good := (rows 480 78 134 350 478 480 320 128 320) }] }

theorem u2611 : Upper (D 9) (R 9) [96,12,130,272,129,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2611 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2612 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 134 280 145 96 320 161 289), lower := (rows 97 14 134 280 145 96 320 128 256), losses := [] }

theorem u2612 : Upper (D 9) (R 9) [96,12,130,272,129,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2612 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2613 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 2, region := 113, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0)], upper := (rows 97 14 134 296 145 48 65 448 320), lower := (rows 97 14 134 296 145 48 65 128 256), losses := [] }

theorem u2613 : Upper (D 9) (R 9) [96,12,130,288,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2613 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2614 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 177, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,8)], upper := (rows 97 14 134 296 145 48 320 193 321), lower := (rows 97 14 134 296 145 48 320 128 256), losses := [] }

theorem u2614 : Upper (D 9) (R 9) [96,12,130,288,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2614 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2615 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 148 168 82 288 65 385 257), lower := (rows 97 14 148 168 82 288 65 128 256), losses := [] }

theorem u2615 : Upper (D 9) (R 9) [96,12,144,160,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2615 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2616 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 14 148 168 82 288 320 129 257), lower := (rows 97 14 148 168 82 288 320 128 256), losses := [] }

theorem u2616 : Upper (D 9) (R 9) [96,12,144,160,66,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2616 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2617 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 329, targets := 128 },{ cop := 0, region := 264, targets := 64 },{ cop := 2, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(2,5),(3,6),(3,7)], upper := (rows 97 14 148 296 82 160 65 385 257), lower := (rows 97 14 148 296 82 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 65 193 321), good := (rows 449 14 148 264 470 128 449 128 256) }] }

theorem u2617 : Upper (D 9) (R 9) [96,12,144,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2617 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2618 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 165, targets := 256 },{ cop := 5, region := 329, targets := 128 },{ cop := 0, region := 264, targets := 64 }], pairs := [(0,7),(0,8),(2,8),(3,6),(3,7)], upper := (rows 97 14 148 296 82 160 320 129 257), lower := (rows 97 14 148 296 82 160 320 128 256), losses := [] }

theorem u2618 : Upper (D 9) (R 9) [96,12,144,288,66,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2618 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2619 : Route 9 := (fun mask => (mask,id))

def c2619 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2619 : Upper (D 9) (R 9) [96,12,144,288,257,128,1] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,257,128,1] 13 (by decide) (choices 1) [2,64] r2619 c2619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u161
  · exact u162

def b2620 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(2,5),(3,7),(4,5),(4,7)], upper := (rows 97 14 148 296 273 160 66 193 321), lower := (rows 97 14 148 296 273 160 66 128 256), losses := [] }

theorem u2620 : Upper (D 9) (R 9) [96,12,144,288,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2620 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2621 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 8, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 14 148 296 336 33 65 130 386), lower := (rows 97 14 148 296 336 33 65 128 256), losses := [] }

theorem u2621 : Upper (D 9) (R 9) [96,12,144,288,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2621 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2622 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,7),(2,5),(3,7),(4,5)], upper := (rows 97 14 148 296 336 33 66 129 385), lower := (rows 97 14 148 296 336 33 66 128 256), losses := [] }

theorem u2622 : Upper (D 9) (R 9) [96,12,144,288,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2622 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2623 : Route 9 := (fun mask => (mask,id))

def c2623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2623 : Upper (D 9) (R 9) [96,12,144,288,320,1,128] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,320,1,128] 13 (by decide) (choices 1) [1,2] r2623 c2623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u163
  · exact u164

def r2624 : Route 9 := (fun mask => (mask,id))

def c2624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2624 : Upper (D 9) (R 9) [96,12,144,288,320,128,1] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,320,128,1] 13 (by decide) (choices 1) [1,2] r2624 c2624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u165
  · exact u166

def b2625 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(2,5),(3,7),(4,5),(4,7)], upper := (rows 97 14 148 296 336 160 66 129 257), lower := (rows 97 14 148 296 336 160 66 128 256), losses := [] }

theorem u2625 : Upper (D 9) (R 9) [96,12,144,288,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2625 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2626 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 392, targets := 1 },{ cop := 1, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(3,0),(4,7)], upper := (rows 97 14 148 392 273 33 66 224 352), lower := (rows 97 14 148 392 273 33 66 128 256), losses := [] }

theorem u2626 : Upper (D 9) (R 9) [96,12,144,384,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2626 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2627 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 14 148 392 273 33 96 194 322), lower := (rows 97 14 148 392 273 33 96 128 256), losses := [] }

theorem u2627 : Upper (D 9) (R 9) [96,12,144,384,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2627 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 14 148 392 304 33 65 194 322), lower := (rows 97 14 148 392 304 33 65 128 256), losses := [] }

theorem u2628 : Upper (D 9) (R 9) [96,12,144,384,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2628 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2629 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 392, targets := 32 },{ cop := 1, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(3,5),(4,7)], upper := (rows 97 14 148 392 304 33 66 193 321), lower := (rows 97 14 148 392 304 33 66 128 256), losses := [] }

theorem u2629 : Upper (D 9) (R 9) [96,12,144,384,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2629 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2630 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0)], upper := (rows 97 14 164 200 273 33 80 386 258), lower := (rows 97 14 164 200 273 33 80 128 256), losses := [] }

theorem u2630 : Upper (D 9) (R 9) [96,12,160,192,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2630 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2631 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 97 14 164 200 273 33 320 146 274), lower := (rows 97 14 164 200 273 33 320 128 256), losses := [] }

theorem u2631 : Upper (D 9) (R 9) [96,12,160,192,257,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2631 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2632 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 14 164 200 273 34 80 385 257), lower := (rows 97 14 164 200 273 34 80 128 256), losses := [] }

theorem u2632 : Upper (D 9) (R 9) [96,12,160,192,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2632 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2633 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 164 200 273 34 320 145 273), lower := (rows 97 14 164 200 273 34 320 128 256), losses := [] }

theorem u2633 : Upper (D 9) (R 9) [96,12,160,192,257,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2633 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2634 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 14 164 200 273 48 320 131 259), lower := (rows 97 14 164 200 273 48 320 128 256), losses := [] }

theorem u2634 : Upper (D 9) (R 9) [96,12,160,192,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2634 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2635 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 97 14 164 200 274 33 320 145 273), lower := (rows 97 14 164 200 274 33 320 128 256), losses := [] }

theorem u2635 : Upper (D 9) (R 9) [96,12,160,192,258,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2635 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2636 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 14 164 200 274 48 320 129 257), lower := (rows 97 14 164 200 274 48 320 128 256), losses := [] }

theorem u2636 : Upper (D 9) (R 9) [96,12,160,192,258,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2636 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2637 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 164 328 145 33 66 400 272), lower := (rows 97 14 164 328 145 33 66 128 256), losses := [] }

theorem u2637 : Upper (D 9) (R 9) [96,12,160,320,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2637 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2638 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 7, region := 113, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0)], upper := (rows 97 14 164 328 145 33 80 386 258), lower := (rows 97 14 164 328 145 33 80 128 256), losses := [] }

theorem u2638 : Upper (D 9) (R 9) [96,12,160,320,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2638 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2639 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 183, targets := 256 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 14 164 328 145 33 320 146 274), lower := (rows 97 14 164 328 145 33 320 128 256), losses := [] }

theorem u2639 : Upper (D 9) (R 9) [96,12,160,320,129,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2639 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2639
end Delivery.IrregularNine14.P09
