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

def b2640 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 81, targets := 256 },{ cop := 5, region := 73, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(3,7),(4,8)], upper := (rows 97 14 164 328 145 288 65 146 274), lower := (rows 97 14 164 328 145 288 65 128 256), losses := [{ target := 7, region := (rows 303 6 4 296 16 296 383 0 256), good := (rows 105 111 111 361 81 361 65 0 361) }] }

theorem u2640 : Upper (D 9) (R 9) [96,12,160,320,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2640 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2641 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 148, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 164 328 145 288 66 145 273), lower := (rows 97 14 164 328 145 288 66 128 256), losses := [] }

theorem u2641 : Upper (D 9) (R 9) [96,12,160,320,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2641 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2642 : Route 9 := (fun mask => (mask,id))

def c2642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2642 : Upper (D 9) (R 9) [96,12,160,320,129,256,16] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,129,256,16] 13 (by decide) (choices 1) [1,2] r2642 c2642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u167
  · exact u168

def b2643 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(4,0),(4,5)], upper := (rows 97 14 164 328 146 33 65 400 272), lower := (rows 97 14 164 328 146 33 65 128 256), losses := [] }

theorem u2643 : Upper (D 9) (R 9) [96,12,160,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2643 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2644 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 4, region := 101, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(3,7)], upper := (rows 97 14 164 328 146 33 80 385 257), lower := (rows 97 14 164 328 146 33 80 128 256), losses := [] }

theorem u2644 : Upper (D 9) (R 9) [96,12,160,320,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2644 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2645 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 183, targets := 256 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 164 328 146 33 320 145 273), lower := (rows 97 14 164 328 146 33 320 128 256), losses := [] }

theorem u2645 : Upper (D 9) (R 9) [96,12,160,320,130,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2645 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2646 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 65, targets := 384 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(3,7),(4,8)], upper := (rows 97 14 164 328 146 288 65 145 273), lower := (rows 97 14 164 328 146 288 65 128 256), losses := [{ target := 7, region := (rows 319 6 4 312 16 312 383 0 272), good := (rows 105 111 111 361 379 361 65 0 361) },{ target := 8, region := (rows 37 2 4 8 18 32 103 130 0), good := (rows 97 223 229 72 210 97 65 128 0) }] }

theorem u2646 : Upper (D 9) (R 9) [96,12,160,320,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2646 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2647 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 0, region := 264, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,7),(2,6),(3,5),(3,7)], upper := (rows 97 14 164 328 146 288 80 129 257), lower := (rows 97 14 164 328 146 288 80 128 256), losses := [] }

theorem u2647 : Upper (D 9) (R 9) [96,12,160,320,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2647 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2648 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(4,0),(4,5)], upper := (rows 97 14 164 328 400 33 65 146 274), lower := (rows 97 14 164 328 400 33 65 128 256), losses := [] }

theorem u2648 : Upper (D 9) (R 9) [96,12,160,320,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2648 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2649 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 164 328 400 33 66 145 273), lower := (rows 97 14 164 328 400 33 66 128 256), losses := [] }

theorem u2649 : Upper (D 9) (R 9) [96,12,160,320,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2649 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2650 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 14 164 328 400 33 80 131 259), lower := (rows 97 14 164 328 400 33 80 128 256), losses := [] }

theorem u2650 : Upper (D 9) (R 9) [96,12,160,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2650 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2651 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 3, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 14 164 392 82 33 65 400 272), lower := (rows 97 14 164 392 82 33 65 128 256), losses := [] }

theorem u2651 : Upper (D 9) (R 9) [96,12,160,384,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2651 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2652 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 164 392 82 33 80 385 257), lower := (rows 97 14 164 392 82 33 80 128 256), losses := [] }

theorem u2652 : Upper (D 9) (R 9) [96,12,160,384,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2652 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2653 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 165, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,0),(4,7)], upper := (rows 97 14 164 392 82 33 320 145 273), lower := (rows 97 14 164 392 82 33 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 32 328 128 256), good := (rows 96 94 164 456 82 32 320 128 320) }] }

theorem u2653 : Upper (D 9) (R 9) [96,12,160,384,66,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2653 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2654 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 14 164 392 273 33 66 208 336), lower := (rows 97 14 164 392 273 33 66 128 256), losses := [] }

theorem u2654 : Upper (D 9) (R 9) [96,12,160,384,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2654 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2655 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0)], upper := (rows 97 14 164 392 273 33 80 194 322), lower := (rows 97 14 164 392 273 33 80 128 256), losses := [] }

theorem u2655 : Upper (D 9) (R 9) [96,12,160,384,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2655 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2656 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0)], upper := (rows 97 14 164 392 273 48 65 194 322), lower := (rows 97 14 164 392 273 48 65 128 256), losses := [] }

theorem u2656 : Upper (D 9) (R 9) [96,12,160,384,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2656 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2657 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 97 14 164 392 273 48 66 193 321), lower := (rows 97 14 164 392 273 48 66 128 256), losses := [] }

theorem u2657 : Upper (D 9) (R 9) [96,12,160,384,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2657 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2658 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 3, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 14 164 392 274 33 65 208 336), lower := (rows 97 14 164 392 274 33 65 128 256), losses := [] }

theorem u2658 : Upper (D 9) (R 9) [96,12,160,384,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2658 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2659 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 229, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,7)], upper := (rows 97 14 164 392 274 33 80 193 321), lower := (rows 97 14 164 392 274 33 80 128 256), losses := [] }

theorem u2659 : Upper (D 9) (R 9) [96,12,160,384,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2659 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2660 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 3, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 14 164 392 336 33 65 146 274), lower := (rows 97 14 164 392 336 33 65 128 256), losses := [] }

theorem u2660 : Upper (D 9) (R 9) [96,12,160,384,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2660 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2661 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 14 164 392 336 33 66 145 273), lower := (rows 97 14 164 392 336 33 66 128 256), losses := [] }

theorem u2661 : Upper (D 9) (R 9) [96,12,160,384,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2661 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2662 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 14 164 392 336 33 80 131 259), lower := (rows 97 14 164 392 336 33 80 128 256), losses := [] }

theorem u2662 : Upper (D 9) (R 9) [96,12,160,384,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2662 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2663 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 434, targets := 65 },{ cop := 3, region := 68, targets := 32 }], pairs := [(1,0),(1,6),(2,5),(4,0),(4,6)], upper := (rows 97 38 76 137 146 288 65 400 272), lower := (rows 97 38 76 137 146 288 65 128 256), losses := [] }

theorem u2663 : Upper (D 9) (R 9) [96,36,72,129,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2663 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7),(2,5),(3,5)], upper := (rows 97 38 76 137 146 288 80 385 257), lower := (rows 97 38 76 137 146 288 80 128 256), losses := [] }

theorem u2664 : Upper (D 9) (R 9) [96,36,72,129,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2664 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 38 76 137 146 288 320 145 273), lower := (rows 97 38 76 137 146 288 320 128 256), losses := [] }

theorem u2665 : Upper (D 9) (R 9) [96,36,72,129,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2665 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 76 137 273 48 66 384 384), lower := (rows 97 38 76 137 273 48 66 128 256), losses := [] }

theorem u2666 : Upper (D 9) (R 9) [96,36,72,129,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2666 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2667 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 38 76 137 273 48 192 386 258), lower := (rows 97 38 76 137 273 48 192 128 256), losses := [] }

theorem u2667 : Upper (D 9) (R 9) [96,36,72,129,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2667 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2668 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 6, region := 49, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 76 137 273 48 320 130 386), lower := (rows 97 38 76 137 273 48 320 128 256), losses := [] }

theorem u2668 : Upper (D 9) (R 9) [96,36,72,129,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2668 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2669 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(2,5),(3,5),(3,6),(4,5)], upper := (rows 97 38 76 137 273 288 66 144 400), lower := (rows 97 38 76 137 273 288 66 128 256), losses := [] }

theorem u2669 : Upper (D 9) (R 9) [96,36,72,129,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2669 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2670 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(1,8),(2,8),(3,8)], upper := (rows 97 38 76 137 273 288 80 130 386), lower := (rows 97 38 76 137 273 288 80 128 256), losses := [] }

theorem u2670 : Upper (D 9) (R 9) [96,36,72,129,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2670 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2671 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 97 38 76 137 273 288 192 146 274), lower := (rows 97 38 76 137 273 288 192 128 256), losses := [] }

theorem u2671 : Upper (D 9) (R 9) [96,36,72,129,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2671 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2672 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 434, targets := 65 },{ cop := 3, region := 68, targets := 32 }], pairs := [(1,0),(1,6),(2,5),(4,0),(4,6)], upper := (rows 97 38 76 137 274 288 65 144 400), lower := (rows 97 38 76 137 274 288 65 128 256), losses := [] }

theorem u2672 : Upper (D 9) (R 9) [96,36,72,129,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2672 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 140, targets := 32 }], pairs := [(1,8),(2,5),(2,8),(3,8)], upper := (rows 97 38 76 137 274 288 80 129 385), lower := (rows 97 38 76 137 274 288 80 128 256), losses := [] }

theorem u2673 : Upper (D 9) (R 9) [96,36,72,129,258,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2673 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2674 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 97 38 76 137 274 288 192 145 273), lower := (rows 97 38 76 137 274 288 192 128 256), losses := [] }

theorem u2674 : Upper (D 9) (R 9) [96,36,72,129,258,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2674 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2675 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 38 76 137 400 48 65 386 258), lower := (rows 97 38 76 137 400 48 65 128 256), losses := [] }

theorem u2675 : Upper (D 9) (R 9) [96,36,72,129,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2675 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2676 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 38 76 137 400 48 66 385 257), lower := (rows 97 38 76 137 400 48 66 128 256), losses := [] }

theorem u2676 : Upper (D 9) (R 9) [96,36,72,129,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2676 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2677 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 76 137 400 48 320 131 259), lower := (rows 97 38 76 137 400 48 320 128 256), losses := [] }

theorem u2677 : Upper (D 9) (R 9) [96,36,72,129,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2677 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2678 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 434, targets := 65 },{ cop := 3, region := 68, targets := 32 }], pairs := [(1,0),(1,6),(2,5),(4,0),(4,6)], upper := (rows 97 38 76 137 400 288 65 146 274), lower := (rows 97 38 76 137 400 288 65 128 256), losses := [] }

theorem u2678 : Upper (D 9) (R 9) [96,36,72,129,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2678 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2679 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(2,5),(3,5),(3,6),(4,5)], upper := (rows 97 38 76 137 400 288 66 145 273), lower := (rows 97 38 76 137 400 288 66 128 256), losses := [] }

theorem u2679 : Upper (D 9) (R 9) [96,36,72,129,384,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2679 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2680 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 76 137 400 288 80 131 259), lower := (rows 97 38 76 137 400 288 80 128 256), losses := [] }

theorem u2680 : Upper (D 9) (R 9) [96,36,72,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2680 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2681 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,6)], upper := (rows 97 38 76 138 145 288 65 400 272), lower := (rows 97 38 76 138 145 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 81 0 81 213 341), good := (rows 465 398 476 138 465 256 465 128 256) }] }

theorem u2681 : Upper (D 9) (R 9) [96,36,72,130,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2681 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2682 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(1,7),(4,5),(4,6)], upper := (rows 97 38 76 138 145 288 80 385 257), lower := (rows 97 38 76 138 145 288 80 128 256), losses := [] }

theorem u2682 : Upper (D 9) (R 9) [96,36,72,130,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2682 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2683 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 38 76 138 145 288 320 145 273), lower := (rows 97 38 76 138 145 288 320 128 256), losses := [] }

theorem u2683 : Upper (D 9) (R 9) [96,36,72,130,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2683 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2684 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(3,5)], upper := (rows 97 38 76 138 273 48 65 384 384), lower := (rows 97 38 76 138 273 48 65 128 256), losses := [] }

theorem u2684 : Upper (D 9) (R 9) [96,36,72,130,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2684 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2685 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 38 76 138 273 48 192 385 257), lower := (rows 97 38 76 138 273 48 192 128 256), losses := [] }

theorem u2685 : Upper (D 9) (R 9) [96,36,72,130,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2685 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2686 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 6, region := 49, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 76 138 273 48 320 129 385), lower := (rows 97 38 76 138 273 48 320 128 256), losses := [] }

theorem u2686 : Upper (D 9) (R 9) [96,36,72,130,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2686 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2687 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(0,8),(4,5),(4,6),(4,7)], upper := (rows 97 38 76 138 273 288 65 144 400), lower := (rows 97 38 76 138 273 288 65 128 256), losses := [] }

theorem u2687 : Upper (D 9) (R 9) [96,36,72,130,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2687 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2688 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 76 138 273 288 80 129 385), lower := (rows 97 38 76 138 273 288 80 128 256), losses := [] }

theorem u2688 : Upper (D 9) (R 9) [96,36,72,130,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2688 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2689 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 97 38 76 138 273 288 192 145 273), lower := (rows 97 38 76 138 273 288 192 128 256), losses := [] }

theorem u2689 : Upper (D 9) (R 9) [96,36,72,130,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2689 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2690 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(0,8),(1,6),(4,5),(4,6)], upper := (rows 97 38 76 138 400 288 65 145 273), lower := (rows 97 38 76 138 400 288 65 128 256), losses := [{ target := 6, region := (rows 1 6 4 12 85 373 0 193 321), good := (rows 433 62 446 138 432 288 433 128 288) }] }

theorem u2690 : Upper (D 9) (R 9) [96,36,72,130,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2690 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2691 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 4, region := 110, targets := 1 }], pairs := [(1,0),(1,8),(2,8),(3,8)], upper := (rows 97 38 76 138 400 288 80 129 257), lower := (rows 97 38 76 138 400 288 80 128 256), losses := [] }

theorem u2691 : Upper (D 9) (R 9) [96,36,72,130,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2691 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2692 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 103, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 76 152 273 33 66 384 384), lower := (rows 97 38 76 152 273 33 66 128 256), losses := [] }

theorem u2692 : Upper (D 9) (R 9) [96,36,72,144,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2692 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2693 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 103, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 97 38 76 152 273 33 192 386 258), lower := (rows 97 38 76 152 273 33 192 128 256), losses := [] }

theorem u2693 : Upper (D 9) (R 9) [96,36,72,144,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2693 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2694 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 35, targets := 256 },{ cop := 6, region := 49, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 97 38 76 152 273 33 320 130 386), lower := (rows 97 38 76 152 273 33 320 128 256), losses := [] }

theorem u2694 : Upper (D 9) (R 9) [96,36,72,144,257,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2694 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2695 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 418, targets := 65 },{ cop := 5, region := 81, targets := 128 },{ cop := 1, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(1,6),(4,7)], upper := (rows 97 38 76 152 273 288 65 130 386), lower := (rows 97 38 76 152 273 288 65 128 256), losses := [] }

theorem u2695 : Upper (D 9) (R 9) [96,36,72,144,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2695 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2696 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(2,5),(3,5),(3,6),(4,5)], upper := (rows 97 38 76 152 273 288 66 129 385), lower := (rows 97 38 76 152 273 288 66 128 256), losses := [] }

theorem u2696 : Upper (D 9) (R 9) [96,36,72,144,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2696 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2697 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 97 38 76 152 273 288 192 131 259), lower := (rows 97 38 76 152 273 288 192 128 256), losses := [] }

theorem u2697 : Upper (D 9) (R 9) [96,36,72,144,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2697 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2698 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 65, targets := 128 },{ cop := 1, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,6),(3,6),(4,6)], upper := (rows 97 38 76 152 274 288 65 129 385), lower := (rows 97 38 76 152 274 288 65 128 256), losses := [{ target := 6, region := (rows 1 6 4 12 20 373 0 193 321), good := (rows 417 62 446 184 306 288 417 128 288) }] }

theorem u2698 : Upper (D 9) (R 9) [96,36,72,144,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2698 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2699 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 97 38 76 152 274 288 192 129 257), lower := (rows 97 38 76 152 274 288 192 128 256), losses := [] }

theorem u2699 : Upper (D 9) (R 9) [96,36,72,144,258,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2699 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2699
end Delivery.IrregularNine14.P09
