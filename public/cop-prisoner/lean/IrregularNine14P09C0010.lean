import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b600 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 157, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 7 98 164 73 152 288 320 145 273), lower := (rows 7 98 164 73 152 288 320 128 256), losses := [] }

theorem u600 : Upper (D 9) (R 9) [6,96,160,65,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b600 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 98 164 73 280 288 65 144 400), lower := (rows 7 98 164 73 280 288 65 128 256), losses := [] }

theorem u601 : Upper (D 9) (R 9) [6,96,160,65,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b601 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 141, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(2,8),(3,5),(3,8)], upper := (rows 7 98 164 73 280 288 80 129 385), lower := (rows 7 98 164 73 280 288 80 128 256), losses := [] }

theorem u602 : Upper (D 9) (R 9) [6,96,160,65,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b602 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 7 98 164 73 280 288 192 145 273), lower := (rows 7 98 164 73 280 288 192 128 256), losses := [] }

theorem u603 : Upper (D 9) (R 9) [6,96,160,65,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b603 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 6, region := 408, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,0)], upper := (rows 7 98 164 88 280 33 65 384 384), lower := (rows 7 98 164 88 280 33 65 128 256), losses := [] }

theorem u604 : Upper (D 9) (R 9) [6,96,160,80,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b604 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 257, camps := [{ cop := 6, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 7 98 164 88 280 33 192 385 257), lower := (rows 7 98 164 88 280 33 192 128 256), losses := [] }

theorem u605 : Upper (D 9) (R 9) [6,96,160,80,264,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b605 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0),(4,5)], upper := (rows 7 98 164 88 280 33 320 129 385), lower := (rows 7 98 164 88 280 33 320 128 256), losses := [] }

theorem u606 : Upper (D 9) (R 9) [6,96,160,80,264,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b606 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 6, region := 408, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,0)], upper := (rows 7 98 164 88 400 33 65 392 264), lower := (rows 7 98 164 88 400 33 65 128 256), losses := [] }

theorem u607 : Upper (D 9) (R 9) [6,96,160,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b607 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 98 164 88 400 33 72 385 257), lower := (rows 7 98 164 88 400 33 72 128 256), losses := [] }

theorem u608 : Upper (D 9) (R 9) [6,96,160,80,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b608 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 33 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,5)], upper := (rows 7 98 164 88 400 33 320 137 265), lower := (rows 7 98 164 88 400 33 320 128 256), losses := [] }

theorem u609 : Upper (D 9) (R 9) [6,96,160,80,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b609 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 7 98 164 200 273 48 65 392 264), lower := (rows 7 98 164 200 273 48 65 128 256), losses := [] }

theorem u610 : Upper (D 9) (R 9) [6,96,160,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b610 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 200 273 48 72 385 257), lower := (rows 7 98 164 200 273 48 72 128 256), losses := [] }

theorem u611 : Upper (D 9) (R 9) [6,96,160,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b611 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 141, targets := 256 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,8),(2,8),(3,5),(3,8)], upper := (rows 7 98 164 200 273 48 320 137 265), lower := (rows 7 98 164 200 273 48 320 128 256), losses := [] }

theorem u612 : Upper (D 9) (R 9) [6,96,160,192,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b612 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 7 98 164 200 273 288 65 152 280), lower := (rows 7 98 164 200 273 288 65 128 256), losses := [] }

theorem u613 : Upper (D 9) (R 9) [6,96,160,192,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b613 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 2, region := 75, targets := 256 }], pairs := [(0,6),(0,8),(2,6),(4,6)], upper := (rows 7 98 164 200 273 288 72 145 273), lower := (rows 7 98 164 200 273 288 72 128 256), losses := [] }

theorem u614 : Upper (D 9) (R 9) [6,96,160,192,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b614 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b615 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 141, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(2,8),(3,5),(3,8)], upper := (rows 7 98 164 200 273 288 80 137 265), lower := (rows 7 98 164 200 273 288 80 128 256), losses := [] }

theorem u615 : Upper (D 9) (R 9) [6,96,160,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b615 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b616 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 7 98 164 200 280 288 65 145 273), lower := (rows 7 98 164 200 280 288 65 128 256), losses := [] }

theorem u616 : Upper (D 9) (R 9) [6,96,160,192,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b616 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 141, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(2,8),(3,5),(3,8)], upper := (rows 7 98 164 200 280 288 80 129 257), lower := (rows 7 98 164 200 280 288 80 128 256), losses := [] }

theorem u617 : Upper (D 9) (R 9) [6,96,160,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b617 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 167, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 7 98 164 265 336 33 72 144 400), lower := (rows 7 98 164 265 336 33 72 128 256), losses := [] }

theorem u618 : Upper (D 9) (R 9) [6,96,160,257,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b618 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 8, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 7 98 164 265 336 33 80 136 392), lower := (rows 7 98 164 265 336 33 80 128 256), losses := [] }

theorem u619 : Upper (D 9) (R 9) [6,96,160,257,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b619 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 7 98 164 265 336 33 192 152 280), lower := (rows 7 98 164 265 336 33 192 128 256), losses := [] }

theorem u620 : Upper (D 9) (R 9) [6,96,160,257,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b620 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b621 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 98 164 265 336 40 65 144 400), lower := (rows 7 98 164 265 336 40 65 128 256), losses := [] }

theorem u621 : Upper (D 9) (R 9) [6,96,160,257,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b621 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 164 265 336 40 80 129 385), lower := (rows 7 98 164 265 336 40 80 128 256), losses := [] }

theorem u622 : Upper (D 9) (R 9) [6,96,160,257,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b622 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8),(3,5),(4,5)], upper := (rows 7 98 164 265 336 40 192 145 273), lower := (rows 7 98 164 265 336 40 192 128 256), losses := [] }

theorem u623 : Upper (D 9) (R 9) [6,96,160,257,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b623 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 6, region := 408, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,0)], upper := (rows 7 98 164 328 400 33 65 152 280), lower := (rows 7 98 164 328 400 33 65 128 256), losses := [] }

theorem u624 : Upper (D 9) (R 9) [6,96,160,320,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b624 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 7 98 164 328 400 33 72 145 273), lower := (rows 7 98 164 328 400 33 72 128 256), losses := [] }

theorem u625 : Upper (D 9) (R 9) [6,96,160,320,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b625 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 7 98 164 328 400 33 80 137 265), lower := (rows 7 98 164 328 400 33 80 128 256), losses := [] }

theorem u626 : Upper (D 9) (R 9) [6,96,160,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b626 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 98 388 25 176 33 72 448 320), lower := (rows 7 98 388 25 176 33 72 128 256), losses := [] }

theorem u627 : Upper (D 9) (R 9) [6,96,384,17,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b627 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b628 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 452, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(3,8)], upper := (rows 7 98 388 25 176 33 320 200 328), lower := (rows 7 98 388 25 176 33 320 128 256), losses := [{ target := 8, region := (rows 1 2 4 41 19 41 64 130 0), good := (rows 191 250 132 57 184 57 64 128 0) }] }

theorem u628 : Upper (D 9) (R 9) [6,96,384,17,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b628 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b629 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 98 388 25 176 40 65 448 320), lower := (rows 7 98 388 25 176 40 65 128 256), losses := [] }

theorem u629 : Upper (D 9) (R 9) [6,96,384,17,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b629 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r630 : Route 9 := (fun mask => (mask,id))

def c630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u630 : Upper (D 9) (R 9) [6,96,384,17,160,8,256] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,160,8,256] 13 (by decide) (choices 1) [1,64] r630 c630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u29
  · exact u30

def b631 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 123, targets := 256 },{ cop := 1, region := 412, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 7 98 388 56 208 33 65 392 264), lower := (rows 7 98 388 56 208 33 65 128 256), losses := [] }

theorem u631 : Upper (D 9) (R 9) [6,96,384,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b631 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b632 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 98 388 56 208 33 72 385 257), lower := (rows 7 98 388 56 208 33 72 128 256), losses := [] }

theorem u632 : Upper (D 9) (R 9) [6,96,384,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b632 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 80, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,8),(4,0),(4,5)], upper := (rows 7 98 388 56 208 33 320 137 265), lower := (rows 7 98 388 56 208 33 320 128 256), losses := [{ target := 8, region := (rows 1 2 4 11 18 33 64 161 0), good := (rows 191 250 132 184 208 169 64 128 0) }] }

theorem u633 : Upper (D 9) (R 9) [6,96,384,48,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b633 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r634 : Route 9 := (fun mask => (mask,id))

def c634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u634 : Upper (D 9) (R 9) [6,96,384,48,192,256,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192,256,1] 13 (by decide) (choices 1) [1,8] r634 c634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u31
  · exact u32

def b635 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 405, targets := 32 },{ cop := 2, region := 122, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 98 388 56 208 288 72 129 257), lower := (rows 7 98 388 56 208 288 72 128 256), losses := [] }

theorem u635 : Upper (D 9) (R 9) [6,96,384,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b635 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 388 168 336 33 65 152 280), lower := (rows 7 98 388 168 336 33 65 128 256), losses := [] }

theorem u636 : Upper (D 9) (R 9) [6,96,384,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b636 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 32 },{ cop := 2, region := 107, targets := 256 }], pairs := [(0,5),(0,8),(2,5),(4,5)], upper := (rows 7 98 388 168 336 33 72 145 273), lower := (rows 7 98 388 168 336 33 72 128 256), losses := [] }

theorem u637 : Upper (D 9) (R 9) [6,96,384,160,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b637 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 2, region := 115, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 7 98 388 168 336 33 80 137 265), lower := (rows 7 98 388 168 336 33 80 128 256), losses := [] }

theorem u638 : Upper (D 9) (R 9) [6,96,384,160,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b638 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b639 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 436, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 35 7 28 73 176 288 192 448 320), lower := (rows 35 7 28 73 176 288 192 128 256), losses := [] }

theorem u639 : Upper (D 9) (R 9) [34,5,24,65,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b639 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(3,5),(4,0)], upper := (rows 35 7 28 73 176 288 320 192 448), lower := (rows 35 7 28 73 176 288 320 128 256), losses := [{ target := 7, region := (rows 17 22 20 25 16 352 352 0 256), good := (rows 107 15 31 105 127 352 352 0 352) }] }

theorem u640 : Upper (D 9) (R 9) [34,5,24,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b640 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 7 28 73 208 288 96 384 384), lower := (rows 35 7 28 73 208 288 96 128 256), losses := [] }

theorem u641 : Upper (D 9) (R 9) [34,5,24,65,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b641 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 7 28 73 208 288 192 416 288), lower := (rows 35 7 28 73 208 288 192 128 256), losses := [] }

theorem u642 : Upper (D 9) (R 9) [34,5,24,65,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b642 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 436, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,5),(4,0)], upper := (rows 35 7 28 73 208 288 320 160 416), lower := (rows 35 7 28 73 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 16 0 352 128 256), good := (rows 75 15 28 73 208 320 320 128 320) }] }

theorem u643 : Upper (D 9) (R 9) [34,5,24,65,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b643 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 0, region := 72, targets := 384 }], pairs := [(2,0),(3,0),(3,7),(3,8),(4,0)], upper := (rows 35 7 28 104 208 288 65 384 384), lower := (rows 35 7 28 104 208 288 65 128 256), losses := [] }

theorem u644 : Upper (D 9) (R 9) [34,5,24,96,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b644 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 7 28 104 208 288 192 385 257), lower := (rows 35 7 28 104 208 288 192 128 256), losses := [] }

theorem u645 : Upper (D 9) (R 9) [34,5,24,96,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b645 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 7 28 104 208 288 320 129 385), lower := (rows 35 7 28 104 208 288 320 128 256), losses := [] }

theorem u646 : Upper (D 9) (R 9) [34,5,24,96,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b646 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 25 176 288 192 448 320), lower := (rows 35 7 76 25 176 288 192 128 256), losses := [] }

theorem u647 : Upper (D 9) (R 9) [34,5,72,17,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b647 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 500, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,6),(1,5),(2,0),(2,5),(4,0)], upper := (rows 35 7 76 25 176 288 320 192 448), lower := (rows 35 7 76 25 176 288 320 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 352 0 128 256), good := (rows 35 7 47 25 176 288 288 128 288) }] }

theorem u648 : Upper (D 9) (R 9) [34,5,72,17,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b648 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 500, targets := 1 },{ cop := 2, region := 400, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(4,0),(4,5)], upper := (rows 35 7 76 25 208 288 96 384 384), lower := (rows 35 7 76 25 208 288 96 128 256), losses := [] }

theorem u649 : Upper (D 9) (R 9) [34,5,72,17,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b649 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 7 76 25 208 288 192 416 288), lower := (rows 35 7 76 25 208 288 192 128 256), losses := [] }

theorem u650 : Upper (D 9) (R 9) [34,5,72,17,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b650 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,6),(0,7),(1,6),(2,0),(4,0)], upper := (rows 35 7 76 25 208 288 320 160 416), lower := (rows 35 7 76 25 208 288 320 128 256), losses := [{ target := 7, region := (rows 21 30 20 24 16 352 352 0 256), good := (rows 99 7 111 31 127 352 352 0 352) }] }

theorem u651 : Upper (D 9) (R 9) [34,5,72,17,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b651 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 3, region := 484, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 35 7 76 25 400 160 96 448 320), lower := (rows 35 7 76 25 400 160 96 128 256), losses := [] }

theorem u652 : Upper (D 9) (R 9) [34,5,72,17,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b652 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 163, targets := 256 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,8),(1,5),(1,8),(2,0),(4,0)], upper := (rows 35 7 76 25 400 160 320 224 352), lower := (rows 35 7 76 25 400 160 320 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 16 0 336 128 256), good := (rows 3 7 78 95 464 128 320 128 320) }] }

theorem u653 : Upper (D 9) (R 9) [34,5,72,17,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b653 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(3,0),(4,5)], upper := (rows 35 7 76 56 145 288 192 448 320), lower := (rows 35 7 76 56 145 288 192 128 256), losses := [] }

theorem u654 : Upper (D 9) (R 9) [34,5,72,48,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b654 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 452, targets := 32 }], pairs := [(0,6),(2,0),(2,5),(3,0),(4,5)], upper := (rows 35 7 76 56 145 288 320 192 448), lower := (rows 35 7 76 56 145 288 320 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 352 0 128 256), good := (rows 35 7 47 56 145 288 288 128 288) }] }

theorem u655 : Upper (D 9) (R 9) [34,5,72,48,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b655 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 7 76 56 208 288 65 384 384), lower := (rows 35 7 76 56 208 288 65 128 256), losses := [] }

theorem u656 : Upper (D 9) (R 9) [34,5,72,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b656 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b657 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 7 76 56 208 288 192 385 257), lower := (rows 35 7 76 56 208 288 192 128 256), losses := [] }

theorem u657 : Upper (D 9) (R 9) [34,5,72,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b657 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b658 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,5)], upper := (rows 35 7 76 56 208 288 320 129 385), lower := (rows 35 7 76 56 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 352 352 128 256), good := (rows 98 6 108 124 252 352 352 128 352) }] }

theorem u658 : Upper (D 9) (R 9) [34,5,72,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b658 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 0, region := 80, targets := 128 }], pairs := [(0,6),(1,6),(3,6),(4,7)], upper := (rows 35 7 76 137 112 288 80 384 384), lower := (rows 35 7 76 137 112 288 80 128 256), losses := [] }

theorem u659 : Upper (D 9) (R 9) [34,5,72,129,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b659 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P09
