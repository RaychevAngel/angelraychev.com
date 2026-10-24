import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0023

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10620 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 42 196 328 49 34 85 149 277), lower := (rows 7 42 196 328 49 34 64 128 256), losses := [] }

theorem u10620 : Upper (D 6) (R 6) [6,40,192,320,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10620
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10621 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 330, targets := 4 },{ cop := 0, region := 48, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 42 196 328 49 36 83 147 275), lower := (rows 7 42 196 328 49 36 64 128 256), losses := [] }

theorem u10621 : Upper (D 6) (R 6) [6,40,192,320,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10621
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10622 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 328 49 48 71 135 263), lower := (rows 7 42 196 328 49 48 64 128 256), losses := [] }

theorem u10622 : Upper (D 6) (R 6) [6,40,192,320,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10622
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10623 : Route 9 := (fun mask => (mask,id))

def c10623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10623 : Upper (D 6) (R 6) [6,40,192,320,36,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,36,1] 13 (by decide) (choices 1) [1,2,16] r10623 c10623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1408
  · exact u1409
  · exact u1410

def b10624 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 328 52 34 81 145 273), lower := (rows 7 42 196 328 52 34 64 128 256), losses := [] }

theorem u10624 : Upper (D 6) (R 6) [6,40,192,320,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10624
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10625 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 328 52 48 67 131 259), lower := (rows 7 42 196 328 52 48 64 128 256), losses := [] }

theorem u10625 : Upper (D 6) (R 6) [6,40,192,320,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10625
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10626 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 388 25 82 33 100 228 356), lower := (rows 7 42 388 25 82 33 64 128 256), losses := [] }

theorem u10626 : Upper (D 6) (R 6) [6,40,384,17,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10626
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10627 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 7 42 388 25 82 36 97 225 353), lower := (rows 7 42 388 25 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 420 58 82 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 16 37 0 128 256), good := (rows 39 42 420 59 18 36 0 128 256) }] }

theorem u10627 : Upper (D 6) (R 6) [6,40,384,17,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10627
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10628 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 7 42 388 25 82 96 101 165 293), lower := (rows 7 42 388 25 82 96 64 128 256), losses := [] }

theorem u10628 : Upper (D 6) (R 6) [6,40,384,17,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10628
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10629 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 388 25 84 33 98 226 354), lower := (rows 7 42 388 25 84 33 64 128 256), losses := [] }

theorem u10629 : Upper (D 6) (R 6) [6,40,384,17,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10629
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10630 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 388 25 84 34 97 225 353), lower := (rows 7 42 388 25 84 34 64 128 256), losses := [] }

theorem u10630 : Upper (D 6) (R 6) [6,40,384,17,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10630
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10631 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 98, targets := 4 }], pairs := [(0,6),(1,2),(2,6)], upper := (rows 7 42 388 25 84 96 99 163 291), lower := (rows 7 42 388 25 84 96 64 128 256), losses := [] }

theorem u10631 : Upper (D 6) (R 6) [6,40,384,17,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10631
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10632 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 7 42 388 25 112 33 70 198 326), lower := (rows 7 42 388 25 112 33 64 128 256), losses := [] }

theorem u10632 : Upper (D 6) (R 6) [6,40,384,17,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10632
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10633 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 388 25 112 34 69 197 325), lower := (rows 7 42 388 25 112 34 64 128 256), losses := [] }

theorem u10633 : Upper (D 6) (R 6) [6,40,384,17,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10633
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10634 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 388 25 112 36 67 195 323), lower := (rows 7 42 388 25 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 420 58 112 36 64 128 256) }] }

theorem u10634 : Upper (D 6) (R 6) [6,40,384,17,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10634
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10635 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 388 25 112 96 71 135 263), lower := (rows 7 42 388 25 112 96 64 128 256), losses := [] }

theorem u10635 : Upper (D 6) (R 6) [6,40,384,17,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10635
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10636 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 42 388 26 81 33 100 228 356), lower := (rows 7 42 388 26 81 33 64 128 256), losses := [] }

theorem u10636 : Upper (D 6) (R 6) [6,40,384,18,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10636
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10637 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 388 26 81 36 97 225 353), lower := (rows 7 42 388 26 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 64 128 256), good := (rows 38 42 420 26 122 36 64 128 256) }] }

theorem u10637 : Upper (D 6) (R 6) [6,40,384,18,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10637
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10638 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 388 26 81 96 101 165 293), lower := (rows 7 42 388 26 81 96 64 128 256), losses := [] }

theorem u10638 : Upper (D 6) (R 6) [6,40,384,18,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10638
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10639 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 388 26 84 33 97 225 353), lower := (rows 7 42 388 26 84 33 64 128 256), losses := [] }

theorem u10639 : Upper (D 6) (R 6) [6,40,384,18,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10639
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10640 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 388 26 84 96 97 161 289), lower := (rows 7 42 388 26 84 96 64 128 256), losses := [] }

theorem u10640 : Upper (D 6) (R 6) [6,40,384,18,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10640
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10641 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 388 28 81 33 98 226 354), lower := (rows 7 42 388 28 81 33 64 128 256), losses := [] }

theorem u10641 : Upper (D 6) (R 6) [6,40,384,20,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10641
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10642 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 388 28 81 34 97 225 353), lower := (rows 7 42 388 28 81 34 64 128 256), losses := [] }

theorem u10642 : Upper (D 6) (R 6) [6,40,384,20,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10642
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10643 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 42 388 28 81 96 99 163 291), lower := (rows 7 42 388 28 81 96 64 128 256), losses := [] }

theorem u10643 : Upper (D 6) (R 6) [6,40,384,20,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10643
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10644 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 7 42 388 28 82 33 97 225 353), lower := (rows 7 42 388 28 82 33 64 128 256), losses := [] }

theorem u10644 : Upper (D 6) (R 6) [6,40,384,20,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10644
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10645 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 7 42 388 28 82 96 97 161 289), lower := (rows 7 42 388 28 82 96 64 128 256), losses := [] }

theorem u10645 : Upper (D 6) (R 6) [6,40,384,20,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10645
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10646 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 50, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 7 42 388 73 49 34 84 212 340), lower := (rows 7 42 388 73 49 34 64 128 256), losses := [] }

theorem u10646 : Upper (D 6) (R 6) [6,40,384,65,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10646
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10647 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 4, region := 74, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 42 388 73 49 36 82 210 338), lower := (rows 7 42 388 73 49 36 64 128 256), losses := [] }

theorem u10647 : Upper (D 6) (R 6) [6,40,384,65,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10647
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10648 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 50, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 42 388 73 49 48 70 198 326), lower := (rows 7 42 388 73 49 48 64 128 256), losses := [] }

theorem u10648 : Upper (D 6) (R 6) [6,40,384,65,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10648
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10649 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 388 73 49 96 86 150 278), lower := (rows 7 42 388 73 49 96 64 128 256), losses := [] }

theorem u10649 : Upper (D 6) (R 6) [6,40,384,65,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10649
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10650 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,1),(4,6)], upper := (rows 7 42 388 73 52 33 82 210 338), lower := (rows 7 42 388 73 52 33 64 128 256), losses := [] }

theorem u10650 : Upper (D 6) (R 6) [6,40,384,65,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10650
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10651 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 388 73 52 34 81 209 337), lower := (rows 7 42 388 73 52 34 64 128 256), losses := [] }

theorem u10651 : Upper (D 6) (R 6) [6,40,384,65,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10651
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10652 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 388 73 52 48 67 195 323), lower := (rows 7 42 388 73 52 48 64 128 256), losses := [] }

theorem u10652 : Upper (D 6) (R 6) [6,40,384,65,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10652
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10653 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 388 73 52 96 83 147 275), lower := (rows 7 42 388 73 52 96 64 128 256), losses := [] }

theorem u10653 : Upper (D 6) (R 6) [6,40,384,65,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10653
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10654 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 388 73 82 33 116 180 308), lower := (rows 7 42 388 73 82 33 64 128 256), losses := [] }

theorem u10654 : Upper (D 6) (R 6) [6,40,384,65,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10654
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10655 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 7 42 388 73 82 36 113 177 305), lower := (rows 7 42 388 73 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 37 64 128 256), good := (rows 38 58 420 122 82 36 64 128 256) }] }

theorem u10655 : Upper (D 6) (R 6) [6,40,384,65,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10655
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10656 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 388 73 82 48 101 165 293), lower := (rows 7 42 388 73 82 48 64 128 256), losses := [] }

theorem u10656 : Upper (D 6) (R 6) [6,40,384,65,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10656
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10657 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 388 73 84 33 114 178 306), lower := (rows 7 42 388 73 84 33 64 128 256), losses := [] }

theorem u10657 : Upper (D 6) (R 6) [6,40,384,65,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10657
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10658 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 388 73 84 34 113 177 305), lower := (rows 7 42 388 73 84 34 64 128 256), losses := [] }

theorem u10658 : Upper (D 6) (R 6) [6,40,384,65,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10658
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10659 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 388 73 84 48 99 163 291), lower := (rows 7 42 388 73 84 48 64 128 256), losses := [] }

theorem u10659 : Upper (D 6) (R 6) [6,40,384,65,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10659
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10660 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 388 73 112 33 86 150 278), lower := (rows 7 42 388 73 112 33 64 128 256), losses := [] }

theorem u10660 : Upper (D 6) (R 6) [6,40,384,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10660
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10661 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 388 73 112 34 85 149 277), lower := (rows 7 42 388 73 112 34 64 128 256), losses := [] }

theorem u10661 : Upper (D 6) (R 6) [6,40,384,65,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10661
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10662 : PairBound 9 := { available := 19, camps := [], pairs := [(1,0),(4,0),(4,1)], upper := (rows 7 42 388 73 112 36 83 147 275), lower := (rows 7 42 388 73 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 37 64 128 256), good := (rows 38 58 420 122 112 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 24 37 64 128 256), good := (rows 37 56 420 121 112 36 64 128 256) }] }

theorem u10662 : Upper (D 6) (R 6) [6,40,384,65,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10662
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10663 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 388 73 112 48 71 135 263), lower := (rows 7 42 388 73 112 48 64 128 256), losses := [] }

theorem u10663 : Upper (D 6) (R 6) [6,40,384,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10663
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10664 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 48, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 388 74 52 33 81 209 337), lower := (rows 7 42 388 74 52 33 64 128 256), losses := [] }

theorem u10664 : Upper (D 6) (R 6) [6,40,384,66,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10664
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10665 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 388 74 52 48 65 193 321), lower := (rows 7 42 388 74 52 48 64 128 256), losses := [] }

theorem u10665 : Upper (D 6) (R 6) [6,40,384,66,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10665
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10666 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 388 74 52 96 81 145 273), lower := (rows 7 42 388 74 52 96 64 128 256), losses := [] }

theorem u10666 : Upper (D 6) (R 6) [6,40,384,66,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10666
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10667 : Route 9 := (fun mask => (mask,id))

def c10667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10667 : Upper (D 6) (R 6) [6,40,384,66,68,1] 13 := by
  apply FastRouting.sound _ _ [6,40,384,66,68,1] 13 (by decide) (choices 1) [1,16,32] r10667 c10667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1411
  · exact u1412
  · exact u1413

def b10668 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 388 74 84 48 97 161 289), lower := (rows 7 42 388 74 84 48 64 128 256), losses := [] }

theorem u10668 : Upper (D 6) (R 6) [6,40,384,66,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10668
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10669 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 42 388 76 49 33 82 210 338), lower := (rows 7 42 388 76 49 33 64 128 256), losses := [] }

theorem u10669 : Upper (D 6) (R 6) [6,40,384,68,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10669
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10670 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 42 388 76 49 34 81 209 337), lower := (rows 7 42 388 76 49 34 64 128 256), losses := [] }

theorem u10670 : Upper (D 6) (R 6) [6,40,384,68,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10670
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10671 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 388 76 49 48 67 195 323), lower := (rows 7 42 388 76 49 48 64 128 256), losses := [] }

theorem u10671 : Upper (D 6) (R 6) [6,40,384,68,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10671
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10672 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 388 76 49 96 83 147 275), lower := (rows 7 42 388 76 49 96 64 128 256), losses := [] }

theorem u10672 : Upper (D 6) (R 6) [6,40,384,68,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10672
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10673 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 388 76 81 33 114 178 306), lower := (rows 7 42 388 76 81 33 64 128 256), losses := [] }

theorem u10673 : Upper (D 6) (R 6) [6,40,384,68,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10673
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10674 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 388 76 81 34 113 177 305), lower := (rows 7 42 388 76 81 34 64 128 256), losses := [] }

theorem u10674 : Upper (D 6) (R 6) [6,40,384,68,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10674
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10675 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 388 76 81 48 99 163 291), lower := (rows 7 42 388 76 81 48 64 128 256), losses := [] }

theorem u10675 : Upper (D 6) (R 6) [6,40,384,68,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10675
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10676 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 388 76 112 33 83 147 275), lower := (rows 7 42 388 76 112 33 64 128 256), losses := [] }

theorem u10676 : Upper (D 6) (R 6) [6,40,384,68,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10676
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10677 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 388 76 112 34 81 145 273), lower := (rows 7 42 388 76 112 34 64 128 256), losses := [] }

theorem u10677 : Upper (D 6) (R 6) [6,40,384,68,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10677
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10678 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 388 76 112 48 67 131 259), lower := (rows 7 42 388 76 112 48 64 128 256), losses := [] }

theorem u10678 : Upper (D 6) (R 6) [6,40,384,68,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10678
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10679 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(4,1),(4,6)], upper := (rows 7 42 388 88 52 33 67 195 323), lower := (rows 7 42 388 88 52 33 64 128 256), losses := [] }

theorem u10679 : Upper (D 6) (R 6) [6,40,384,80,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10679
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10679
end Delivery.IrregularNine14.P06
