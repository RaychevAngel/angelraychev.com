import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0009

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7620 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 2, region := 161, targets := 66 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 14 280 81 160 66 129 385), lower := (rows 37 98 14 280 81 160 66 128 256), losses := [] }

theorem u7620 : Upper (D 7) (R 7) [36,96,10,272,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7621 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 280 81 160 192 131 259), lower := (rows 37 98 14 280 81 160 192 128 256), losses := [] }

theorem u7621 : Upper (D 7) (R 7) [36,96,10,272,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7622 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,7)], upper := (rows 37 98 14 280 145 160 65 194 322), lower := (rows 37 98 14 280 145 160 65 128 256), losses := [{ target := 7, region := (rows 1 3 20 24 16 32 81 0 339), good := (rows 359 354 270 348 351 32 323 0 256) }] }

theorem u7622 : Upper (D 7) (R 7) [36,96,10,272,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7623 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(3,5)], upper := (rows 37 98 14 280 145 160 66 193 321), lower := (rows 37 98 14 280 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 187 12 8 16 176 255 128 256), good := (rows 102 98 78 382 242 226 66 226 256) },{ target := 5, region := (rows 1 2 4 25 17 0 70 129 257), good := (rows 477 66 78 280 409 128 66 128 256) }] }

theorem u7623 : Upper (D 7) (R 7) [36,96,10,272,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7624 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,7),(2,5),(3,5)], upper := (rows 37 98 14 280 146 160 65 193 321), lower := (rows 37 98 14 280 146 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 22 10 18 0 65 193 321), good := (rows 453 478 30 284 158 128 449 128 256) }] }

theorem u7624 : Upper (D 7) (R 7) [36,96,10,272,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7625 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 14 280 208 33 65 130 386), lower := (rows 37 98 14 280 208 33 65 128 256), losses := [] }

theorem u7625 : Upper (D 7) (R 7) [36,96,10,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7626 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 280 208 33 66 129 385), lower := (rows 37 98 14 280 208 33 66 128 256), losses := [] }

theorem u7626 : Upper (D 7) (R 7) [36,96,10,272,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7627 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 14 280 208 33 192 131 259), lower := (rows 37 98 14 280 208 33 192 128 256), losses := [] }

theorem u7627 : Upper (D 7) (R 7) [36,96,10,272,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7628 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 14 328 145 48 65 130 386), lower := (rows 37 98 14 328 145 48 65 128 256), losses := [] }

theorem u7628 : Upper (D 7) (R 7) [36,96,10,320,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7628 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7629 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 14 328 145 48 66 129 385), lower := (rows 37 98 14 328 145 48 66 128 256), losses := [] }

theorem u7629 : Upper (D 7) (R 7) [36,96,10,320,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7629 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7630 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 14 328 145 48 192 131 259), lower := (rows 37 98 14 328 145 48 192 128 256), losses := [] }

theorem u7630 : Upper (D 7) (R 7) [36,96,10,320,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7630 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7631 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,7),(2,7),(4,6)], upper := (rows 37 98 14 328 145 160 65 146 274), lower := (rows 37 98 14 328 145 160 65 128 256), losses := [{ target := 7, region := (rows 1 3 20 24 16 32 81 0 272), good := (rows 103 98 14 328 351 32 67 0 256) }] }

theorem u7631 : Upper (D 7) (R 7) [36,96,10,320,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7632 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 14 328 145 160 66 145 273), lower := (rows 37 98 14 328 145 160 66 128 256), losses := [] }

theorem u7632 : Upper (D 7) (R 7) [36,96,10,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7633 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 14 328 145 160 80 131 259), lower := (rows 37 98 14 328 145 160 80 128 256), losses := [] }

theorem u7633 : Upper (D 7) (R 7) [36,96,10,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7633 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7634 : Route 9 := (fun mask => (mask,id))

def c7634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7634 : Upper (D 7) (R 7) [36,96,10,320,130,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,10,320,130,128,1] 13 (by decide) (choices 1) [1,16] r7634 c7634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u570
  · exact u571

def b7635 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 14 328 146 160 80 129 257), lower := (rows 37 98 14 328 146 160 80 128 256), losses := [] }

theorem u7635 : Upper (D 7) (R 7) [36,96,10,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7635 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7636 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 14 392 145 48 65 194 322), lower := (rows 37 98 14 392 145 48 65 128 256), losses := [] }

theorem u7636 : Upper (D 7) (R 7) [36,96,10,384,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7636 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7637 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(3,5)], upper := (rows 37 98 14 392 145 48 66 193 321), lower := (rows 37 98 14 392 145 48 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 25 17 0 70 129 257), good := (rows 477 66 78 392 409 24 66 128 256) }] }

theorem u7637 : Upper (D 7) (R 7) [36,96,10,384,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7637 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7638 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 14 392 146 33 65 208 336), lower := (rows 37 98 14 392 146 33 65 128 256), losses := [] }

theorem u7638 : Upper (D 7) (R 7) [36,96,10,384,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7639 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 14 392 146 33 80 193 321), lower := (rows 37 98 14 392 146 33 80 128 256), losses := [] }

theorem u7639 : Upper (D 7) (R 7) [36,96,10,384,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7639 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7640 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 14 392 208 33 65 146 274), lower := (rows 37 98 14 392 208 33 65 128 256), losses := [] }

theorem u7640 : Upper (D 7) (R 7) [36,96,10,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7641 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 392 208 33 66 145 273), lower := (rows 37 98 14 392 208 33 66 128 256), losses := [] }

theorem u7641 : Upper (D 7) (R 7) [36,96,10,384,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7642 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 392 208 33 80 131 259), lower := (rows 37 98 14 392 208 33 80 128 256), losses := [] }

theorem u7642 : Upper (D 7) (R 7) [36,96,10,384,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7642 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7643 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 28 11 273 160 66 192 448), lower := (rows 37 98 28 11 273 160 66 128 256), losses := [] }

theorem u7643 : Upper (D 7) (R 7) [36,96,24,3,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7644 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 28 11 273 160 192 194 322), lower := (rows 37 98 28 11 273 160 192 128 256), losses := [] }

theorem u7644 : Upper (D 7) (R 7) [36,96,24,3,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7645 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 28 11 274 160 65 192 448), lower := (rows 37 98 28 11 274 160 65 128 256), losses := [] }

theorem u7645 : Upper (D 7) (R 7) [36,96,24,3,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7646 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 28 11 274 160 192 193 321), lower := (rows 37 98 28 11 274 160 192 128 256), losses := [] }

theorem u7646 : Upper (D 7) (R 7) [36,96,24,3,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7647 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 28 11 336 160 65 130 386), lower := (rows 37 98 28 11 336 160 65 128 256), losses := [] }

theorem u7647 : Upper (D 7) (R 7) [36,96,24,3,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7648 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 2, region := 161, targets := 66 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 98 28 11 336 160 66 129 385), lower := (rows 37 98 28 11 336 160 66 128 256), losses := [] }

theorem u7648 : Upper (D 7) (R 7) [36,96,24,3,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7649 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 28 11 336 160 192 131 259), lower := (rows 37 98 28 11 336 160 192 128 256), losses := [] }

theorem u7649 : Upper (D 7) (R 7) [36,96,24,3,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7650 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 28 73 145 288 66 130 386), lower := (rows 37 98 28 73 145 288 66 128 256), losses := [] }

theorem u7650 : Upper (D 7) (R 7) [36,96,24,65,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7650 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7651 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 37 98 28 73 145 288 192 130 258), lower := (rows 37 98 28 73 145 288 192 128 256), losses := [] }

theorem u7651 : Upper (D 7) (R 7) [36,96,24,65,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7651 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7652 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 28 73 146 288 65 130 386), lower := (rows 37 98 28 73 146 288 65 128 256), losses := [] }

theorem u7652 : Upper (D 7) (R 7) [36,96,24,65,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7652 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7653 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 98 28 73 146 288 66 129 385), lower := (rows 37 98 28 73 146 288 66 128 256), losses := [] }

theorem u7653 : Upper (D 7) (R 7) [36,96,24,65,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7653 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7654 : Route 9 := (fun mask => (mask,id))

def c7654 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7654 : Upper (D 7) (R 7) [36,96,24,65,130,256,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,130,256,128] 13 (by decide) (choices 1) [1,2] r7654 c7654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u572
  · exact u573

def b7655 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(2,5),(3,7)], upper := (rows 37 98 28 73 273 160 66 130 386), lower := (rows 37 98 28 73 273 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 24 0 66 194 322), good := (rows 5 450 28 477 273 128 450 128 256) }] }

theorem u7655 : Upper (D 7) (R 7) [36,96,24,65,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7656 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 28 73 273 160 192 130 258), lower := (rows 37 98 28 73 273 160 192 128 256), losses := [] }

theorem u7656 : Upper (D 7) (R 7) [36,96,24,65,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7657 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 98 28 73 274 160 65 130 386), lower := (rows 37 98 28 73 274 160 65 128 256), losses := [] }

theorem u7657 : Upper (D 7) (R 7) [36,96,24,65,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7658 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 2, region := 161, targets := 66 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 98 28 73 274 160 66 129 385), lower := (rows 37 98 28 73 274 160 66 128 256), losses := [] }

theorem u7658 : Upper (D 7) (R 7) [36,96,24,65,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7659 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 28 73 274 160 192 131 259), lower := (rows 37 98 28 73 274 160 192 128 256), losses := [] }

theorem u7659 : Upper (D 7) (R 7) [36,96,24,65,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7660 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 111, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 28 73 400 34 65 130 386), lower := (rows 37 98 28 73 400 34 65 128 256), losses := [] }

theorem u7660 : Upper (D 7) (R 7) [36,96,24,65,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7661 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 28 73 400 34 66 129 385), lower := (rows 37 98 28 73 400 34 66 128 256), losses := [] }

theorem u7661 : Upper (D 7) (R 7) [36,96,24,65,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7662 : Route 9 := (fun mask => (mask,id))

def c7662 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7662 : Upper (D 7) (R 7) [36,96,24,65,384,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,384,2,128] 13 (by decide) (choices 1) [1,2] r7662 c7662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u574
  · exact u575

def b7663 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 290, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 28 137 146 288 65 194 322), lower := (rows 37 98 28 137 146 288 65 128 256), losses := [] }

theorem u7663 : Upper (D 7) (R 7) [36,96,24,129,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7663 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7664 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 28 137 146 288 66 193 321), lower := (rows 37 98 28 137 146 288 66 128 256), losses := [] }

theorem u7664 : Upper (D 7) (R 7) [36,96,24,129,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7664 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7665 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 84, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 28 137 208 34 65 386 258), lower := (rows 37 98 28 137 208 34 65 128 256), losses := [] }

theorem u7665 : Upper (D 7) (R 7) [36,96,24,129,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7666 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 28 137 208 34 66 385 257), lower := (rows 37 98 28 137 208 34 66 128 256), losses := [] }

theorem u7666 : Upper (D 7) (R 7) [36,96,24,129,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7667 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 28 137 208 34 320 131 259), lower := (rows 37 98 28 137 208 34 320 128 256), losses := [] }

theorem u7667 : Upper (D 7) (R 7) [36,96,24,129,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7667 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7668 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 84, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 37 98 28 137 208 288 65 130 258), lower := (rows 37 98 28 137 208 288 65 128 256), losses := [] }

theorem u7668 : Upper (D 7) (R 7) [36,96,24,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7668 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7669 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 28 137 208 288 66 131 259), lower := (rows 37 98 28 137 208 288 66 128 256), losses := [] }

theorem u7669 : Upper (D 7) (R 7) [36,96,24,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7669 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7670 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 28 137 336 34 65 130 386), lower := (rows 37 98 28 137 336 34 65 128 256), losses := [] }

theorem u7670 : Upper (D 7) (R 7) [36,96,24,129,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7671 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 28 137 336 34 66 129 385), lower := (rows 37 98 28 137 336 34 66 128 256), losses := [] }

theorem u7671 : Upper (D 7) (R 7) [36,96,24,129,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7672 : Route 9 := (fun mask => (mask,id))

def c7672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7672 : Upper (D 7) (R 7) [36,96,24,129,320,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,320,2,128] 13 (by decide) (choices 1) [1,2] r7672 c7672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u576
  · exact u577

def b7673 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 28 137 400 34 65 194 322), lower := (rows 37 98 28 137 400 34 65 128 256), losses := [] }

theorem u7673 : Upper (D 7) (R 7) [36,96,24,129,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7674 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 28 137 400 34 66 193 321), lower := (rows 37 98 28 137 400 34 66 128 256), losses := [] }

theorem u7674 : Upper (D 7) (R 7) [36,96,24,129,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7675 : Route 9 := (fun mask => (mask,id))

def c7675 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7675 : Upper (D 7) (R 7) [36,96,24,130,192,256,1] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,192,256,1] 13 (by decide) (choices 1) [1,2] r7675 c7675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u578
  · exact u579

def b7676 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 28 138 208 288 66 129 257), lower := (rows 37 98 28 138 208 288 66 128 256), losses := [] }

theorem u7676 : Upper (D 7) (R 7) [36,96,24,130,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7676 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7677 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 28 138 336 33 65 130 386), lower := (rows 37 98 28 138 336 33 65 128 256), losses := [] }

theorem u7677 : Upper (D 7) (R 7) [36,96,24,130,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7678 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 28 138 336 33 66 129 385), lower := (rows 37 98 28 138 336 33 66 128 256), losses := [] }

theorem u7678 : Upper (D 7) (R 7) [36,96,24,130,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7679 : Route 9 := (fun mask => (mask,id))

def c7679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7679 : Upper (D 7) (R 7) [36,96,24,130,320,1,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,320,1,128] 13 (by decide) (choices 1) [1,2] r7679 c7679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u580
  · exact u581

#print axioms u7679
end Delivery.IrregularNine14.P07
