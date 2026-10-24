import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0005

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2580 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 262 100 137 208 48 105 169 297), lower := (rows 35 262 100 137 208 48 64 128 256), losses := [] }

theorem u2580 : Upper (D 8) (R 8) [34,260,96,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2580 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2581 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 168 208 33 89 153 281), lower := (rows 35 262 100 168 208 33 64 128 256), losses := [] }

theorem u2581 : Upper (D 8) (R 8) [34,260,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2582 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 262 100 168 208 40 81 145 273), lower := (rows 35 262 100 168 208 40 64 128 256), losses := [] }

theorem u2582 : Upper (D 8) (R 8) [34,260,96,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2582 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2583 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 262 100 168 208 48 73 137 265), lower := (rows 35 262 100 168 208 48 64 128 256), losses := [] }

theorem u2583 : Upper (D 8) (R 8) [34,260,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2583 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2584 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 196 25 112 33 232 168 424), lower := (rows 35 262 196 25 112 33 64 128 256), losses := [] }

theorem u2584 : Upper (D 8) (R 8) [34,260,192,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2585 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 196 25 112 40 225 161 417), lower := (rows 35 262 196 25 112 40 64 128 256), losses := [] }

theorem u2585 : Upper (D 8) (R 8) [34,260,192,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2585 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2586 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 35 262 196 25 112 160 105 169 297), lower := (rows 35 262 196 25 112 160 64 128 256), losses := [] }

theorem u2586 : Upper (D 8) (R 8) [34,260,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2587 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 196 88 176 33 105 169 297), lower := (rows 35 262 196 88 176 33 64 128 256), losses := [] }

theorem u2587 : Upper (D 8) (R 8) [34,260,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2588 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 262 196 88 176 40 97 161 289), lower := (rows 35 262 196 88 176 40 64 128 256), losses := [] }

theorem u2588 : Upper (D 8) (R 8) [34,260,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2588 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2589 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 196 104 176 33 89 153 281), lower := (rows 35 262 196 104 176 33 64 128 256), losses := [] }

theorem u2589 : Upper (D 8) (R 8) [34,260,192,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2590 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 262 196 104 176 40 81 145 273), lower := (rows 35 262 196 104 176 40 64 128 256), losses := [] }

theorem u2590 : Upper (D 8) (R 8) [34,260,192,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2590 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2591 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 28 176 33 224 224 480), lower := (rows 35 322 13 28 176 33 64 128 256), losses := [] }

theorem u2591 : Upper (D 8) (R 8) [34,320,9,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2592 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 28 176 96 225 161 417), lower := (rows 35 322 13 28 176 96 64 128 256), losses := [] }

theorem u2592 : Upper (D 8) (R 8) [34,320,9,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2593 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 28 176 160 97 225 353), lower := (rows 35 322 13 28 176 160 64 128 256), losses := [] }

theorem u2593 : Upper (D 8) (R 8) [34,320,9,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2594 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 56 148 33 224 224 480), lower := (rows 35 322 13 56 148 33 64 128 256), losses := [] }

theorem u2594 : Upper (D 8) (R 8) [34,320,9,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2595 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 56 148 96 225 161 417), lower := (rows 35 322 13 56 148 96 64 128 256), losses := [] }

theorem u2595 : Upper (D 8) (R 8) [34,320,9,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2596 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 56 148 160 97 225 353), lower := (rows 35 322 13 56 148 160 64 128 256), losses := [] }

theorem u2596 : Upper (D 8) (R 8) [34,320,9,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2597 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 56 208 33 228 164 420), lower := (rows 35 322 13 56 208 33 64 128 256), losses := [] }

theorem u2597 : Upper (D 8) (R 8) [34,320,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2598 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 322 13 56 208 36 225 161 417), lower := (rows 35 322 13 56 208 36 64 128 256), losses := [] }

theorem u2598 : Upper (D 8) (R 8) [34,320,9,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2598 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2599 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 56 208 160 101 165 293), lower := (rows 35 322 13 56 208 160 64 128 256), losses := [] }

theorem u2599 : Upper (D 8) (R 8) [34,320,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2600 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 140 112 33 240 176 432), lower := (rows 35 322 13 140 112 33 64 128 256), losses := [] }

theorem u2600 : Upper (D 8) (R 8) [34,320,9,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2601 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 322 13 140 112 48 225 161 417), lower := (rows 35 322 13 140 112 48 64 128 256), losses := [] }

theorem u2601 : Upper (D 8) (R 8) [34,320,9,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2601 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2602 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 140 112 160 113 177 305), lower := (rows 35 322 13 140 112 160 64 128 256), losses := [] }

theorem u2602 : Upper (D 8) (R 8) [34,320,9,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2603 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 152 52 33 224 224 480), lower := (rows 35 322 13 152 52 33 64 128 256), losses := [] }

theorem u2603 : Upper (D 8) (R 8) [34,320,9,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2604 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 152 52 96 225 161 417), lower := (rows 35 322 13 152 52 96 64 128 256), losses := [] }

theorem u2604 : Upper (D 8) (R 8) [34,320,9,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2605 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 152 52 160 97 225 353), lower := (rows 35 322 13 152 52 160 64 128 256), losses := [] }

theorem u2605 : Upper (D 8) (R 8) [34,320,9,144,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2606 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 152 112 33 228 164 420), lower := (rows 35 322 13 152 112 33 64 128 256), losses := [] }

theorem u2606 : Upper (D 8) (R 8) [34,320,9,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2607 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 322 13 152 112 36 225 161 417), lower := (rows 35 322 13 152 112 36 64 128 256), losses := [] }

theorem u2607 : Upper (D 8) (R 8) [34,320,9,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2607 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2608 : Route 9 := (fun mask => (mask,id))

def c2608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2608 : Upper (D 8) (R 8) [34,320,9,144,96,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,96,128] 13 (by decide) (choices 1) [1,4,32] r2608 c2608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u309
  · exact u310
  · exact u311

def b2609 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 168 52 33 208 208 464), lower := (rows 35 322 13 168 52 33 64 128 256), losses := [] }

theorem u2609 : Upper (D 8) (R 8) [34,320,9,160,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2610 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 322 13 168 52 48 193 193 449), lower := (rows 35 322 13 168 52 48 64 128 256), losses := [] }

theorem u2610 : Upper (D 8) (R 8) [34,320,9,160,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2610 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2611 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 168 52 96 209 145 401), lower := (rows 35 322 13 168 52 96 64 128 256), losses := [] }

theorem u2611 : Upper (D 8) (R 8) [34,320,9,160,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2612 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 168 52 160 81 209 337), lower := (rows 35 322 13 168 52 160 64 128 256), losses := [] }

theorem u2612 : Upper (D 8) (R 8) [34,320,9,160,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2613 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 168 84 33 240 176 432), lower := (rows 35 322 13 168 84 33 64 128 256), losses := [] }

theorem u2613 : Upper (D 8) (R 8) [34,320,9,160,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2614 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 322 13 168 84 48 225 161 417), lower := (rows 35 322 13 168 84 48 64 128 256), losses := [] }

theorem u2614 : Upper (D 8) (R 8) [34,320,9,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2614 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2615 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 168 84 160 113 177 305), lower := (rows 35 322 13 168 84 160 64 128 256), losses := [] }

theorem u2615 : Upper (D 8) (R 8) [34,320,9,160,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2616 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 168 112 33 212 148 404), lower := (rows 35 322 13 168 112 33 64 128 256), losses := [] }

theorem u2616 : Upper (D 8) (R 8) [34,320,9,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2617 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 322 13 168 112 36 209 145 401), lower := (rows 35 322 13 168 112 36 64 128 256), losses := [] }

theorem u2617 : Upper (D 8) (R 8) [34,320,9,160,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2617 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2618 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 322 13 168 112 48 197 133 389), lower := (rows 35 322 13 168 112 48 64 128 256), losses := [] }

theorem u2618 : Upper (D 8) (R 8) [34,320,9,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2618 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2619 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 168 112 160 85 149 277), lower := (rows 35 322 13 168 112 160 64 128 256), losses := [] }

theorem u2619 : Upper (D 8) (R 8) [34,320,9,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2620 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 35 322 13 168 145 36 112 240 368), lower := (rows 35 322 13 168 145 36 64 128 256), losses := [] }

theorem u2620 : Upper (D 8) (R 8) [34,320,9,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2620 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2621 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 35 322 13 168 145 48 100 228 356), lower := (rows 35 322 13 168 145 48 64 128 256), losses := [] }

theorem u2621 : Upper (D 8) (R 8) [34,320,9,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2621 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2622 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 168 145 96 116 180 308), lower := (rows 35 322 13 168 145 96 64 128 256), losses := [] }

theorem u2622 : Upper (D 8) (R 8) [34,320,9,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2623 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 168 208 33 116 180 308), lower := (rows 35 322 13 168 208 33 64 128 256), losses := [] }

theorem u2623 : Upper (D 8) (R 8) [34,320,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2624 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 322 13 168 208 36 113 177 305), lower := (rows 35 322 13 168 208 36 64 128 256), losses := [] }

theorem u2624 : Upper (D 8) (R 8) [34,320,9,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2624 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2625 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 322 13 168 208 48 101 165 293), lower := (rows 35 322 13 168 208 48 64 128 256), losses := [] }

theorem u2625 : Upper (D 8) (R 8) [34,320,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2625 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2626 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 44 145 33 224 224 480), lower := (rows 35 322 28 44 145 33 64 128 256), losses := [] }

theorem u2626 : Upper (D 8) (R 8) [34,320,24,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2627 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 44 145 96 225 161 417), lower := (rows 35 322 28 44 145 96 64 128 256), losses := [] }

theorem u2627 : Upper (D 8) (R 8) [34,320,24,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 44, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 44 145 160 97 225 353), lower := (rows 35 322 28 44 145 160 64 128 256), losses := [] }

theorem u2628 : Upper (D 8) (R 8) [34,320,24,36,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2629 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 104 145 33 228 164 420), lower := (rows 35 322 28 104 145 33 64 128 256), losses := [] }

theorem u2629 : Upper (D 8) (R 8) [34,320,24,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2630 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 322 28 104 145 36 225 161 417), lower := (rows 35 322 28 104 145 36 64 128 256), losses := [] }

theorem u2630 : Upper (D 8) (R 8) [34,320,24,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2630 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2631 : Route 9 := (fun mask => (mask,id))

def c2631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2631 : Upper (D 8) (R 8) [34,320,24,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,129,128] 13 (by decide) (choices 1) [1,4,32] r2631 c2631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u312
  · exact u313
  · exact u314

def b2632 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 104 176 33 197 133 389), lower := (rows 35 322 28 104 176 33 64 128 256), losses := [] }

theorem u2632 : Upper (D 8) (R 8) [34,320,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2633 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 322 28 104 176 36 193 129 385), lower := (rows 35 322 28 104 176 36 64 128 256), losses := [] }

theorem u2633 : Upper (D 8) (R 8) [34,320,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2633 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2634 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 104 176 160 69 133 261), lower := (rows 35 322 28 104 176 160 64 128 256), losses := [] }

theorem u2634 : Upper (D 8) (R 8) [34,320,24,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2635 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 88 145 33 228 164 420), lower := (rows 35 322 44 88 145 33 64 128 256), losses := [] }

theorem u2635 : Upper (D 8) (R 8) [34,320,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2636 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 322 44 88 145 36 225 161 417), lower := (rows 35 322 44 88 145 36 64 128 256), losses := [] }

theorem u2636 : Upper (D 8) (R 8) [34,320,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2636 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2637 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 88 145 160 101 165 293), lower := (rows 35 322 44 88 145 160 64 128 256), losses := [] }

theorem u2637 : Upper (D 8) (R 8) [34,320,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2638 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 88 176 33 197 133 389), lower := (rows 35 322 44 88 176 33 64 128 256), losses := [] }

theorem u2638 : Upper (D 8) (R 8) [34,320,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2639 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 322 44 88 176 36 193 129 385), lower := (rows 35 322 44 88 176 36 64 128 256), losses := [] }

theorem u2639 : Upper (D 8) (R 8) [34,320,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2639 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2639
end Delivery.IrregularNine14.P08
