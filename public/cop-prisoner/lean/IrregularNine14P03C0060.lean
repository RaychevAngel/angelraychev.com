import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0023

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3600 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 13 280 208 37 101 165 293), lower := (rows 35 194 13 280 208 32 64 128 256), losses := [] }

theorem u3600 : Upper (D 3) (R 3) [34,192,9,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3600
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3601 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 296 84 177 209 145 401), lower := (rows 35 194 13 296 84 32 64 128 256), losses := [] }

theorem u3601 : Upper (D 3) (R 3) [34,192,9,288,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3601
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3602 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 328 52 177 209 145 401), lower := (rows 35 194 13 328 52 32 64 128 256), losses := [] }

theorem u3602 : Upper (D 3) (R 3) [34,192,9,320,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3602
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3603 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 328 148 49 113 177 305), lower := (rows 35 194 13 328 148 32 64 128 256), losses := [] }

theorem u3603 : Upper (D 3) (R 3) [34,192,9,320,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3603
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3604 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 328 176 53 85 149 277), lower := (rows 35 194 13 328 176 32 64 128 256), losses := [] }

theorem u3604 : Upper (D 3) (R 3) [34,192,9,320,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3604
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3605 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 28 41 273 229 197 197 453), lower := (rows 35 194 28 41 273 32 64 128 256), losses := [] }

theorem u3605 : Upper (D 3) (R 3) [34,192,24,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3605
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3606 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 28 41 276 225 193 193 449), lower := (rows 35 194 28 41 276 32 64 128 256), losses := [] }

theorem u3606 : Upper (D 3) (R 3) [34,192,24,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3606
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3607 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 28 41 336 165 197 133 389), lower := (rows 35 194 28 41 336 32 64 128 256), losses := [] }

theorem u3607 : Upper (D 3) (R 3) [34,192,24,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3607
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3608 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 28 44 273 225 193 193 449), lower := (rows 35 194 28 44 273 32 64 128 256), losses := [] }

theorem u3608 : Upper (D 3) (R 3) [34,192,24,36,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3608
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3609 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 28 44 336 161 193 129 385), lower := (rows 35 194 28 44 336 32 64 128 256), losses := [] }

theorem u3609 : Upper (D 3) (R 3) [34,192,24,36,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3609
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3610 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 176 293 325 389 261), lower := (rows 35 194 28 73 176 32 64 128 256), losses := [] }

theorem u3610 : Upper (D 3) (R 3) [34,192,24,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3610
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3611 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 273 165 229 165 421), lower := (rows 35 194 28 73 273 32 64 128 256), losses := [] }

theorem u3611 : Upper (D 3) (R 3) [34,192,24,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3611
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3612 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 276 161 225 161 417), lower := (rows 35 194 28 73 276 32 64 128 256), losses := [] }

theorem u3612 : Upper (D 3) (R 3) [34,192,24,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3612
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3613 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 304 165 197 133 389), lower := (rows 35 194 28 73 304 32 64 128 256), losses := [] }

theorem u3613 : Upper (D 3) (R 3) [34,192,24,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3613
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3614 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 400 37 101 165 293), lower := (rows 35 194 28 73 400 32 64 128 256), losses := [] }

theorem u3614 : Upper (D 3) (R 3) [34,192,24,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3614
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3615 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 76 176 289 321 385 257), lower := (rows 35 194 28 76 176 32 64 128 256), losses := [] }

theorem u3615 : Upper (D 3) (R 3) [34,192,24,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3615
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3616 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 76 273 161 225 161 417), lower := (rows 35 194 28 76 273 32 64 128 256), losses := [] }

theorem u3616 : Upper (D 3) (R 3) [34,192,24,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3616
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3617 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 76 304 161 193 129 385), lower := (rows 35 194 28 76 304 32 64 128 256), losses := [] }

theorem u3617 : Upper (D 3) (R 3) [34,192,24,68,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3617
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3618 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 76 400 33 97 161 289), lower := (rows 35 194 28 76 400 32 64 128 256), losses := [] }

theorem u3618 : Upper (D 3) (R 3) [34,192,24,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3618
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3619 : Route 9 := (fun mask => (mask,id))

def c3619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3619 : Upper (D 3) (R 3) [34,192,24,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,257] 13 (by decide) (choices 1) [1,4,128] r3619 c3619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1404
  · exact u1405
  · exact u1406

def b3620 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 28 104 276 161 193 129 385), lower := (rows 35 194 28 104 276 32 64 128 256), losses := [] }

theorem u3620 : Upper (D 3) (R 3) [34,192,24,96,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3620
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3621 : Route 9 := (fun mask => (mask,id))

def c3621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3621 : Upper (D 3) (R 3) [34,192,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,384] 13 (by decide) (choices 1) [1,4] r3621 c3621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1407
  · exact u1408

def b3622 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 28 200 273 37 101 165 293), lower := (rows 35 194 28 200 273 32 64 128 256), losses := [] }

theorem u3622 : Upper (D 3) (R 3) [34,192,24,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3622
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3623 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 28 200 276 33 97 161 289), lower := (rows 35 194 28 200 276 32 64 128 256), losses := [] }

theorem u3623 : Upper (D 3) (R 3) [34,192,24,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3623
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3624 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 28 200 304 37 69 133 261), lower := (rows 35 194 28 200 304 32 64 128 256), losses := [] }

theorem u3624 : Upper (D 3) (R 3) [34,192,24,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3624
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3625 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 37 76 152 305 337 401 273), lower := (rows 35 194 37 76 152 32 64 128 256), losses := [] }

theorem u3625 : Upper (D 3) (R 3) [34,192,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3625
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3626 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 37 76 273 185 217 153 409), lower := (rows 35 194 37 76 273 32 64 128 256), losses := [] }

theorem u3626 : Upper (D 3) (R 3) [34,192,33,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3626
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3627 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 37 76 280 177 209 145 401), lower := (rows 35 194 37 76 280 32 64 128 256), losses := [] }

theorem u3627 : Upper (D 3) (R 3) [34,192,33,68,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3627
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3628 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 37 76 400 57 89 153 281), lower := (rows 35 194 37 76 400 32 64 128 256), losses := [] }

theorem u3628 : Upper (D 3) (R 3) [34,192,33,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3628
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3629 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 37 88 273 173 205 141 397), lower := (rows 35 194 37 88 273 32 64 128 256), losses := [] }

theorem u3629 : Upper (D 3) (R 3) [34,192,33,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3629
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3630 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 37 88 276 169 201 137 393), lower := (rows 35 194 37 88 276 32 64 128 256), losses := [] }

theorem u3630 : Upper (D 3) (R 3) [34,192,33,80,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3630
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3631 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 37 88 400 45 77 141 269), lower := (rows 35 194 37 88 400 32 64 128 256), losses := [] }

theorem u3631 : Upper (D 3) (R 3) [34,192,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3631
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3632 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 148 305 337 401 273), lower := (rows 35 194 44 73 148 32 64 128 256), losses := [] }

theorem u3632 : Upper (D 3) (R 3) [34,192,40,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3632
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3633 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 273 181 213 149 405), lower := (rows 35 194 44 73 273 32 64 128 256), losses := [] }

theorem u3633 : Upper (D 3) (R 3) [34,192,40,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3633
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3634 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 276 177 209 145 401), lower := (rows 35 194 44 73 276 32 64 128 256), losses := [] }

theorem u3634 : Upper (D 3) (R 3) [34,192,40,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3634
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3635 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 73 400 53 85 149 277), lower := (rows 35 194 44 73 400 32 64 128 256), losses := [] }

theorem u3635 : Upper (D 3) (R 3) [34,192,40,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3635
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3636 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 44 76 273 177 209 145 401), lower := (rows 35 194 44 76 273 32 64 128 256), losses := [] }

theorem u3636 : Upper (D 3) (R 3) [34,192,40,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3636
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3637 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 44 76 400 49 81 145 273), lower := (rows 35 194 44 76 400 32 64 128 256), losses := [] }

theorem u3637 : Upper (D 3) (R 3) [34,192,40,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3637
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3638 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 88 145 293 325 389 261), lower := (rows 35 194 44 88 145 32 64 128 256), losses := [] }

theorem u3638 : Upper (D 3) (R 3) [34,192,40,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3638
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3639 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 44 88 148 289 321 385 257), lower := (rows 35 194 44 88 148 32 64 128 256), losses := [] }

theorem u3639 : Upper (D 3) (R 3) [34,192,40,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3639
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3640 : Route 9 := (fun mask => (mask,id))

def c3640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3640 : Upper (D 3) (R 3) [34,192,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,257] 13 (by decide) (choices 1) [1,4,128] r3640 c3640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1409
  · exact u1410
  · exact u1411

def b3641 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 44 88 276 161 193 129 385), lower := (rows 35 194 44 88 276 32 64 128 256), losses := [] }

theorem u3641 : Upper (D 3) (R 3) [34,192,40,80,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3641
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3642 : Route 9 := (fun mask => (mask,id))

def c3642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3642 : Upper (D 3) (R 3) [34,192,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,384] 13 (by decide) (choices 1) [1,4] r3642 c3642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1412
  · exact u1413

def b3643 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 44 200 273 53 85 149 277), lower := (rows 35 194 44 200 273 32 64 128 256), losses := [] }

theorem u3643 : Upper (D 3) (R 3) [34,192,40,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3643
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3644 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 44 200 276 49 81 145 273), lower := (rows 35 194 44 200 276 32 64 128 256), losses := [] }

theorem u3644 : Upper (D 3) (R 3) [34,192,40,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3644
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3645 : PairBound 9 := { available := 149, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 265 81 181 213 149 405), lower := (rows 35 194 44 265 81 32 64 128 256), losses := [] }

theorem u3645 : Upper (D 3) (R 3) [34,192,40,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3645
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3646 : Route 9 := (fun mask => (mask,id))

def c3646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3646 : Upper (D 3) (R 3) [34,192,40,257,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,68] 13 (by decide) (choices 1) [1,16,128] r3646 c3646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1414
  · exact u1415
  · exact u1416

def b3647 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 44 265 208 53 85 149 277), lower := (rows 35 194 44 265 208 32 64 128 256), losses := [] }

theorem u3647 : Upper (D 3) (R 3) [34,192,40,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3647
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3648 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 280 81 165 197 133 389), lower := (rows 35 194 44 280 81 32 64 128 256), losses := [] }

theorem u3648 : Upper (D 3) (R 3) [34,192,40,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3648
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3649 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 44 280 84 161 193 129 385), lower := (rows 35 194 44 280 84 32 64 128 256), losses := [] }

theorem u3649 : Upper (D 3) (R 3) [34,192,40,272,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3649
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3650 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 44 280 208 37 69 133 261), lower := (rows 35 194 44 280 208 32 64 128 256), losses := [] }

theorem u3650 : Upper (D 3) (R 3) [34,192,40,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3650
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3651 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 328 145 53 85 149 277), lower := (rows 35 194 44 328 145 32 64 128 256), losses := [] }

theorem u3651 : Upper (D 3) (R 3) [34,192,40,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3651
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3652 : Route 9 := (fun mask => (mask,id))

def c3652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3652 : Upper (D 3) (R 3) [34,192,40,320,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,132] 13 (by decide) (choices 1) [1,16] r3652 c3652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1417
  · exact u1418

def b3653 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 140 273 57 121 185 313), lower := (rows 35 194 69 140 273 32 64 128 256), losses := [] }

theorem u3653 : Upper (D 3) (R 3) [34,192,65,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3653
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3654 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 140 280 49 113 177 305), lower := (rows 35 194 69 140 280 32 64 128 256), losses := [] }

theorem u3654 : Upper (D 3) (R 3) [34,192,65,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3654
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3655 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 140 304 57 89 153 281), lower := (rows 35 194 69 140 304 32 64 128 256), losses := [] }

theorem u3655 : Upper (D 3) (R 3) [34,192,65,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3655
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3656 : PairBound 9 := { available := 45, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 152 273 45 109 173 301), lower := (rows 35 194 69 152 273 32 64 128 256), losses := [] }

theorem u3656 : Upper (D 3) (R 3) [34,192,65,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3656
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3657 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 152 276 41 105 169 297), lower := (rows 35 194 69 152 276 32 64 128 256), losses := [] }

theorem u3657 : Upper (D 3) (R 3) [34,192,65,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3657
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3658 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 152 304 45 77 141 269), lower := (rows 35 194 69 152 304 32 64 128 256), losses := [] }

theorem u3658 : Upper (D 3) (R 3) [34,192,65,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3658
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3659 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 168 273 61 93 157 285), lower := (rows 35 194 69 168 273 32 64 128 256), losses := [] }

theorem u3659 : Upper (D 3) (R 3) [34,192,65,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3659
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3659
end Delivery.IrregularNine14.P03
