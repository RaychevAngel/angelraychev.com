import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0184
import IrregularNine14P06C0185

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29580 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 131 268 56 21 98 98 226 354), lower := (rows 7 131 268 56 21 32 64 128 256), losses := [] }

theorem u29580 : Upper (D 6) (R 6) [6,129,264,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29580
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29581 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 131 268 56 22 97 97 225 353), lower := (rows 7 131 268 56 22 32 64 128 256), losses := [] }

theorem u29581 : Upper (D 6) (R 6) [6,129,264,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29581
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29582 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 268 56 49 102 70 198 326), lower := (rows 7 131 268 56 49 32 64 128 256), losses := [] }

theorem u29582 : Upper (D 6) (R 6) [6,129,264,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29582
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29583 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 268 56 50 101 69 197 325), lower := (rows 7 131 268 56 50 32 64 128 256), losses := [] }

theorem u29583 : Upper (D 6) (R 6) [6,129,264,48,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29583
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29584 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 268 56 52 99 67 195 323), lower := (rows 7 131 268 56 52 32 64 128 256), losses := [] }

theorem u29584 : Upper (D 6) (R 6) [6,129,264,48,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29584
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29585 : Route 9 := (fun mask => (mask,id))

def c29585 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29585 : Upper (D 6) (R 6) [6,129,264,48,65] 13 := by
  apply FastRouting.sound _ _ [6,129,264,48,65] 13 (by decide) (choices 1) [2,4,64] r29585 c29585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11067
  · exact u11068
  · exact u11069

def r29586 : Route 9 := (fun mask => (mask,id))

def c29586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29586 : Upper (D 6) (R 6) [6,129,264,48,66] 13 := by
  apply FastRouting.sound _ _ [6,129,264,48,66] 13 (by decide) (choices 1) [1,4,64] r29586 c29586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11070
  · exact u11071
  · exact u11072

def r29587 : Route 9 := (fun mask => (mask,id))

def c29587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29587 : Upper (D 6) (R 6) [6,129,264,48,68] 13 := by
  apply FastRouting.sound _ _ [6,129,264,48,68] 13 (by decide) (choices 1) [1,2,64] r29587 c29587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11073
  · exact u11074
  · exact u11075

def b29588 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 268 56 112 103 71 199 327), lower := (rows 7 131 268 56 112 32 64 128 256), losses := [] }

theorem u29588 : Upper (D 6) (R 6) [6,129,264,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29588
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29589 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 104 19 116 116 244 372), lower := (rows 7 131 268 104 19 32 64 128 256), losses := [] }

theorem u29589 : Upper (D 6) (R 6) [6,129,264,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29589
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29590 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 131 268 104 21 114 114 242 370), lower := (rows 7 131 268 104 21 32 64 128 256), losses := [] }

theorem u29590 : Upper (D 6) (R 6) [6,129,264,96,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29590
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29591 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 131 268 104 22 113 113 241 369), lower := (rows 7 131 268 104 22 32 64 128 256), losses := [] }

theorem u29591 : Upper (D 6) (R 6) [6,129,264,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29591
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29592 : Route 9 := (fun mask => (mask,id))

def c29592 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29592 : Upper (D 6) (R 6) [6,129,264,96,33] 13 := by
  apply FastRouting.sound _ _ [6,129,264,96,33] 13 (by decide) (choices 1) [2,4,16,64] r29592 c29592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11076
  · exact u11077
  · exact u11078
  · exact u11079

def r29593 : Route 9 := (fun mask => (mask,id))

def c29593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29593 : Upper (D 6) (R 6) [6,129,264,96,34] 13 := by
  apply FastRouting.sound _ _ [6,129,264,96,34] 13 (by decide) (choices 1) [1,4,16,64] r29593 c29593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11080
  · exact u11081
  · exact u11082
  · exact u11083

def r29594 : Route 9 := (fun mask => (mask,id))

def c29594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29594 : Upper (D 6) (R 6) [6,129,264,96,36] 13 := by
  apply FastRouting.sound _ _ [6,129,264,96,36] 13 (by decide) (choices 1) [1,2,16,64] r29594 c29594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11084
  · exact u11085
  · exact u11086
  · exact u11087

def b29595 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 268 104 112 55 87 151 279), lower := (rows 7 131 268 104 112 32 64 128 256), losses := [] }

theorem u29595 : Upper (D 6) (R 6) [6,129,264,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29595
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29596 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 131 292 11 28 112 112 240 368), lower := (rows 7 131 292 11 28 32 64 128 256), losses := [] }

theorem u29596 : Upper (D 6) (R 6) [6,129,288,3,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29596
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29597 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 11 56 116 84 212 340), lower := (rows 7 131 292 11 56 32 64 128 256), losses := [] }

theorem u29597 : Upper (D 6) (R 6) [6,129,288,3,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29597
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29598 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 11 84 120 120 248 376), lower := (rows 7 131 292 11 84 32 64 128 256), losses := [] }

theorem u29598 : Upper (D 6) (R 6) [6,129,288,3,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29598
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29599 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 11 88 116 116 244 372), lower := (rows 7 131 292 11 88 32 64 128 256), losses := [] }

theorem u29599 : Upper (D 6) (R 6) [6,129,288,3,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29599
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29600 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 11 112 124 92 220 348), lower := (rows 7 131 292 11 112 32 64 128 256), losses := [] }

theorem u29600 : Upper (D 6) (R 6) [6,129,288,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29600
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29601 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 131 292 13 26 112 112 240 368), lower := (rows 7 131 292 13 26 32 64 128 256), losses := [] }

theorem u29601 : Upper (D 6) (R 6) [6,129,288,5,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29601
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29602 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 131 292 13 50 120 88 216 344), lower := (rows 7 131 292 13 50 32 64 128 256), losses := [] }

theorem u29602 : Upper (D 6) (R 6) [6,129,288,5,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29602
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29603 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 131 292 13 56 114 82 210 338), lower := (rows 7 131 292 13 56 32 64 128 256), losses := [] }

theorem u29603 : Upper (D 6) (R 6) [6,129,288,5,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29603
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29604 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 131 292 13 82 120 120 248 376), lower := (rows 7 131 292 13 82 32 64 128 256), losses := [] }

theorem u29604 : Upper (D 6) (R 6) [6,129,288,5,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29604
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29605 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 131 292 13 88 114 114 242 370), lower := (rows 7 131 292 13 88 32 64 128 256), losses := [] }

theorem u29605 : Upper (D 6) (R 6) [6,129,288,5,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29605
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29606 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 131 292 13 112 122 90 218 346), lower := (rows 7 131 292 13 112 32 64 128 256), losses := [] }

theorem u29606 : Upper (D 6) (R 6) [6,129,288,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29606
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29607 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 131 292 14 25 112 112 240 368), lower := (rows 7 131 292 14 25 32 64 128 256), losses := [] }

theorem u29607 : Upper (D 6) (R 6) [6,129,288,6,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29607
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29608 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 131 292 14 49 120 88 216 344), lower := (rows 7 131 292 14 49 32 64 128 256), losses := [] }

theorem u29608 : Upper (D 6) (R 6) [6,129,288,6,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29608
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29609 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 131 292 14 56 113 81 209 337), lower := (rows 7 131 292 14 56 32 64 128 256), losses := [] }

theorem u29609 : Upper (D 6) (R 6) [6,129,288,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29609
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29610 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 131 292 14 81 120 120 248 376), lower := (rows 7 131 292 14 81 32 64 128 256), losses := [] }

theorem u29610 : Upper (D 6) (R 6) [6,129,288,6,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29610
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29611 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 131 292 14 88 113 113 241 369), lower := (rows 7 131 292 14 88 32 64 128 256), losses := [] }

theorem u29611 : Upper (D 6) (R 6) [6,129,288,6,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29611
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29612 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 131 292 14 112 121 89 217 345), lower := (rows 7 131 292 14 112 32 64 128 256), losses := [] }

theorem u29612 : Upper (D 6) (R 6) [6,129,288,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29612
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29613 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 131 292 25 26 100 100 228 356), lower := (rows 7 131 292 25 26 32 64 128 256), losses := [] }

theorem u29613 : Upper (D 6) (R 6) [6,129,288,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29613
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29614 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 131 292 25 28 98 98 226 354), lower := (rows 7 131 292 25 28 32 64 128 256), losses := [] }

theorem u29614 : Upper (D 6) (R 6) [6,129,288,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29614
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29615 : Route 9 := (fun mask => (mask,id))

def c29615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29615 : Upper (D 6) (R 6) [6,129,288,17,34] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,34] 13 (by decide) (choices 1) [4,8,64] r29615 c29615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11088
  · exact u11089
  · exact u11090

def b29616 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 131 292 25 52 106 74 202 330), lower := (rows 7 131 292 25 52 32 64 128 256), losses := [] }

theorem u29616 : Upper (D 6) (R 6) [6,129,288,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29616
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29617 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 195, targets := 32 },{ cop := 0, region := 356, targets := 1 }], pairs := [(0,5),(1,5),(2,0)], upper := (rows 7 131 292 25 56 102 70 198 326), lower := (rows 7 131 292 25 56 32 64 128 256), losses := [] }

theorem u29617 : Upper (D 6) (R 6) [6,129,288,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29617
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29618 : Route 9 := (fun mask => (mask,id))

def c29618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29618 : Upper (D 6) (R 6) [6,129,288,17,66] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,66] 13 (by decide) (choices 1) [4,8,64] r29618 c29618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11091
  · exact u11092
  · exact u11093

def r29619 : Route 9 := (fun mask => (mask,id))

def c29619 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29619 : Upper (D 6) (R 6) [6,129,288,17,68] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,68] 13 (by decide) (choices 1) [2,8,64] r29619 c29619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11094
  · exact u11095
  · exact u11096

def r29620 : Route 9 := (fun mask => (mask,id))

def c29620 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29620 : Upper (D 6) (R 6) [6,129,288,17,72] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,72] 13 (by decide) (choices 1) [2,4,64] r29620 c29620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11097
  · exact u11098
  · exact u11099

def r29621 : Route 9 := (fun mask => (mask,id))

def c29621 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29621 : Upper (D 6) (R 6) [6,129,288,17,96] 13 := by
  apply FastRouting.sound _ _ [6,129,288,17,96] 13 (by decide) (choices 1) [2,4,8,64] r29621 c29621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11100
  · exact u11101
  · exact u11102
  · exact u11103

def b29622 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 131 292 26 28 97 97 225 353), lower := (rows 7 131 292 26 28 32 64 128 256), losses := [] }

theorem u29622 : Upper (D 6) (R 6) [6,129,288,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29622
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29623 : Route 9 := (fun mask => (mask,id))

def c29623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29623 : Upper (D 6) (R 6) [6,129,288,18,33] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,33] 13 (by decide) (choices 1) [4,8,64] r29623 c29623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11104
  · exact u11105
  · exact u11106

def b29624 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 131 292 26 52 105 73 201 329), lower := (rows 7 131 292 26 52 32 64 128 256), losses := [] }

theorem u29624 : Upper (D 6) (R 6) [6,129,288,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29624
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29625 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 195, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 7 131 292 26 56 101 69 197 325), lower := (rows 7 131 292 26 56 32 64 128 256), losses := [] }

theorem u29625 : Upper (D 6) (R 6) [6,129,288,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29625
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29626 : Route 9 := (fun mask => (mask,id))

def c29626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29626 : Upper (D 6) (R 6) [6,129,288,18,65] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,65] 13 (by decide) (choices 1) [4,8,64] r29626 c29626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11107
  · exact u11108
  · exact u11109

def r29627 : Route 9 := (fun mask => (mask,id))

def c29627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29627 : Upper (D 6) (R 6) [6,129,288,18,68] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,68] 13 (by decide) (choices 1) [1,8,64] r29627 c29627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11110
  · exact u11111
  · exact u11112

def r29628 : Route 9 := (fun mask => (mask,id))

def c29628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29628 : Upper (D 6) (R 6) [6,129,288,18,72] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,72] 13 (by decide) (choices 1) [1,4,64] r29628 c29628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11113
  · exact u11114
  · exact u11115

def r29629 : Route 9 := (fun mask => (mask,id))

def c29629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29629 : Upper (D 6) (R 6) [6,129,288,18,96] 13 := by
  apply FastRouting.sound _ _ [6,129,288,18,96] 13 (by decide) (choices 1) [1,4,8,64] r29629 c29629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11116
  · exact u11117
  · exact u11118
  · exact u11119

def r29630 : Route 9 := (fun mask => (mask,id))

def c29630 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29630 : Upper (D 6) (R 6) [6,129,288,20,33] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,33] 13 (by decide) (choices 1) [2,8,64] r29630 c29630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11120
  · exact u11121
  · exact u11122

def r29631 : Route 9 := (fun mask => (mask,id))

def c29631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29631 : Upper (D 6) (R 6) [6,129,288,20,34] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,34] 13 (by decide) (choices 1) [1,8,64] r29631 c29631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11123
  · exact u11124
  · exact u11125

def b29632 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 131 292 28 56 99 67 195 323), lower := (rows 7 131 292 28 56 32 64 128 256), losses := [] }

theorem u29632 : Upper (D 6) (R 6) [6,129,288,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29632
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29633 : Route 9 := (fun mask => (mask,id))

def c29633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29633 : Upper (D 6) (R 6) [6,129,288,20,65] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,65] 13 (by decide) (choices 1) [2,8,64] r29633 c29633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11126
  · exact u11127
  · exact u11128

def r29634 : Route 9 := (fun mask => (mask,id))

def c29634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29634 : Upper (D 6) (R 6) [6,129,288,20,66] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,66] 13 (by decide) (choices 1) [1,8,64] r29634 c29634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11129
  · exact u11130
  · exact u11131

def r29635 : Route 9 := (fun mask => (mask,id))

def c29635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29635 : Upper (D 6) (R 6) [6,129,288,20,72] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,72] 13 (by decide) (choices 1) [1,2,64] r29635 c29635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11132
  · exact u11133
  · exact u11134

def r29636 : Route 9 := (fun mask => (mask,id))

def c29636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29636 : Upper (D 6) (R 6) [6,129,288,20,96] 13 := by
  apply FastRouting.sound _ _ [6,129,288,20,96] 13 (by decide) (choices 1) [1,2,8,64] r29636 c29636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11135
  · exact u11136
  · exact u11137
  · exact u11138

def r29637 : Route 9 := (fun mask => (mask,id))

def c29637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29637 : Upper (D 6) (R 6) [6,129,288,33,66] 13 := by
  apply FastRouting.sound _ _ [6,129,288,33,66] 13 (by decide) (choices 1) [4,8,16,64] r29637 c29637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11139
  · exact u11140
  · exact u11141
  · exact u11142

def r29638 : Route 9 := (fun mask => (mask,id))

def c29638 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29638 : Upper (D 6) (R 6) [6,129,288,33,68] 13 := by
  apply FastRouting.sound _ _ [6,129,288,33,68] 13 (by decide) (choices 1) [2,8,16,64] r29638 c29638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11143
  · exact u11144
  · exact u11145
  · exact u11146

def r29639 : Route 9 := (fun mask => (mask,id))

def c29639 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29639 : Upper (D 6) (R 6) [6,129,288,33,72] 13 := by
  apply FastRouting.sound _ _ [6,129,288,33,72] 13 (by decide) (choices 1) [2,4,16,64] r29639 c29639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11147
  · exact u11148
  · exact u11149
  · exact u11150

#print axioms u29639
end Delivery.IrregularNine14.P06
