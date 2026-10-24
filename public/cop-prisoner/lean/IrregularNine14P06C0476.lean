import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0162
import IrregularNine14P06C0163
import IrregularNine14P06C0164

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r28560 : Route 9 := (fun mask => (mask,id))

def c28560 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28560 : Upper (D 6) (R 6) [6,33,136,96,257] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96,257] 13 (by decide) (choices 1) [2,4,16,64] r28560 c28560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9776
  · exact u9777
  · exact u9778
  · exact u9779

def r28561 : Route 9 := (fun mask => (mask,id))

def c28561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28561 : Upper (D 6) (R 6) [6,33,136,96,258] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96,258] 13 (by decide) (choices 1) [1,4,16,64] r28561 c28561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9780
  · exact u9781
  · exact u9782
  · exact u9783

def r28562 : Route 9 := (fun mask => (mask,id))

def c28562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28562 : Upper (D 6) (R 6) [6,33,136,96,260] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96,260] 13 (by decide) (choices 1) [1,2,16,64] r28562 c28562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9784
  · exact u9785
  · exact u9786
  · exact u9787

def r28563 : Route 9 := (fun mask => (mask,id))

def c28563 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28563 : Upper (D 6) (R 6) [6,33,136,96,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96,320] 13 (by decide) (choices 1) [1,2,4,16] r28563 c28563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9788
  · exact u9789
  · exact u9790
  · exact u9791

def b28564 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 35 140 265 22 112 112 240 368), lower := (rows 7 35 140 265 22 32 64 128 256), losses := [] }

theorem u28564 : Upper (D 6) (R 6) [6,33,136,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28564
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28565 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 140 265 50 116 84 212 340), lower := (rows 7 35 140 265 50 32 64 128 256), losses := [] }

theorem u28565 : Upper (D 6) (R 6) [6,33,136,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28565
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28566 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 112, targets := 1 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 7 35 140 265 52 114 82 210 338), lower := (rows 7 35 140 265 52 32 64 128 256), losses := [] }

theorem u28566 : Upper (D 6) (R 6) [6,33,136,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28566
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28567 : Route 9 := (fun mask => (mask,id))

def c28567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28567 : Upper (D 6) (R 6) [6,33,136,257,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,257,66] 13 (by decide) (choices 1) [4,16,64] r28567 c28567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9792
  · exact u9793
  · exact u9794

def r28568 : Route 9 := (fun mask => (mask,id))

def c28568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28568 : Upper (D 6) (R 6) [6,33,136,257,68] 13 := by
  apply FastRouting.sound _ _ [6,33,136,257,68] 13 (by decide) (choices 1) [2,16,64] r28568 c28568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9795
  · exact u9796
  · exact u9797

def r28569 : Route 9 := (fun mask => (mask,id))

def c28569 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28569 : Upper (D 6) (R 6) [6,33,136,257,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,257,96] 13 (by decide) (choices 1) [2,4,16,64] r28569 c28569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9798
  · exact u9799
  · exact u9800
  · exact u9801

def b28570 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 35 140 266 21 112 112 240 368), lower := (rows 7 35 140 266 21 32 64 128 256), losses := [] }

theorem u28570 : Upper (D 6) (R 6) [6,33,136,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28570
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28571 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 140 266 49 116 84 212 340), lower := (rows 7 35 140 266 49 32 64 128 256), losses := [] }

theorem u28571 : Upper (D 6) (R 6) [6,33,136,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28571
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28572 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 112, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 7 35 140 266 52 113 81 209 337), lower := (rows 7 35 140 266 52 32 64 128 256), losses := [] }

theorem u28572 : Upper (D 6) (R 6) [6,33,136,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28572
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28573 : Route 9 := (fun mask => (mask,id))

def c28573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28573 : Upper (D 6) (R 6) [6,33,136,258,65] 13 := by
  apply FastRouting.sound _ _ [6,33,136,258,65] 13 (by decide) (choices 1) [4,16,64] r28573 c28573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9802
  · exact u9803
  · exact u9804

def r28574 : Route 9 := (fun mask => (mask,id))

def c28574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28574 : Upper (D 6) (R 6) [6,33,136,258,68] 13 := by
  apply FastRouting.sound _ _ [6,33,136,258,68] 13 (by decide) (choices 1) [1,16,64] r28574 c28574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9805
  · exact u9806
  · exact u9807

def r28575 : Route 9 := (fun mask => (mask,id))

def c28575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28575 : Upper (D 6) (R 6) [6,33,136,258,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,258,96] 13 (by decide) (choices 1) [1,4,16,64] r28575 c28575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9808
  · exact u9809
  · exact u9810
  · exact u9811

def b28576 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 268 19 112 112 240 368), lower := (rows 7 35 140 268 19 32 64 128 256), losses := [] }

theorem u28576 : Upper (D 6) (R 6) [6,33,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28576
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28577 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 114, targets := 4 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,2),(4,1),(4,2)], upper := (rows 7 35 140 268 49 114 82 210 338), lower := (rows 7 35 140 268 49 32 64 128 256), losses := [] }

theorem u28577 : Upper (D 6) (R 6) [6,33,136,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28577
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28578 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 140 268 50 113 81 209 337), lower := (rows 7 35 140 268 50 32 64 128 256), losses := [] }

theorem u28578 : Upper (D 6) (R 6) [6,33,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28578
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28579 : Route 9 := (fun mask => (mask,id))

def c28579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28579 : Upper (D 6) (R 6) [6,33,136,260,65] 13 := by
  apply FastRouting.sound _ _ [6,33,136,260,65] 13 (by decide) (choices 1) [2,16,64] r28579 c28579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9812
  · exact u9813
  · exact u9814

def r28580 : Route 9 := (fun mask => (mask,id))

def c28580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28580 : Upper (D 6) (R 6) [6,33,136,260,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,260,66] 13 (by decide) (choices 1) [1,16,64] r28580 c28580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9815
  · exact u9816
  · exact u9817

def r28581 : Route 9 := (fun mask => (mask,id))

def c28581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28581 : Upper (D 6) (R 6) [6,33,136,260,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,260,96] 13 (by decide) (choices 1) [1,2,16,64] r28581 c28581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9818
  · exact u9819
  · exact u9820
  · exact u9821

def b28582 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 280 19 100 100 228 356), lower := (rows 7 35 140 280 19 32 64 128 256), losses := [] }

theorem u28582 : Upper (D 6) (R 6) [6,33,136,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28582
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28583 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 35 140 280 21 98 98 226 354), lower := (rows 7 35 140 280 21 32 64 128 256), losses := [] }

theorem u28583 : Upper (D 6) (R 6) [6,33,136,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28583
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28584 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 35 140 280 22 97 97 225 353), lower := (rows 7 35 140 280 22 32 64 128 256), losses := [] }

theorem u28584 : Upper (D 6) (R 6) [6,33,136,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28584
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28585 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 140 280 49 102 70 198 326), lower := (rows 7 35 140 280 49 32 64 128 256), losses := [] }

theorem u28585 : Upper (D 6) (R 6) [6,33,136,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28585
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28586 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 140 280 50 101 69 197 325), lower := (rows 7 35 140 280 50 32 64 128 256), losses := [] }

theorem u28586 : Upper (D 6) (R 6) [6,33,136,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28586
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28587 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 98, targets := 4 }], pairs := [(0,6),(1,2),(1,6)], upper := (rows 7 35 140 280 52 99 67 195 323), lower := (rows 7 35 140 280 52 32 64 128 256), losses := [] }

theorem u28587 : Upper (D 6) (R 6) [6,33,136,272,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28587
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28588 : Route 9 := (fun mask => (mask,id))

def c28588 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28588 : Upper (D 6) (R 6) [6,33,136,272,65] 13 := by
  apply FastRouting.sound _ _ [6,33,136,272,65] 13 (by decide) (choices 1) [2,4,64] r28588 c28588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9822
  · exact u9823
  · exact u9824

def r28589 : Route 9 := (fun mask => (mask,id))

def c28589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28589 : Upper (D 6) (R 6) [6,33,136,272,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,272,66] 13 (by decide) (choices 1) [1,4,64] r28589 c28589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9825
  · exact u9826
  · exact u9827

def r28590 : Route 9 := (fun mask => (mask,id))

def c28590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28590 : Upper (D 6) (R 6) [6,33,136,272,68] 13 := by
  apply FastRouting.sound _ _ [6,33,136,272,68] 13 (by decide) (choices 1) [1,2,64] r28590 c28590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9828
  · exact u9829
  · exact u9830

def r28591 : Route 9 := (fun mask => (mask,id))

def c28591 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28591 : Upper (D 6) (R 6) [6,33,136,272,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,272,96] 13 (by decide) (choices 1) [1,2,4,64] r28591 c28591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9831
  · exact u9832
  · exact u9833
  · exact u9834

def b28592 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 296 19 116 84 212 340), lower := (rows 7 35 140 296 19 32 64 128 256), losses := [] }

theorem u28592 : Upper (D 6) (R 6) [6,33,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28592
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28593 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 35 140 296 21 114 82 210 338), lower := (rows 7 35 140 296 21 32 64 128 256), losses := [] }

theorem u28593 : Upper (D 6) (R 6) [6,33,136,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28593
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28594 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 35 140 296 22 113 81 209 337), lower := (rows 7 35 140 296 22 32 64 128 256), losses := [] }

theorem u28594 : Upper (D 6) (R 6) [6,33,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28594
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28595 : Route 9 := (fun mask => (mask,id))

def c28595 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28595 : Upper (D 6) (R 6) [6,33,136,288,65] 13 := by
  apply FastRouting.sound _ _ [6,33,136,288,65] 13 (by decide) (choices 1) [2,4,16,64] r28595 c28595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9835
  · exact u9836
  · exact u9837
  · exact u9838

def r28596 : Route 9 := (fun mask => (mask,id))

def c28596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28596 : Upper (D 6) (R 6) [6,33,136,288,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,288,66] 13 (by decide) (choices 1) [1,4,16,64] r28596 c28596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9839
  · exact u9840
  · exact u9841
  · exact u9842

def r28597 : Route 9 := (fun mask => (mask,id))

def c28597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28597 : Upper (D 6) (R 6) [6,33,136,288,68] 13 := by
  apply FastRouting.sound _ _ [6,33,136,288,68] 13 (by decide) (choices 1) [1,2,16,64] r28597 c28597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9843
  · exact u9844
  · exact u9845
  · exact u9846

def b28598 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 328 19 116 116 244 372), lower := (rows 7 35 140 328 19 32 64 128 256), losses := [] }

theorem u28598 : Upper (D 6) (R 6) [6,33,136,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28598
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28599 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 35 140 328 21 114 114 242 370), lower := (rows 7 35 140 328 21 32 64 128 256), losses := [] }

theorem u28599 : Upper (D 6) (R 6) [6,33,136,320,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28599
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28600 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 35 140 328 22 113 113 241 369), lower := (rows 7 35 140 328 22 32 64 128 256), losses := [] }

theorem u28600 : Upper (D 6) (R 6) [6,33,136,320,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28600
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28601 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 140 328 49 118 86 214 342), lower := (rows 7 35 140 328 49 32 64 128 256), losses := [] }

theorem u28601 : Upper (D 6) (R 6) [6,33,136,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28601
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28602 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 140 328 50 117 85 213 341), lower := (rows 7 35 140 328 50 32 64 128 256), losses := [] }

theorem u28602 : Upper (D 6) (R 6) [6,33,136,320,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28602
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28603 : Route 9 := (fun mask => (mask,id))

def c28603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28603 : Upper (D 6) (R 6) [6,33,136,320,36] 13 := by
  apply FastRouting.sound _ _ [6,33,136,320,36] 13 (by decide) (choices 1) [1,2,16,64] r28603 c28603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9847
  · exact u9848
  · exact u9849
  · exact u9850

def r28604 : Route 9 := (fun mask => (mask,id))

def c28604 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28604 : Upper (D 6) (R 6) [6,33,136,320,65] 13 := by
  apply FastRouting.sound _ _ [6,33,136,320,65] 13 (by decide) (choices 1) [2,4,16] r28604 c28604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9851
  · exact u9852
  · exact u9853

def r28605 : Route 9 := (fun mask => (mask,id))

def c28605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28605 : Upper (D 6) (R 6) [6,33,136,320,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,320,66] 13 (by decide) (choices 1) [1,4,16] r28605 c28605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9854
  · exact u9855
  · exact u9856

def r28606 : Route 9 := (fun mask => (mask,id))

def c28606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28606 : Upper (D 6) (R 6) [6,33,136,320,68] 13 := by
  apply FastRouting.sound _ _ [6,33,136,320,68] 13 (by decide) (choices 1) [1,2,16] r28606 c28606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9857
  · exact u9858
  · exact u9859

def r28607 : Route 9 := (fun mask => (mask,id))

def c28607 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28607 : Upper (D 6) (R 6) [6,33,136,320,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,320,96] 13 (by decide) (choices 1) [1,2,4,16] r28607 c28607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9860
  · exact u9861
  · exact u9862
  · exact u9863

def b28608 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 196 11 28 368 368 496 368), lower := (rows 7 35 196 11 28 32 64 128 256), losses := [] }

theorem u28608 : Upper (D 6) (R 6) [6,33,192,3,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28608
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28609 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 11 52 376 344 472 344), lower := (rows 7 35 196 11 52 32 64 128 256), losses := [] }

theorem u28609 : Upper (D 6) (R 6) [6,33,192,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28609
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28610 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 196 11 56 372 340 468 340), lower := (rows 7 35 196 11 56 32 64 128 256), losses := [] }

theorem u28610 : Upper (D 6) (R 6) [6,33,192,3,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28610
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28611 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 11 88 308 372 436 308), lower := (rows 7 35 196 11 88 32 64 128 256), losses := [] }

theorem u28611 : Upper (D 6) (R 6) [6,33,192,3,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28611
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28612 : PairBound 9 := { available := 284, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 11 112 316 348 412 284), lower := (rows 7 35 196 11 112 32 64 128 256), losses := [] }

theorem u28612 : Upper (D 6) (R 6) [6,33,192,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28612
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28613 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 11 276 120 120 248 376), lower := (rows 7 35 196 11 276 32 64 128 256), losses := [] }

theorem u28613 : Upper (D 6) (R 6) [6,33,192,3,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28613
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28614 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 11 280 116 116 244 372), lower := (rows 7 35 196 11 280 32 64 128 256), losses := [] }

theorem u28614 : Upper (D 6) (R 6) [6,33,192,3,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28614
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28615 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 11 304 124 92 220 348), lower := (rows 7 35 196 11 304 32 64 128 256), losses := [] }

theorem u28615 : Upper (D 6) (R 6) [6,33,192,3,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28615
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28616 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 11 336 60 124 188 316), lower := (rows 7 35 196 11 336 32 64 128 256), losses := [] }

theorem u28616 : Upper (D 6) (R 6) [6,33,192,3,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28616
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28617 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 196 13 26 368 368 496 368), lower := (rows 7 35 196 13 26 32 64 128 256), losses := [] }

theorem u28617 : Upper (D 6) (R 6) [6,33,192,5,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28617
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28618 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 56 370 338 466 338), lower := (rows 7 35 196 13 56 32 64 128 256), losses := [] }

theorem u28618 : Upper (D 6) (R 6) [6,33,192,5,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28618
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28619 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 82 312 376 440 312), lower := (rows 7 35 196 13 82 32 64 128 256), losses := [] }

theorem u28619 : Upper (D 6) (R 6) [6,33,192,5,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28619
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28619
end Delivery.IrregularNine14.P06
