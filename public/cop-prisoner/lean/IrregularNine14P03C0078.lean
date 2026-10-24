import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0028

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4680 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 265 145 179 211 147 403), lower := (rows 97 14 100 265 145 32 64 128 256), losses := [] }

theorem u4680 : Upper (D 3) (R 3) [96,12,96,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4680
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4681 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 265 146 177 209 145 401), lower := (rows 97 14 100 265 146 32 64 128 256), losses := [] }

theorem u4681 : Upper (D 3) (R 3) [96,12,96,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4681
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4682 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 266 145 177 209 145 401), lower := (rows 97 14 100 266 145 32 64 128 256), losses := [] }

theorem u4682 : Upper (D 3) (R 3) [96,12,96,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4682
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4683 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 280 145 163 195 131 387), lower := (rows 97 14 100 280 145 32 64 128 256), losses := [] }

theorem u4683 : Upper (D 3) (R 3) [96,12,96,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4683
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4684 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 280 146 161 193 129 385), lower := (rows 97 14 100 280 146 32 64 128 256), losses := [] }

theorem u4684 : Upper (D 3) (R 3) [96,12,96,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4684
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4685 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 392 145 51 83 147 275), lower := (rows 97 14 100 392 145 32 64 128 256), losses := [] }

theorem u4685 : Upper (D 3) (R 3) [96,12,96,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4685
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4686 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 50 369 337 465 337), lower := (rows 97 14 133 137 50 32 64 128 256), losses := [] }

theorem u4686 : Upper (D 3) (R 3) [96,12,129,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4686
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4687 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 273 114 114 242 370), lower := (rows 97 14 133 137 273 32 64 128 256), losses := [] }

theorem u4687 : Upper (D 3) (R 3) [96,12,129,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4687
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4688 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 274 113 113 241 369), lower := (rows 97 14 133 137 274 32 64 128 256), losses := [] }

theorem u4688 : Upper (D 3) (R 3) [96,12,129,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4688
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4689 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 304 115 83 211 339), lower := (rows 97 14 133 137 304 32 64 128 256), losses := [] }

theorem u4689 : Upper (D 3) (R 3) [96,12,129,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4689
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4690 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 133 138 273 113 113 241 369), lower := (rows 97 14 133 138 273 32 64 128 256), losses := [] }

theorem u4690 : Upper (D 3) (R 3) [96,12,129,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4690
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4691 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 133 138 304 113 81 209 337), lower := (rows 97 14 133 138 304 32 64 128 256), losses := [] }

theorem u4691 : Upper (D 3) (R 3) [96,12,129,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4691
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4692 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 50 353 321 449 321), lower := (rows 97 14 133 152 50 32 64 128 256), losses := [] }

theorem u4692 : Upper (D 3) (R 3) [96,12,129,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4692
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4693 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 273 99 99 227 355), lower := (rows 97 14 133 152 273 32 64 128 256), losses := [] }

theorem u4693 : Upper (D 3) (R 3) [96,12,129,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4693
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4694 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 274 97 97 225 353), lower := (rows 97 14 133 152 274 32 64 128 256), losses := [] }

theorem u4694 : Upper (D 3) (R 3) [96,12,129,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4694
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4695 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 304 99 67 195 323), lower := (rows 97 14 133 152 304 32 64 128 256), losses := [] }

theorem u4695 : Upper (D 3) (R 3) [96,12,129,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4695
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4696 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 82 305 337 401 273), lower := (rows 97 14 133 168 82 32 64 128 256), losses := [] }

theorem u4696 : Upper (D 3) (R 3) [96,12,129,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4696
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4697 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 273 115 83 211 339), lower := (rows 97 14 133 168 273 32 64 128 256), losses := [] }

theorem u4697 : Upper (D 3) (R 3) [96,12,129,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4697
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4698 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 274 113 81 209 337), lower := (rows 97 14 133 168 274 32 64 128 256), losses := [] }

theorem u4698 : Upper (D 3) (R 3) [96,12,129,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4698
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4699 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 336 51 83 147 275), lower := (rows 97 14 133 168 336 32 64 128 256), losses := [] }

theorem u4699 : Upper (D 3) (R 3) [96,12,129,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4699
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4700 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 265 49 242 210 210 466), lower := (rows 97 14 133 265 49 32 64 128 256), losses := [] }

theorem u4700 : Upper (D 3) (R 3) [96,12,129,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4700
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4701 : Route 9 := (fun mask => (mask,id))

def c4701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4701 : Upper (D 3) (R 3) [96,12,129,257,34] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,34] 13 (by decide) (choices 1) [1,16,64,128] r4701 c4701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1719
  · exact u1720
  · exact u1721
  · exact u1722

def b4702 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 265 112 179 211 147 403), lower := (rows 97 14 133 265 112 32 64 128 256), losses := [] }

theorem u4702 : Upper (D 3) (R 3) [96,12,129,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4702
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4703 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 133 265 145 114 114 242 370), lower := (rows 97 14 133 265 145 32 64 128 256), losses := [] }

theorem u4703 : Upper (D 3) (R 3) [96,12,129,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4703
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4704 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 265 146 113 113 241 369), lower := (rows 97 14 133 265 146 32 64 128 256), losses := [] }

theorem u4704 : Upper (D 3) (R 3) [96,12,129,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4704
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4705 : Route 9 := (fun mask => (mask,id))

def c4705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4705 : Upper (D 3) (R 3) [96,12,129,257,160] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,160] 13 (by decide) (choices 1) [1,2,16,64] r4705 c4705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1723
  · exact u1724
  · exact u1725
  · exact u1726

def b4706 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 266 49 241 209 209 465), lower := (rows 97 14 133 266 49 32 64 128 256), losses := [] }

theorem u4706 : Upper (D 3) (R 3) [96,12,129,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4706
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4707 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 266 112 177 209 145 401), lower := (rows 97 14 133 266 112 32 64 128 256), losses := [] }

theorem u4707 : Upper (D 3) (R 3) [96,12,129,258,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4707
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4708 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 133 266 145 113 113 241 369), lower := (rows 97 14 133 266 145 32 64 128 256), losses := [] }

theorem u4708 : Upper (D 3) (R 3) [96,12,129,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4708
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4709 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 266 176 113 81 209 337), lower := (rows 97 14 133 266 176 32 64 128 256), losses := [] }

theorem u4709 : Upper (D 3) (R 3) [96,12,129,258,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4709
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4710 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 280 49 227 195 195 451), lower := (rows 97 14 133 280 49 32 64 128 256), losses := [] }

theorem u4710 : Upper (D 3) (R 3) [96,12,129,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4710
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4711 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5)], upper := (rows 97 14 133 280 50 225 193 193 449), lower := (rows 97 14 133 280 50 32 64 128 256), losses := [] }

theorem u4711 : Upper (D 3) (R 3) [96,12,129,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4711
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4712 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 280 112 163 195 131 387), lower := (rows 97 14 133 280 112 32 64 128 256), losses := [] }

theorem u4712 : Upper (D 3) (R 3) [96,12,129,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4712
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4713 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 133 280 145 99 99 227 355), lower := (rows 97 14 133 280 145 32 64 128 256), losses := [] }

theorem u4713 : Upper (D 3) (R 3) [96,12,129,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4713
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4714 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 280 146 97 97 225 353), lower := (rows 97 14 133 280 146 32 64 128 256), losses := [] }

theorem u4714 : Upper (D 3) (R 3) [96,12,129,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4714
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4715 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 280 176 99 67 195 323), lower := (rows 97 14 133 280 176 32 64 128 256), losses := [] }

theorem u4715 : Upper (D 3) (R 3) [96,12,129,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4715
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4716 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 296 81 179 211 147 403), lower := (rows 97 14 133 296 81 32 64 128 256), losses := [] }

theorem u4716 : Upper (D 3) (R 3) [96,12,129,288,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4716
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4717 : Route 9 := (fun mask => (mask,id))

def c4717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4717 : Upper (D 3) (R 3) [96,12,129,288,66] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,66] 13 (by decide) (choices 1) [1,16,128] r4717 c4717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1727
  · exact u1728
  · exact u1729

def b4718 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 133 296 145 115 83 211 339), lower := (rows 97 14 133 296 145 32 64 128 256), losses := [] }

theorem u4718 : Upper (D 3) (R 3) [96,12,129,288,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4718
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4719 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 146 113 81 209 337), lower := (rows 97 14 133 296 146 32 64 128 256), losses := [] }

theorem u4719 : Upper (D 3) (R 3) [96,12,129,288,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4719
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4720 : Route 9 := (fun mask => (mask,id))

def c4720 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4720 : Upper (D 3) (R 3) [96,12,129,288,192] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,192] 13 (by decide) (choices 1) [1,2,16] r4720 c4720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1730
  · exact u1731
  · exact u1732

def b4721 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 392 50 113 81 209 337), lower := (rows 97 14 133 392 50 32 64 128 256), losses := [] }

theorem u4721 : Upper (D 3) (R 3) [96,12,129,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4721
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4722 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 152 273 97 97 225 353), lower := (rows 97 14 134 152 273 32 64 128 256), losses := [] }

theorem u4722 : Upper (D 3) (R 3) [96,12,130,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4722
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4723 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 152 304 97 65 193 321), lower := (rows 97 14 134 152 304 32 64 128 256), losses := [] }

theorem u4723 : Upper (D 3) (R 3) [96,12,130,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4723
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4724 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 168 273 113 81 209 337), lower := (rows 97 14 134 168 273 32 64 128 256), losses := [] }

theorem u4724 : Upper (D 3) (R 3) [96,12,130,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4724
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4725 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 168 336 49 81 145 273), lower := (rows 97 14 134 168 336 32 64 128 256), losses := [] }

theorem u4725 : Upper (D 3) (R 3) [96,12,130,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4725
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4726 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 134 265 49 241 209 209 465), lower := (rows 97 14 134 265 49 32 64 128 256), losses := [] }

theorem u4726 : Upper (D 3) (R 3) [96,12,130,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4726
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4727 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 134 265 112 177 209 145 401), lower := (rows 97 14 134 265 112 32 64 128 256), losses := [] }

theorem u4727 : Upper (D 3) (R 3) [96,12,130,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4727
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4728 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 265 145 113 113 241 369), lower := (rows 97 14 134 265 145 32 64 128 256), losses := [] }

theorem u4728 : Upper (D 3) (R 3) [96,12,130,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4728
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4729 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 265 176 113 81 209 337), lower := (rows 97 14 134 265 176 32 64 128 256), losses := [] }

theorem u4729 : Upper (D 3) (R 3) [96,12,130,257,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4729
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4730 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 134 280 49 225 193 193 449), lower := (rows 97 14 134 280 49 32 64 128 256), losses := [] }

theorem u4730 : Upper (D 3) (R 3) [96,12,130,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4730
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4731 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 134 280 112 161 193 129 385), lower := (rows 97 14 134 280 112 32 64 128 256), losses := [] }

theorem u4731 : Upper (D 3) (R 3) [96,12,130,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4731
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4732 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 280 145 97 97 225 353), lower := (rows 97 14 134 280 145 32 64 128 256), losses := [] }

theorem u4732 : Upper (D 3) (R 3) [96,12,130,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4732
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4733 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 280 176 97 65 193 321), lower := (rows 97 14 134 280 176 32 64 128 256), losses := [] }

theorem u4733 : Upper (D 3) (R 3) [96,12,130,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4733
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4734 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 296 145 113 81 209 337), lower := (rows 97 14 134 296 145 32 64 128 256), losses := [] }

theorem u4734 : Upper (D 3) (R 3) [96,12,130,288,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4734
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4735 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 296 208 49 81 145 273), lower := (rows 97 14 134 296 208 32 64 128 256), losses := [] }

theorem u4735 : Upper (D 3) (R 3) [96,12,130,288,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4735
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4736 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 82 289 321 385 257), lower := (rows 97 14 148 168 82 32 64 128 256), losses := [] }

theorem u4736 : Upper (D 3) (R 3) [96,12,144,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4736
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4737 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 273 99 67 195 323), lower := (rows 97 14 148 168 273 32 64 128 256), losses := [] }

theorem u4737 : Upper (D 3) (R 3) [96,12,144,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4737
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4738 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 274 97 65 193 321), lower := (rows 97 14 148 168 274 32 64 128 256), losses := [] }

theorem u4738 : Upper (D 3) (R 3) [96,12,144,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4738
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4739 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 336 35 67 131 259), lower := (rows 97 14 148 168 336 32 64 128 256), losses := [] }

theorem u4739 : Upper (D 3) (R 3) [96,12,144,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4739
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4739
end Delivery.IrregularNine14.P03
