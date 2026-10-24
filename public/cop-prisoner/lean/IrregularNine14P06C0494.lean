import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0185
import IrregularNine14P06C0186
import IrregularNine14P06C0187

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r29640 : Route 9 := (fun mask => (mask,id))

def c29640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29640 : Upper (D 6) (R 6) [6,129,288,34,65] 13 := by
  apply FastRouting.sound _ _ [6,129,288,34,65] 13 (by decide) (choices 1) [4,8,16,64] r29640 c29640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11151
  · exact u11152
  · exact u11153
  · exact u11154

def r29641 : Route 9 := (fun mask => (mask,id))

def c29641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29641 : Upper (D 6) (R 6) [6,129,288,34,68] 13 := by
  apply FastRouting.sound _ _ [6,129,288,34,68] 13 (by decide) (choices 1) [1,8,16,64] r29641 c29641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11155
  · exact u11156
  · exact u11157
  · exact u11158

def r29642 : Route 9 := (fun mask => (mask,id))

def c29642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29642 : Upper (D 6) (R 6) [6,129,288,34,72] 13 := by
  apply FastRouting.sound _ _ [6,129,288,34,72] 13 (by decide) (choices 1) [1,4,16,64] r29642 c29642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11159
  · exact u11160
  · exact u11161
  · exact u11162

def b29643 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 131 292 44 81 122 90 218 346), lower := (rows 7 131 292 44 81 32 64 128 256), losses := [] }

theorem u29643 : Upper (D 6) (R 6) [6,129,288,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29643
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29644 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 131 292 44 82 121 89 217 345), lower := (rows 7 131 292 44 82 32 64 128 256), losses := [] }

theorem u29644 : Upper (D 6) (R 6) [6,129,288,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29644
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29645 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 131 292 44 88 115 83 211 339), lower := (rows 7 131 292 44 88 32 64 128 256), losses := [] }

theorem u29645 : Upper (D 6) (R 6) [6,129,288,36,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29645
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29646 : Route 9 := (fun mask => (mask,id))

def c29646 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29646 : Upper (D 6) (R 6) [6,129,288,48,65] 13 := by
  apply FastRouting.sound _ _ [6,129,288,48,65] 13 (by decide) (choices 1) [2,4,8,64] r29646 c29646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11163
  · exact u11164
  · exact u11165
  · exact u11166

def r29647 : Route 9 := (fun mask => (mask,id))

def c29647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29647 : Upper (D 6) (R 6) [6,129,288,48,66] 13 := by
  apply FastRouting.sound _ _ [6,129,288,48,66] 13 (by decide) (choices 1) [1,4,8,64] r29647 c29647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11167
  · exact u11168
  · exact u11169
  · exact u11170

def r29648 : Route 9 := (fun mask => (mask,id))

def c29648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29648 : Upper (D 6) (R 6) [6,129,288,48,68] 13 := by
  apply FastRouting.sound _ _ [6,129,288,48,68] 13 (by decide) (choices 1) [1,2,8,64] r29648 c29648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11171
  · exact u11172
  · exact u11173
  · exact u11174

def r29649 : Route 9 := (fun mask => (mask,id))

def c29649 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29649 : Upper (D 6) (R 6) [6,129,288,48,72] 13 := by
  apply FastRouting.sound _ _ [6,129,288,48,72] 13 (by decide) (choices 1) [1,2,4,64] r29649 c29649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11175
  · exact u11176
  · exact u11177
  · exact u11178

def r29650 : Route 9 := (fun mask => (mask,id))

def c29650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29650 : Upper (D 6) (R 6) [6,129,288,65,66] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65,66] 13 (by decide) (choices 1) [4,8,16] r29650 c29650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11179
  · exact u11180
  · exact u11181

def r29651 : Route 9 := (fun mask => (mask,id))

def c29651 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29651 : Upper (D 6) (R 6) [6,129,288,65,68] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65,68] 13 (by decide) (choices 1) [2,8,16] r29651 c29651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11182
  · exact u11183
  · exact u11184

def b29652 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 292 73 88 54 118 182 310), lower := (rows 7 131 292 73 88 32 64 128 256), losses := [] }

theorem u29652 : Upper (D 6) (R 6) [6,129,288,65,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29652
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29653 : Route 9 := (fun mask => (mask,id))

def c29653 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29653 : Upper (D 6) (R 6) [6,129,288,65,96] 13 := by
  apply FastRouting.sound _ _ [6,129,288,65,96] 13 (by decide) (choices 1) [2,4,8,16] r29653 c29653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11185
  · exact u11186
  · exact u11187
  · exact u11188

def r29654 : Route 9 := (fun mask => (mask,id))

def c29654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29654 : Upper (D 6) (R 6) [6,129,288,66,68] 13 := by
  apply FastRouting.sound _ _ [6,129,288,66,68] 13 (by decide) (choices 1) [1,8,16] r29654 c29654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11189
  · exact u11190
  · exact u11191

def b29655 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 292 74 88 53 117 181 309), lower := (rows 7 131 292 74 88 32 64 128 256), losses := [] }

theorem u29655 : Upper (D 6) (R 6) [6,129,288,66,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29655
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29656 : Route 9 := (fun mask => (mask,id))

def c29656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29656 : Upper (D 6) (R 6) [6,129,288,66,96] 13 := by
  apply FastRouting.sound _ _ [6,129,288,66,96] 13 (by decide) (choices 1) [1,4,8,16] r29656 c29656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11192
  · exact u11193
  · exact u11194
  · exact u11195

def b29657 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 292 76 88 51 115 179 307), lower := (rows 7 131 292 76 88 32 64 128 256), losses := [] }

theorem u29657 : Upper (D 6) (R 6) [6,129,288,68,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29657
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29658 : Route 9 := (fun mask => (mask,id))

def c29658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29658 : Upper (D 6) (R 6) [6,129,288,68,96] 13 := by
  apply FastRouting.sound _ _ [6,129,288,68,96] 13 (by decide) (choices 1) [1,2,8,16] r29658 c29658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11196
  · exact u11197
  · exact u11198
  · exact u11199

def b29659 : PairBound 9 := { available := 39, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 292 88 88 39 103 167 295), lower := (rows 7 131 292 88 88 32 64 128 256), losses := [] }

theorem u29659 : Upper (D 6) (R 6) [6,129,288,80,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29659
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29660 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 292 88 112 47 79 143 271), lower := (rows 7 131 292 88 112 32 64 128 256), losses := [] }

theorem u29660 : Upper (D 6) (R 6) [6,129,288,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29660
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29661 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 138 276 11 49 100 100 228 356), lower := (rows 7 138 276 11 49 32 64 128 256), losses := [] }

theorem u29661 : Upper (D 6) (R 6) [6,136,272,3,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29661
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29662 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 138 276 11 52 97 97 225 353), lower := (rows 7 138 276 11 52 32 64 128 256), losses := [] }

theorem u29662 : Upper (D 6) (R 6) [6,136,272,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29662
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29663 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 138 276 11 112 101 101 229 357), lower := (rows 7 138 276 11 112 32 64 128 256), losses := [] }

theorem u29663 : Upper (D 6) (R 6) [6,136,272,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29663
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29664 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 138 276 13 49 98 98 226 354), lower := (rows 7 138 276 13 49 32 64 128 256), losses := [] }

theorem u29664 : Upper (D 6) (R 6) [6,136,272,5,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29664
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29665 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 226, targets := 4 }], pairs := [(1,2),(3,5),(3,6)], upper := (rows 7 138 276 13 50 97 97 225 353), lower := (rows 7 138 276 13 50 32 64 128 256), losses := [] }

theorem u29665 : Upper (D 6) (R 6) [6,136,272,5,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29665
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29666 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 138 276 13 112 99 99 227 355), lower := (rows 7 138 276 13 112 32 64 128 256), losses := [] }

theorem u29666 : Upper (D 6) (R 6) [6,136,272,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29666
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29667 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 138 276 14 49 97 97 225 353), lower := (rows 7 138 276 14 49 32 64 128 256), losses := [] }

theorem u29667 : Upper (D 6) (R 6) [6,136,272,6,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29667
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29668 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 138 276 14 112 97 97 225 353), lower := (rows 7 138 276 14 112 32 64 128 256), losses := [] }

theorem u29668 : Upper (D 6) (R 6) [6,136,272,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29668
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29669 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 7 138 276 41 49 102 70 198 326), lower := (rows 7 138 276 41 49 32 64 128 256), losses := [] }

theorem u29669 : Upper (D 6) (R 6) [6,136,272,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29669
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29670 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 325, targets := 32 },{ cop := 0, region := 104, targets := 2 }], pairs := [(0,5),(2,5),(3,1)], upper := (rows 7 138 276 41 50 101 69 197 325), lower := (rows 7 138 276 41 50 32 64 128 256), losses := [] }

theorem u29670 : Upper (D 6) (R 6) [6,136,272,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29670
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29671 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 138 276 41 52 99 67 195 323), lower := (rows 7 138 276 41 52 32 64 128 256), losses := [] }

theorem u29671 : Upper (D 6) (R 6) [6,136,272,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29671
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29672 : Route 9 := (fun mask => (mask,id))

def c29672 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29672 : Upper (D 6) (R 6) [6,136,272,33,65] 13 := by
  apply FastRouting.sound _ _ [6,136,272,33,65] 13 (by decide) (choices 1) [2,4,64] r29672 c29672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11200
  · exact u11201
  · exact u11202

def r29673 : Route 9 := (fun mask => (mask,id))

def c29673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29673 : Upper (D 6) (R 6) [6,136,272,33,66] 13 := by
  apply FastRouting.sound _ _ [6,136,272,33,66] 13 (by decide) (choices 1) [1,4,64] r29673 c29673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11203
  · exact u11204
  · exact u11205

def r29674 : Route 9 := (fun mask => (mask,id))

def c29674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29674 : Upper (D 6) (R 6) [6,136,272,33,68] 13 := by
  apply FastRouting.sound _ _ [6,136,272,33,68] 13 (by decide) (choices 1) [1,2,64] r29674 c29674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11206
  · exact u11207
  · exact u11208

def r29675 : Route 9 := (fun mask => (mask,id))

def c29675 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29675 : Upper (D 6) (R 6) [6,136,272,33,96] 13 := by
  apply FastRouting.sound _ _ [6,136,272,33,96] 13 (by decide) (choices 1) [1,2,4,64] r29675 c29675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11209
  · exact u11210
  · exact u11211
  · exact u11212

def b29676 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 138 276 42 52 97 65 193 321), lower := (rows 7 138 276 42 52 32 64 128 256), losses := [] }

theorem u29676 : Upper (D 6) (R 6) [6,136,272,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29676
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29677 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 138 276 42 84 97 97 225 353), lower := (rows 7 138 276 42 84 32 64 128 256), losses := [] }

theorem u29677 : Upper (D 6) (R 6) [6,136,272,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29677
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29678 : Route 9 := (fun mask => (mask,id))

def c29678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29678 : Upper (D 6) (R 6) [6,136,272,34,96] 13 := by
  apply FastRouting.sound _ _ [6,136,272,34,96] 13 (by decide) (choices 1) [1,4,64] r29678 c29678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11213
  · exact u11214
  · exact u11215

def b29679 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 104, targets := 2 }], pairs := [(0,5),(1,5),(3,1)], upper := (rows 7 138 276 44 50 97 65 193 321), lower := (rows 7 138 276 44 50 32 64 128 256), losses := [] }

theorem u29679 : Upper (D 6) (R 6) [6,136,272,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29679
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29680 : Route 9 := (fun mask => (mask,id))

def c29680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29680 : Upper (D 6) (R 6) [6,136,272,36,66] 13 := by
  apply FastRouting.sound _ _ [6,136,272,36,66] 13 (by decide) (choices 1) [1,64] r29680 c29680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11216
  · exact u11217

def b29681 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 7 138 276 44 112 99 67 195 323), lower := (rows 7 138 276 44 112 32 64 128 256), losses := [] }

theorem u29681 : Upper (D 6) (R 6) [6,136,272,36,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29681
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29682 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 138 276 104 112 39 71 135 263), lower := (rows 7 138 276 104 112 32 64 128 256), losses := [] }

theorem u29682 : Upper (D 6) (R 6) [6,136,272,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29682
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29683 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 138 292 25 19 100 100 228 356), lower := (rows 7 138 292 25 19 32 64 128 256), losses := [] }

theorem u29683 : Upper (D 6) (R 6) [6,136,288,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29683
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29684 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 138 292 25 21 98 98 226 354), lower := (rows 7 138 292 25 21 32 64 128 256), losses := [] }

theorem u29684 : Upper (D 6) (R 6) [6,136,288,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29684
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29685 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 138 292 25 22 97 97 225 353), lower := (rows 7 138 292 25 22 32 64 128 256), losses := [] }

theorem u29685 : Upper (D 6) (R 6) [6,136,288,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29685
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29686 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 138 292 25 49 102 70 198 326), lower := (rows 7 138 292 25 49 32 64 128 256), losses := [] }

theorem u29686 : Upper (D 6) (R 6) [6,136,288,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29686
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29687 : Route 9 := (fun mask => (mask,id))

def c29687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29687 : Upper (D 6) (R 6) [6,136,288,17,34] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,34] 13 (by decide) (choices 1) [1,4,64] r29687 c29687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11218
  · exact u11219
  · exact u11220

def b29688 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 138 292 25 52 99 67 195 323), lower := (rows 7 138 292 25 52 32 64 128 256), losses := [] }

theorem u29688 : Upper (D 6) (R 6) [6,136,288,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29688
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29689 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 138 292 25 81 102 102 230 358), lower := (rows 7 138 292 25 81 32 64 128 256), losses := [] }

theorem u29689 : Upper (D 6) (R 6) [6,136,288,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29689
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29690 : Route 9 := (fun mask => (mask,id))

def c29690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29690 : Upper (D 6) (R 6) [6,136,288,17,66] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,66] 13 (by decide) (choices 1) [1,4,64] r29690 c29690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11221
  · exact u11222
  · exact u11223

def r29691 : Route 9 := (fun mask => (mask,id))

def c29691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29691 : Upper (D 6) (R 6) [6,136,288,17,68] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,68] 13 (by decide) (choices 1) [1,2,64] r29691 c29691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11224
  · exact u11225
  · exact u11226

def r29692 : Route 9 := (fun mask => (mask,id))

def c29692 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29692 : Upper (D 6) (R 6) [6,136,288,17,96] 13 := by
  apply FastRouting.sound _ _ [6,136,288,17,96] 13 (by decide) (choices 1) [1,2,4,64] r29692 c29692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11227
  · exact u11228
  · exact u11229
  · exact u11230

def b29693 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 138 292 26 21 97 97 225 353), lower := (rows 7 138 292 26 21 32 64 128 256), losses := [] }

theorem u29693 : Upper (D 6) (R 6) [6,136,288,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29693
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29694 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 372, targets := 2 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 7 138 292 26 49 101 69 197 325), lower := (rows 7 138 292 26 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 24 16 0 65 129 257), good := (rows 455 138 260 26 475 0 64 128 256) }] }

theorem u29694 : Upper (D 6) (R 6) [6,136,288,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29694
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29695 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 138 292 26 52 97 65 193 321), lower := (rows 7 138 292 26 52 32 64 128 256), losses := [] }

theorem u29695 : Upper (D 6) (R 6) [6,136,288,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29695
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29696 : Route 9 := (fun mask => (mask,id))

def c29696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29696 : Upper (D 6) (R 6) [6,136,288,18,65] 13 := by
  apply FastRouting.sound _ _ [6,136,288,18,65] 13 (by decide) (choices 1) [1,4,64] r29696 c29696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11231
  · exact u11232
  · exact u11233

def r29697 : Route 9 := (fun mask => (mask,id))

def c29697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29697 : Upper (D 6) (R 6) [6,136,288,18,68] 13 := by
  apply FastRouting.sound _ _ [6,136,288,18,68] 13 (by decide) (choices 1) [1,64] r29697 c29697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11234
  · exact u11235

def r29698 : Route 9 := (fun mask => (mask,id))

def c29698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29698 : Upper (D 6) (R 6) [6,136,288,18,96] 13 := by
  apply FastRouting.sound _ _ [6,136,288,18,96] 13 (by decide) (choices 1) [1,4,64] r29698 c29698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11236
  · exact u11237
  · exact u11238

def b29699 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 138 292 28 19 97 97 225 353), lower := (rows 7 138 292 28 19 32 64 128 256), losses := [] }

theorem u29699 : Upper (D 6) (R 6) [6,136,288,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29699
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29699
end Delivery.IrregularNine14.P06
