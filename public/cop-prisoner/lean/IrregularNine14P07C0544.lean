import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0267
import IrregularNine14P07C0268

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32640 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,7),(3,5),(4,5)], upper := (rows 13 35 100 392 145 114 82 210 338), lower := (rows 13 35 100 392 145 32 64 128 256), losses := [] }

theorem u32640 : Upper (D 7) (R 7) [12,33,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32641 : Route 9 := (fun mask => (mask,id))

def c32641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32641 : Upper (D 7) (R 7) [12,33,96,384,130] 13 := by
  apply FastRouting.sound _ _ [12,33,96,384,130] 13 (by decide) (choices 1) [1,2,16,64] r32641 c32641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16029
  · exact u16030
  · exact u16031
  · exact u16032

def r32642 : Route 9 := (fun mask => (mask,id))

def c32642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32642 : Upper (D 7) (R 7) [12,33,96,384,192] 13 := by
  apply FastRouting.sound _ _ [12,33,96,384,192] 13 (by decide) (choices 1) [1,2,16] r32642 c32642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16033
  · exact u16034
  · exact u16035

def b32643 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(0,5),(2,0),(2,5),(3,5)], upper := (rows 13 35 196 265 50 242 210 210 466), lower := (rows 13 35 196 265 50 32 64 128 256), losses := [] }

theorem u32643 : Upper (D 7) (R 7) [12,33,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32644 : Route 9 := (fun mask => (mask,id))

def c32644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32644 : Upper (D 7) (R 7) [12,33,192,257,66] 13 := by
  apply FastRouting.sound _ _ [12,33,192,257,66] 13 (by decide) (choices 1) [2,16,128] r32644 c32644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16036
  · exact u16037
  · exact u16038

def r32645 : Route 9 := (fun mask => (mask,id))

def c32645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32645 : Upper (D 7) (R 7) [12,33,192,257,96] 13 := by
  apply FastRouting.sound _ _ [12,33,192,257,96] 13 (by decide) (choices 1) [2,16,128] r32645 c32645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16039
  · exact u16040
  · exact u16041

def b32646 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 13 35 196 265 208 50 114 178 306), lower := (rows 13 35 196 265 208 32 64 128 256), losses := [] }

theorem u32646 : Upper (D 7) (R 7) [12,33,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32647 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 35 196 266 19 240 240 240 496), lower := (rows 13 35 196 266 19 32 64 128 256), losses := [] }

theorem u32647 : Upper (D 7) (R 7) [12,33,192,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32648 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 196 266 49 242 210 210 466), lower := (rows 13 35 196 266 49 32 64 128 256), losses := [] }

theorem u32648 : Upper (D 7) (R 7) [12,33,192,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32649 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 35 196 266 50 241 209 209 465), lower := (rows 13 35 196 266 50 32 64 128 256), losses := [] }

theorem u32649 : Upper (D 7) (R 7) [12,33,192,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32650 : Route 9 := (fun mask => (mask,id))

def c32650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32650 : Upper (D 7) (R 7) [12,33,192,258,65] 13 := by
  apply FastRouting.sound _ _ [12,33,192,258,65] 13 (by decide) (choices 1) [2,16,128] r32650 c32650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16042
  · exact u16043
  · exact u16044

def r32651 : Route 9 := (fun mask => (mask,id))

def c32651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32651 : Upper (D 7) (R 7) [12,33,192,258,66] 13 := by
  apply FastRouting.sound _ _ [12,33,192,258,66] 13 (by decide) (choices 1) [1,16,128] r32651 c32651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16045
  · exact u16046
  · exact u16047

def r32652 : Route 9 := (fun mask => (mask,id))

def c32652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32652 : Upper (D 7) (R 7) [12,33,192,258,96] 13 := by
  apply FastRouting.sound _ _ [12,33,192,258,96] 13 (by decide) (choices 1) [1,2,16,128] r32652 c32652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16048
  · exact u16049
  · exact u16050
  · exact u16051

def b32653 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 13 35 196 266 208 51 115 179 307), lower := (rows 13 35 196 266 208 32 64 128 256), losses := [] }

theorem u32653 : Upper (D 7) (R 7) [12,33,192,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32654 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 35 196 280 19 226 226 226 482), lower := (rows 13 35 196 280 19 32 64 128 256), losses := [] }

theorem u32654 : Upper (D 7) (R 7) [12,33,192,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32655 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 196 280 49 226 194 194 450), lower := (rows 13 35 196 280 49 32 64 128 256), losses := [] }

theorem u32655 : Upper (D 7) (R 7) [12,33,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32656 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 35 196 280 50 227 195 195 451), lower := (rows 13 35 196 280 50 32 64 128 256), losses := [] }

theorem u32656 : Upper (D 7) (R 7) [12,33,192,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32657 : Route 9 := (fun mask => (mask,id))

def c32657 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32657 : Upper (D 7) (R 7) [12,33,192,272,65] 13 := by
  apply FastRouting.sound _ _ [12,33,192,272,65] 13 (by decide) (choices 1) [2,128] r32657 c32657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16052
  · exact u16053

def r32658 : Route 9 := (fun mask => (mask,id))

def c32658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32658 : Upper (D 7) (R 7) [12,33,192,272,66] 13 := by
  apply FastRouting.sound _ _ [12,33,192,272,66] 13 (by decide) (choices 1) [1,2,128] r32658 c32658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16054
  · exact u16055
  · exact u16056

def r32659 : Route 9 := (fun mask => (mask,id))

def c32659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32659 : Upper (D 7) (R 7) [12,33,192,272,96] 13 := by
  apply FastRouting.sound _ _ [12,33,192,272,96] 13 (by decide) (choices 1) [1,2,128] r32659 c32659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16057
  · exact u16058
  · exact u16059

def b32660 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 13 35 196 280 208 35 99 163 291), lower := (rows 13 35 196 280 208 32 64 128 256), losses := [] }

theorem u32660 : Upper (D 7) (R 7) [12,33,192,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32661 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 35 196 296 19 242 210 210 466), lower := (rows 13 35 196 296 19 32 64 128 256), losses := [] }

theorem u32661 : Upper (D 7) (R 7) [12,33,192,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32662 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 13 35 196 296 81 178 210 146 402), lower := (rows 13 35 196 296 81 32 64 128 256), losses := [] }

theorem u32662 : Upper (D 7) (R 7) [12,33,192,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32663 : Route 9 := (fun mask => (mask,id))

def c32663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32663 : Upper (D 7) (R 7) [12,33,192,288,66] 13 := by
  apply FastRouting.sound _ _ [12,33,192,288,66] 13 (by decide) (choices 1) [1,2,16,128] r32663 c32663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16060
  · exact u16061
  · exact u16062
  · exact u16063

def b32664 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 13 35 196 296 208 51 83 147 275), lower := (rows 13 35 196 296 208 32 64 128 256), losses := [] }

theorem u32664 : Upper (D 7) (R 7) [12,33,192,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32665 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 16, targets := 160 }], pairs := [(1,6),(4,5),(4,6),(4,7)], upper := (rows 13 35 196 328 19 178 242 178 434), lower := (rows 13 35 196 328 19 32 64 128 256), losses := [] }

theorem u32665 : Upper (D 7) (R 7) [12,33,192,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32666 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 16, targets := 2 },{ cop := 1, region := 16, targets := 128 }], pairs := [(1,6),(4,1),(4,6),(4,7)], upper := (rows 13 35 196 328 49 178 210 146 402), lower := (rows 13 35 196 328 49 32 64 128 256), losses := [] }

theorem u32666 : Upper (D 7) (R 7) [12,33,192,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32667 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 35 196 328 50 179 211 147 403), lower := (rows 13 35 196 328 50 32 64 128 256), losses := [] }

theorem u32667 : Upper (D 7) (R 7) [12,33,192,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32668 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 13 35 196 328 145 50 114 178 306), lower := (rows 13 35 196 328 145 32 64 128 256), losses := [] }

theorem u32668 : Upper (D 7) (R 7) [12,33,192,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32669 : Route 9 := (fun mask => (mask,id))

def c32669 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32669 : Upper (D 7) (R 7) [12,33,192,320,130] 13 := by
  apply FastRouting.sound _ _ [12,33,192,320,130] 13 (by decide) (choices 1) [1,2,16] r32669 c32669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16064
  · exact u16065
  · exact u16066

def r32670 : Route 9 := (fun mask => (mask,id))

def c32670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32670 : Upper (D 7) (R 7) [12,33,192,320,160] 13 := by
  apply FastRouting.sound _ _ [12,33,192,320,160] 13 (by decide) (choices 1) [1,2,16] r32670 c32670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16067
  · exact u16068
  · exact u16069

def b32671 : PairBound 9 := { available := 448, camps := [{ cop := 5, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 7 73 50 480 448 448 448), lower := (rows 13 50 7 73 50 32 64 128 256), losses := [] }

theorem u32671 : Upper (D 7) (R 7) [12,48,3,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32672 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 7 73 82 416 480 416 416), lower := (rows 13 50 7 73 82 32 64 128 256), losses := [] }

theorem u32672 : Upper (D 7) (R 7) [12,48,3,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32673 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 73 112 418 450 386 386), lower := (rows 13 50 7 73 112 32 64 128 256), losses := [] }

theorem u32673 : Upper (D 7) (R 7) [12,48,3,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32674 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(1,0),(3,1),(4,0)], upper := (rows 13 50 7 73 146 480 480 480 480), lower := (rows 13 50 7 73 146 32 64 128 256), losses := [] }

theorem u32674 : Upper (D 7) (R 7) [12,48,3,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32675 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 7 73 176 482 450 450 450), lower := (rows 13 50 7 73 176 32 64 128 256), losses := [] }

theorem u32675 : Upper (D 7) (R 7) [12,48,3,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32676 : Route 9 := (fun mask => (mask,id))

def c32676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32676 : Upper (D 7) (R 7) [12,48,3,65,192] 13 := by
  apply FastRouting.sound _ _ [12,48,3,65,192] 13 (by decide) (choices 1) [2,128,256] r32676 c32676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16070
  · exact u16071
  · exact u16072

def b32677 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,1),(4,0)], upper := (rows 13 50 7 73 274 224 224 224 480), lower := (rows 13 50 7 73 274 32 64 128 256), losses := [] }

theorem u32677 : Upper (D 7) (R 7) [12,48,3,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32678 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 7 73 304 226 194 194 450), lower := (rows 13 50 7 73 304 32 64 128 256), losses := [] }

theorem u32678 : Upper (D 7) (R 7) [12,48,3,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32679 : Route 9 := (fun mask => (mask,id))

def c32679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32679 : Upper (D 7) (R 7) [12,48,3,65,320] 13 := by
  apply FastRouting.sound _ _ [12,48,3,65,320] 13 (by decide) (choices 1) [2,128] r32679 c32679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16073
  · exact u16074

def r32680 : Route 9 := (fun mask => (mask,id))

def c32680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32680 : Upper (D 7) (R 7) [12,48,3,65,384] 13 := by
  apply FastRouting.sound _ _ [12,48,3,65,384] 13 (by decide) (choices 1) [2,64,128] r32680 c32680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16075
  · exact u16076
  · exact u16077

def b32681 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 23, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 13 50 7 104 19 480 448 448 448), lower := (rows 13 50 7 104 19 32 64 128 256), losses := [] }

theorem u32681 : Upper (D 7) (R 7) [12,48,3,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32682 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 104 81 418 450 386 386), lower := (rows 13 50 7 104 81 32 64 128 256), losses := [] }

theorem u32682 : Upper (D 7) (R 7) [12,48,3,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32683 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 104 82 417 449 385 385), lower := (rows 13 50 7 104 82 32 64 128 256), losses := [] }

theorem u32683 : Upper (D 7) (R 7) [12,48,3,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32684 : Route 9 := (fun mask => (mask,id))

def c32684 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32684 : Upper (D 7) (R 7) [12,48,3,96,129] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,129] 13 (by decide) (choices 1) [2,64,128,256] r32684 c32684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16078
  · exact u16079
  · exact u16080
  · exact u16081

def r32685 : Route 9 := (fun mask => (mask,id))

def c32685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32685 : Upper (D 7) (R 7) [12,48,3,96,130] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,130] 13 (by decide) (choices 1) [1,64,128,256] r32685 c32685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16082
  · exact u16083
  · exact u16084
  · exact u16085

def r32686 : Route 9 := (fun mask => (mask,id))

def c32686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32686 : Upper (D 7) (R 7) [12,48,3,96,192] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,192] 13 (by decide) (choices 1) [1,2,128,256] r32686 c32686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16086
  · exact u16087
  · exact u16088
  · exact u16089

def r32687 : Route 9 := (fun mask => (mask,id))

def c32687 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32687 : Upper (D 7) (R 7) [12,48,3,96,257] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,257] 13 (by decide) (choices 1) [2,64,128] r32687 c32687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16090
  · exact u16091
  · exact u16092

def r32688 : Route 9 := (fun mask => (mask,id))

def c32688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32688 : Upper (D 7) (R 7) [12,48,3,96,258] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,258] 13 (by decide) (choices 1) [1,64,128] r32688 c32688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16093
  · exact u16094
  · exact u16095

def r32689 : Route 9 := (fun mask => (mask,id))

def c32689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32689 : Upper (D 7) (R 7) [12,48,3,96,320] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,320] 13 (by decide) (choices 1) [1,2,128] r32689 c32689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16096
  · exact u16097
  · exact u16098

def r32690 : Route 9 := (fun mask => (mask,id))

def c32690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32690 : Upper (D 7) (R 7) [12,48,3,96,384] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,384] 13 (by decide) (choices 1) [1,2,64,128] r32690 c32690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16099
  · exact u16100
  · exact u16101
  · exact u16102

def b32691 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 50 7 200 19 480 480 480 480), lower := (rows 13 50 7 200 19 32 64 128 256), losses := [] }

theorem u32691 : Upper (D 7) (R 7) [12,48,3,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32692 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 6, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 7 200 49 482 450 450 450), lower := (rows 13 50 7 200 49 32 64 128 256), losses := [] }

theorem u32692 : Upper (D 7) (R 7) [12,48,3,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32693 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 7 200 50 481 449 449 449), lower := (rows 13 50 7 200 50 32 64 128 256), losses := [] }

theorem u32693 : Upper (D 7) (R 7) [12,48,3,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32694 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 50 7 200 81 418 482 418 418), lower := (rows 13 50 7 200 81 32 64 128 256), losses := [] }

theorem u32694 : Upper (D 7) (R 7) [12,48,3,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32695 : Route 9 := (fun mask => (mask,id))

def c32695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32695 : Upper (D 7) (R 7) [12,48,3,192,66] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,66] 13 (by decide) (choices 1) [1,128,256] r32695 c32695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16103
  · exact u16104
  · exact u16105

def b32696 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 7 200 112 419 451 387 387), lower := (rows 13 50 7 200 112 32 64 128 256), losses := [] }

theorem u32696 : Upper (D 7) (R 7) [12,48,3,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32697 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 50 7 200 208 291 355 419 291), lower := (rows 13 50 7 200 208 32 64 128 256), losses := [] }

theorem u32697 : Upper (D 7) (R 7) [12,48,3,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32698 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32698 : Upper (D 7) (R 7) [12,48,3,192,257] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,257] 13 (by decide) (choices 1) [2,64] r32698 c32698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16106
  · exact u16107

def r32699 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32699 : Upper (D 7) (R 7) [12,48,3,192,258] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,258] 13 (by decide) (choices 1) [1,64] r32699 c32699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16108
  · exact u16109

#print axioms u32699
end Delivery.IrregularNine14.P07
