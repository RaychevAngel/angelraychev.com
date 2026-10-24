import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0126
import IrregularNine14P07C0127

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r23700 : Route 9 := (fun mask => (mask,id))

def c23700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23700 : Upper (D 7) (R 7) [36,96,10,192,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,10,192,257,16] 13 (by decide) (choices 1) [1,2,128] r23700 c23700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7606
  · exact u7607
  · exact u7608

def b23701 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(1,7),(4,6),(4,7)], upper := (rows 37 98 14 200 273 160 83 147 275), lower := (rows 37 98 14 200 273 160 64 128 256), losses := [] }

theorem u23701 : Upper (D 7) (R 7) [36,96,10,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23702 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 200 274 33 209 145 401), lower := (rows 37 98 14 200 274 33 64 128 256), losses := [] }

theorem u23702 : Upper (D 7) (R 7) [36,96,10,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23703 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(3,1),(3,5)], upper := (rows 37 98 14 200 274 48 193 129 385), lower := (rows 37 98 14 200 274 48 64 128 256), losses := [] }

theorem u23703 : Upper (D 7) (R 7) [36,96,10,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23703 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23704 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(1,7),(4,6),(4,7)], upper := (rows 37 98 14 200 274 160 81 145 273), lower := (rows 37 98 14 200 274 160 64 128 256), losses := [] }

theorem u23704 : Upper (D 7) (R 7) [36,96,10,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23705 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 200 400 33 83 147 275), lower := (rows 37 98 14 200 400 33 64 128 256), losses := [] }

theorem u23705 : Upper (D 7) (R 7) [36,96,10,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23706 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 200 400 34 81 145 273), lower := (rows 37 98 14 200 400 34 64 128 256), losses := [] }

theorem u23706 : Upper (D 7) (R 7) [36,96,10,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23707 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,7),(4,6)], upper := (rows 37 98 14 200 400 48 67 131 259), lower := (rows 37 98 14 200 400 48 64 128 256), losses := [] }

theorem u23707 : Upper (D 7) (R 7) [36,96,10,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23707 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23708 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 265 81 34 208 144 400), lower := (rows 37 98 14 265 81 34 64 128 256), losses := [] }

theorem u23708 : Upper (D 7) (R 7) [36,96,10,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23709 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 265 81 48 194 130 386), lower := (rows 37 98 14 265 81 48 64 128 256), losses := [] }

theorem u23709 : Upper (D 7) (R 7) [36,96,10,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23709 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23710 : Route 9 := (fun mask => (mask,id))

def c23710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23710 : Upper (D 7) (R 7) [36,96,10,257,65,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257,65,128] 13 (by decide) (choices 1) [2,16,128] r23710 c23710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7609
  · exact u7610
  · exact u7611

def b23711 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 265 145 34 208 208 464), lower := (rows 37 98 14 265 145 34 64 128 256), losses := [] }

theorem u23711 : Upper (D 7) (R 7) [36,96,10,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23712 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(2,0),(3,5)], upper := (rows 37 98 14 265 145 48 194 194 450), lower := (rows 37 98 14 265 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 51 12 8 16 48 127 191 319), good := (rows 486 482 462 462 498 498 64 128 256) },{ target := 5, region := (rows 1 2 4 9 17 0 70 134 262), good := (rows 477 450 462 281 153 16 64 128 256) }] }

theorem u23712 : Upper (D 7) (R 7) [36,96,10,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23712 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23713 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 265 145 96 210 146 402), lower := (rows 37 98 14 265 145 96 64 128 256), losses := [] }

theorem u23713 : Upper (D 7) (R 7) [36,96,10,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23714 : Route 9 := (fun mask => (mask,id))

def c23714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23714 : Upper (D 7) (R 7) [36,96,10,257,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257,129,128] 13 (by decide) (choices 1) [2,16] r23714 c23714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7612
  · exact u7613

def b23715 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 265 146 33 208 208 464), lower := (rows 37 98 14 265 146 33 64 128 256), losses := [] }

theorem u23715 : Upper (D 7) (R 7) [36,96,10,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23716 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 456, targets := 34 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 37 98 14 265 146 48 193 193 449), lower := (rows 37 98 14 265 146 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 20 0 73 137 265), good := (rows 477 66 478 457 146 16 64 128 256) }] }

theorem u23716 : Upper (D 7) (R 7) [36,96,10,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23716 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23717 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 265 146 96 209 145 401), lower := (rows 37 98 14 265 146 96 64 128 256), losses := [] }

theorem u23717 : Upper (D 7) (R 7) [36,96,10,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23718 : Route 9 := (fun mask => (mask,id))

def c23718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23718 : Upper (D 7) (R 7) [36,96,10,257,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257,130,128] 13 (by decide) (choices 1) [1,16] r23718 c23718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7614
  · exact u7615

def b23719 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 265 208 33 210 146 402), lower := (rows 37 98 14 265 208 33 64 128 256), losses := [] }

theorem u23719 : Upper (D 7) (R 7) [36,96,10,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23720 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 265 208 34 209 145 401), lower := (rows 37 98 14 265 208 34 64 128 256), losses := [] }

theorem u23720 : Upper (D 7) (R 7) [36,96,10,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23721 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 265 208 48 195 131 387), lower := (rows 37 98 14 265 208 48 64 128 256), losses := [] }

theorem u23721 : Upper (D 7) (R 7) [36,96,10,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23721 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23722 : Route 9 := (fun mask => (mask,id))

def c23722 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23722 : Upper (D 7) (R 7) [36,96,10,257,192,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257,192,128] 13 (by decide) (choices 1) [1,2,16] r23722 c23722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7616
  · exact u7617
  · exact u7618

def b23723 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 0, region := 194, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 280 81 33 194 130 386), lower := (rows 37 98 14 280 81 33 64 128 256), losses := [] }

theorem u23723 : Upper (D 7) (R 7) [36,96,10,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23724 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 280 81 34 193 129 385), lower := (rows 37 98 14 280 81 34 64 128 256), losses := [] }

theorem u23724 : Upper (D 7) (R 7) [36,96,10,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23725 : Route 9 := (fun mask => (mask,id))

def c23725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23725 : Upper (D 7) (R 7) [36,96,10,272,65,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272,65,128] 13 (by decide) (choices 1) [1,2,128] r23725 c23725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7619
  · exact u7620
  · exact u7621

def b23726 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 280 145 33 194 194 450), lower := (rows 37 98 14 280 145 33 64 128 256), losses := [] }

theorem u23726 : Upper (D 7) (R 7) [36,96,10,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23727 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 280 145 34 193 193 449), lower := (rows 37 98 14 280 145 34 64 128 256), losses := [] }

theorem u23727 : Upper (D 7) (R 7) [36,96,10,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23728 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 280 145 96 195 131 387), lower := (rows 37 98 14 280 145 96 64 128 256), losses := [] }

theorem u23728 : Upper (D 7) (R 7) [36,96,10,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23729 : Route 9 := (fun mask => (mask,id))

def c23729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23729 : Upper (D 7) (R 7) [36,96,10,272,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272,129,128] 13 (by decide) (choices 1) [1,2] r23729 c23729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7622
  · exact u7623

def b23730 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 98 14 280 146 33 193 193 449), lower := (rows 37 98 14 280 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 22 10 18 0 97 161 289), good := (rows 453 478 30 284 158 449 64 128 256) }] }

theorem u23730 : Upper (D 7) (R 7) [36,96,10,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23731 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 280 146 96 193 129 385), lower := (rows 37 98 14 280 146 96 64 128 256), losses := [] }

theorem u23731 : Upper (D 7) (R 7) [36,96,10,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23732 : Route 9 := (fun mask => (mask,id))

def c23732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23732 : Upper (D 7) (R 7) [36,96,10,272,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272,130,128] 13 (by decide) (choices 1) [1] r23732 c23732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u7624

def r23733 : Route 9 := (fun mask => (mask,id))

def c23733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23733 : Upper (D 7) (R 7) [36,96,10,272,192,1] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272,192,1] 13 (by decide) (choices 1) [1,2,128] r23733 c23733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7625
  · exact u7626
  · exact u7627

def b23734 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 280 208 34 193 129 385), lower := (rows 37 98 14 280 208 34 64 128 256), losses := [] }

theorem u23734 : Upper (D 7) (R 7) [36,96,10,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23735 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 161, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(1,7),(2,0)], upper := (rows 37 98 14 280 208 160 67 131 259), lower := (rows 37 98 14 280 208 160 64 128 256), losses := [{ target := 0, region := (rows 0 18 12 8 16 176 64 128 256), good := (rows 36 98 14 318 242 160 64 160 256) }] }

theorem u23735 : Upper (D 7) (R 7) [36,96,10,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23736 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 328 145 33 210 146 402), lower := (rows 37 98 14 328 145 33 64 128 256), losses := [] }

theorem u23736 : Upper (D 7) (R 7) [36,96,10,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23737 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 328 145 34 209 145 401), lower := (rows 37 98 14 328 145 34 64 128 256), losses := [] }

theorem u23737 : Upper (D 7) (R 7) [36,96,10,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23738 : Route 9 := (fun mask => (mask,id))

def c23738 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23738 : Upper (D 7) (R 7) [36,96,10,320,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,10,320,129,16] 13 (by decide) (choices 1) [1,2,128] r23738 c23738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7628
  · exact u7629
  · exact u7630

def r23739 : Route 9 := (fun mask => (mask,id))

def c23739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23739 : Upper (D 7) (R 7) [36,96,10,320,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,320,129,128] 13 (by decide) (choices 1) [1,2,16] r23739 c23739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7631
  · exact u7632
  · exact u7633

def b23740 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 328 146 33 209 145 401), lower := (rows 37 98 14 328 146 33 64 128 256), losses := [] }

theorem u23740 : Upper (D 7) (R 7) [36,96,10,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23741 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 456, targets := 34 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(3,5)], upper := (rows 37 98 14 328 146 48 193 129 385), lower := (rows 37 98 14 328 146 48 64 128 256), losses := [] }

theorem u23741 : Upper (D 7) (R 7) [36,96,10,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23741 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23742 : Route 9 := (fun mask => (mask,id))

def c23742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23742 : Upper (D 7) (R 7) [36,96,10,320,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,320,130,128] 13 (by decide) (choices 1) [1,16] r23742 c23742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7634
  · exact u7635

def b23743 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 98 14 392 19 33 208 208 464), lower := (rows 37 98 14 392 19 33 64 128 256), losses := [] }

theorem u23743 : Upper (D 7) (R 7) [36,96,10,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23744 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 98 14 392 19 48 193 193 449), lower := (rows 37 98 14 392 19 48 64 128 256), losses := [] }

theorem u23744 : Upper (D 7) (R 7) [36,96,10,384,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23744 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23745 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 392 19 96 209 145 401), lower := (rows 37 98 14 392 19 96 64 128 256), losses := [] }

theorem u23745 : Upper (D 7) (R 7) [36,96,10,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23746 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 98 14 392 19 160 81 209 337), lower := (rows 37 98 14 392 19 160 64 128 256), losses := [] }

theorem u23746 : Upper (D 7) (R 7) [36,96,10,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23747 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 14 392 81 33 210 146 402), lower := (rows 37 98 14 392 81 33 64 128 256), losses := [] }

theorem u23747 : Upper (D 7) (R 7) [36,96,10,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23748 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 392 81 34 209 145 401), lower := (rows 37 98 14 392 81 34 64 128 256), losses := [] }

theorem u23748 : Upper (D 7) (R 7) [36,96,10,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23749 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 392 81 48 195 131 387), lower := (rows 37 98 14 392 81 48 64 128 256), losses := [] }

theorem u23749 : Upper (D 7) (R 7) [36,96,10,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23749 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23750 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 82, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 14 392 81 160 83 147 275), lower := (rows 37 98 14 392 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 45 424 81 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 47 424 17 160 0 160 256) }] }

theorem u23750 : Upper (D 7) (R 7) [36,96,10,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23751 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 98, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 14 392 145 33 82 210 338), lower := (rows 37 98 14 392 145 33 64 128 256), losses := [] }

theorem u23751 : Upper (D 7) (R 7) [36,96,10,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23752 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 392 145 34 81 209 337), lower := (rows 37 98 14 392 145 34 64 128 256), losses := [] }

theorem u23752 : Upper (D 7) (R 7) [36,96,10,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23753 : Route 9 := (fun mask => (mask,id))

def c23753 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23753 : Upper (D 7) (R 7) [36,96,10,384,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384,129,16] 13 (by decide) (choices 1) [1,2] r23753 c23753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7636
  · exact u7637

def b23754 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 392 145 96 83 147 275), lower := (rows 37 98 14 392 145 96 64 128 256), losses := [] }

theorem u23754 : Upper (D 7) (R 7) [36,96,10,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23755 : Route 9 := (fun mask => (mask,id))

def c23755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23755 : Upper (D 7) (R 7) [36,96,10,384,130,1] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384,130,1] 13 (by decide) (choices 1) [1,16] r23755 c23755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7638
  · exact u7639

def b23756 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 456, targets := 34 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(3,1),(3,5)], upper := (rows 37 98 14 392 146 48 65 193 321), lower := (rows 37 98 14 392 146 48 64 128 256), losses := [] }

theorem u23756 : Upper (D 7) (R 7) [36,96,10,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23756 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23757 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 392 146 96 81 145 273), lower := (rows 37 98 14 392 146 96 64 128 256), losses := [] }

theorem u23757 : Upper (D 7) (R 7) [36,96,10,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23758 : Route 9 := (fun mask => (mask,id))

def c23758 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23758 : Upper (D 7) (R 7) [36,96,10,384,192,1] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384,192,1] 13 (by decide) (choices 1) [1,2,16] r23758 c23758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7640
  · exact u7641
  · exact u7642

def b23759 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 392 208 34 81 145 273), lower := (rows 37 98 14 392 208 34 64 128 256), losses := [] }

theorem u23759 : Upper (D 7) (R 7) [36,96,10,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23759
end Delivery.IrregularNine14.P07
