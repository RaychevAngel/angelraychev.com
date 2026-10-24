import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0089

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19680 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 88 145 34 329 393 265), lower := (rows 35 70 164 88 145 34 64 128 256), losses := [] }

theorem u19680 : Upper (D 7) (R 7) [34,68,160,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19681 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 145 40 323 387 259), lower := (rows 35 70 164 88 145 40 64 128 256), losses := [] }

theorem u19681 : Upper (D 7) (R 7) [34,68,160,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19681 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19682 : Route 9 := (fun mask => (mask,id))

def c19682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19682 : Upper (D 7) (R 7) [34,68,160,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,129,256] 13 (by decide) (choices 1) [1,2,8] r19682 c19682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5352
  · exact u5353
  · exact u5354

def b19683 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 88 273 33 202 138 394), lower := (rows 35 70 164 88 273 33 64 128 256), losses := [] }

theorem u19683 : Upper (D 7) (R 7) [34,68,160,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19684 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 88 273 34 201 137 393), lower := (rows 35 70 164 88 273 34 64 128 256), losses := [] }

theorem u19684 : Upper (D 7) (R 7) [34,68,160,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19685 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 273 40 195 131 387), lower := (rows 35 70 164 88 273 40 64 128 256), losses := [] }

theorem u19685 : Upper (D 7) (R 7) [34,68,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19685 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19686 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 88 273 160 75 139 267), lower := (rows 35 70 164 88 273 160 64 128 256), losses := [] }

theorem u19686 : Upper (D 7) (R 7) [34,68,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19687 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 88 274 33 201 137 393), lower := (rows 35 70 164 88 274 33 64 128 256), losses := [] }

theorem u19687 : Upper (D 7) (R 7) [34,68,160,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19688 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 274 40 193 129 385), lower := (rows 35 70 164 88 274 40 64 128 256), losses := [] }

theorem u19688 : Upper (D 7) (R 7) [34,68,160,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19688 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19689 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 88 274 160 73 137 265), lower := (rows 35 70 164 88 274 160 64 128 256), losses := [] }

theorem u19689 : Upper (D 7) (R 7) [34,68,160,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19690 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 88 400 33 75 139 267), lower := (rows 35 70 164 88 400 33 64 128 256), losses := [] }

theorem u19690 : Upper (D 7) (R 7) [34,68,160,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19691 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 88 400 34 73 137 265), lower := (rows 35 70 164 88 400 34 64 128 256), losses := [] }

theorem u19691 : Upper (D 7) (R 7) [34,68,160,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19692 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 400 40 67 131 259), lower := (rows 35 70 164 88 400 40 64 128 256), losses := [] }

theorem u19692 : Upper (D 7) (R 7) [34,68,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19692 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19693 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 137 273 34 88 216 344), lower := (rows 35 70 164 137 273 34 64 128 256), losses := [] }

theorem u19693 : Upper (D 7) (R 7) [34,68,160,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19694 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 70 164 137 273 40 82 210 338), lower := (rows 35 70 164 137 273 40 64 128 256), losses := [] }

theorem u19694 : Upper (D 7) (R 7) [34,68,160,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19694 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19695 : Route 9 := (fun mask => (mask,id))

def c19695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19695 : Upper (D 7) (R 7) [34,68,160,129,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,257,16] 13 (by decide) (choices 1) [2,8] r19695 c19695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5355
  · exact u5356

def b19696 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 137 273 96 90 154 282), lower := (rows 35 70 164 137 273 96 64 128 256), losses := [] }

theorem u19696 : Upper (D 7) (R 7) [34,68,160,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19697 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 137 274 33 88 216 344), lower := (rows 35 70 164 137 274 33 64 128 256), losses := [] }

theorem u19697 : Upper (D 7) (R 7) [34,68,160,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19698 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 70 164 137 274 40 81 209 337), lower := (rows 35 70 164 137 274 40 64 128 256), losses := [] }

theorem u19698 : Upper (D 7) (R 7) [34,68,160,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19698 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19699 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 70 164 137 274 48 73 201 329), lower := (rows 35 70 164 137 274 48 64 128 256), losses := [] }

theorem u19699 : Upper (D 7) (R 7) [34,68,160,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19699 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19700 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 137 274 96 89 153 281), lower := (rows 35 70 164 137 274 96 64 128 256), losses := [] }

theorem u19700 : Upper (D 7) (R 7) [34,68,160,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19701 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 137 280 33 82 210 338), lower := (rows 35 70 164 137 280 33 64 128 256), losses := [] }

theorem u19701 : Upper (D 7) (R 7) [34,68,160,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19702 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 137 280 34 81 209 337), lower := (rows 35 70 164 137 280 34 64 128 256), losses := [] }

theorem u19702 : Upper (D 7) (R 7) [34,68,160,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19703 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 164 137 280 48 67 195 323), lower := (rows 35 70 164 137 280 48 64 128 256), losses := [] }

theorem u19703 : Upper (D 7) (R 7) [34,68,160,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19703 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19704 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 137 280 96 83 147 275), lower := (rows 35 70 164 137 280 96 64 128 256), losses := [] }

theorem u19704 : Upper (D 7) (R 7) [34,68,160,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19705 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 137 336 33 90 154 282), lower := (rows 35 70 164 137 336 33 64 128 256), losses := [] }

theorem u19705 : Upper (D 7) (R 7) [34,68,160,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19706 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 137 336 34 89 153 281), lower := (rows 35 70 164 137 336 34 64 128 256), losses := [] }

theorem u19706 : Upper (D 7) (R 7) [34,68,160,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19707 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 70 164 137 336 40 83 147 275), lower := (rows 35 70 164 137 336 40 64 128 256), losses := [] }

theorem u19707 : Upper (D 7) (R 7) [34,68,160,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19707 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19708 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 137 336 48 75 139 267), lower := (rows 35 70 164 137 336 48 64 128 256), losses := [] }

theorem u19708 : Upper (D 7) (R 7) [34,68,160,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19708 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19709 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 152 273 33 74 202 330), lower := (rows 35 70 164 152 273 33 64 128 256), losses := [] }

theorem u19709 : Upper (D 7) (R 7) [34,68,160,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19710 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 152 273 34 73 201 329), lower := (rows 35 70 164 152 273 34 64 128 256), losses := [] }

theorem u19710 : Upper (D 7) (R 7) [34,68,160,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19711 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 70 164 152 273 40 67 195 323), lower := (rows 35 70 164 152 273 40 64 128 256), losses := [] }

theorem u19711 : Upper (D 7) (R 7) [34,68,160,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19711 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19712 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 152 273 96 75 139 267), lower := (rows 35 70 164 152 273 96 64 128 256), losses := [] }

theorem u19712 : Upper (D 7) (R 7) [34,68,160,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19713 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 152 274 33 73 201 329), lower := (rows 35 70 164 152 274 33 64 128 256), losses := [] }

theorem u19713 : Upper (D 7) (R 7) [34,68,160,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19714 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 70 164 152 274 40 65 193 321), lower := (rows 35 70 164 152 274 40 64 128 256), losses := [] }

theorem u19714 : Upper (D 7) (R 7) [34,68,160,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19714 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19715 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 152 274 96 73 137 265), lower := (rows 35 70 164 152 274 96 64 128 256), losses := [] }

theorem u19715 : Upper (D 7) (R 7) [34,68,160,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19716 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 152 336 33 75 139 267), lower := (rows 35 70 164 152 336 33 64 128 256), losses := [] }

theorem u19716 : Upper (D 7) (R 7) [34,68,160,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19717 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 152 336 34 73 137 265), lower := (rows 35 70 164 152 336 34 64 128 256), losses := [] }

theorem u19717 : Upper (D 7) (R 7) [34,68,160,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19718 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 70 164 152 336 40 67 131 259), lower := (rows 35 70 164 152 336 40 64 128 256), losses := [] }

theorem u19718 : Upper (D 7) (R 7) [34,68,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19718 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19719 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 200 273 33 90 154 282), lower := (rows 35 70 164 200 273 33 64 128 256), losses := [] }

theorem u19719 : Upper (D 7) (R 7) [34,68,160,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19720 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 200 273 34 89 153 281), lower := (rows 35 70 164 200 273 34 64 128 256), losses := [] }

theorem u19720 : Upper (D 7) (R 7) [34,68,160,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19721 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 70 164 200 273 40 83 147 275), lower := (rows 35 70 164 200 273 40 64 128 256), losses := [] }

theorem u19721 : Upper (D 7) (R 7) [34,68,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19721 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19722 : Route 9 := (fun mask => (mask,id))

def c19722 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19722 : Upper (D 7) (R 7) [34,68,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257,16] 13 (by decide) (choices 1) [1,2,8] r19722 c19722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5357
  · exact u5358
  · exact u5359

def b19723 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 200 274 33 89 153 281), lower := (rows 35 70 164 200 274 33 64 128 256), losses := [] }

theorem u19723 : Upper (D 7) (R 7) [34,68,160,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19724 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 70 164 200 274 40 81 145 273), lower := (rows 35 70 164 200 274 40 64 128 256), losses := [] }

theorem u19724 : Upper (D 7) (R 7) [34,68,160,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19724 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19725 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 70 164 200 274 48 73 137 265), lower := (rows 35 70 164 200 274 48 64 128 256), losses := [] }

theorem u19725 : Upper (D 7) (R 7) [34,68,160,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19725 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19726 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 200 280 33 83 147 275), lower := (rows 35 70 164 200 280 33 64 128 256), losses := [] }

theorem u19726 : Upper (D 7) (R 7) [34,68,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19727 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 200 280 34 81 145 273), lower := (rows 35 70 164 200 280 34 64 128 256), losses := [] }

theorem u19727 : Upper (D 7) (R 7) [34,68,160,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19728 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 164 200 280 48 67 131 259), lower := (rows 35 70 164 200 280 48 64 128 256), losses := [] }

theorem u19728 : Upper (D 7) (R 7) [34,68,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19728 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19729 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 25 112 34 200 136 392), lower := (rows 35 70 261 25 112 34 64 128 256), losses := [] }

theorem u19729 : Upper (D 7) (R 7) [34,68,257,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19730 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 261 25 112 40 194 130 386), lower := (rows 35 70 261 25 112 40 64 128 256), losses := [] }

theorem u19730 : Upper (D 7) (R 7) [34,68,257,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19730 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19731 : Route 9 := (fun mask => (mask,id))

def c19731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19731 : Upper (D 7) (R 7) [34,68,257,17,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,96,128] 13 (by decide) (choices 1) [2,8,128] r19731 c19731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5360
  · exact u5361
  · exact u5362

def b19732 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 70 261 25 146 40 224 224 480), lower := (rows 35 70 261 25 146 40 64 128 256), losses := [] }

theorem u19732 : Upper (D 7) (R 7) [34,68,257,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19732 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19733 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 25 146 96 232 168 424), lower := (rows 35 70 261 25 146 96 64 128 256), losses := [] }

theorem u19733 : Upper (D 7) (R 7) [34,68,257,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19734 : Route 9 := (fun mask => (mask,id))

def c19734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19734 : Upper (D 7) (R 7) [34,68,257,17,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,130,128] 13 (by decide) (choices 1) [8,32] r19734 c19734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5363
  · exact u5364

def b19735 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 25 152 34 224 224 480), lower := (rows 35 70 261 25 152 34 64 128 256), losses := [] }

theorem u19735 : Upper (D 7) (R 7) [34,68,257,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19736 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 25 152 96 226 162 418), lower := (rows 35 70 261 25 152 96 64 128 256), losses := [] }

theorem u19736 : Upper (D 7) (R 7) [34,68,257,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19737 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 35 70 261 25 152 160 98 226 354), lower := (rows 35 70 261 25 152 160 64 128 256), losses := [] }

theorem u19737 : Upper (D 7) (R 7) [34,68,257,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19738 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 25 176 34 200 200 456), lower := (rows 35 70 261 25 176 34 64 128 256), losses := [] }

theorem u19738 : Upper (D 7) (R 7) [34,68,257,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19739 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 208, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 35 70 261 25 176 40 194 194 450), lower := (rows 35 70 261 25 176 40 64 128 256), losses := [] }

theorem u19739 : Upper (D 7) (R 7) [34,68,257,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19739 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19739
end Delivery.IrregularNine14.P07
