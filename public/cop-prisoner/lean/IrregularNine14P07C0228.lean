import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0034
import IrregularNine14P07C0035

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13680 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 324 200 176 48 67 131 259), lower := (rows 7 42 324 200 176 48 64 128 256), losses := [] }

theorem u13680 : Upper (D 7) (R 7) [6,40,320,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13680 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13681 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 98 13 56 145 34 448 448 448), lower := (rows 7 98 13 56 145 34 64 128 256), losses := [] }

theorem u13681 : Upper (D 7) (R 7) [6,96,9,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13682 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 56 145 96 450 386 386), lower := (rows 7 98 13 56 145 96 64 128 256), losses := [] }

theorem u13682 : Upper (D 7) (R 7) [6,96,9,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13683 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 7 98 13 56 145 160 322 450 322), lower := (rows 7 98 13 56 145 160 64 128 256), losses := [] }

theorem u13683 : Upper (D 7) (R 7) [6,96,9,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13684 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 7 98 13 56 145 288 194 194 450), lower := (rows 7 98 13 56 145 288 64 128 256), losses := [] }

theorem u13684 : Upper (D 7) (R 7) [6,96,9,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13684 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13685 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 13 56 146 33 448 448 448), lower := (rows 7 98 13 56 146 33 64 128 256), losses := [] }

theorem u13685 : Upper (D 7) (R 7) [6,96,9,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13686 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 56 146 96 449 385 385), lower := (rows 7 98 13 56 146 96 64 128 256), losses := [] }

theorem u13686 : Upper (D 7) (R 7) [6,96,9,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13687 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 7 98 13 56 146 160 321 449 321), lower := (rows 7 98 13 56 146 160 64 128 256), losses := [] }

theorem u13687 : Upper (D 7) (R 7) [6,96,9,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13688 : Route 9 := (fun mask => (mask,id))

def c13688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13688 : Upper (D 7) (R 7) [6,96,9,48,130,256] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,130,256] 13 (by decide) (choices 1) [1,128] r13688 c13688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2083
  · exact u2084

def b13689 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 13 56 208 33 450 386 386), lower := (rows 7 98 13 56 208 33 64 128 256), losses := [] }

theorem u13689 : Upper (D 7) (R 7) [6,96,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13690 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 13 56 208 34 449 385 385), lower := (rows 7 98 13 56 208 34 64 128 256), losses := [] }

theorem u13690 : Upper (D 7) (R 7) [6,96,9,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13691 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 56 208 160 323 387 259), lower := (rows 7 98 13 56 208 160 64 128 256), losses := [] }

theorem u13691 : Upper (D 7) (R 7) [6,96,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13692 : Route 9 := (fun mask => (mask,id))

def c13692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13692 : Upper (D 7) (R 7) [6,96,9,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,192,256] 13 (by decide) (choices 1) [1,2,128] r13692 c13692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2085
  · exact u2086
  · exact u2087

def b13693 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 98 13 56 273 34 192 192 448), lower := (rows 7 98 13 56 273 34 64 128 256), losses := [] }

theorem u13693 : Upper (D 7) (R 7) [6,96,9,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13694 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 56 273 96 194 130 386), lower := (rows 7 98 13 56 273 96 64 128 256), losses := [] }

theorem u13694 : Upper (D 7) (R 7) [6,96,9,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13695 : Route 9 := (fun mask => (mask,id))

def c13695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13695 : Upper (D 7) (R 7) [6,96,9,48,257,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,257,128] 13 (by decide) (choices 1) [2,128] r13695 c13695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2088
  · exact u2089

def b13696 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 13 56 274 33 192 192 448), lower := (rows 7 98 13 56 274 33 64 128 256), losses := [] }

theorem u13696 : Upper (D 7) (R 7) [6,96,9,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13697 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 56 274 96 193 129 385), lower := (rows 7 98 13 56 274 96 64 128 256), losses := [] }

theorem u13697 : Upper (D 7) (R 7) [6,96,9,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13698 : Route 9 := (fun mask => (mask,id))

def c13698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13698 : Upper (D 7) (R 7) [6,96,9,48,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,258,128] 13 (by decide) (choices 1) [1,128] r13698 c13698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2090
  · exact u2091

def b13699 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 13 56 336 33 194 130 386), lower := (rows 7 98 13 56 336 33 64 128 256), losses := [] }

theorem u13699 : Upper (D 7) (R 7) [6,96,9,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13700 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 13 56 336 34 193 129 385), lower := (rows 7 98 13 56 336 34 64 128 256), losses := [] }

theorem u13700 : Upper (D 7) (R 7) [6,96,9,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13701 : Route 9 := (fun mask => (mask,id))

def c13701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13701 : Upper (D 7) (R 7) [6,96,9,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,320,128] 13 (by decide) (choices 1) [1,2,128] r13701 c13701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2092
  · exact u2093
  · exact u2094

def b13702 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 98 13 56 400 33 194 194 450), lower := (rows 7 98 13 56 400 33 64 128 256), losses := [] }

theorem u13702 : Upper (D 7) (R 7) [6,96,9,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13703 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 13 56 400 34 193 193 449), lower := (rows 7 98 13 56 400 34 64 128 256), losses := [] }

theorem u13703 : Upper (D 7) (R 7) [6,96,9,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13704 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 56 400 96 195 131 387), lower := (rows 7 98 13 56 400 96 64 128 256), losses := [] }

theorem u13704 : Upper (D 7) (R 7) [6,96,9,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13705 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 98 13 56 400 160 67 195 323), lower := (rows 7 98 13 56 400 160 64 128 256), losses := [] }

theorem u13705 : Upper (D 7) (R 7) [6,96,9,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13706 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(3,0)], upper := (rows 7 98 13 152 273 34 224 224 480), lower := (rows 7 98 13 152 273 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 21 9 17 32 98 162 290), good := (rows 477 480 29 156 285 480 64 128 256) }] }

theorem u13706 : Upper (D 7) (R 7) [6,96,9,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13707 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 152 273 96 226 162 418), lower := (rows 7 98 13 152 273 96 64 128 256), losses := [] }

theorem u13707 : Upper (D 7) (R 7) [6,96,9,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13708 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 7 98 13 152 273 160 98 226 354), lower := (rows 7 98 13 152 273 160 64 128 256), losses := [{ target := 7, region := (rows 1 34 4 8 17 32 98 0 290), good := (rows 343 354 29 24 273 354 64 0 256) }] }

theorem u13708 : Upper (D 7) (R 7) [6,96,9,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13709 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 13 152 274 33 224 224 480), lower := (rows 7 98 13 152 274 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 103 167 295), good := (rows 485 480 493 152 472 481 64 128 256) }] }

theorem u13709 : Upper (D 7) (R 7) [6,96,9,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13710 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 152 274 96 225 161 417), lower := (rows 7 98 13 152 274 96 64 128 256), losses := [] }

theorem u13710 : Upper (D 7) (R 7) [6,96,9,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m13711_1 : Upper (D 7) (R 7) [6,96,9,144,258,128,1] 13 :=
  permutation_upper _ _ _ [6,96,9,144,258,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2095

theorem m13711_32 : Upper (D 7) (R 7) [6,96,9,144,258,128,32] 13 :=
  permutation_upper _ _ _ [6,96,9,144,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2096

def r13711 : Route 9 := (fun mask => (mask,id))

def c13711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13711 : Upper (D 7) (R 7) [6,96,9,144,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144,258,128] 13 (by decide) (choices 1) [1,32] r13711 c13711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m13711_1
  · exact m13711_32

def r13712 : Route 9 := (fun mask => (mask,id))

def c13712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13712 : Upper (D 7) (R 7) [6,96,9,144,288,1] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144,288,1] 13 (by decide) (choices 1) [2,128] r13712 c13712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2097
  · exact u2098

def r13713 : Route 9 := (fun mask => (mask,id))

def c13713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13713 : Upper (D 7) (R 7) [6,96,9,144,288,2] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144,288,2] 13 (by decide) (choices 1) [1,128] r13713 c13713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2099
  · exact u2100

def b13714 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 152 304 96 195 131 387), lower := (rows 7 98 13 152 304 96 64 128 256), losses := [] }

theorem u13714 : Upper (D 7) (R 7) [6,96,9,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13715 : Route 9 := (fun mask => (mask,id))

def c13715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13715 : Upper (D 7) (R 7) [6,96,9,144,288,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144,288,128] 13 (by decide) (choices 1) [1,2] r13715 c13715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2101
  · exact u2102

def b13716 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 98 13 168 81 34 464 400 400), lower := (rows 7 98 13 168 81 34 64 128 256), losses := [] }

theorem u13716 : Upper (D 7) (R 7) [6,96,9,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13717 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 13 168 81 48 450 386 386), lower := (rows 7 98 13 168 81 48 64 128 256), losses := [] }

theorem u13717 : Upper (D 7) (R 7) [6,96,9,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13717 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13718 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 13 168 81 160 338 402 274), lower := (rows 7 98 13 168 81 160 64 128 256), losses := [] }

theorem u13718 : Upper (D 7) (R 7) [6,96,9,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13719 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 7 98 13 168 81 288 210 146 402), lower := (rows 7 98 13 168 81 288 64 128 256), losses := [] }

theorem u13719 : Upper (D 7) (R 7) [6,96,9,160,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13719 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13720 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 7 98 13 168 146 33 336 464 336), lower := (rows 7 98 13 168 146 33 64 128 256), losses := [] }

theorem u13720 : Upper (D 7) (R 7) [6,96,9,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13721 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 168 146 48 321 449 321), lower := (rows 7 98 13 168 146 48 64 128 256), losses := [] }

theorem u13721 : Upper (D 7) (R 7) [6,96,9,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13721 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13722 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 168 146 96 337 401 273), lower := (rows 7 98 13 168 146 96 64 128 256), losses := [] }

theorem u13722 : Upper (D 7) (R 7) [6,96,9,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13723 : Route 9 := (fun mask => (mask,id))

def c13723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13723 : Upper (D 7) (R 7) [6,96,9,160,130,256] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,130,256] 13 (by decide) (choices 1) [1,16] r13723 c13723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2103
  · exact u2104

def b13724 : PairBound 9 := { available := 274, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 98 13 168 208 33 338 402 274), lower := (rows 7 98 13 168 208 33 64 128 256), losses := [] }

theorem u13724 : Upper (D 7) (R 7) [6,96,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13725 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 98 13 168 208 34 337 401 273), lower := (rows 7 98 13 168 208 34 64 128 256), losses := [] }

theorem u13725 : Upper (D 7) (R 7) [6,96,9,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13726 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 13 168 208 48 323 387 259), lower := (rows 7 98 13 168 208 48 64 128 256), losses := [] }

theorem u13726 : Upper (D 7) (R 7) [6,96,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13726 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13727 : Route 9 := (fun mask => (mask,id))

def c13727 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13727 : Upper (D 7) (R 7) [6,96,9,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,192,256] 13 (by decide) (choices 1) [1,2,16] r13727 c13727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2105
  · exact u2106
  · exact u2107

def b13728 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 98 13 168 273 34 208 208 464), lower := (rows 7 98 13 168 273 34 64 128 256), losses := [] }

theorem u13728 : Upper (D 7) (R 7) [6,96,9,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13729 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 7 98 13 168 273 48 194 194 450), lower := (rows 7 98 13 168 273 48 64 128 256), losses := [] }

theorem u13729 : Upper (D 7) (R 7) [6,96,9,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13729 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13730 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 168 273 96 210 146 402), lower := (rows 7 98 13 168 273 96 64 128 256), losses := [] }

theorem u13730 : Upper (D 7) (R 7) [6,96,9,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13731 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 13 168 273 160 82 210 338), lower := (rows 7 98 13 168 273 160 64 128 256), losses := [] }

theorem u13731 : Upper (D 7) (R 7) [6,96,9,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13732 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 98 13 168 274 33 208 208 464), lower := (rows 7 98 13 168 274 33 64 128 256), losses := [] }

theorem u13732 : Upper (D 7) (R 7) [6,96,9,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13733 : Route 9 := (fun mask => (mask,id))

def c13733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13733 : Upper (D 7) (R 7) [6,96,9,160,258,16] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,258,16] 13 (by decide) (choices 1) [1,128] r13733 c13733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2108
  · exact u2109

def b13734 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 168 274 96 209 145 401), lower := (rows 7 98 13 168 274 96 64 128 256), losses := [] }

theorem u13734 : Upper (D 7) (R 7) [6,96,9,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13735 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 13 168 274 160 81 209 337), lower := (rows 7 98 13 168 274 160 64 128 256), losses := [] }

theorem u13735 : Upper (D 7) (R 7) [6,96,9,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13736 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 98 13 168 336 33 210 146 402), lower := (rows 7 98 13 168 336 33 64 128 256), losses := [] }

theorem u13736 : Upper (D 7) (R 7) [6,96,9,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13737 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 13 168 336 34 209 145 401), lower := (rows 7 98 13 168 336 34 64 128 256), losses := [] }

theorem u13737 : Upper (D 7) (R 7) [6,96,9,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13738 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 13 168 336 48 195 131 387), lower := (rows 7 98 13 168 336 48 64 128 256), losses := [] }

theorem u13738 : Upper (D 7) (R 7) [6,96,9,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13738 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13739 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 13 168 336 160 83 147 275), lower := (rows 7 98 13 168 336 160 64 128 256), losses := [] }

theorem u13739 : Upper (D 7) (R 7) [6,96,9,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13739
end Delivery.IrregularNine14.P07
