import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0048

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13680 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 134 296 84 96 81 145 273), lower := (rows 11 38 134 296 84 96 64 128 256), losses := [] }

theorem u13680 : Upper (D 6) (R 6) [10,36,130,288,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13681 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 38 134 328 21 33 112 240 368), lower := (rows 11 38 134 328 21 33 64 128 256), losses := [] }

theorem u13681 : Upper (D 6) (R 6) [10,36,130,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13682 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 134 328 21 48 97 225 353), lower := (rows 11 38 134 328 21 48 64 128 256), losses := [] }

theorem u13682 : Upper (D 6) (R 6) [10,36,130,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13682 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13683 : Route 9 := (fun mask => (mask,id))

def c13683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13683 : Upper (D 6) (R 6) [10,36,130,320,5,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,5,64] 13 (by decide) (choices 1) [1,16,32] r13683 c13683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2881
  · exact u2882
  · exact u2883

def b13684 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 134 328 49 33 84 212 340), lower := (rows 11 38 134 328 49 33 64 128 256), losses := [] }

theorem u13684 : Upper (D 6) (R 6) [10,36,130,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13685 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 328 49 36 81 209 337), lower := (rows 11 38 134 328 49 36 64 128 256), losses := [] }

theorem u13685 : Upper (D 6) (R 6) [10,36,130,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13686 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 328 49 48 69 197 325), lower := (rows 11 38 134 328 49 48 64 128 256), losses := [] }

theorem u13686 : Upper (D 6) (R 6) [10,36,130,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13686 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13687 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 134, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 38 134 328 49 96 85 149 277), lower := (rows 11 38 134 328 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 104 64 128 256), good := (rows 57 36 132 360 49 96 96 128 256) }] }

theorem u13687 : Upper (D 6) (R 6) [10,36,130,320,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13688 : Route 9 := (fun mask => (mask,id))

def c13688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13688 : Upper (D 6) (R 6) [10,36,130,320,65,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,65,1] 13 (by decide) (choices 1) [4,16,32] r13688 c13688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2884
  · exact u2885
  · exact u2886

def b13689 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 328 81 36 113 177 305), lower := (rows 11 38 134 328 81 36 64 128 256), losses := [] }

theorem u13689 : Upper (D 6) (R 6) [10,36,130,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13690 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 38 134 328 81 48 101 165 293), lower := (rows 11 38 134 328 81 48 64 128 256), losses := [] }

theorem u13690 : Upper (D 6) (R 6) [10,36,130,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13690 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13691 : Route 9 := (fun mask => (mask,id))

def c13691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13691 : Upper (D 6) (R 6) [10,36,130,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,68,1] 13 (by decide) (choices 1) [1,16,32] r13691 c13691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2887
  · exact u2888
  · exact u2889

def b13692 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 134 328 84 48 97 161 289), lower := (rows 11 38 134 328 84 48 64 128 256), losses := [] }

theorem u13692 : Upper (D 6) (R 6) [10,36,130,320,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13692 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13693 : Route 9 := (fun mask => (mask,id))

def c13693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13693 : Upper (D 6) (R 6) [10,36,130,320,96,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,96,1] 13 (by decide) (choices 1) [1,4,16] r13693 c13693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2890
  · exact u2891
  · exact u2892

def b13694 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 328 112 36 81 145 273), lower := (rows 11 38 134 328 112 36 64 128 256), losses := [] }

theorem u13694 : Upper (D 6) (R 6) [10,36,130,320,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13695 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 134 328 112 48 69 133 261), lower := (rows 11 38 134 328 112 48 64 128 256), losses := [] }

theorem u13695 : Upper (D 6) (R 6) [10,36,130,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13695 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13696 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 73 84 33 354 418 290), lower := (rows 11 38 148 73 84 33 64 128 256), losses := [] }

theorem u13696 : Upper (D 6) (R 6) [10,36,144,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13697 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 148 73 84 34 353 417 289), lower := (rows 11 38 148 73 84 34 64 128 256), losses := [] }

theorem u13697 : Upper (D 6) (R 6) [10,36,144,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13698 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 148 73 84 288 99 163 291), lower := (rows 11 38 148 73 84 288 64 128 256), losses := [] }

theorem u13698 : Upper (D 6) (R 6) [10,36,144,65,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13698 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13699 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 73 112 33 326 390 262), lower := (rows 11 38 148 73 112 33 64 128 256), losses := [] }

theorem u13699 : Upper (D 6) (R 6) [10,36,144,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13700 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 73 112 34 325 389 261), lower := (rows 11 38 148 73 112 34 64 128 256), losses := [] }

theorem u13700 : Upper (D 6) (R 6) [10,36,144,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13701 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 73 112 36 323 387 259), lower := (rows 11 38 148 73 112 36 64 128 256), losses := [] }

theorem u13701 : Upper (D 6) (R 6) [10,36,144,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13702 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 148 73 112 288 71 135 263), lower := (rows 11 38 148 73 112 288 64 128 256), losses := [] }

theorem u13702 : Upper (D 6) (R 6) [10,36,144,65,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13702 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13703 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 148 73 273 34 100 228 356), lower := (rows 11 38 148 73 273 34 64 128 256), losses := [] }

theorem u13703 : Upper (D 6) (R 6) [10,36,144,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13704 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 73 273 36 98 226 354), lower := (rows 11 38 148 73 273 36 64 128 256), losses := [] }

theorem u13704 : Upper (D 6) (R 6) [10,36,144,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13705 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 38 148 73 273 96 102 166 294), lower := (rows 11 38 148 73 273 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 17 32 0 130 258), good := (rows 415 422 148 29 277 32 0 128 256) }] }

theorem u13705 : Upper (D 6) (R 6) [10,36,144,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13706 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 73 274 33 100 228 356), lower := (rows 11 38 148 73 274 33 64 128 256), losses := [] }

theorem u13706 : Upper (D 6) (R 6) [10,36,144,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13707 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 73 274 36 97 225 353), lower := (rows 11 38 148 73 274 36 64 128 256), losses := [] }

theorem u13707 : Upper (D 6) (R 6) [10,36,144,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13708 : Route 9 := (fun mask => (mask,id))

def c13708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13708 : Upper (D 6) (R 6) [10,36,144,65,258,64] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,258,64] 13 (by decide) (choices 1) [1,4,32] r13708 c13708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2893
  · exact u2894
  · exact u2895

def b13709 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 73 276 33 98 226 354), lower := (rows 11 38 148 73 276 33 64 128 256), losses := [] }

theorem u13709 : Upper (D 6) (R 6) [10,36,144,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13710 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 148 73 276 34 97 225 353), lower := (rows 11 38 148 73 276 34 64 128 256), losses := [] }

theorem u13710 : Upper (D 6) (R 6) [10,36,144,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13711 : Route 9 := (fun mask => (mask,id))

def c13711 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13711 : Upper (D 6) (R 6) [10,36,144,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,260,64] 13 (by decide) (choices 1) [1,2,32] r13711 c13711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2896
  · exact u2897
  · exact u2898

def b13712 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 73 304 33 70 198 326), lower := (rows 11 38 148 73 304 33 64 128 256), losses := [] }

theorem u13712 : Upper (D 6) (R 6) [10,36,144,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13713 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 73 304 34 69 197 325), lower := (rows 11 38 148 73 304 34 64 128 256), losses := [] }

theorem u13713 : Upper (D 6) (R 6) [10,36,144,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13714 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 73 304 36 67 195 323), lower := (rows 11 38 148 73 304 36 64 128 256), losses := [] }

theorem u13714 : Upper (D 6) (R 6) [10,36,144,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13715 : Route 9 := (fun mask => (mask,id))

def c13715 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13715 : Upper (D 6) (R 6) [10,36,144,65,288,64] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,288,64] 13 (by decide) (choices 1) [1,2,4] r13715 c13715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2899
  · exact u2900
  · exact u2901

def b13716 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 73 336 33 102 166 294), lower := (rows 11 38 148 73 336 33 64 128 256), losses := [] }

theorem u13716 : Upper (D 6) (R 6) [10,36,144,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13717 : Route 9 := (fun mask => (mask,id))

def c13717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13717 : Upper (D 6) (R 6) [10,36,144,65,320,2] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,320,2] 13 (by decide) (choices 1) [1,4,32] r13717 c13717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2902
  · exact u2903
  · exact u2904

def b13718 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 73 336 36 99 163 291), lower := (rows 11 38 148 73 336 36 64 128 256), losses := [] }

theorem u13718 : Upper (D 6) (R 6) [10,36,144,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13719 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 148 76 273 33 98 226 354), lower := (rows 11 38 148 76 273 33 64 128 256), losses := [] }

theorem u13719 : Upper (D 6) (R 6) [10,36,144,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13720 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 148 76 273 34 97 225 353), lower := (rows 11 38 148 76 273 34 64 128 256), losses := [] }

theorem u13720 : Upper (D 6) (R 6) [10,36,144,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13721 : Route 9 := (fun mask => (mask,id))

def c13721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13721 : Upper (D 6) (R 6) [10,36,144,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,36,144,68,257,64] 13 (by decide) (choices 1) [1,2,32] r13721 c13721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2905
  · exact u2906
  · exact u2907

def b13722 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 148 76 274 33 97 225 353), lower := (rows 11 38 148 76 274 33 64 128 256), losses := [] }

theorem u13722 : Upper (D 6) (R 6) [10,36,144,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13723 : Route 9 := (fun mask => (mask,id))

def c13723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13723 : Upper (D 6) (R 6) [10,36,144,68,258,64] 13 := by
  apply FastRouting.sound _ _ [10,36,144,68,258,64] 13 (by decide) (choices 1) [1,32] r13723 c13723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2908
  · exact u2909

def b13724 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 148 104 82 33 325 389 261), lower := (rows 11 38 148 104 82 33 64 128 256), losses := [] }

theorem u13724 : Upper (D 6) (R 6) [10,36,144,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13725 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 104 82 36 321 385 257), lower := (rows 11 38 148 104 82 36 64 128 256), losses := [] }

theorem u13725 : Upper (D 6) (R 6) [10,36,144,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13726 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 148 104 82 288 69 133 261), lower := (rows 11 38 148 104 82 288 64 128 256), losses := [] }

theorem u13726 : Upper (D 6) (R 6) [10,36,144,96,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13726 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13727 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 148 104 273 33 70 198 326), lower := (rows 11 38 148 104 273 33 64 128 256), losses := [] }

theorem u13727 : Upper (D 6) (R 6) [10,36,144,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13728 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 148 104 273 34 69 197 325), lower := (rows 11 38 148 104 273 34 64 128 256), losses := [] }

theorem u13728 : Upper (D 6) (R 6) [10,36,144,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13729 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 104 273 36 67 195 323), lower := (rows 11 38 148 104 273 36 64 128 256), losses := [] }

theorem u13729 : Upper (D 6) (R 6) [10,36,144,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13730 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 148 104 273 96 71 135 263), lower := (rows 11 38 148 104 273 96 64 128 256), losses := [] }

theorem u13730 : Upper (D 6) (R 6) [10,36,144,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13731 : Route 9 := (fun mask => (mask,id))

def c13731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13731 : Upper (D 6) (R 6) [10,36,144,96,258,1] 13 := by
  apply FastRouting.sound _ _ [10,36,144,96,258,1] 13 (by decide) (choices 1) [1,4] r13731 c13731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2910
  · exact u2911

def b13732 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 104 274 36 65 193 321), lower := (rows 11 38 148 104 274 36 64 128 256), losses := [] }

theorem u13732 : Upper (D 6) (R 6) [10,36,144,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13733 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 148 104 274 96 69 133 261), lower := (rows 11 38 148 104 274 96 64 128 256), losses := [] }

theorem u13733 : Upper (D 6) (R 6) [10,36,144,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13734 : Route 9 := (fun mask => (mask,id))

def c13734 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13734 : Upper (D 6) (R 6) [10,36,144,96,320,1] 13 := by
  apply FastRouting.sound _ _ [10,36,144,96,320,1] 13 (by decide) (choices 1) [1,2,4] r13734 c13734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2912
  · exact u2913
  · exact u2914

def b13735 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 148 104 336 34 69 133 261), lower := (rows 11 38 148 104 336 34 64 128 256), losses := [] }

theorem u13735 : Upper (D 6) (R 6) [10,36,144,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13736 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 104 336 36 67 131 259), lower := (rows 11 38 148 104 336 36 64 128 256), losses := [] }

theorem u13736 : Upper (D 6) (R 6) [10,36,144,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13737 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 148 265 81 34 100 228 356), lower := (rows 11 38 148 265 81 34 64 128 256), losses := [] }

theorem u13737 : Upper (D 6) (R 6) [10,36,144,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13738 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 265 81 36 98 226 354), lower := (rows 11 38 148 265 81 36 64 128 256), losses := [] }

theorem u13738 : Upper (D 6) (R 6) [10,36,144,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13739 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 265, targets := 64 },{ cop := 4, region := 166, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 38 148 265 81 96 102 166 294), lower := (rows 11 38 148 265 81 96 64 128 256), losses := [] }

theorem u13739 : Upper (D 6) (R 6) [10,36,144,257,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13739
end Delivery.IrregularNine14.P06
