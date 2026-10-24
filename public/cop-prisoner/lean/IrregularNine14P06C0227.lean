import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0047
import IrregularNine14P06C0048

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r13620 : Route 9 := (fun mask => (mask,id))

def c13620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13620 : Upper (D 6) (R 6) [10,36,130,80,257,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,257,64] 13 (by decide) (choices 1) [1,4,32] r13620 c13620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2827
  · exact u2828
  · exact u2829

def r13621 : Route 9 := (fun mask => (mask,id))

def c13621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13621 : Upper (D 6) (R 6) [10,36,130,80,260,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,260,1] 13 (by decide) (choices 1) [1,32] r13621 c13621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2830
  · exact u2831

def r13622 : Route 9 := (fun mask => (mask,id))

def c13622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13622 : Upper (D 6) (R 6) [10,36,130,80,260,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,260,64] 13 (by decide) (choices 1) [1,32] r13622 c13622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2832
  · exact u2833

def r13623 : Route 9 := (fun mask => (mask,id))

def c13623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13623 : Upper (D 6) (R 6) [10,36,130,80,288,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,288,1] 13 (by decide) (choices 1) [1,4] r13623 c13623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2834
  · exact u2835

def b13624 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 88 304 36 65 193 321), lower := (rows 11 38 134 88 304 36 64 128 256), losses := [] }

theorem u13624 : Upper (D 6) (R 6) [10,36,130,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13625 : Route 9 := (fun mask => (mask,id))

def c13625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13625 : Upper (D 6) (R 6) [10,36,130,80,288,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,288,64] 13 (by decide) (choices 1) [1,4] r13625 c13625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2836
  · exact u2837

def r13626 : Route 9 := (fun mask => (mask,id))

def c13626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u13626 : Upper (D 6) (R 6) [10,36,130,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96,68,1] 13 (by decide) (choices 1) [1,16,256] r13626 c13626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2838
  · exact u2839
  · exact u2840

def b13627 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 134 104 84 48 321 385 257), lower := (rows 11 38 134 104 84 48 64 128 256), losses := [] }

theorem u13627 : Upper (D 6) (R 6) [10,36,130,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13627 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13628 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 104 84 288 81 145 273), lower := (rows 11 38 134 104 84 288 64 128 256), losses := [] }

theorem u13628 : Upper (D 6) (R 6) [10,36,130,96,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13628 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13629 : Route 9 := (fun mask => (mask,id))

def c13629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13629 : Upper (D 6) (R 6) [10,36,130,96,257,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96,257,1] 13 (by decide) (choices 1) [4,16] r13629 c13629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2841
  · exact u2842

def b13630 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 104 273 36 81 209 337), lower := (rows 11 38 134 104 273 36 64 128 256), losses := [] }

theorem u13630 : Upper (D 6) (R 6) [10,36,130,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13631 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 104 273 48 69 197 325), lower := (rows 11 38 134 104 273 48 64 128 256), losses := [] }

theorem u13631 : Upper (D 6) (R 6) [10,36,130,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13631 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13632 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 104 273 96 85 149 277), lower := (rows 11 38 134 104 273 96 64 128 256), losses := [] }

theorem u13632 : Upper (D 6) (R 6) [10,36,130,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13633 : Route 9 := (fun mask => (mask,id))

def c13633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13633 : Upper (D 6) (R 6) [10,36,130,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96,260,1] 13 (by decide) (choices 1) [1,16] r13633 c13633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2843
  · exact u2844

def b13634 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 104 276 48 65 193 321), lower := (rows 11 38 134 104 276 48 64 128 256), losses := [] }

theorem u13634 : Upper (D 6) (R 6) [10,36,130,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13634 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13635 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 104 276 96 81 145 273), lower := (rows 11 38 134 104 276 96 64 128 256), losses := [] }

theorem u13635 : Upper (D 6) (R 6) [10,36,130,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13636 : Route 9 := (fun mask => (mask,id))

def c13636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13636 : Upper (D 6) (R 6) [10,36,130,96,320,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96,320,1] 13 (by decide) (choices 1) [1,4,16] r13636 c13636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2845
  · exact u2846
  · exact u2847

def b13637 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 104 336 36 81 145 273), lower := (rows 11 38 134 104 336 36 64 128 256), losses := [] }

theorem u13637 : Upper (D 6) (R 6) [10,36,130,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13638 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 134 104 336 48 69 133 261), lower := (rows 11 38 134 104 336 48 64 128 256), losses := [] }

theorem u13638 : Upper (D 6) (R 6) [10,36,130,96,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13638 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13639 : PairBound 9 := { available := 80, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 265 49 36 80 208 336), lower := (rows 11 38 134 265 49 36 64 128 256), losses := [] }

theorem u13639 : Upper (D 6) (R 6) [10,36,130,257,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13640 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 265 49 48 68 196 324), lower := (rows 11 38 134 265 49 48 64 128 256), losses := [] }

theorem u13640 : Upper (D 6) (R 6) [10,36,130,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13640 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13641 : Route 9 := (fun mask => (mask,id))

def c13641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13641 : Upper (D 6) (R 6) [10,36,130,257,33,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,257,33,64] 13 (by decide) (choices 1) [4,16] r13641 c13641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2848
  · exact u2849

def b13642 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 265 81 36 112 240 368), lower := (rows 11 38 134 265 81 36 64 128 256), losses := [] }

theorem u13642 : Upper (D 6) (R 6) [10,36,130,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13643 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 134 265 81 48 100 228 356), lower := (rows 11 38 134 265 81 48 64 128 256), losses := [] }

theorem u13643 : Upper (D 6) (R 6) [10,36,130,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13643 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13644 : Route 9 := (fun mask => (mask,id))

def c13644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13644 : Upper (D 6) (R 6) [10,36,130,257,65,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,257,65,64] 13 (by decide) (choices 1) [4,16,32] r13644 c13644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2850
  · exact u2851
  · exact u2852

def b13645 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 265 84 33 112 240 368), lower := (rows 11 38 134 265 84 33 64 128 256), losses := [] }

theorem u13645 : Upper (D 6) (R 6) [10,36,130,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13646 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 134 265 84 48 97 225 353), lower := (rows 11 38 134 265 84 48 64 128 256), losses := [] }

theorem u13646 : Upper (D 6) (R 6) [10,36,130,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13646 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13647 : Route 9 := (fun mask => (mask,id))

def c13647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13647 : Upper (D 6) (R 6) [10,36,130,257,68,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,257,68,64] 13 (by decide) (choices 1) [1,16,32] r13647 c13647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2853
  · exact u2854
  · exact u2855

def b13648 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 265 112 33 84 212 340), lower := (rows 11 38 134 265 112 33 64 128 256), losses := [] }

theorem u13648 : Upper (D 6) (R 6) [10,36,130,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13649 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 265 112 36 81 209 337), lower := (rows 11 38 134 265 112 36 64 128 256), losses := [] }

theorem u13649 : Upper (D 6) (R 6) [10,36,130,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13650 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 134 265 112 48 69 197 325), lower := (rows 11 38 134 265 112 48 64 128 256), losses := [] }

theorem u13650 : Upper (D 6) (R 6) [10,36,130,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13650 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13651 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 265 112 96 85 149 277), lower := (rows 11 38 134 265 112 96 64 128 256), losses := [] }

theorem u13651 : Upper (D 6) (R 6) [10,36,130,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13652 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 38 134 268 49 33 80 208 336), lower := (rows 11 38 134 268 49 33 64 128 256), losses := [] }

theorem u13652 : Upper (D 6) (R 6) [10,36,130,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13653 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 134 268 49 48 65 193 321), lower := (rows 11 38 134 268 49 48 64 128 256), losses := [] }

theorem u13653 : Upper (D 6) (R 6) [10,36,130,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13653 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13654 : Route 9 := (fun mask => (mask,id))

def c13654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13654 : Upper (D 6) (R 6) [10,36,130,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,260,33,64] 13 (by decide) (choices 1) [1,16] r13654 c13654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2856
  · exact u2857

def b13655 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 268 81 33 112 240 368), lower := (rows 11 38 134 268 81 33 64 128 256), losses := [] }

theorem u13655 : Upper (D 6) (R 6) [10,36,130,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13656 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 268 81 48 97 225 353), lower := (rows 11 38 134 268 81 48 64 128 256), losses := [] }

theorem u13656 : Upper (D 6) (R 6) [10,36,130,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13656 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13657 : Route 9 := (fun mask => (mask,id))

def c13657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13657 : Upper (D 6) (R 6) [10,36,130,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,260,65,64] 13 (by decide) (choices 1) [1,16,32] r13657 c13657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2858
  · exact u2859
  · exact u2860

def b13658 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 268 112 33 81 209 337), lower := (rows 11 38 134 268 112 33 64 128 256), losses := [] }

theorem u13658 : Upper (D 6) (R 6) [10,36,130,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13659 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 134 268 112 48 65 193 321), lower := (rows 11 38 134 268 112 48 64 128 256), losses := [] }

theorem u13659 : Upper (D 6) (R 6) [10,36,130,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13659 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13660 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 268 112 96 81 145 273), lower := (rows 11 38 134 268 112 96 64 128 256), losses := [] }

theorem u13660 : Upper (D 6) (R 6) [10,36,130,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13661 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 38 134 280 21 33 96 224 352), lower := (rows 11 38 134 280 21 33 64 128 256), losses := [] }

theorem u13661 : Upper (D 6) (R 6) [10,36,130,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13662 : Route 9 := (fun mask => (mask,id))

def c13662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13662 : Upper (D 6) (R 6) [10,36,130,272,5,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,5,64] 13 (by decide) (choices 1) [1,32] r13662 c13662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2861
  · exact u2862

def b13663 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 134 280 49 33 68 196 324), lower := (rows 11 38 134 280 49 33 64 128 256), losses := [] }

theorem u13663 : Upper (D 6) (R 6) [10,36,130,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13664 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 280 49 36 65 193 321), lower := (rows 11 38 134 280 49 36 64 128 256), losses := [] }

theorem u13664 : Upper (D 6) (R 6) [10,36,130,272,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13665 : Route 9 := (fun mask => (mask,id))

def c13665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13665 : Upper (D 6) (R 6) [10,36,130,272,33,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,33,64] 13 (by decide) (choices 1) [1,4] r13665 c13665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2863
  · exact u2864

def b13666 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 280 81 33 100 228 356), lower := (rows 11 38 134 280 81 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 49 66 130 258), good := (rows 505 484 452 312 121 57 64 128 256) }] }

theorem u13666 : Upper (D 6) (R 6) [10,36,130,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13667 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 280 81 36 97 225 353), lower := (rows 11 38 134 280 81 36 64 128 256), losses := [] }

theorem u13667 : Upper (D 6) (R 6) [10,36,130,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13668 : Route 9 := (fun mask => (mask,id))

def c13668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13668 : Upper (D 6) (R 6) [10,36,130,272,65,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,65,64] 13 (by decide) (choices 1) [1,4,32] r13668 c13668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2865
  · exact u2866
  · exact u2867

def r13669 : Route 9 := (fun mask => (mask,id))

def c13669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13669 : Upper (D 6) (R 6) [10,36,130,272,68,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,68,1] 13 (by decide) (choices 1) [1,32] r13669 c13669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2868
  · exact u2869

def r13670 : Route 9 := (fun mask => (mask,id))

def c13670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13670 : Upper (D 6) (R 6) [10,36,130,272,68,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,68,64] 13 (by decide) (choices 1) [1,32] r13670 c13670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2870
  · exact u2871

def r13671 : Route 9 := (fun mask => (mask,id))

def c13671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13671 : Upper (D 6) (R 6) [10,36,130,272,96,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,96,1] 13 (by decide) (choices 1) [1,4] r13671 c13671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2872
  · exact u2873

def b13672 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 280 112 36 65 193 321), lower := (rows 11 38 134 280 112 36 64 128 256), losses := [] }

theorem u13672 : Upper (D 6) (R 6) [10,36,130,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13673 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 280 112 96 69 133 261), lower := (rows 11 38 134 280 112 96 64 128 256), losses := [] }

theorem u13673 : Upper (D 6) (R 6) [10,36,130,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13674 : Route 9 := (fun mask => (mask,id))

def c13674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13674 : Upper (D 6) (R 6) [10,36,130,288,65,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,288,65,1] 13 (by decide) (choices 1) [4,16] r13674 c13674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2874
  · exact u2875

def b13675 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 296 81 36 81 209 337), lower := (rows 11 38 134 296 81 36 64 128 256), losses := [] }

theorem u13675 : Upper (D 6) (R 6) [10,36,130,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13676 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 296 81 48 69 197 325), lower := (rows 11 38 134 296 81 48 64 128 256), losses := [] }

theorem u13676 : Upper (D 6) (R 6) [10,36,130,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13676 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13677 : Route 9 := (fun mask => (mask,id))

def c13677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13677 : Upper (D 6) (R 6) [10,36,130,288,65,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,288,65,64] 13 (by decide) (choices 1) [1,4,16] r13677 c13677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2876
  · exact u2877
  · exact u2878

def r13678 : Route 9 := (fun mask => (mask,id))

def c13678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13678 : Upper (D 6) (R 6) [10,36,130,288,68,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,288,68,1] 13 (by decide) (choices 1) [1,16] r13678 c13678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2879
  · exact u2880

def b13679 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 296 84 48 65 193 321), lower := (rows 11 38 134 296 84 48 64 128 256), losses := [] }

theorem u13679 : Upper (D 6) (R 6) [10,36,130,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13679 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13679
end Delivery.IrregularNine14.P06
