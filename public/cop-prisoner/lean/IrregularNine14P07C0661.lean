import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0463
import IrregularNine14P07C0464
import IrregularNine14P07C0465

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39660 : Route 9 := (fun mask => (mask,id))

def c39660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39660 : Upper (D 7) (R 7) [36,320,136,3,192] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,192] 13 (by decide) (choices 1) [1,2,16] r39660 c39660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27838
  · exact u27839
  · exact u27840

def b39661 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 322 140 25 19 226 226 226 482), lower := (rows 37 322 140 25 19 32 64 128 256), losses := [] }

theorem u39661 : Upper (D 7) (R 7) [36,320,136,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39662 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 140 25 49 226 194 194 450), lower := (rows 37 322 140 25 49 32 64 128 256), losses := [] }

theorem u39662 : Upper (D 7) (R 7) [36,320,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39663 : Route 9 := (fun mask => (mask,id))

def c39663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39663 : Upper (D 7) (R 7) [36,320,136,17,34] 13 := by
  apply FastRouting.sound _ _ [36,320,136,17,34] 13 (by decide) (choices 1) [1,2,64,128] r39663 c39663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27841
  · exact u27842
  · exact u27843
  · exact u27844

def b39664 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 322 140 25 81 162 226 162 418), lower := (rows 37 322 140 25 81 32 64 128 256), losses := [] }

theorem u39664 : Upper (D 7) (R 7) [36,320,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39665 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 140 25 82 163 227 163 419), lower := (rows 37 322 140 25 82 32 64 128 256), losses := [] }

theorem u39665 : Upper (D 7) (R 7) [36,320,136,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39666 : Route 9 := (fun mask => (mask,id))

def c39666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39666 : Upper (D 7) (R 7) [36,320,136,17,96] 13 := by
  apply FastRouting.sound _ _ [36,320,136,17,96] 13 (by decide) (choices 1) [1,2,128] r39666 c39666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27845
  · exact u27846
  · exact u27847

def b39667 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 322 140 25 145 98 98 226 354), lower := (rows 37 322 140 25 145 32 64 128 256), losses := [] }

theorem u39667 : Upper (D 7) (R 7) [36,320,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39668 : Route 9 := (fun mask => (mask,id))

def c39668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39668 : Upper (D 7) (R 7) [36,320,136,17,130] 13 := by
  apply FastRouting.sound _ _ [36,320,136,17,130] 13 (by decide) (choices 1) [1,2,64] r39668 c39668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27848
  · exact u27849
  · exact u27850

def b39669 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 13, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 140 25 176 99 67 195 323), lower := (rows 37 322 140 25 176 32 64 128 256), losses := [] }

theorem u39669 : Upper (D 7) (R 7) [36,320,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39670 : Route 9 := (fun mask => (mask,id))

def c39670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39670 : Upper (D 7) (R 7) [36,320,136,17,192] 13 := by
  apply FastRouting.sound _ _ [36,320,136,17,192] 13 (by decide) (choices 1) [1,2] r39670 c39670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27851
  · exact u27852

def b39671 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 140 26 19 225 225 225 481), lower := (rows 37 322 140 26 19 32 64 128 256), losses := [] }

theorem u39671 : Upper (D 7) (R 7) [36,320,136,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39672 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 140 26 49 227 195 195 451), lower := (rows 37 322 140 26 49 32 64 128 256), losses := [] }

theorem u39672 : Upper (D 7) (R 7) [36,320,136,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39673 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 140 26 50 225 193 193 449), lower := (rows 37 322 140 26 50 32 64 128 256), losses := [] }

theorem u39673 : Upper (D 7) (R 7) [36,320,136,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39674 : Route 9 := (fun mask => (mask,id))

def c39674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39674 : Upper (D 7) (R 7) [36,320,136,18,65] 13 := by
  apply FastRouting.sound _ _ [36,320,136,18,65] 13 (by decide) (choices 1) [1,2,128] r39674 c39674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27853
  · exact u27854
  · exact u27855

def b39675 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 322 140 26 82 161 225 161 417), lower := (rows 37 322 140 26 82 32 64 128 256), losses := [] }

theorem u39675 : Upper (D 7) (R 7) [36,320,136,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39676 : Route 9 := (fun mask => (mask,id))

def c39676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39676 : Upper (D 7) (R 7) [36,320,136,18,96] 13 := by
  apply FastRouting.sound _ _ [36,320,136,18,96] 13 (by decide) (choices 1) [1,2,128] r39676 c39676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27856
  · exact u27857
  · exact u27858

def r39677 : Route 9 := (fun mask => (mask,id))

def c39677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39677 : Upper (D 7) (R 7) [36,320,136,18,129] 13 := by
  apply FastRouting.sound _ _ [36,320,136,18,129] 13 (by decide) (choices 1) [1,2,64] r39677 c39677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27859
  · exact u27860
  · exact u27861

def b39678 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 37 322 140 26 146 97 97 225 353), lower := (rows 37 322 140 26 146 32 64 128 256), losses := [] }

theorem u39678 : Upper (D 7) (R 7) [36,320,136,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39679 : Route 9 := (fun mask => (mask,id))

def c39679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39679 : Upper (D 7) (R 7) [36,320,136,18,160] 13 := by
  apply FastRouting.sound _ _ [36,320,136,18,160] 13 (by decide) (choices 1) [1,2,64] r39679 c39679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27862
  · exact u27863
  · exact u27864

def b39680 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 37 322 140 26 208 35 99 163 291), lower := (rows 37 322 140 26 208 32 64 128 256), losses := [] }

theorem u39680 : Upper (D 7) (R 7) [36,320,136,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39681 : Route 9 := (fun mask => (mask,id))

def c39681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39681 : Upper (D 7) (R 7) [36,320,136,34,3] 13 := by
  apply FastRouting.sound _ _ [36,320,136,34,3] 13 (by decide) (choices 1) [1,16,64,128] r39681 c39681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27865
  · exact u27866
  · exact u27867
  · exact u27868

def r39682 : Route 9 := (fun mask => (mask,id))

def c39682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39682 : Upper (D 7) (R 7) [36,320,136,34,65] 13 := by
  apply FastRouting.sound _ _ [36,320,136,34,65] 13 (by decide) (choices 1) [1,2,16,128] r39682 c39682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27869
  · exact u27870
  · exact u27871
  · exact u27872

def b39683 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 140 42 82 177 209 145 401), lower := (rows 37 322 140 42 82 32 64 128 256), losses := [] }

theorem u39683 : Upper (D 7) (R 7) [36,320,136,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39684 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,5),(1,7),(3,7),(4,5)], upper := (rows 37 322 140 42 145 115 83 211 339), lower := (rows 37 322 140 42 145 32 64 128 256), losses := [] }

theorem u39684 : Upper (D 7) (R 7) [36,320,136,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39685 : Route 9 := (fun mask => (mask,id))

def c39685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39685 : Upper (D 7) (R 7) [36,320,136,34,130] 13 := by
  apply FastRouting.sound _ _ [36,320,136,34,130] 13 (by decide) (choices 1) [1,16,64] r39685 c39685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27873
  · exact u27874
  · exact u27875

def r39686 : Route 9 := (fun mask => (mask,id))

def c39686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39686 : Upper (D 7) (R 7) [36,320,136,34,192] 13 := by
  apply FastRouting.sound _ _ [36,320,136,34,192] 13 (by decide) (choices 1) [1,2,16] r39686 c39686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27876
  · exact u27877
  · exact u27878

def r39687 : Route 9 := (fun mask => (mask,id))

def c39687 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39687 : Upper (D 7) (R 7) [36,320,136,48,3] 13 := by
  apply FastRouting.sound _ _ [36,320,136,48,3] 13 (by decide) (choices 1) [1,2,64,128] r39687 c39687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27879
  · exact u27880
  · exact u27881
  · exact u27882

def r39688 : Route 9 := (fun mask => (mask,id))

def c39688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39688 : Upper (D 7) (R 7) [36,320,136,48,65] 13 := by
  apply FastRouting.sound _ _ [36,320,136,48,65] 13 (by decide) (choices 1) [1,2,128] r39688 c39688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27883
  · exact u27884
  · exact u27885

def b39689 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 140 56 82 163 195 131 387), lower := (rows 37 322 140 56 82 32 64 128 256), losses := [] }

theorem u39689 : Upper (D 7) (R 7) [36,320,136,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39690 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 37 322 140 56 145 99 67 195 323), lower := (rows 37 322 140 56 145 32 64 128 256), losses := [] }

theorem u39690 : Upper (D 7) (R 7) [36,320,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39691 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 37 322 140 56 146 99 67 195 323), lower := (rows 37 322 140 56 146 32 64 128 256), losses := [] }

theorem u39691 : Upper (D 7) (R 7) [36,320,136,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39692 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 37 322 140 56 208 35 67 131 259), lower := (rows 37 322 140 56 208 32 64 128 256), losses := [] }

theorem u39692 : Upper (D 7) (R 7) [36,320,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39693 : Route 9 := (fun mask => (mask,id))

def c39693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39693 : Upper (D 7) (R 7) [36,320,136,65,3] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,3] 13 (by decide) (choices 1) [2,16,128] r39693 c39693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27886
  · exact u27887
  · exact u27888

def b39694 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 140 73 49 178 210 146 402), lower := (rows 37 322 140 73 49 32 64 128 256), losses := [] }

theorem u39694 : Upper (D 7) (R 7) [36,320,136,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39695 : Route 9 := (fun mask => (mask,id))

def c39695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39695 : Upper (D 7) (R 7) [36,320,136,65,34] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,34] 13 (by decide) (choices 1) [1,2,16,128] r39695 c39695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27889
  · exact u27890
  · exact u27891
  · exact u27892

def r39696 : Route 9 := (fun mask => (mask,id))

def c39696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39696 : Upper (D 7) (R 7) [36,320,136,65,129] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,129] 13 (by decide) (choices 1) [2,16] r39696 c39696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27893
  · exact u27894

def r39697 : Route 9 := (fun mask => (mask,id))

def c39697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39697 : Upper (D 7) (R 7) [36,320,136,65,130] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,130] 13 (by decide) (choices 1) [1,2,16] r39697 c39697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27895
  · exact u27896
  · exact u27897

def r39698 : Route 9 := (fun mask => (mask,id))

def c39698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39698 : Upper (D 7) (R 7) [36,320,136,65,160] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,160] 13 (by decide) (choices 1) [1,2,16] r39698 c39698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27898
  · exact u27899
  · exact u27900

def r39699 : Route 9 := (fun mask => (mask,id))

def c39699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39699 : Upper (D 7) (R 7) [36,320,136,80,3] 13 := by
  apply FastRouting.sound _ _ [36,320,136,80,3] 13 (by decide) (choices 1) [1,2,128] r39699 c39699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27901
  · exact u27902
  · exact u27903

def b39700 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 140 88 49 163 195 131 387), lower := (rows 37 322 140 88 49 32 64 128 256), losses := [] }

theorem u39700 : Upper (D 7) (R 7) [36,320,136,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39701 : Route 9 := (fun mask => (mask,id))

def c39701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39701 : Upper (D 7) (R 7) [36,320,136,80,34] 13 := by
  apply FastRouting.sound _ _ [36,320,136,80,34] 13 (by decide) (choices 1) [1,2,128] r39701 c39701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27904
  · exact u27905
  · exact u27906

def r39702 : Route 9 := (fun mask => (mask,id))

def c39702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39702 : Upper (D 7) (R 7) [36,320,136,80,129] 13 := by
  apply FastRouting.sound _ _ [36,320,136,80,129] 13 (by decide) (choices 1) [1,2] r39702 c39702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27907
  · exact u27908

def r39703 : Route 9 := (fun mask => (mask,id))

def c39703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39703 : Upper (D 7) (R 7) [36,320,136,80,130] 13 := by
  apply FastRouting.sound _ _ [36,320,136,80,130] 13 (by decide) (choices 1) [1,2] r39703 c39703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27909
  · exact u27910

def r39704 : Route 9 := (fun mask => (mask,id))

def c39704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39704 : Upper (D 7) (R 7) [36,320,136,80,160] 13 := by
  apply FastRouting.sound _ _ [36,320,136,80,160] 13 (by decide) (choices 1) [1,2] r39704 c39704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27911
  · exact u27912

def r39705 : Route 9 := (fun mask => (mask,id))

def c39705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39705 : Upper (D 7) (R 7) [36,320,136,96,3] 13 := by
  apply FastRouting.sound _ _ [36,320,136,96,3] 13 (by decide) (choices 1) [1,2,16,128] r39705 c39705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27913
  · exact u27914
  · exact u27915
  · exact u27916

def b39706 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,5),(1,7),(3,7),(4,5)], upper := (rows 37 322 140 104 145 51 83 147 275), lower := (rows 37 322 140 104 145 32 64 128 256), losses := [] }

theorem u39706 : Upper (D 7) (R 7) [36,320,136,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39707 : Route 9 := (fun mask => (mask,id))

def c39707 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39707 : Upper (D 7) (R 7) [36,320,136,96,130] 13 := by
  apply FastRouting.sound _ _ [36,320,136,96,130] 13 (by decide) (choices 1) [1,2,16] r39707 c39707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27917
  · exact u27918
  · exact u27919

def b39708 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 16, targets := 160 },{ cop := 4, region := 8, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 37 322 196 11 19 184 248 184 440), lower := (rows 37 322 196 11 19 32 64 128 256), losses := [] }

theorem u39708 : Upper (D 7) (R 7) [36,320,192,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39709 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 322 196 11 25 178 242 178 434), lower := (rows 37 322 196 11 25 32 64 128 256), losses := [] }

theorem u39709 : Upper (D 7) (R 7) [36,320,192,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39710 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 322 196 11 26 177 241 177 433), lower := (rows 37 322 196 11 26 32 64 128 256), losses := [] }

theorem u39710 : Upper (D 7) (R 7) [36,320,192,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39711 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 196 11 49 186 218 154 410), lower := (rows 37 322 196 11 49 32 64 128 256), losses := [] }

theorem u39711 : Upper (D 7) (R 7) [36,320,192,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39712 : Route 9 := (fun mask => (mask,id))

def c39712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39712 : Upper (D 7) (R 7) [36,320,192,3,34] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,34] 13 (by decide) (choices 1) [1,8,16,128] r39712 c39712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27920
  · exact u27921
  · exact u27922
  · exact u27923

def r39713 : Route 9 := (fun mask => (mask,id))

def c39713 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39713 : Upper (D 7) (R 7) [36,320,192,3,40] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,40] 13 (by decide) (choices 1) [1,2,16,128] r39713 c39713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27924
  · exact u27925
  · exact u27926
  · exact u27927

def r39714 : Route 9 := (fun mask => (mask,id))

def c39714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39714 : Upper (D 7) (R 7) [36,320,192,3,129] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,129] 13 (by decide) (choices 1) [2,8,16] r39714 c39714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27928
  · exact u27929
  · exact u27930

def r39715 : Route 9 := (fun mask => (mask,id))

def c39715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39715 : Upper (D 7) (R 7) [36,320,192,3,130] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,130] 13 (by decide) (choices 1) [1,8,16] r39715 c39715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27931
  · exact u27932
  · exact u27933

def r39716 : Route 9 := (fun mask => (mask,id))

def c39716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39716 : Upper (D 7) (R 7) [36,320,192,3,136] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,136] 13 (by decide) (choices 1) [1,2,16] r39716 c39716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27934
  · exact u27935
  · exact u27936

def r39717 : Route 9 := (fun mask => (mask,id))

def c39717 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39717 : Upper (D 7) (R 7) [36,320,192,3,160] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,160] 13 (by decide) (choices 1) [1,2,8,16] r39717 c39717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27937
  · exact u27938
  · exact u27939
  · exact u27940

def b39718 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 322 196 25 25 162 226 162 418), lower := (rows 37 322 196 25 25 32 64 128 256), losses := [] }

theorem u39718 : Upper (D 7) (R 7) [36,320,192,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39719 : Route 9 := (fun mask => (mask,id))

def c39719 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39719 : Upper (D 7) (R 7) [36,320,192,17,10] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,10] 13 (by decide) (choices 1) [1,2,128] r39719 c39719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27941
  · exact u27942
  · exact u27943

#print axioms u39719
end Delivery.IrregularNine14.P07
