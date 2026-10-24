import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0414
import IrregularNine14P06C0415
import IrregularNine14P06C0416

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38820 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 194 261 42 88 53 85 149 277), lower := (rows 35 194 261 42 88 32 64 128 256), losses := [] }

theorem u38820 : Upper (D 6) (R 6) [34,192,257,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38821 : Route 9 := (fun mask => (mask,id))

def c38821 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38821 : Upper (D 6) (R 6) [34,192,257,36,65] 13 := by
  apply FastRouting.sound _ _ [34,192,257,36,65] 13 (by decide) (choices 1) [2,4,8,16] r38821 c38821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24892
  · exact u24893
  · exact u24894
  · exact u24895

def b38822 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 261 44 82 61 93 157 285), lower := (rows 35 194 261 44 82 32 64 128 256), losses := [] }

theorem u38822 : Upper (D 6) (R 6) [34,192,257,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38823 : Route 9 := (fun mask => (mask,id))

def c38823 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38823 : Upper (D 6) (R 6) [34,192,257,36,68] 13 := by
  apply FastRouting.sound _ _ [34,192,257,36,68] 13 (by decide) (choices 1) [1,2,8,16] r38823 c38823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24896
  · exact u24897
  · exact u24898
  · exact u24899

def r38824 : Route 9 := (fun mask => (mask,id))

def c38824 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38824 : Upper (D 6) (R 6) [34,192,257,36,72] 13 := by
  apply FastRouting.sound _ _ [34,192,257,36,72] 13 (by decide) (choices 1) [1,2,4,16] r38824 c38824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24900
  · exact u24901
  · exact u24902
  · exact u24903

def r38825 : Route 9 := (fun mask => (mask,id))

def c38825 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38825 : Upper (D 6) (R 6) [34,192,257,48,65] 13 := by
  apply FastRouting.sound _ _ [34,192,257,48,65] 13 (by decide) (choices 1) [2,4,8] r38825 c38825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24904
  · exact u24905
  · exact u24906

def b38826 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 261 56 82 45 77 141 269), lower := (rows 35 194 261 56 82 32 64 128 256), losses := [] }

theorem u38826 : Upper (D 6) (R 6) [34,192,257,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38827 : Route 9 := (fun mask => (mask,id))

def c38827 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38827 : Upper (D 6) (R 6) [34,192,257,48,68] 13 := by
  apply FastRouting.sound _ _ [34,192,257,48,68] 13 (by decide) (choices 1) [1,2,4,8] r38827 c38827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24907
  · exact u24908
  · exact u24909
  · exact u24910

def b38828 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 194 261 56 88 39 71 135 263), lower := (rows 35 194 261 56 88 32 64 128 256), losses := [] }

theorem u38828 : Upper (D 6) (R 6) [34,192,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38829 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 96 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 35 194 262 13 21 120 120 248 376), lower := (rows 35 194 262 13 21 32 64 128 256), losses := [] }

theorem u38829 : Upper (D 6) (R 6) [34,192,258,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38830 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 262 13 25 116 116 244 372), lower := (rows 35 194 262 13 25 32 64 128 256), losses := [] }

theorem u38830 : Upper (D 6) (R 6) [34,192,258,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38831 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 194 262 13 28 113 113 241 369), lower := (rows 35 194 262 13 28 32 64 128 256), losses := [] }

theorem u38831 : Upper (D 6) (R 6) [34,192,258,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38832 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 262 13 49 124 92 220 348), lower := (rows 35 194 262 13 49 32 64 128 256), losses := [] }

theorem u38832 : Upper (D 6) (R 6) [34,192,258,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38833 : Route 9 := (fun mask => (mask,id))

def c38833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38833 : Upper (D 6) (R 6) [34,192,258,5,36] 13 := by
  apply FastRouting.sound _ _ [34,192,258,5,36] 13 (by decide) (choices 1) [1,8,16,64] r38833 c38833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24911
  · exact u24912
  · exact u24913
  · exact u24914

def r38834 : Route 9 := (fun mask => (mask,id))

def c38834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38834 : Upper (D 6) (R 6) [34,192,258,5,40] 13 := by
  apply FastRouting.sound _ _ [34,192,258,5,40] 13 (by decide) (choices 1) [1,4,16,64] r38834 c38834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24915
  · exact u24916
  · exact u24917
  · exact u24918

def r38835 : Route 9 := (fun mask => (mask,id))

def c38835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38835 : Upper (D 6) (R 6) [34,192,258,5,65] 13 := by
  apply FastRouting.sound _ _ [34,192,258,5,65] 13 (by decide) (choices 1) [4,8,16] r38835 c38835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24919
  · exact u24920
  · exact u24921

def r38836 : Route 9 := (fun mask => (mask,id))

def c38836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38836 : Upper (D 6) (R 6) [34,192,258,5,68] 13 := by
  apply FastRouting.sound _ _ [34,192,258,5,68] 13 (by decide) (choices 1) [1,8,16] r38836 c38836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24922
  · exact u24923
  · exact u24924

def r38837 : Route 9 := (fun mask => (mask,id))

def c38837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38837 : Upper (D 6) (R 6) [34,192,258,5,72] 13 := by
  apply FastRouting.sound _ _ [34,192,258,5,72] 13 (by decide) (choices 1) [1,4,16] r38837 c38837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24925
  · exact u24926
  · exact u24927

def r38838 : Route 9 := (fun mask => (mask,id))

def c38838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38838 : Upper (D 6) (R 6) [34,192,258,5,96] 13 := by
  apply FastRouting.sound _ _ [34,192,258,5,96] 13 (by decide) (choices 1) [1,4,8,16] r38838 c38838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24928
  · exact u24929
  · exact u24930
  · exact u24931

def b38839 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 262 25 25 100 100 228 356), lower := (rows 35 194 262 25 25 32 64 128 256), losses := [] }

theorem u38839 : Upper (D 6) (R 6) [34,192,258,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38840 : Route 9 := (fun mask => (mask,id))

def c38840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38840 : Upper (D 6) (R 6) [34,192,258,17,12] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,12] 13 (by decide) (choices 1) [1,4,64] r38840 c38840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24932
  · exact u24933
  · exact u24934

def b38841 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 262 25 49 108 76 204 332), lower := (rows 35 194 262 25 49 32 64 128 256), losses := [] }

theorem u38841 : Upper (D 6) (R 6) [34,192,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38842 : Route 9 := (fun mask => (mask,id))

def c38842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38842 : Upper (D 6) (R 6) [34,192,258,17,36] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,36] 13 (by decide) (choices 1) [1,4,8,64] r38842 c38842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24935
  · exact u24936
  · exact u24937
  · exact u24938

def b38843 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 262 25 56 101 69 197 325), lower := (rows 35 194 262 25 56 32 64 128 256), losses := [] }

theorem u38843 : Upper (D 6) (R 6) [34,192,258,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38844 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 262 25 81 44 108 172 300), lower := (rows 35 194 262 25 81 32 64 128 256), losses := [] }

theorem u38844 : Upper (D 6) (R 6) [34,192,258,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38845 : Route 9 := (fun mask => (mask,id))

def c38845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38845 : Upper (D 6) (R 6) [34,192,258,17,68] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,68] 13 (by decide) (choices 1) [1,4,8] r38845 c38845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24939
  · exact u24940
  · exact u24941

def r38846 : Route 9 := (fun mask => (mask,id))

def c38846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38846 : Upper (D 6) (R 6) [34,192,258,17,72] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,72] 13 (by decide) (choices 1) [1,4] r38846 c38846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24942
  · exact u24943

def r38847 : Route 9 := (fun mask => (mask,id))

def c38847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38847 : Upper (D 6) (R 6) [34,192,258,17,96] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,96] 13 (by decide) (choices 1) [1,4,8] r38847 c38847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24944
  · exact u24945
  · exact u24946

def b38848 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 262 28 28 97 97 225 353), lower := (rows 35 194 262 28 28 32 64 128 256), losses := [] }

theorem u38848 : Upper (D 6) (R 6) [34,192,258,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38849 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 262 28 49 109 77 205 333), lower := (rows 35 194 262 28 49 32 64 128 256), losses := [] }

theorem u38849 : Upper (D 6) (R 6) [34,192,258,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38850 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 262 28 52 105 73 201 329), lower := (rows 35 194 262 28 52 32 64 128 256), losses := [] }

theorem u38850 : Upper (D 6) (R 6) [34,192,258,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38851 : Route 9 := (fun mask => (mask,id))

def c38851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38851 : Upper (D 6) (R 6) [34,192,258,20,40] 13 := by
  apply FastRouting.sound _ _ [34,192,258,20,40] 13 (by decide) (choices 1) [1,4,64] r38851 c38851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24947
  · exact u24948
  · exact u24949

def r38852 : Route 9 := (fun mask => (mask,id))

def c38852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38852 : Upper (D 6) (R 6) [34,192,258,20,65] 13 := by
  apply FastRouting.sound _ _ [34,192,258,20,65] 13 (by decide) (choices 1) [1,4,8] r38852 c38852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24950
  · exact u24951
  · exact u24952

def b38853 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 262 28 84 41 105 169 297), lower := (rows 35 194 262 28 84 32 64 128 256), losses := [] }

theorem u38853 : Upper (D 6) (R 6) [34,192,258,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38854 : Route 9 := (fun mask => (mask,id))

def c38854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38854 : Upper (D 6) (R 6) [34,192,258,20,72] 13 := by
  apply FastRouting.sound _ _ [34,192,258,20,72] 13 (by decide) (choices 1) [1,4] r38854 c38854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24953
  · exact u24954

def r38855 : Route 9 := (fun mask => (mask,id))

def c38855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38855 : Upper (D 6) (R 6) [34,192,258,20,96] 13 := by
  apply FastRouting.sound _ _ [34,192,258,20,96] 13 (by decide) (choices 1) [1,4,8] r38855 c38855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24955
  · exact u24956
  · exact u24957

def b38856 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 262 41 81 60 92 156 284), lower := (rows 35 194 262 41 81 32 64 128 256), losses := [] }

theorem u38856 : Upper (D 6) (R 6) [34,192,258,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38857 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 262 41 84 61 93 157 285), lower := (rows 35 194 262 41 84 32 64 128 256), losses := [] }

theorem u38857 : Upper (D 6) (R 6) [34,192,258,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38858 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 262 41 88 53 85 149 277), lower := (rows 35 194 262 41 88 32 64 128 256), losses := [] }

theorem u38858 : Upper (D 6) (R 6) [34,192,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38859 : Route 9 := (fun mask => (mask,id))

def c38859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38859 : Upper (D 6) (R 6) [34,192,258,36,65] 13 := by
  apply FastRouting.sound _ _ [34,192,258,36,65] 13 (by decide) (choices 1) [1,4,8,16] r38859 c38859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24958
  · exact u24959
  · exact u24960
  · exact u24961

def r38860 : Route 9 := (fun mask => (mask,id))

def c38860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38860 : Upper (D 6) (R 6) [34,192,258,36,68] 13 := by
  apply FastRouting.sound _ _ [34,192,258,36,68] 13 (by decide) (choices 1) [1,8,16] r38860 c38860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24962
  · exact u24963
  · exact u24964

def r38861 : Route 9 := (fun mask => (mask,id))

def c38861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38861 : Upper (D 6) (R 6) [34,192,258,36,72] 13 := by
  apply FastRouting.sound _ _ [34,192,258,36,72] 13 (by decide) (choices 1) [1,4,16] r38861 c38861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24965
  · exact u24966
  · exact u24967

def r38862 : Route 9 := (fun mask => (mask,id))

def c38862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38862 : Upper (D 6) (R 6) [34,192,258,48,65] 13 := by
  apply FastRouting.sound _ _ [34,192,258,48,65] 13 (by decide) (choices 1) [1,4,8] r38862 c38862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24968
  · exact u24969
  · exact u24970

def r38863 : Route 9 := (fun mask => (mask,id))

def c38863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38863 : Upper (D 6) (R 6) [34,192,258,48,68] 13 := by
  apply FastRouting.sound _ _ [34,192,258,48,68] 13 (by decide) (choices 1) [1,4,8] r38863 c38863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24971
  · exact u24972
  · exact u24973

def b38864 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 194 262 56 88 37 69 133 261), lower := (rows 35 194 262 56 88 32 64 128 256), losses := [] }

theorem u38864 : Upper (D 6) (R 6) [34,192,258,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38865 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 268 13 19 116 116 244 372), lower := (rows 35 194 268 13 19 32 64 128 256), losses := [] }

theorem u38865 : Upper (D 6) (R 6) [34,192,264,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38866 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 194 268 13 21 114 114 242 370), lower := (rows 35 194 268 13 21 32 64 128 256), losses := [] }

theorem u38866 : Upper (D 6) (R 6) [34,192,264,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38867 : Route 9 := (fun mask => (mask,id))

def c38867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38867 : Upper (D 6) (R 6) [34,192,264,5,6] 13 := by
  apply FastRouting.sound _ _ [34,192,264,5,6] 13 (by decide) (choices 1) [1,16,64] r38867 c38867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24974
  · exact u24975
  · exact u24976

def b38868 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 268 13 49 118 86 214 342), lower := (rows 35 194 268 13 49 32 64 128 256), losses := [] }

theorem u38868 : Upper (D 6) (R 6) [34,192,264,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38869 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 268 13 50 117 85 213 341), lower := (rows 35 194 268 13 50 32 64 128 256), losses := [] }

theorem u38869 : Upper (D 6) (R 6) [34,192,264,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38870 : Route 9 := (fun mask => (mask,id))

def c38870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38870 : Upper (D 6) (R 6) [34,192,264,5,36] 13 := by
  apply FastRouting.sound _ _ [34,192,264,5,36] 13 (by decide) (choices 1) [1,2,16,64] r38870 c38870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24977
  · exact u24978
  · exact u24979
  · exact u24980

def r38871 : Route 9 := (fun mask => (mask,id))

def c38871 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38871 : Upper (D 6) (R 6) [34,192,264,5,65] 13 := by
  apply FastRouting.sound _ _ [34,192,264,5,65] 13 (by decide) (choices 1) [2,4,16] r38871 c38871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24981
  · exact u24982
  · exact u24983

def b38872 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 268 13 82 53 117 181 309), lower := (rows 35 194 268 13 82 32 64 128 256), losses := [] }

theorem u38872 : Upper (D 6) (R 6) [34,192,264,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38873 : Route 9 := (fun mask => (mask,id))

def c38873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38873 : Upper (D 6) (R 6) [34,192,264,5,68] 13 := by
  apply FastRouting.sound _ _ [34,192,264,5,68] 13 (by decide) (choices 1) [1,2,16] r38873 c38873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24984
  · exact u24985
  · exact u24986

def r38874 : Route 9 := (fun mask => (mask,id))

def c38874 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38874 : Upper (D 6) (R 6) [34,192,264,5,96] 13 := by
  apply FastRouting.sound _ _ [34,192,264,5,96] 13 (by decide) (choices 1) [1,2,4,16] r38874 c38874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24987
  · exact u24988
  · exact u24989
  · exact u24990

def r38875 : Route 9 := (fun mask => (mask,id))

def c38875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38875 : Upper (D 6) (R 6) [34,192,264,6,5] 13 := by
  apply FastRouting.sound _ _ [34,192,264,6,5] 13 (by decide) (choices 1) [1,16,64] r38875 c38875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24991
  · exact u24992
  · exact u24993

def b38876 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 268 14 49 117 85 213 341), lower := (rows 35 194 268 14 49 32 64 128 256), losses := [] }

theorem u38876 : Upper (D 6) (R 6) [34,192,264,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38877 : Route 9 := (fun mask => (mask,id))

def c38877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38877 : Upper (D 6) (R 6) [34,192,264,6,36] 13 := by
  apply FastRouting.sound _ _ [34,192,264,6,36] 13 (by decide) (choices 1) [1,16,64] r38877 c38877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24994
  · exact u24995
  · exact u24996

def r38878 : Route 9 := (fun mask => (mask,id))

def c38878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38878 : Upper (D 6) (R 6) [34,192,264,6,65] 13 := by
  apply FastRouting.sound _ _ [34,192,264,6,65] 13 (by decide) (choices 1) [1,4,16] r38878 c38878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24997
  · exact u24998
  · exact u24999

def r38879 : Route 9 := (fun mask => (mask,id))

def c38879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38879 : Upper (D 6) (R 6) [34,192,264,6,68] 13 := by
  apply FastRouting.sound _ _ [34,192,264,6,68] 13 (by decide) (choices 1) [1,16] r38879 c38879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25000
  · exact u25001

#print axioms u38879
end Delivery.IrregularNine14.P06
