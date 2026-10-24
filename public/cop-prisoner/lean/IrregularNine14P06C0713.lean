import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0614
import IrregularNine14P06C0615
import IrregularNine14P06C0616
import IrregularNine14P06C0617
import IrregularNine14P06C0618
import IrregularNine14P06C0619

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42780 : Route 9 := (fun mask => (mask,id))

def c42780 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42780 : Upper (D 6) (R 6) [34,72,192,258] 13 := by
  apply FastRouting.sound _ _ [34,72,192,258] 13 (by decide) (choices 2) [5,33,36] r42780 c42780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36878
  · exact u36879
  · exact u36880

def r42781 : Route 9 := (fun mask => (mask,id))

def c42781 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42781 : Upper (D 6) (R 6) [34,72,192,260] 13 := by
  apply FastRouting.sound _ _ [34,72,192,260] 13 (by decide) (choices 2) [3,5,6,33,34,36] r42781 c42781
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36881
  · exact u36882
  · exact u36883
  · exact u36884
  · exact u36885
  · exact u36886

def r42782 : Route 9 := (fun mask => (mask,id))

def c42782 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42782 : Upper (D 6) (R 6) [34,72,192,272] 13 := by
  apply FastRouting.sound _ _ [34,72,192,272] 13 (by decide) (choices 2) [3,5,6,33,34,36] r42782 c42782
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36887
  · exact u36888
  · exact u36889
  · exact u36890
  · exact u36891
  · exact u36892

def r42783 : Route 9 := (fun mask => (mask,id))

def c42783 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42783 : Upper (D 6) (R 6) [34,72,192,288] 13 := by
  apply FastRouting.sound _ _ [34,72,192,288] 13 (by decide) (choices 2) [3,5,6] r42783 c42783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36893
  · exact u36894
  · exact u36895

def b42784 : PairBound 9 := { available := 117, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 388 11 117 117 117 245 373), lower := (rows 35 74 388 11 16 32 64 128 256), losses := [] }

theorem u42784 : Upper (D 6) (R 6) [34,72,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42785 : Route 9 := (fun mask => (mask,id))

def c42785 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42785 : Upper (D 6) (R 6) [34,72,384,5] 13 := by
  apply FastRouting.sound _ _ [34,72,384,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42785 c42785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36896
  · exact u36897
  · exact u36898
  · exact u36899
  · exact u36900
  · exact u36901
  · exact u36902
  · exact u36903
  · exact u36904
  · exact u36905

def r42786 : Route 9 := (fun mask => (mask,id))

def c42786 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42786 : Upper (D 6) (R 6) [34,72,384,6] 13 := by
  apply FastRouting.sound _ _ [34,72,384,6] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42786 c42786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36906
  · exact u36907
  · exact u36908
  · exact u36909
  · exact u36910
  · exact u36911

def r42787 : Route 9 := (fun mask => (mask,id))

def c42787 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42787 : Upper (D 6) (R 6) [34,72,384,17] 13 := by
  apply FastRouting.sound _ _ [34,72,384,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42787 c42787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36912
  · exact u36913
  · exact u36914
  · exact u36915
  · exact u36916
  · exact u36917
  · exact u36918
  · exact u36919
  · exact u36920
  · exact u36921

def r42788 : Route 9 := (fun mask => (mask,id))

def c42788 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42788 : Upper (D 6) (R 6) [34,72,384,18] 13 := by
  apply FastRouting.sound _ _ [34,72,384,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42788 c42788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36922
  · exact u36923
  · exact u36924
  · exact u36925
  · exact u36926
  · exact u36927

def r42789 : Route 9 := (fun mask => (mask,id))

def c42789 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42789 : Upper (D 6) (R 6) [34,72,384,20] 13 := by
  apply FastRouting.sound _ _ [34,72,384,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42789 c42789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36928
  · exact u36929
  · exact u36930
  · exact u36931
  · exact u36932
  · exact u36933
  · exact u36934
  · exact u36935
  · exact u36936
  · exact u36937

def b42790 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 388 41 87 119 87 215 343), lower := (rows 35 74 388 41 16 32 64 128 256), losses := [] }

theorem u42790 : Upper (D 6) (R 6) [34,72,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42791 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 74 388 42 85 117 85 213 341), lower := (rows 35 74 388 42 16 32 64 128 256), losses := [] }

theorem u42791 : Upper (D 6) (R 6) [34,72,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42792 : Route 9 := (fun mask => (mask,id))

def c42792 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42792 : Upper (D 6) (R 6) [34,72,384,36] 13 := by
  apply FastRouting.sound _ _ [34,72,384,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42792 c42792
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36938
  · exact u36939
  · exact u36940
  · exact u36941
  · exact u36942
  · exact u36943

def r42793 : Route 9 := (fun mask => (mask,id))

def c42793 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42793 : Upper (D 6) (R 6) [34,72,384,48] 13 := by
  apply FastRouting.sound _ _ [34,72,384,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42793 c42793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36944
  · exact u36945
  · exact u36946
  · exact u36947
  · exact u36948
  · exact u36949

def b42794 : PairBound 9 := { available := 55, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 388 73 55 55 119 183 311), lower := (rows 35 74 388 73 16 32 64 128 256), losses := [] }

theorem u42794 : Upper (D 6) (R 6) [34,72,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42795 : PairBound 9 := { available := 53, camps := [{ cop := 6, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 388 74 53 53 117 181 309), lower := (rows 35 74 388 74 16 32 64 128 256), losses := [] }

theorem u42795 : Upper (D 6) (R 6) [34,72,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42796 : PairBound 9 := { available := 55, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 388 76 55 55 119 183 311), lower := (rows 35 74 388 76 16 32 64 128 256), losses := [] }

theorem u42796 : Upper (D 6) (R 6) [34,72,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42797 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 388 88 55 39 103 167 295), lower := (rows 35 74 388 88 16 32 64 128 256), losses := [] }

theorem u42797 : Upper (D 6) (R 6) [34,72,384,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42798 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 388 104 23 55 87 151 279), lower := (rows 35 74 388 104 16 32 64 128 256), losses := [] }

theorem u42798 : Upper (D 6) (R 6) [34,72,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42799 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 44 11 340 372 340 468 340), lower := (rows 35 131 44 11 16 32 64 128 256), losses := [] }

theorem u42799 : Upper (D 6) (R 6) [34,129,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42800 : PairBound 9 := { available := 342, camps := [{ cop := 0, region := 12, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 131 44 13 342 374 342 470 342), lower := (rows 35 131 44 13 16 32 64 128 256), losses := [] }

theorem u42800 : Upper (D 6) (R 6) [34,129,40,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42801 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 12, targets := 1 },{ cop := 0, region := 12, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 35 131 44 14 341 373 341 469 341), lower := (rows 35 131 44 14 16 32 64 128 256), losses := [] }

theorem u42801 : Upper (D 6) (R 6) [34,129,40,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42802 : Route 9 := (fun mask => (mask,id))

def c42802 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42802 : Upper (D 6) (R 6) [34,129,40,17] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42802 c42802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36950
  · exact u36951
  · exact u36952
  · exact u36953
  · exact u36954
  · exact u36955

def r42803 : Route 9 := (fun mask => (mask,id))

def c42803 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42803 : Upper (D 6) (R 6) [34,129,40,18] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42803 c42803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36956
  · exact u36957
  · exact u36958
  · exact u36959
  · exact u36960
  · exact u36961

def r42804 : Route 9 := (fun mask => (mask,id))

def c42804 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42804 : Upper (D 6) (R 6) [34,129,40,20] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42804 c42804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36962
  · exact u36963
  · exact u36964
  · exact u36965
  · exact u36966
  · exact u36967
  · exact u36968
  · exact u36969
  · exact u36970
  · exact u36971

def r42805 : Route 9 := (fun mask => (mask,id))

def c42805 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42805 : Upper (D 6) (R 6) [34,129,40,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42805 c42805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36972
  · exact u36973
  · exact u36974
  · exact u36975
  · exact u36976
  · exact u36977

def r42806 : Route 9 := (fun mask => (mask,id))

def c42806 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42806 : Upper (D 6) (R 6) [34,129,40,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42806 c42806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36978
  · exact u36979
  · exact u36980
  · exact u36981
  · exact u36982
  · exact u36983

def r42807 : Route 9 := (fun mask => (mask,id))

def c42807 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42807 : Upper (D 6) (R 6) [34,129,40,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42807 c42807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36984
  · exact u36985
  · exact u36986
  · exact u36987
  · exact u36988
  · exact u36989
  · exact u36990
  · exact u36991
  · exact u36992
  · exact u36993

def r42808 : Route 9 := (fun mask => (mask,id))

def c42808 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42808 : Upper (D 6) (R 6) [34,129,40,80] 13 := by
  apply FastRouting.sound _ _ [34,129,40,80] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42808 c42808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36994
  · exact u36995
  · exact u36996
  · exact u36997
  · exact u36998
  · exact u36999
  · exact u37000
  · exact u37001
  · exact u37002
  · exact u37003

def r42809 : Route 9 := (fun mask => (mask,id))

def c42809 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42809 : Upper (D 6) (R 6) [34,129,40,257] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257] 13 (by decide) (choices 2) [6,66,68] r42809 c42809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37004
  · exact u37005
  · exact u37006

def r42810 : Route 9 := (fun mask => (mask,id))

def c42810 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42810 : Upper (D 6) (R 6) [34,129,40,258] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258] 13 (by decide) (choices 2) [5,65,68] r42810 c42810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37007
  · exact u37008
  · exact u37009

def r42811 : Route 9 := (fun mask => (mask,id))

def c42811 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42811 : Upper (D 6) (R 6) [34,129,40,260] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42811 c42811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37010
  · exact u37011
  · exact u37012
  · exact u37013
  · exact u37014
  · exact u37015

def r42812 : Route 9 := (fun mask => (mask,id))

def c42812 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42812 : Upper (D 6) (R 6) [34,129,40,272] 13 := by
  apply FastRouting.sound _ _ [34,129,40,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42812 c42812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37016
  · exact u37017
  · exact u37018
  · exact u37019
  · exact u37020
  · exact u37021

def r42813 : Route 9 := (fun mask => (mask,id))

def c42813 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42813 : Upper (D 6) (R 6) [34,129,40,320] 13 := by
  apply FastRouting.sound _ _ [34,129,40,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42813 c42813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37022
  · exact u37023
  · exact u37024
  · exact u37025
  · exact u37026
  · exact u37027

def r42814 : Route 9 := (fun mask => (mask,id))

def c42814 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42814 : Upper (D 6) (R 6) [34,129,66,5] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r42814 c42814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37028
  · exact u37029
  · exact u37030
  · exact u37031
  · exact u37032
  · exact u37033
  · exact u37034
  · exact u37035
  · exact u37036
  · exact u37037

def r42815 : Route 9 := (fun mask => (mask,id))

def c42815 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42815 : Upper (D 6) (R 6) [34,129,66,17] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r42815 c42815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37038
  · exact u37039
  · exact u37040
  · exact u37041
  · exact u37042
  · exact u37043
  · exact u37044
  · exact u37045
  · exact u37046
  · exact u37047

theorem m42816_5 : Upper (D 6) (R 6) [34,129,66,20,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37028

theorem m42816_9 : Upper (D 6) (R 6) [34,129,66,20,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37038

def r42816 : Route 9 := (fun mask => (mask,id))

def c42816 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42816 : Upper (D 6) (R 6) [34,129,66,20] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,257,260,264,288,320] r42816 c42816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42816_5
  · exact m42816_9
  · exact u37048
  · exact u37049
  · exact u37050
  · exact u37051
  · exact u37052
  · exact u37053
  · exact u37054
  · exact u37055
  · exact u37056
  · exact u37057
  · exact u37058
  · exact u37059
  · exact u37060

def b42817 : PairBound 9 := { available := 348, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 70 41 348 380 348 476 348), lower := (rows 35 131 70 41 16 32 64 128 256), losses := [] }

theorem u42817 : Upper (D 6) (R 6) [34,129,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42818_5 : Upper (D 6) (R 6) [34,129,66,36,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37029

theorem m42818_9 : Upper (D 6) (R 6) [34,129,66,36,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37039

theorem m42818_12 : Upper (D 6) (R 6) [34,129,66,36,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37050

def r42818 : Route 9 := (fun mask => (mask,id))

def c42818 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42818 : Upper (D 6) (R 6) [34,129,66,36] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r42818 c42818
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42818_5
  · exact m42818_9
  · exact m42818_12
  · exact u37065
  · exact u37066
  · exact u37067
  · exact u37068
  · exact u37069
  · exact u37070
  · exact u37071

theorem m42819_5 : Upper (D 6) (R 6) [34,129,66,48,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37030

theorem m42819_9 : Upper (D 6) (R 6) [34,129,66,48,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37040

theorem m42819_12 : Upper (D 6) (R 6) [34,129,66,48,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37051

def r42819 : Route 9 := (fun mask => (mask,id))

def c42819 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42819 : Upper (D 6) (R 6) [34,129,66,48] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r42819 c42819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42819_5
  · exact m42819_9
  · exact m42819_12
  · exact u37072
  · exact u37073
  · exact u37074
  · exact u37075
  · exact u37076
  · exact u37077
  · exact u37078

theorem m42820_12 : Upper (D 6) (R 6) [34,129,66,65,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37052

theorem m42820_36 : Upper (D 6) (R 6) [34,129,66,65,36] 13 :=
  permutation_upper _ _ _ [34,129,66,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37065

theorem m42820_40 : Upper (D 6) (R 6) [34,129,66,65,40] 13 :=
  permutation_upper _ _ _ [34,129,66,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37072

def r42820 : Route 9 := (fun mask => (mask,id))

def c42820 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42820 : Upper (D 6) (R 6) [34,129,66,65] 13 := by
  apply FastRouting.sound _ _ [34,129,66,65] 13 (by decide) (choices 2) [12,36,40,260,264,288] r42820 c42820
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42820_12
  · exact m42820_36
  · exact m42820_40
  · exact u37079
  · exact u37080
  · exact u37081

def b42821 : PairBound 9 := { available := 317, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 76 317 317 381 445 317), lower := (rows 35 131 70 76 16 32 64 128 256), losses := [] }

theorem u42821 : Upper (D 6) (R 6) [34,129,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42822_5 : Upper (D 6) (R 6) [34,129,66,80,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37032

theorem m42822_9 : Upper (D 6) (R 6) [34,129,66,80,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37042

theorem m42822_12 : Upper (D 6) (R 6) [34,129,66,80,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37054

theorem m42822_33 : Upper (D 6) (R 6) [34,129,66,80,33] 13 :=
  permutation_upper _ _ _ [34,129,66,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37061

theorem m42822_36 : Upper (D 6) (R 6) [34,129,66,80,36] 13 :=
  permutation_upper _ _ _ [34,129,66,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37067

theorem m42822_40 : Upper (D 6) (R 6) [34,129,66,80,40] 13 :=
  permutation_upper _ _ _ [34,129,66,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37074

def r42822 : Route 9 := (fun mask => (mask,id))

def c42822 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42822 : Upper (D 6) (R 6) [34,129,66,80] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r42822 c42822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42822_5
  · exact m42822_9
  · exact m42822_12
  · exact m42822_33
  · exact m42822_36
  · exact m42822_40
  · exact u37086
  · exact u37087
  · exact u37088
  · exact u37089

theorem m42823_5 : Upper (D 6) (R 6) [34,129,66,96,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37033

theorem m42823_9 : Upper (D 6) (R 6) [34,129,66,96,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37043

theorem m42823_12 : Upper (D 6) (R 6) [34,129,66,96,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37055

def r42823 : Route 9 := (fun mask => (mask,id))

def c42823 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42823 : Upper (D 6) (R 6) [34,129,66,96] 13 := by
  apply FastRouting.sound _ _ [34,129,66,96] 13 (by decide) (choices 2) [5,9,12,257,260,264] r42823 c42823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42823_5
  · exact m42823_9
  · exact m42823_12
  · exact u37090
  · exact u37091
  · exact u37092

theorem m42824_12 : Upper (D 6) (R 6) [34,129,66,257,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37056

theorem m42824_36 : Upper (D 6) (R 6) [34,129,66,257,36] 13 :=
  permutation_upper _ _ _ [34,129,66,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37068

theorem m42824_40 : Upper (D 6) (R 6) [34,129,66,257,40] 13 :=
  permutation_upper _ _ _ [34,129,66,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37075

theorem m42824_68 : Upper (D 6) (R 6) [34,129,66,257,68] 13 :=
  permutation_upper _ _ _ [34,129,66,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37082

theorem m42824_72 : Upper (D 6) (R 6) [34,129,66,257,72] 13 :=
  permutation_upper _ _ _ [34,129,66,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37086

theorem m42824_96 : Upper (D 6) (R 6) [34,129,66,257,96] 13 :=
  permutation_upper _ _ _ [34,129,66,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37090

def r42824 : Route 9 := (fun mask => (mask,id))

def c42824 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42824 : Upper (D 6) (R 6) [34,129,66,257] 13 := by
  apply FastRouting.sound _ _ [34,129,66,257] 13 (by decide) (choices 2) [12,36,40,68,72,96] r42824 c42824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42824_12
  · exact m42824_36
  · exact m42824_40
  · exact m42824_68
  · exact m42824_72
  · exact m42824_96

theorem m42825_5 : Upper (D 6) (R 6) [34,129,66,260,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37034

theorem m42825_9 : Upper (D 6) (R 6) [34,129,66,260,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37044

theorem m42825_12 : Upper (D 6) (R 6) [34,129,66,260,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37057

theorem m42825_33 : Upper (D 6) (R 6) [34,129,66,260,33] 13 :=
  permutation_upper _ _ _ [34,129,66,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37062

theorem m42825_36 : Upper (D 6) (R 6) [34,129,66,260,36] 13 :=
  permutation_upper _ _ _ [34,129,66,36,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37069

theorem m42825_40 : Upper (D 6) (R 6) [34,129,66,260,40] 13 :=
  permutation_upper _ _ _ [34,129,66,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37076

theorem m42825_65 : Upper (D 6) (R 6) [34,129,66,260,65] 13 :=
  permutation_upper _ _ _ [34,129,66,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37079

theorem m42825_68 : Upper (D 6) (R 6) [34,129,66,260,68] 13 :=
  permutation_upper _ _ _ [34,129,66,68,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37083

theorem m42825_72 : Upper (D 6) (R 6) [34,129,66,260,72] 13 :=
  permutation_upper _ _ _ [34,129,66,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37087

theorem m42825_96 : Upper (D 6) (R 6) [34,129,66,260,96] 13 :=
  permutation_upper _ _ _ [34,129,66,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37091

def r42825 : Route 9 := (fun mask => (mask,id))

def c42825 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42825 : Upper (D 6) (R 6) [34,129,66,260] 13 := by
  apply FastRouting.sound _ _ [34,129,66,260] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42825 c42825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42825_5
  · exact m42825_9
  · exact m42825_12
  · exact m42825_33
  · exact m42825_36
  · exact m42825_40
  · exact m42825_65
  · exact m42825_68
  · exact m42825_72
  · exact m42825_96

theorem m42826_5 : Upper (D 6) (R 6) [34,129,66,272,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37035

theorem m42826_9 : Upper (D 6) (R 6) [34,129,66,272,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37045

theorem m42826_12 : Upper (D 6) (R 6) [34,129,66,272,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37058

theorem m42826_33 : Upper (D 6) (R 6) [34,129,66,272,33] 13 :=
  permutation_upper _ _ _ [34,129,66,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37063

theorem m42826_36 : Upper (D 6) (R 6) [34,129,66,272,36] 13 :=
  permutation_upper _ _ _ [34,129,66,36,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37070

theorem m42826_40 : Upper (D 6) (R 6) [34,129,66,272,40] 13 :=
  permutation_upper _ _ _ [34,129,66,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37077

theorem m42826_65 : Upper (D 6) (R 6) [34,129,66,272,65] 13 :=
  permutation_upper _ _ _ [34,129,66,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37080

theorem m42826_68 : Upper (D 6) (R 6) [34,129,66,272,68] 13 :=
  permutation_upper _ _ _ [34,129,66,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37084

theorem m42826_72 : Upper (D 6) (R 6) [34,129,66,272,72] 13 :=
  permutation_upper _ _ _ [34,129,66,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37088

theorem m42826_96 : Upper (D 6) (R 6) [34,129,66,272,96] 13 :=
  permutation_upper _ _ _ [34,129,66,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37092

def r42826 : Route 9 := (fun mask => (mask,id))

def c42826 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42826 : Upper (D 6) (R 6) [34,129,66,272] 13 := by
  apply FastRouting.sound _ _ [34,129,66,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42826 c42826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42826_5
  · exact m42826_9
  · exact m42826_12
  · exact m42826_33
  · exact m42826_36
  · exact m42826_40
  · exact m42826_65
  · exact m42826_68
  · exact m42826_72
  · exact m42826_96

theorem m42827_5 : Upper (D 6) (R 6) [34,129,66,288,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37036

theorem m42827_9 : Upper (D 6) (R 6) [34,129,66,288,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37046

theorem m42827_12 : Upper (D 6) (R 6) [34,129,66,288,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37059

theorem m42827_65 : Upper (D 6) (R 6) [34,129,66,288,65] 13 :=
  permutation_upper _ _ _ [34,129,66,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37081

theorem m42827_68 : Upper (D 6) (R 6) [34,129,66,288,68] 13 :=
  permutation_upper _ _ _ [34,129,66,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37085

theorem m42827_72 : Upper (D 6) (R 6) [34,129,66,288,72] 13 :=
  permutation_upper _ _ _ [34,129,66,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37089

def r42827 : Route 9 := (fun mask => (mask,id))

def c42827 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42827 : Upper (D 6) (R 6) [34,129,66,288] 13 := by
  apply FastRouting.sound _ _ [34,129,66,288] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42827 c42827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42827_5
  · exact m42827_9
  · exact m42827_12
  · exact m42827_65
  · exact m42827_68
  · exact m42827_72

theorem m42828_5 : Upper (D 6) (R 6) [34,129,66,320,5] 13 :=
  permutation_upper _ _ _ [34,129,66,5,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37037

theorem m42828_9 : Upper (D 6) (R 6) [34,129,66,320,9] 13 :=
  permutation_upper _ _ _ [34,129,66,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37047

theorem m42828_12 : Upper (D 6) (R 6) [34,129,66,320,12] 13 :=
  permutation_upper _ _ _ [34,129,66,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37060

theorem m42828_33 : Upper (D 6) (R 6) [34,129,66,320,33] 13 :=
  permutation_upper _ _ _ [34,129,66,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37064

theorem m42828_36 : Upper (D 6) (R 6) [34,129,66,320,36] 13 :=
  permutation_upper _ _ _ [34,129,66,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37071

theorem m42828_40 : Upper (D 6) (R 6) [34,129,66,320,40] 13 :=
  permutation_upper _ _ _ [34,129,66,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37078

def r42828 : Route 9 := (fun mask => (mask,id))

def c42828 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42828 : Upper (D 6) (R 6) [34,129,66,320] 13 := by
  apply FastRouting.sound _ _ [34,129,66,320] 13 (by decide) (choices 2) [5,9,12,33,36,40] r42828 c42828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42828_5
  · exact m42828_9
  · exact m42828_12
  · exact m42828_33
  · exact m42828_36
  · exact m42828_40

def b42829 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 76 11 372 372 372 500 372), lower := (rows 35 131 76 11 16 32 64 128 256), losses := [] }

theorem u42829 : Upper (D 6) (R 6) [34,129,72,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42830 : Route 9 := (fun mask => (mask,id))

def c42830 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42830 : Upper (D 6) (R 6) [34,129,72,5] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42830 c42830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37093
  · exact u37094
  · exact u37095
  · exact u37096
  · exact u37097
  · exact u37098
  · exact u37099
  · exact u37100
  · exact u37101
  · exact u37102

def r42831 : Route 9 := (fun mask => (mask,id))

def c42831 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42831 : Upper (D 6) (R 6) [34,129,72,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42831 c42831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37103
  · exact u37104
  · exact u37105
  · exact u37106
  · exact u37107
  · exact u37108
  · exact u37109
  · exact u37110
  · exact u37111
  · exact u37112

def r42832 : Route 9 := (fun mask => (mask,id))

def c42832 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42832 : Upper (D 6) (R 6) [34,129,72,17] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42832 c42832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37113
  · exact u37114
  · exact u37115
  · exact u37116
  · exact u37117
  · exact u37118
  · exact u37119
  · exact u37120
  · exact u37121
  · exact u37122

def r42833 : Route 9 := (fun mask => (mask,id))

def c42833 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42833 : Upper (D 6) (R 6) [34,129,72,18] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42833 c42833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37123
  · exact u37124
  · exact u37125
  · exact u37126
  · exact u37127
  · exact u37128
  · exact u37129
  · exact u37130
  · exact u37131
  · exact u37132

def r42834 : Route 9 := (fun mask => (mask,id))

def c42834 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42834 : Upper (D 6) (R 6) [34,129,72,20] 13 := by
  apply FastRouting.sound _ _ [34,129,72,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r42834 c42834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37133
  · exact u37134
  · exact u37135
  · exact u37136
  · exact u37137
  · exact u37138
  · exact u37139
  · exact u37140
  · exact u37141
  · exact u37142
  · exact u37143
  · exact u37144
  · exact u37145
  · exact u37146
  · exact u37147

def b42835 : PairBound 9 := { available := 342, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 76 41 342 374 342 470 342), lower := (rows 35 131 76 41 16 32 64 128 256), losses := [] }

theorem u42835 : Upper (D 6) (R 6) [34,129,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42836 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 131 76 42 341 373 341 469 341), lower := (rows 35 131 76 42 16 32 64 128 256), losses := [] }

theorem u42836 : Upper (D 6) (R 6) [34,129,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42837 : Route 9 := (fun mask => (mask,id))

def c42837 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42837 : Upper (D 6) (R 6) [34,129,72,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42837 c42837
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37148
  · exact u37149
  · exact u37150
  · exact u37151
  · exact u37152
  · exact u37153
  · exact u37154
  · exact u37155
  · exact u37156
  · exact u37157

def r42838 : Route 9 := (fun mask => (mask,id))

def c42838 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42838 : Upper (D 6) (R 6) [34,129,72,48] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42838 c42838
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37158
  · exact u37159
  · exact u37160
  · exact u37161
  · exact u37162
  · exact u37163
  · exact u37164
  · exact u37165
  · exact u37166
  · exact u37167

def b42839 : PairBound 9 := { available := 310, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 76 73 310 310 374 438 310), lower := (rows 35 131 76 73 16 32 64 128 256), losses := [] }

theorem u42839 : Upper (D 6) (R 6) [34,129,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u42839
end Delivery.IrregularNine14.P06
