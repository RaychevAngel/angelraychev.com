import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0563
import IrregularNine14P06C0564
import IrregularNine14P06C0565
import IrregularNine14P06C0566
import IrregularNine14P06C0567
import IrregularNine14P06C0568

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42060 : Route 9 := (fun mask => (mask,id))

def c42060 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42060 : Upper (D 6) (R 6) [10,160,33,272] 13 := by
  apply FastRouting.sound _ _ [10,160,33,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42060 c42060
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33837
  · exact u33838
  · exact u33839
  · exact u33840
  · exact u33841
  · exact u33842

def r42061 : Route 9 := (fun mask => (mask,id))

def c42061 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42061 : Upper (D 6) (R 6) [10,160,33,320] 13 := by
  apply FastRouting.sound _ _ [10,160,33,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42061 c42061
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33843
  · exact u33844
  · exact u33845
  · exact u33846
  · exact u33847
  · exact u33848

def b42062 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 52 11 341 357 325 453 325), lower := (rows 11 162 52 11 16 32 64 128 256), losses := [] }

theorem u42062 : Upper (D 6) (R 6) [10,160,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42063 : Route 9 := (fun mask => (mask,id))

def c42063 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42063 : Upper (D 6) (R 6) [10,160,48,5] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42063 c42063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33849
  · exact u33850
  · exact u33851
  · exact u33852
  · exact u33853
  · exact u33854
  · exact u33855
  · exact u33856
  · exact u33857
  · exact u33858

def b42064 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 162 52 14 341 357 325 453 325), lower := (rows 11 162 52 14 16 32 64 128 256), losses := [] }

theorem u42064 : Upper (D 6) (R 6) [10,160,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42065 : Route 9 := (fun mask => (mask,id))

def c42065 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42065 : Upper (D 6) (R 6) [10,160,48,65] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42065 c42065
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33859
  · exact u33860
  · exact u33861
  · exact u33862
  · exact u33863
  · exact u33864
  · exact u33865
  · exact u33866
  · exact u33867
  · exact u33868

def b42066 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 52 74 341 357 325 453 325), lower := (rows 11 162 52 74 16 32 64 128 256), losses := [] }

theorem u42066 : Upper (D 6) (R 6) [10,160,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42067 : Route 9 := (fun mask => (mask,id))

def c42067 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42067 : Upper (D 6) (R 6) [10,160,48,68] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42067 c42067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33869
  · exact u33870
  · exact u33871
  · exact u33872
  · exact u33873
  · exact u33874
  · exact u33875
  · exact u33876
  · exact u33877
  · exact u33878

def r42068 : Route 9 := (fun mask => (mask,id))

def c42068 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42068 : Upper (D 6) (R 6) [10,160,48,257] 13 := by
  apply FastRouting.sound _ _ [10,160,48,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42068 c42068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33879
  · exact u33880
  · exact u33881
  · exact u33882
  · exact u33883
  · exact u33884

def b42069 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 52 266 85 101 69 197 325), lower := (rows 11 162 52 266 16 32 64 128 256), losses := [] }

theorem u42069 : Upper (D 6) (R 6) [10,160,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42070 : Route 9 := (fun mask => (mask,id))

def c42070 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42070 : Upper (D 6) (R 6) [10,160,48,260] 13 := by
  apply FastRouting.sound _ _ [10,160,48,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42070 c42070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33885
  · exact u33886
  · exact u33887
  · exact u33888
  · exact u33889
  · exact u33890

def r42071 : Route 9 := (fun mask => (mask,id))

def c42071 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42071 : Upper (D 6) (R 6) [10,160,48,320] 13 := by
  apply FastRouting.sound _ _ [10,160,48,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42071 c42071
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33891
  · exact u33892
  · exact u33893
  · exact u33894
  · exact u33895
  · exact u33896

def b42072 : PairBound 9 := { available := 372, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 69 11 372 372 372 500 372), lower := (rows 11 162 69 11 16 32 64 128 256), losses := [] }

theorem u42072 : Upper (D 6) (R 6) [10,160,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42073 : PairBound 9 := { available := 374, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 162 69 13 374 374 374 502 374), lower := (rows 11 162 69 13 16 32 64 128 256), losses := [] }

theorem u42073 : Upper (D 6) (R 6) [10,160,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42074 : PairBound 9 := { available := 373, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 69 14 373 373 373 501 373), lower := (rows 11 162 69 14 16 32 64 128 256), losses := [] }

theorem u42074 : Upper (D 6) (R 6) [10,160,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42075 : Route 9 := (fun mask => (mask,id))

def c42075 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42075 : Upper (D 6) (R 6) [10,160,65,17] 13 := by
  apply FastRouting.sound _ _ [10,160,65,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42075 c42075
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33897
  · exact u33898
  · exact u33899
  · exact u33900
  · exact u33901
  · exact u33902
  · exact u33903
  · exact u33904
  · exact u33905
  · exact u33906

def b42076 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 69 26 373 357 357 485 357), lower := (rows 11 162 69 26 16 32 64 128 256), losses := [] }

theorem u42076 : Upper (D 6) (R 6) [10,160,65,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42077 : Route 9 := (fun mask => (mask,id))

def c42077 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42077 : Upper (D 6) (R 6) [10,160,65,20] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r42077 c42077
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33907
  · exact u33908
  · exact u33909
  · exact u33910
  · exact u33911
  · exact u33912
  · exact u33913
  · exact u33914
  · exact u33915
  · exact u33916
  · exact u33917
  · exact u33918
  · exact u33919
  · exact u33920
  · exact u33921

def b42078 : PairBound 9 := { available := 342, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 69 41 342 374 342 470 342), lower := (rows 11 162 69 41 16 32 64 128 256), losses := [] }

theorem u42078 : Upper (D 6) (R 6) [10,160,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42079 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 69 42 341 373 341 469 341), lower := (rows 11 162 69 42 16 32 64 128 256), losses := [] }

theorem u42079 : Upper (D 6) (R 6) [10,160,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42080 : Route 9 := (fun mask => (mask,id))

def c42080 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42080 : Upper (D 6) (R 6) [10,160,65,36] 13 := by
  apply FastRouting.sound _ _ [10,160,65,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42080 c42080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33922
  · exact u33923
  · exact u33924
  · exact u33925
  · exact u33926
  · exact u33927
  · exact u33928
  · exact u33929
  · exact u33930
  · exact u33931

def r42081 : Route 9 := (fun mask => (mask,id))

def c42081 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42081 : Upper (D 6) (R 6) [10,160,65,48] 13 := by
  apply FastRouting.sound _ _ [10,160,65,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42081 c42081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33932
  · exact u33933
  · exact u33934
  · exact u33935
  · exact u33936
  · exact u33937
  · exact u33938
  · exact u33939
  · exact u33940
  · exact u33941

def b42082 : PairBound 9 := { available := 310, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 2, region := 8, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 162 69 73 310 310 374 438 310), lower := (rows 11 162 69 73 16 32 64 128 256), losses := [] }

theorem u42082 : Upper (D 6) (R 6) [10,160,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42083 : PairBound 9 := { available := 309, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 11 162 69 74 309 309 373 437 309), lower := (rows 11 162 69 74 16 32 64 128 256), losses := [] }

theorem u42083 : Upper (D 6) (R 6) [10,160,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42084 : PairBound 9 := { available := 311, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 69 76 311 311 375 439 311), lower := (rows 11 162 69 76 16 32 64 128 256), losses := [] }

theorem u42084 : Upper (D 6) (R 6) [10,160,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42085 : Route 9 := (fun mask => (mask,id))

def c42085 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42085 : Upper (D 6) (R 6) [10,160,65,80] 13 := by
  apply FastRouting.sound _ _ [10,160,65,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r42085 c42085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33942
  · exact u33943
  · exact u33944
  · exact u33945
  · exact u33946
  · exact u33947
  · exact u33948
  · exact u33949
  · exact u33950
  · exact u33951

def b42086 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 162 69 104 279 311 343 407 279), lower := (rows 11 162 69 104 16 32 64 128 256), losses := [] }

theorem u42086 : Upper (D 6) (R 6) [10,160,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42087 : Route 9 := (fun mask => (mask,id))

def c42087 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42087 : Upper (D 6) (R 6) [10,160,65,257] 13 := by
  apply FastRouting.sound _ _ [10,160,65,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42087 c42087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33952
  · exact u33953
  · exact u33954
  · exact u33955
  · exact u33956
  · exact u33957

def b42088 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 69 266 117 117 117 245 373), lower := (rows 11 162 69 266 16 32 64 128 256), losses := [] }

theorem u42088 : Upper (D 6) (R 6) [10,160,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42089 : Route 9 := (fun mask => (mask,id))

def c42089 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42089 : Upper (D 6) (R 6) [10,160,65,260] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42089 c42089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33958
  · exact u33959
  · exact u33960
  · exact u33961
  · exact u33962
  · exact u33963
  · exact u33964
  · exact u33965
  · exact u33966
  · exact u33967

def r42090 : Route 9 := (fun mask => (mask,id))

def c42090 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42090 : Upper (D 6) (R 6) [10,160,65,272] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42090 c42090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33968
  · exact u33969
  · exact u33970
  · exact u33971
  · exact u33972
  · exact u33973
  · exact u33974
  · exact u33975
  · exact u33976
  · exact u33977

def r42091 : Route 9 := (fun mask => (mask,id))

def c42091 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42091 : Upper (D 6) (R 6) [10,160,65,288] 13 := by
  apply FastRouting.sound _ _ [10,160,65,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42091 c42091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33978
  · exact u33979
  · exact u33980
  · exact u33981
  · exact u33982
  · exact u33983

def r42092 : Route 9 := (fun mask => (mask,id))

def c42092 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42092 : Upper (D 6) (R 6) [10,160,65,320] 13 := by
  apply FastRouting.sound _ _ [10,160,65,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r42092 c42092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33984
  · exact u33985
  · exact u33986
  · exact u33987
  · exact u33988
  · exact u33989

def b42093 : PairBound 9 := { available := 373, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 70 13 373 373 373 501 373), lower := (rows 11 162 70 13 16 32 64 128 256), losses := [] }

theorem u42093 : Upper (D 6) (R 6) [10,160,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42094 : Route 9 := (fun mask => (mask,id))

def c42094 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42094 : Upper (D 6) (R 6) [10,160,66,17] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42094 c42094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33990
  · exact u33991
  · exact u33992
  · exact u33993
  · exact u33994
  · exact u33995
  · exact u33996
  · exact u33997
  · exact u33998
  · exact u33999

def r42095 : Route 9 := (fun mask => (mask,id))

def c42095 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42095 : Upper (D 6) (R 6) [10,160,66,20] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42095 c42095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34000
  · exact u34001
  · exact u34002
  · exact u34003
  · exact u34004
  · exact u34005
  · exact u34006
  · exact u34007
  · exact u34008
  · exact u34009

def b42096 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 70 41 341 373 341 469 341), lower := (rows 11 162 70 41 16 32 64 128 256), losses := [] }

theorem u42096 : Upper (D 6) (R 6) [10,160,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42097 : Route 9 := (fun mask => (mask,id))

def c42097 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42097 : Upper (D 6) (R 6) [10,160,66,36] 13 := by
  apply FastRouting.sound _ _ [10,160,66,36] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42097 c42097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34010
  · exact u34011
  · exact u34012
  · exact u34013
  · exact u34014
  · exact u34015

def r42098 : Route 9 := (fun mask => (mask,id))

def c42098 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42098 : Upper (D 6) (R 6) [10,160,66,48] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42098 c42098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34016
  · exact u34017
  · exact u34018
  · exact u34019
  · exact u34020
  · exact u34021

def b42099 : PairBound 9 := { available := 309, camps := [{ cop := 2, region := 9, targets := 4 },{ cop := 2, region := 9, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 70 73 309 309 373 437 309), lower := (rows 11 162 70 73 16 32 64 128 256), losses := [] }

theorem u42099 : Upper (D 6) (R 6) [10,160,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42100 : PairBound 9 := { available := 309, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 70 76 309 309 373 437 309), lower := (rows 11 162 70 76 16 32 64 128 256), losses := [] }

theorem u42100 : Upper (D 6) (R 6) [10,160,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42101 : Route 9 := (fun mask => (mask,id))

def c42101 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42101 : Upper (D 6) (R 6) [10,160,66,80] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80] 13 (by decide) (choices 2) [5,33,36,257,260,288] r42101 c42101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34022
  · exact u34023
  · exact u34024
  · exact u34025
  · exact u34026
  · exact u34027

def r42102 : Route 9 := (fun mask => (mask,id))

def c42102 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42102 : Upper (D 6) (R 6) [10,160,66,96] 13 := by
  apply FastRouting.sound _ _ [10,160,66,96] 13 (by decide) (choices 2) [5,257,260] r42102 c42102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34028
  · exact u34029
  · exact u34030

def r42103 : Route 9 := (fun mask => (mask,id))

def c42103 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42103 : Upper (D 6) (R 6) [10,160,66,257] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42103 c42103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34031
  · exact u34032
  · exact u34033
  · exact u34034
  · exact u34035
  · exact u34036

def r42104 : Route 9 := (fun mask => (mask,id))

def c42104 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42104 : Upper (D 6) (R 6) [10,160,66,260] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42104 c42104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34037
  · exact u34038
  · exact u34039
  · exact u34040
  · exact u34041
  · exact u34042

def r42105 : Route 9 := (fun mask => (mask,id))

def c42105 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42105 : Upper (D 6) (R 6) [10,160,66,272] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42105 c42105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34043
  · exact u34044
  · exact u34045
  · exact u34046
  · exact u34047
  · exact u34048

def r42106 : Route 9 := (fun mask => (mask,id))

def c42106 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42106 : Upper (D 6) (R 6) [10,160,66,288] 13 := by
  apply FastRouting.sound _ _ [10,160,66,288] 13 (by decide) (choices 2) [5,65,68] r42106 c42106
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34049
  · exact u34050
  · exact u34051

def r42107 : Route 9 := (fun mask => (mask,id))

def c42107 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42107 : Upper (D 6) (R 6) [10,160,66,320] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320] 13 (by decide) (choices 2) [5,33,36] r42107 c42107
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34052
  · exact u34053
  · exact u34054

def b42108 : PairBound 9 := { available := 357, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 84 11 373 357 357 485 357), lower := (rows 11 162 84 11 16 32 64 128 256), losses := [] }

theorem u42108 : Upper (D 6) (R 6) [10,160,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42109 : Route 9 := (fun mask => (mask,id))

def c42109 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42109 : Upper (D 6) (R 6) [10,160,80,5] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r42109 c42109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34055
  · exact u34056
  · exact u34057
  · exact u34058
  · exact u34059
  · exact u34060
  · exact u34061
  · exact u34062
  · exact u34063
  · exact u34064
  · exact u34065
  · exact u34066
  · exact u34067
  · exact u34068
  · exact u34069

def b42110 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 84 14 373 357 357 485 357), lower := (rows 11 162 84 14 16 32 64 128 256), losses := [] }

theorem u42110 : Upper (D 6) (R 6) [10,160,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42111 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 84 41 343 359 327 455 327), lower := (rows 11 162 84 41 16 32 64 128 256), losses := [] }

theorem u42111 : Upper (D 6) (R 6) [10,160,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42112 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 84 42 341 357 325 453 325), lower := (rows 11 162 84 42 16 32 64 128 256), losses := [] }

theorem u42112 : Upper (D 6) (R 6) [10,160,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42113 : Route 9 := (fun mask => (mask,id))

def c42113 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42113 : Upper (D 6) (R 6) [10,160,80,36] 13 := by
  apply FastRouting.sound _ _ [10,160,80,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42113 c42113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34070
  · exact u34071
  · exact u34072
  · exact u34073
  · exact u34074
  · exact u34075
  · exact u34076
  · exact u34077
  · exact u34078
  · exact u34079

def r42114 : Route 9 := (fun mask => (mask,id))

def c42114 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42114 : Upper (D 6) (R 6) [10,160,80,65] 13 := by
  apply FastRouting.sound _ _ [10,160,80,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r42114 c42114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34080
  · exact u34081
  · exact u34082
  · exact u34083
  · exact u34084
  · exact u34085
  · exact u34086
  · exact u34087
  · exact u34088
  · exact u34089

def b42115 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 84 74 309 293 357 421 293), lower := (rows 11 162 84 74 16 32 64 128 256), losses := [] }

theorem u42115 : Upper (D 6) (R 6) [10,160,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42116 : PairBound 9 := { available := 295, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 84 76 311 295 359 423 295), lower := (rows 11 162 84 76 16 32 64 128 256), losses := [] }

theorem u42116 : Upper (D 6) (R 6) [10,160,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42117 : Route 9 := (fun mask => (mask,id))

def c42117 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42117 : Upper (D 6) (R 6) [10,160,80,96] 13 := by
  apply FastRouting.sound _ _ [10,160,80,96] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42117 c42117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34090
  · exact u34091
  · exact u34092
  · exact u34093
  · exact u34094
  · exact u34095

def r42118 : Route 9 := (fun mask => (mask,id))

def c42118 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42118 : Upper (D 6) (R 6) [10,160,80,257] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42118 c42118
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34096
  · exact u34097
  · exact u34098
  · exact u34099
  · exact u34100
  · exact u34101
  · exact u34102
  · exact u34103
  · exact u34104
  · exact u34105

def b42119 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 84 266 117 101 101 229 357), lower := (rows 11 162 84 266 16 32 64 128 256), losses := [] }

theorem u42119 : Upper (D 6) (R 6) [10,160,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u42119
end Delivery.IrregularNine14.P06
