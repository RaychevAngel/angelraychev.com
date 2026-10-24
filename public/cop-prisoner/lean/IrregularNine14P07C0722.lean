import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0647
import IrregularNine14P07C0648
import IrregularNine14P07C0649
import IrregularNine14P07C0650
import IrregularNine14P07C0651
import IrregularNine14P07C0652

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r43320 : Route 9 := (fun mask => (mask,id))

def c43320 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43320 : Upper (D 7) (R 7) [36,264,66,3] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3] 13 (by decide) (choices 2) [33,65,96,129,160,192] r43320 c43320
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38859
  · exact u38860
  · exact u38861
  · exact u38862
  · exact u38863
  · exact u38864

def r43321 : Route 9 := (fun mask => (mask,id))

def c43321 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43321 : Upper (D 7) (R 7) [36,264,66,17] 13 := by
  apply FastRouting.sound _ _ [36,264,66,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43321 c43321
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38865
  · exact u38866
  · exact u38867
  · exact u38868
  · exact u38869
  · exact u38870
  · exact u38871
  · exact u38872
  · exact u38873
  · exact u38874

def r43322 : Route 9 := (fun mask => (mask,id))

def c43322 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43322 : Upper (D 7) (R 7) [36,264,66,18] 13 := by
  apply FastRouting.sound _ _ [36,264,66,18] 13 (by decide) (choices 2) [33,65,96,129,160,192] r43322 c43322
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38875
  · exact u38876
  · exact u38877
  · exact u38878
  · exact u38879
  · exact u38880

def b43323 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 266 70 41 211 243 211 211 467), lower := (rows 37 266 70 41 16 32 64 128 256), losses := [] }

theorem u43323 : Upper (D 7) (R 7) [36,264,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43324 : Route 9 := (fun mask => (mask,id))

def c43324 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43324 : Upper (D 7) (R 7) [36,264,66,34] 13 := by
  apply FastRouting.sound _ _ [36,264,66,34] 13 (by decide) (choices 2) [65,129,192] r43324 c43324
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38881
  · exact u38882
  · exact u38883

def r43325 : Route 9 := (fun mask => (mask,id))

def c43325 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43325 : Upper (D 7) (R 7) [36,264,66,48] 13 := by
  apply FastRouting.sound _ _ [36,264,66,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43325 c43325
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38884
  · exact u38885
  · exact u38886
  · exact u38887
  · exact u38888
  · exact u38889

def r43326 : Route 9 := (fun mask => (mask,id))

def c43326 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43326 : Upper (D 7) (R 7) [36,264,66,65] 13 := by
  apply FastRouting.sound _ _ [36,264,66,65] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43326 c43326
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38890
  · exact u38891
  · exact u38892
  · exact u38893
  · exact u38894
  · exact u38895

def b43327 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 161 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,7)], upper := (rows 37 266 70 74 177 177 241 177 433), lower := (rows 37 266 70 74 16 32 64 128 256), losses := [] }

theorem u43327 : Upper (D 7) (R 7) [36,264,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43328 : Route 9 := (fun mask => (mask,id))

def c43328 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43328 : Upper (D 7) (R 7) [36,264,66,80] 13 := by
  apply FastRouting.sound _ _ [36,264,66,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43328 c43328
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38896
  · exact u38897
  · exact u38898
  · exact u38899
  · exact u38900
  · exact u38901

def r43329 : Route 9 := (fun mask => (mask,id))

def c43329 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43329 : Upper (D 7) (R 7) [36,264,66,96] 13 := by
  apply FastRouting.sound _ _ [36,264,66,96] 13 (by decide) (choices 2) [3,129,130] r43329 c43329
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38902
  · exact u38903
  · exact u38904

def r43330 : Route 9 := (fun mask => (mask,id))

def c43330 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43330 : Upper (D 7) (R 7) [36,264,66,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43330 c43330
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38905
  · exact u38906
  · exact u38907
  · exact u38908
  · exact u38909
  · exact u38910
  · exact u38911
  · exact u38912
  · exact u38913
  · exact u38914

def r43331 : Route 9 := (fun mask => (mask,id))

def c43331 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43331 : Upper (D 7) (R 7) [36,264,66,130] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r43331 c43331
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38915
  · exact u38916
  · exact u38917
  · exact u38918
  · exact u38919
  · exact u38920

def r43332 : Route 9 := (fun mask => (mask,id))

def c43332 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43332 : Upper (D 7) (R 7) [36,264,66,144] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43332 c43332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38921
  · exact u38922
  · exact u38923
  · exact u38924
  · exact u38925
  · exact u38926
  · exact u38927
  · exact u38928
  · exact u38929
  · exact u38930

def r43333 : Route 9 := (fun mask => (mask,id))

def c43333 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43333 : Upper (D 7) (R 7) [36,264,66,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43333 c43333
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38931
  · exact u38932
  · exact u38933
  · exact u38934
  · exact u38935
  · exact u38936

def r43334 : Route 9 := (fun mask => (mask,id))

def c43334 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43334 : Upper (D 7) (R 7) [36,264,66,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43334 c43334
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38937
  · exact u38938
  · exact u38939
  · exact u38940
  · exact u38941
  · exact u38942

def r43335 : Route 9 := (fun mask => (mask,id))

def c43335 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43335 : Upper (D 7) (R 7) [36,264,80,3] 13 := by
  apply FastRouting.sound _ _ [36,264,80,3] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43335 c43335
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38943
  · exact u38944
  · exact u38945
  · exact u38946
  · exact u38947
  · exact u38948
  · exact u38949
  · exact u38950
  · exact u38951
  · exact u38952

def b43336 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 266 84 41 211 227 195 195 451), lower := (rows 37 266 84 41 16 32 64 128 256), losses := [] }

theorem u43336 : Upper (D 7) (R 7) [36,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43337 : Route 9 := (fun mask => (mask,id))

def c43337 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43337 : Upper (D 7) (R 7) [36,264,80,34] 13 := by
  apply FastRouting.sound _ _ [36,264,80,34] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43337 c43337
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38953
  · exact u38954
  · exact u38955
  · exact u38956
  · exact u38957
  · exact u38958

def r43338 : Route 9 := (fun mask => (mask,id))

def c43338 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43338 : Upper (D 7) (R 7) [36,264,80,65] 13 := by
  apply FastRouting.sound _ _ [36,264,80,65] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43338 c43338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38959
  · exact u38960
  · exact u38961
  · exact u38962
  · exact u38963
  · exact u38964

def r43339 : Route 9 := (fun mask => (mask,id))

def c43339 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43339 : Upper (D 7) (R 7) [36,264,80,66] 13 := by
  apply FastRouting.sound _ _ [36,264,80,66] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43339 c43339
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38965
  · exact u38966
  · exact u38967
  · exact u38968
  · exact u38969
  · exact u38970

def r43340 : Route 9 := (fun mask => (mask,id))

def c43340 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43340 : Upper (D 7) (R 7) [36,264,80,96] 13 := by
  apply FastRouting.sound _ _ [36,264,80,96] 13 (by decide) (choices 2) [3,129,130] r43340 c43340
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38971
  · exact u38972
  · exact u38973

def r43341 : Route 9 := (fun mask => (mask,id))

def c43341 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43341 : Upper (D 7) (R 7) [36,264,80,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43341 c43341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38974
  · exact u38975
  · exact u38976
  · exact u38977
  · exact u38978
  · exact u38979
  · exact u38980
  · exact u38981
  · exact u38982
  · exact u38983

def r43342 : Route 9 := (fun mask => (mask,id))

def c43342 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43342 : Upper (D 7) (R 7) [36,264,80,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43342 c43342
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38984
  · exact u38985
  · exact u38986
  · exact u38987
  · exact u38988
  · exact u38989
  · exact u38990
  · exact u38991
  · exact u38992
  · exact u38993

def r43343 : Route 9 := (fun mask => (mask,id))

def c43343 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43343 : Upper (D 7) (R 7) [36,264,80,160] 13 := by
  apply FastRouting.sound _ _ [36,264,80,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43343 c43343
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38994
  · exact u38995
  · exact u38996
  · exact u38997
  · exact u38998
  · exact u38999

def r43344 : Route 9 := (fun mask => (mask,id))

def c43344 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43344 : Upper (D 7) (R 7) [36,264,80,192] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43344 c43344
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39000
  · exact u39001
  · exact u39002
  · exact u39003
  · exact u39004
  · exact u39005

def r43345 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43345 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43345 : Upper (D 7) (R 7) [36,264,192,3] 13 := by
  apply FastRouting.sound _ _ [36,264,192,3] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43345 c43345
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39006
  · exact u39007
  · exact u39008
  · exact u39009
  · exact u39010
  · exact u39011
  · exact u39012

def r43346 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43346 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43346 : Upper (D 7) (R 7) [36,264,192,17] 13 := by
  apply FastRouting.sound _ _ [36,264,192,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43346 c43346
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39013
  · exact u39014
  · exact u39015
  · exact u39016
  · exact u39017
  · exact u39018
  · exact u39019

def r43347 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43347 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43347 : Upper (D 7) (R 7) [36,264,192,18] 13 := by
  apply FastRouting.sound _ _ [36,264,192,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43347 c43347
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39020
  · exact u39021
  · exact u39022
  · exact u39023
  · exact u39024
  · exact u39025
  · exact u39026

def b43348 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 266 196 41 211 243 211 211 467), lower := (rows 37 266 196 41 16 32 64 128 256), losses := [] }

theorem u43348 : Upper (D 7) (R 7) [36,264,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43349 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43349 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43349 : Upper (D 7) (R 7) [36,264,192,34] 13 := by
  apply FastRouting.sound _ _ [36,264,192,34] 13 (by decide) (choices 2) [3,65,66,192] r43349 c43349
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u39027
  · exact u39028
  · exact u39029
  · exact u39030

def r43350 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43350 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43350 : Upper (D 7) (R 7) [36,264,192,48] 13 := by
  apply FastRouting.sound _ _ [36,264,192,48] 13 (by decide) (choices 2) [3,65,66,192] r43350 c43350
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u39031
  · exact u39032
  · exact u39033
  · exact u39034

def r43351 : Route 9 := (fun mask => (mask,id))

def c43351 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43351 : Upper (D 7) (R 7) [36,264,192,65] 13 := by
  apply FastRouting.sound _ _ [36,264,192,65] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43351 c43351
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39035
  · exact u39036
  · exact u39037
  · exact u39038
  · exact u39039
  · exact u39040

def r43352 : Route 9 := (fun mask => (mask,id))

def c43352 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43352 : Upper (D 7) (R 7) [36,264,192,66] 13 := by
  apply FastRouting.sound _ _ [36,264,192,66] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43352 c43352
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39041
  · exact u39042
  · exact u39043
  · exact u39044
  · exact u39045
  · exact u39046

def r43353 : Route 9 := (fun mask => (mask,id))

def c43353 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43353 : Upper (D 7) (R 7) [36,264,192,80] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43353 c43353
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39047
  · exact u39048
  · exact u39049
  · exact u39050
  · exact u39051
  · exact u39052

def r43354 : Route 9 := (fun mask => (mask,id))

def c43354 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43354 : Upper (D 7) (R 7) [36,264,192,96] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96] 13 (by decide) (choices 2) [3,129,130] r43354 c43354
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39053
  · exact u39054
  · exact u39055

def b43355 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 37 266 196 200 51 51 115 179 307), lower := (rows 37 266 196 200 16 32 64 128 256), losses := [] }

theorem u43355 : Upper (D 7) (R 7) [36,264,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43356 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 13 11 210 242 210 210 466), lower := (rows 37 290 13 11 16 32 64 128 256), losses := [] }

theorem u43356 : Upper (D 7) (R 7) [36,288,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43357 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 290 13 25 210 226 194 194 450), lower := (rows 37 290 13 25 16 32 64 128 256), losses := [] }

theorem u43357 : Upper (D 7) (R 7) [36,288,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43358 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43358 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43358 : Upper (D 7) (R 7) [36,288,9,18] 13 := by
  apply FastRouting.sound _ _ [36,288,9,18] 13 (by decide) (choices 2) [3,65,66,192] r43358 c43358
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u39056
  · exact u39057
  · exact u39058
  · exact u39059

def b43359 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 290 13 73 210 242 210 210 466), lower := (rows 37 290 13 73 16 32 64 128 256), losses := [] }

theorem u43359 : Upper (D 7) (R 7) [36,288,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43360 : Route 9 := (fun mask => (mask,id))

def c43360 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43360 : Upper (D 7) (R 7) [36,288,9,66] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43360 c43360
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39060
  · exact u39061
  · exact u39062
  · exact u39063
  · exact u39064
  · exact u39065

def r43361 : Route 9 := (fun mask => (mask,id))

def c43361 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43361 : Upper (D 7) (R 7) [36,288,9,80] 13 := by
  apply FastRouting.sound _ _ [36,288,9,80] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43361 c43361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39066
  · exact u39067
  · exact u39068
  · exact u39069
  · exact u39070
  · exact u39071

def r43362 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43362 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43362 : Upper (D 7) (R 7) [36,288,9,192] 13 := by
  apply FastRouting.sound _ _ [36,288,9,192] 13 (by decide) (choices 2) [3,65,66,192] r43362 c43362
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u39072
  · exact u39073
  · exact u39074
  · exact u39075

def b43363 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 14 11 209 241 209 209 465), lower := (rows 37 290 14 11 16 32 64 128 256), losses := [] }

theorem u43363 : Upper (D 7) (R 7) [36,288,10,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43364 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43364 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43364 : Upper (D 7) (R 7) [36,288,10,17] 13 := by
  apply FastRouting.sound _ _ [36,288,10,17] 13 (by decide) (choices 2) [3,65,66,192] r43364 c43364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u39076
  · exact u39077
  · exact u39078
  · exact u39079

def b43365 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 290 14 26 209 225 193 193 449), lower := (rows 37 290 14 26 16 32 64 128 256), losses := [] }

theorem u43365 : Upper (D 7) (R 7) [36,288,10,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43366 : Route 9 := (fun mask => (mask,id))

def c43366 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43366 : Upper (D 7) (R 7) [36,288,10,65] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43366 c43366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39080
  · exact u39081
  · exact u39082
  · exact u39083
  · exact u39084
  · exact u39085

def b43367 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 290 14 74 209 241 209 209 465), lower := (rows 37 290 14 74 16 32 64 128 256), losses := [] }

theorem u43367 : Upper (D 7) (R 7) [36,288,10,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43368 : Route 9 := (fun mask => (mask,id))

def c43368 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43368 : Upper (D 7) (R 7) [36,288,10,80] 13 := by
  apply FastRouting.sound _ _ [36,288,10,80] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43368 c43368
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39086
  · exact u39087
  · exact u39088
  · exact u39089
  · exact u39090
  · exact u39091

def r43369 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43369 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43369 : Upper (D 7) (R 7) [36,288,10,192] 13 := by
  apply FastRouting.sound _ _ [36,288,10,192] 13 (by decide) (choices 2) [3,65,66,192] r43369 c43369
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u39092
  · exact u39093
  · exact u39094
  · exact u39095

def r43370 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43370 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43370 : Upper (D 7) (R 7) [36,288,24,3] 13 := by
  apply FastRouting.sound _ _ [36,288,24,3] 13 (by decide) (choices 2) [3,65,66,192] r43370 c43370
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u39096
  · exact u39097
  · exact u39098
  · exact u39099

theorem m43371_3 : Upper (D 7) (R 7) [36,288,24,65,3] 13 :=
  permutation_upper _ _ _ [36,288,24,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39097

def r43371 : Route 9 := (fun mask => (mask,id))

def c43371 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43371 : Upper (D 7) (R 7) [36,288,24,65] 13 := by
  apply FastRouting.sound _ _ [36,288,24,65] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43371 c43371
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43371_3
  · exact u39100
  · exact u39101
  · exact u39102
  · exact u39103
  · exact u39104

theorem m43372_3 : Upper (D 7) (R 7) [36,288,24,66,3] 13 :=
  permutation_upper _ _ _ [36,288,24,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39098

theorem m43372_65 : Upper (D 7) (R 7) [36,288,24,66,65] 13 :=
  permutation_upper _ _ _ [36,288,24,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39101

theorem m43372_129 : Upper (D 7) (R 7) [36,288,24,66,129] 13 :=
  permutation_upper _ _ _ [36,288,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39103

def r43372 : Route 9 := (fun mask => (mask,id))

def c43372 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43372 : Upper (D 7) (R 7) [36,288,24,66] 13 := by
  apply FastRouting.sound _ _ [36,288,24,66] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43372 c43372
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43372_3
  · exact m43372_65
  · exact u39105
  · exact m43372_129
  · exact u39106
  · exact u39107

theorem m43373_3 : Upper (D 7) (R 7) [36,288,24,192,3] 13 :=
  permutation_upper _ _ _ [36,288,24,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39099

theorem m43373_65 : Upper (D 7) (R 7) [36,288,24,192,65] 13 :=
  permutation_upper _ _ _ [36,288,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39104

theorem m43373_66 : Upper (D 7) (R 7) [36,288,24,192,66] 13 :=
  permutation_upper _ _ _ [36,288,24,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39107

def r43373 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43373 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43373 : Upper (D 7) (R 7) [36,288,24,192] 13 := by
  apply FastRouting.sound _ _ [36,288,24,192] 13 (by decide) (choices 2) [3,65,66,192] r43373 c43373
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m43373_3
  · exact m43373_65
  · exact m43373_66
  · exact u39108

def b43374 : PairBound 9 := { available := 218, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 69 11 218 250 218 218 474), lower := (rows 37 290 69 11 16 32 64 128 256), losses := [] }

theorem u43374 : Upper (D 7) (R 7) [36,288,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43375 : Route 9 := (fun mask => (mask,id))

def c43375 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43375 : Upper (D 7) (R 7) [36,288,65,17] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17] 13 (by decide) (choices 2) [10,66,72,130,136,192] r43375 c43375
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39115
  · exact u39116
  · exact u39117
  · exact u39118
  · exact u39119
  · exact u39120

theorem m43376_3 : Upper (D 7) (R 7) [36,288,65,18,3] 13 :=
  permutation_upper _ _ _ [36,288,65,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39109

theorem m43376_9 : Upper (D 7) (R 7) [36,288,65,18,9] 13 :=
  permutation_upper _ _ _ [36,288,65,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39115

def r43376 : Route 9 := (fun mask => (mask,id))

def c43376 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43376 : Upper (D 7) (R 7) [36,288,65,18] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43376 c43376
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43376_3
  · exact m43376_9
  · exact u39121
  · exact u39122
  · exact u39123
  · exact u39124
  · exact u39125
  · exact u39126
  · exact u39127
  · exact u39128

def b43377 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 37 290 69 73 154 186 218 154 410), lower := (rows 37 290 69 73 16 32 64 128 256), losses := [] }

theorem u43377 : Upper (D 7) (R 7) [36,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43378_3 : Upper (D 7) (R 7) [36,288,65,66,3] 13 :=
  permutation_upper _ _ _ [36,288,65,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39110

theorem m43378_9 : Upper (D 7) (R 7) [36,288,65,66,9] 13 :=
  permutation_upper _ _ _ [36,288,65,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39116

theorem m43378_10 : Upper (D 7) (R 7) [36,288,65,66,10] 13 :=
  permutation_upper _ _ _ [36,288,65,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39123

def r43378 : Route 9 := (fun mask => (mask,id))

def c43378 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43378 : Upper (D 7) (R 7) [36,288,65,66] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43378 c43378
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43378_3
  · exact m43378_9
  · exact m43378_10
  · exact u39131
  · exact u39132
  · exact u39133

theorem m43379_3 : Upper (D 7) (R 7) [36,288,65,80,3] 13 :=
  permutation_upper _ _ _ [36,288,65,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39111

theorem m43379_9 : Upper (D 7) (R 7) [36,288,65,80,9] 13 :=
  permutation_upper _ _ _ [36,288,65,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39117

theorem m43379_10 : Upper (D 7) (R 7) [36,288,65,80,10] 13 :=
  permutation_upper _ _ _ [36,288,65,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39124

def r43379 : Route 9 := (fun mask => (mask,id))

def c43379 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43379 : Upper (D 7) (R 7) [36,288,65,80] 13 := by
  apply FastRouting.sound _ _ [36,288,65,80] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43379 c43379
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43379_3
  · exact m43379_9
  · exact m43379_10
  · exact u39134
  · exact u39135
  · exact u39136

#print axioms u43379
end Delivery.IrregularNine14.P07
