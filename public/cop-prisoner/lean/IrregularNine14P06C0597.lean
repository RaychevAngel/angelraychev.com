import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0331
import IrregularNine14P06C0332
import IrregularNine14P06C0333

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35820 : Route 9 := (fun mask => (mask,id))

def c35820 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35820 : Upper (D 6) (R 6) [34,65,160,20,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,20,257] 13 (by decide) (choices 1) [2,4,8,64] r35820 c35820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19913
  · exact u19914
  · exact u19915
  · exact u19916

def r35821 : Route 9 := (fun mask => (mask,id))

def c35821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35821 : Upper (D 6) (R 6) [34,65,160,20,258] 13 := by
  apply FastRouting.sound _ _ [34,65,160,20,258] 13 (by decide) (choices 1) [1,4,8,64] r35821 c35821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19917
  · exact u19918
  · exact u19919
  · exact u19920

def b35822 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 164 28 276 107 75 203 331), lower := (rows 35 67 164 28 276 32 64 128 256), losses := [] }

theorem u35822 : Upper (D 6) (R 6) [34,65,160,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35823 : Route 9 := (fun mask => (mask,id))

def c35823 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35823 : Upper (D 6) (R 6) [34,65,160,20,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,20,264] 13 (by decide) (choices 1) [1,2,4,64] r35823 c35823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19921
  · exact u19922
  · exact u19923
  · exact u19924

def r35824 : Route 9 := (fun mask => (mask,id))

def c35824 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35824 : Upper (D 6) (R 6) [34,65,160,20,320] 13 := by
  apply FastRouting.sound _ _ [34,65,160,20,320] 13 (by decide) (choices 1) [1,2,4,8] r35824 c35824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19925
  · exact u19926
  · exact u19927
  · exact u19928

def b35825 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 8, targets := 36 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 35 67 164 73 274 60 92 156 284), lower := (rows 35 67 164 73 274 32 64 128 256), losses := [] }

theorem u35825 : Upper (D 6) (R 6) [34,65,160,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35826 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 8, targets := 36 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 35 67 164 73 276 62 94 158 286), lower := (rows 35 67 164 73 276 32 64 128 256), losses := [] }

theorem u35826 : Upper (D 6) (R 6) [34,65,160,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35827 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 8, targets := 36 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 35 67 164 73 280 54 86 150 278), lower := (rows 35 67 164 73 280 32 64 128 256), losses := [] }

theorem u35827 : Upper (D 6) (R 6) [34,65,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35828 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 164 74 273 60 92 156 284), lower := (rows 35 67 164 74 273 32 64 128 256), losses := [] }

theorem u35828 : Upper (D 6) (R 6) [34,65,160,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35829 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 164 74 276 61 93 157 285), lower := (rows 35 67 164 74 276 32 64 128 256), losses := [] }

theorem u35829 : Upper (D 6) (R 6) [34,65,160,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35830 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 164 74 280 53 85 149 277), lower := (rows 35 67 164 74 280 32 64 128 256), losses := [] }

theorem u35830 : Upper (D 6) (R 6) [34,65,160,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35831 : Route 9 := (fun mask => (mask,id))

def c35831 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35831 : Upper (D 6) (R 6) [34,65,160,68,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,68,257] 13 (by decide) (choices 1) [2,4,8,16] r35831 c35831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19929
  · exact u19930
  · exact u19931
  · exact u19932

def r35832 : Route 9 := (fun mask => (mask,id))

def c35832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35832 : Upper (D 6) (R 6) [34,65,160,68,258] 13 := by
  apply FastRouting.sound _ _ [34,65,160,68,258] 13 (by decide) (choices 1) [1,4,8,16] r35832 c35832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19933
  · exact u19934
  · exact u19935
  · exact u19936

def r35833 : Route 9 := (fun mask => (mask,id))

def c35833 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35833 : Upper (D 6) (R 6) [34,65,160,68,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,68,260] 13 (by decide) (choices 1) [1,2,8,16] r35833 c35833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19937
  · exact u19938
  · exact u19939
  · exact u19940

def r35834 : Route 9 := (fun mask => (mask,id))

def c35834 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35834 : Upper (D 6) (R 6) [34,65,160,68,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,68,264] 13 (by decide) (choices 1) [1,2,4,16] r35834 c35834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19941
  · exact u19942
  · exact u19943
  · exact u19944

def r35835 : Route 9 := (fun mask => (mask,id))

def c35835 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35835 : Upper (D 6) (R 6) [34,65,160,80,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,80,257] 13 (by decide) (choices 1) [2,4,8] r35835 c35835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19945
  · exact u19946
  · exact u19947

def r35836 : Route 9 := (fun mask => (mask,id))

def c35836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35836 : Upper (D 6) (R 6) [34,65,160,80,258] 13 := by
  apply FastRouting.sound _ _ [34,65,160,80,258] 13 (by decide) (choices 1) [1,4,8] r35836 c35836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19948
  · exact u19949
  · exact u19950

def r35837 : Route 9 := (fun mask => (mask,id))

def c35837 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35837 : Upper (D 6) (R 6) [34,65,160,80,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,80,260] 13 (by decide) (choices 1) [1,2,4,8] r35837 c35837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19951
  · exact u19952
  · exact u19953
  · exact u19954

def r35838 : Route 9 := (fun mask => (mask,id))

def c35838 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35838 : Upper (D 6) (R 6) [34,65,160,80,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,80,264] 13 (by decide) (choices 1) [1,2,4] r35838 c35838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19955
  · exact u19956
  · exact u19957

def b35839 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 388 11 28 116 116 244 372), lower := (rows 35 67 388 11 28 32 64 128 256), losses := [] }

theorem u35839 : Upper (D 6) (R 6) [34,65,384,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35840 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 388 11 52 124 92 220 348), lower := (rows 35 67 388 11 52 32 64 128 256), losses := [] }

theorem u35840 : Upper (D 6) (R 6) [34,65,384,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35841 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 67 388 11 56 116 84 212 340), lower := (rows 35 67 388 11 56 32 64 128 256), losses := [] }

theorem u35841 : Upper (D 6) (R 6) [34,65,384,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35842 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 388 11 112 60 92 156 284), lower := (rows 35 67 388 11 112 32 64 128 256), losses := [] }

theorem u35842 : Upper (D 6) (R 6) [34,65,384,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35843 : Route 9 := (fun mask => (mask,id))

def c35843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35843 : Upper (D 6) (R 6) [34,65,384,5,6] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,6] 13 (by decide) (choices 1) [8,16,64] r35843 c35843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19958
  · exact u19959
  · exact u19960

def r35844 : Route 9 := (fun mask => (mask,id))

def c35844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35844 : Upper (D 6) (R 6) [34,65,384,5,10] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,10] 13 (by decide) (choices 1) [4,16,64] r35844 c35844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19961
  · exact u19962
  · exact u19963

def b35845 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 67 388 13 28 114 114 242 370), lower := (rows 35 67 388 13 28 32 64 128 256), losses := [] }

theorem u35845 : Upper (D 6) (R 6) [34,65,384,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35846 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 67 388 13 50 124 92 220 348), lower := (rows 35 67 388 13 50 32 64 128 256), losses := [] }

theorem u35846 : Upper (D 6) (R 6) [34,65,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35847 : Route 9 := (fun mask => (mask,id))

def c35847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35847 : Upper (D 6) (R 6) [34,65,384,5,36] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,36] 13 (by decide) (choices 1) [2,8,16,64] r35847 c35847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19964
  · exact u19965
  · exact u19966
  · exact u19967

def r35848 : Route 9 := (fun mask => (mask,id))

def c35848 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35848 : Upper (D 6) (R 6) [34,65,384,5,40] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,40] 13 (by decide) (choices 1) [2,4,16,64] r35848 c35848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19968
  · exact u19969
  · exact u19970
  · exact u19971

def b35849 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 388 13 82 60 124 188 316), lower := (rows 35 67 388 13 82 32 64 128 256), losses := [] }

theorem u35849 : Upper (D 6) (R 6) [34,65,384,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35850 : Route 9 := (fun mask => (mask,id))

def c35850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35850 : Upper (D 6) (R 6) [34,65,384,5,68] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,68] 13 (by decide) (choices 1) [2,8,16] r35850 c35850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19972
  · exact u19973
  · exact u19974

def r35851 : Route 9 := (fun mask => (mask,id))

def c35851 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35851 : Upper (D 6) (R 6) [34,65,384,5,72] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,72] 13 (by decide) (choices 1) [2,4,16] r35851 c35851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19975
  · exact u19976
  · exact u19977

def r35852 : Route 9 := (fun mask => (mask,id))

def c35852 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35852 : Upper (D 6) (R 6) [34,65,384,5,96] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,96] 13 (by decide) (choices 1) [2,4,8,16] r35852 c35852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19978
  · exact u19979
  · exact u19980
  · exact u19981

def b35853 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 67 388 25 26 100 100 228 356), lower := (rows 35 67 388 25 26 32 64 128 256), losses := [] }

theorem u35853 : Upper (D 6) (R 6) [34,65,384,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35854 : Route 9 := (fun mask => (mask,id))

def c35854 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35854 : Upper (D 6) (R 6) [34,65,384,17,12] 13 := by
  apply FastRouting.sound _ _ [34,65,384,17,12] 13 (by decide) (choices 1) [2,4,64] r35854 c35854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19982
  · exact u19983
  · exact u19984

def b35855 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 67 388 25 50 108 76 204 332), lower := (rows 35 67 388 25 50 32 64 128 256), losses := [] }

theorem u35855 : Upper (D 6) (R 6) [34,65,384,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35856 : Route 9 := (fun mask => (mask,id))

def c35856 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35856 : Upper (D 6) (R 6) [34,65,384,17,36] 13 := by
  apply FastRouting.sound _ _ [34,65,384,17,36] 13 (by decide) (choices 1) [2,4,8,64] r35856 c35856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19985
  · exact u19986
  · exact u19987
  · exact u19988

def b35857 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 67 388 25 56 102 70 198 326), lower := (rows 35 67 388 25 56 32 64 128 256), losses := [] }

theorem u35857 : Upper (D 6) (R 6) [34,65,384,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35858 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 388 25 82 44 108 172 300), lower := (rows 35 67 388 25 82 32 64 128 256), losses := [] }

theorem u35858 : Upper (D 6) (R 6) [34,65,384,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35859 : Route 9 := (fun mask => (mask,id))

def c35859 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35859 : Upper (D 6) (R 6) [34,65,384,17,68] 13 := by
  apply FastRouting.sound _ _ [34,65,384,17,68] 13 (by decide) (choices 1) [2,4,8] r35859 c35859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19989
  · exact u19990
  · exact u19991

def b35860 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 388 25 88 38 102 166 294), lower := (rows 35 67 388 25 88 32 64 128 256), losses := [] }

theorem u35860 : Upper (D 6) (R 6) [34,65,384,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35861 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 67 388 25 112 46 78 142 270), lower := (rows 35 67 388 25 112 32 64 128 256), losses := [] }

theorem u35861 : Upper (D 6) (R 6) [34,65,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35862 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 388 28 28 99 99 227 355), lower := (rows 35 67 388 28 28 32 64 128 256), losses := [] }

theorem u35862 : Upper (D 6) (R 6) [34,65,384,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35863 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 67 388 28 49 110 78 206 334), lower := (rows 35 67 388 28 49 32 64 128 256), losses := [] }

theorem u35863 : Upper (D 6) (R 6) [34,65,384,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35864 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 67 388 28 50 109 77 205 333), lower := (rows 35 67 388 28 50 32 64 128 256), losses := [] }

theorem u35864 : Upper (D 6) (R 6) [34,65,384,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35865 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 388 28 52 107 75 203 331), lower := (rows 35 67 388 28 52 32 64 128 256), losses := [] }

theorem u35865 : Upper (D 6) (R 6) [34,65,384,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35866 : Route 9 := (fun mask => (mask,id))

def c35866 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35866 : Upper (D 6) (R 6) [34,65,384,20,40] 13 := by
  apply FastRouting.sound _ _ [34,65,384,20,40] 13 (by decide) (choices 1) [1,2,4,64] r35866 c35866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19992
  · exact u19993
  · exact u19994
  · exact u19995

def r35867 : Route 9 := (fun mask => (mask,id))

def c35867 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35867 : Upper (D 6) (R 6) [34,65,384,20,96] 13 := by
  apply FastRouting.sound _ _ [34,65,384,20,96] 13 (by decide) (choices 1) [1,2,4,8] r35867 c35867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19996
  · exact u19997
  · exact u19998
  · exact u19999

def b35868 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 67 388 41 84 62 94 158 286), lower := (rows 35 67 388 41 84 32 64 128 256), losses := [] }

theorem u35868 : Upper (D 6) (R 6) [34,65,384,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35869 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 67 388 41 88 54 86 150 278), lower := (rows 35 67 388 41 88 32 64 128 256), losses := [] }

theorem u35869 : Upper (D 6) (R 6) [34,65,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35870 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 388 42 84 61 93 157 285), lower := (rows 35 67 388 42 84 32 64 128 256), losses := [] }

theorem u35870 : Upper (D 6) (R 6) [34,65,384,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35871 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 388 42 88 53 85 149 277), lower := (rows 35 67 388 42 88 32 64 128 256), losses := [] }

theorem u35871 : Upper (D 6) (R 6) [34,65,384,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35872 : Route 9 := (fun mask => (mask,id))

def c35872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35872 : Upper (D 6) (R 6) [34,65,384,36,68] 13 := by
  apply FastRouting.sound _ _ [34,65,384,36,68] 13 (by decide) (choices 1) [1,2,8,16] r35872 c35872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20000
  · exact u20001
  · exact u20002
  · exact u20003

def r35873 : Route 9 := (fun mask => (mask,id))

def c35873 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35873 : Upper (D 6) (R 6) [34,65,384,36,72] 13 := by
  apply FastRouting.sound _ _ [34,65,384,36,72] 13 (by decide) (choices 1) [1,2,4,16] r35873 c35873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20004
  · exact u20005
  · exact u20006
  · exact u20007

def b35874 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 67 388 56 88 39 71 135 263), lower := (rows 35 67 388 56 88 32 64 128 256), losses := [] }

theorem u35874 : Upper (D 6) (R 6) [34,65,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35875 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 25 19 484 452 452 452), lower := (rows 35 70 44 25 19 32 64 128 256), losses := [] }

theorem u35875 : Upper (D 6) (R 6) [34,68,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35876 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 70 44 25 21 482 450 450 450), lower := (rows 35 70 44 25 21 32 64 128 256), losses := [] }

theorem u35876 : Upper (D 6) (R 6) [34,68,40,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35877 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 25 22 481 449 449 449), lower := (rows 35 70 44 25 22 32 64 128 256), losses := [] }

theorem u35877 : Upper (D 6) (R 6) [34,68,40,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35878 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 44 25 81 422 454 390 390), lower := (rows 35 70 44 25 81 32 64 128 256), losses := [] }

theorem u35878 : Upper (D 6) (R 6) [34,68,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35879 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 44 25 82 421 453 389 389), lower := (rows 35 70 44 25 82 32 64 128 256), losses := [] }

theorem u35879 : Upper (D 6) (R 6) [34,68,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35879
end Delivery.IrregularNine14.P06
