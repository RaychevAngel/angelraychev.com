import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0213
import IrregularNine14P06C0214

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30900 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 268 19 116 84 212 340), lower := (rows 11 35 164 268 19 32 64 128 256), losses := [] }

theorem u30900 : Upper (D 6) (R 6) [10,33,160,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30901 : Route 9 := (fun mask => (mask,id))

def c30901 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30901 : Upper (D 6) (R 6) [10,33,160,260,5] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,5] 13 (by decide) (choices 1) [2,16,64] r30901 c30901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12781
  · exact u12782
  · exact u12783

def r30902 : Route 9 := (fun mask => (mask,id))

def c30902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30902 : Upper (D 6) (R 6) [10,33,160,260,6] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,6] 13 (by decide) (choices 1) [1,16,64] r30902 c30902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12784
  · exact u12785
  · exact u12786

def r30903 : Route 9 := (fun mask => (mask,id))

def c30903 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30903 : Upper (D 6) (R 6) [10,33,160,260,65] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,65] 13 (by decide) (choices 1) [2,4,16,64] r30903 c30903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12787
  · exact u12788
  · exact u12789
  · exact u12790

def r30904 : Route 9 := (fun mask => (mask,id))

def c30904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30904 : Upper (D 6) (R 6) [10,33,160,260,66] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,66] 13 (by decide) (choices 1) [1,4,16,64] r30904 c30904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12791
  · exact u12792
  · exact u12793
  · exact u12794

def r30905 : Route 9 := (fun mask => (mask,id))

def c30905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30905 : Upper (D 6) (R 6) [10,33,160,260,68] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,68] 13 (by decide) (choices 1) [1,2,16,64] r30905 c30905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12795
  · exact u12796
  · exact u12797
  · exact u12798

def b30906 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 280 19 100 68 196 324), lower := (rows 11 35 164 280 19 32 64 128 256), losses := [] }

theorem u30906 : Upper (D 6) (R 6) [10,33,160,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30907 : Route 9 := (fun mask => (mask,id))

def c30907 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30907 : Upper (D 6) (R 6) [10,33,160,272,5] 13 := by
  apply FastRouting.sound _ _ [10,33,160,272,5] 13 (by decide) (choices 1) [2,4,64] r30907 c30907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12799
  · exact u12800
  · exact u12801

def b30908 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 329, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 35 164 280 22 101 69 197 325), lower := (rows 11 35 164 280 22 32 64 128 256), losses := [] }

theorem u30908 : Upper (D 6) (R 6) [10,33,160,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30909 : Route 9 := (fun mask => (mask,id))

def c30909 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30909 : Upper (D 6) (R 6) [10,33,160,272,65] 13 := by
  apply FastRouting.sound _ _ [10,33,160,272,65] 13 (by decide) (choices 1) [2,4,64] r30909 c30909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12802
  · exact u12803
  · exact u12804

def r30910 : Route 9 := (fun mask => (mask,id))

def c30910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30910 : Upper (D 6) (R 6) [10,33,160,272,66] 13 := by
  apply FastRouting.sound _ _ [10,33,160,272,66] 13 (by decide) (choices 1) [1,4,64] r30910 c30910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12805
  · exact u12806
  · exact u12807

def r30911 : Route 9 := (fun mask => (mask,id))

def c30911 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30911 : Upper (D 6) (R 6) [10,33,160,272,68] 13 := by
  apply FastRouting.sound _ _ [10,33,160,272,68] 13 (by decide) (choices 1) [1,2,4,64] r30911 c30911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12808
  · exact u12809
  · exact u12810
  · exact u12811

def b30912 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 328 19 116 84 212 340), lower := (rows 11 35 164 328 19 32 64 128 256), losses := [] }

theorem u30912 : Upper (D 6) (R 6) [10,33,160,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30913 : Route 9 := (fun mask => (mask,id))

def c30913 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30913 : Upper (D 6) (R 6) [10,33,160,320,5] 13 := by
  apply FastRouting.sound _ _ [10,33,160,320,5] 13 (by decide) (choices 1) [2,4,16,64] r30913 c30913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12812
  · exact u12813
  · exact u12814
  · exact u12815

def r30914 : Route 9 := (fun mask => (mask,id))

def c30914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30914 : Upper (D 6) (R 6) [10,33,160,320,6] 13 := by
  apply FastRouting.sound _ _ [10,33,160,320,6] 13 (by decide) (choices 1) [1,4,16,64] r30914 c30914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12816
  · exact u12817
  · exact u12818
  · exact u12819

def r30915 : Route 9 := (fun mask => (mask,id))

def c30915 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30915 : Upper (D 6) (R 6) [10,33,160,320,65] 13 := by
  apply FastRouting.sound _ _ [10,33,160,320,65] 13 (by decide) (choices 1) [2,4,16] r30915 c30915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12820
  · exact u12821
  · exact u12822

def r30916 : Route 9 := (fun mask => (mask,id))

def c30916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30916 : Upper (D 6) (R 6) [10,33,160,320,66] 13 := by
  apply FastRouting.sound _ _ [10,33,160,320,66] 13 (by decide) (choices 1) [1,4,16] r30916 c30916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12823
  · exact u12824
  · exact u12825

def r30917 : Route 9 := (fun mask => (mask,id))

def c30917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30917 : Upper (D 6) (R 6) [10,33,160,320,68] 13 := by
  apply FastRouting.sound _ _ [10,33,160,320,68] 13 (by decide) (choices 1) [1,2,4,16] r30917 c30917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12826
  · exact u12827
  · exact u12828
  · exact u12829

def b30918 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 196 13 22 368 368 496 368), lower := (rows 11 35 196 13 22 32 64 128 256), losses := [] }

theorem u30918 : Upper (D 6) (R 6) [10,33,192,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30919 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 196 13 50 372 340 468 340), lower := (rows 11 35 196 13 50 32 64 128 256), losses := [] }

theorem u30919 : Upper (D 6) (R 6) [10,33,192,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30920 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 196 13 52 370 338 466 338), lower := (rows 11 35 196 13 52 32 64 128 256), losses := [] }

theorem u30920 : Upper (D 6) (R 6) [10,33,192,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30921 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 420, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 13 82 308 372 436 308), lower := (rows 11 35 196 13 82 32 64 128 256), losses := [] }

theorem u30921 : Upper (D 6) (R 6) [10,33,192,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30922 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 196 13 84 306 370 434 306), lower := (rows 11 35 196 13 84 32 64 128 256), losses := [] }

theorem u30922 : Upper (D 6) (R 6) [10,33,192,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30923 : Route 9 := (fun mask => (mask,id))

def c30923 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30923 : Upper (D 6) (R 6) [10,33,192,5,96] 13 := by
  apply FastRouting.sound _ _ [10,33,192,5,96] 13 (by decide) (choices 1) [2,4,16,256] r30923 c30923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12830
  · exact u12831
  · exact u12832
  · exact u12833

def b30924 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 13 274 116 116 244 372), lower := (rows 11 35 196 13 274 32 64 128 256), losses := [] }

theorem u30924 : Upper (D 6) (R 6) [10,33,192,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30925 : Route 9 := (fun mask => (mask,id))

def c30925 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30925 : Upper (D 6) (R 6) [10,33,192,5,260] 13 := by
  apply FastRouting.sound _ _ [10,33,192,5,260] 13 (by decide) (choices 1) [2,16,64] r30925 c30925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12834
  · exact u12835
  · exact u12836

def r30926 : Route 9 := (fun mask => (mask,id))

def c30926 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30926 : Upper (D 6) (R 6) [10,33,192,5,288] 13 := by
  apply FastRouting.sound _ _ [10,33,192,5,288] 13 (by decide) (choices 1) [2,4,16,64] r30926 c30926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12837
  · exact u12838
  · exact u12839
  · exact u12840

def r30927 : Route 9 := (fun mask => (mask,id))

def c30927 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30927 : Upper (D 6) (R 6) [10,33,192,5,320] 13 := by
  apply FastRouting.sound _ _ [10,33,192,5,320] 13 (by decide) (choices 1) [2,4,16] r30927 c30927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12841
  · exact u12842
  · exact u12843

def b30928 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 196 25 22 356 356 484 356), lower := (rows 11 35 196 25 22 32 64 128 256), losses := [] }

theorem u30928 : Upper (D 6) (R 6) [10,33,192,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30929 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 27, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 25 50 356 324 452 324), lower := (rows 11 35 196 25 50 32 64 128 256), losses := [] }

theorem u30929 : Upper (D 6) (R 6) [10,33,192,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30930 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 25 52 358 326 454 326), lower := (rows 11 35 196 25 52 32 64 128 256), losses := [] }

theorem u30930 : Upper (D 6) (R 6) [10,33,192,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30931 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 196 25 82 292 356 420 292), lower := (rows 11 35 196 25 82 32 64 128 256), losses := [] }

theorem u30931 : Upper (D 6) (R 6) [10,33,192,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30932 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 196 25 84 294 358 422 294), lower := (rows 11 35 196 25 84 32 64 128 256), losses := [] }

theorem u30932 : Upper (D 6) (R 6) [10,33,192,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30933 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 25 112 294 326 390 262), lower := (rows 11 35 196 25 112 32 64 128 256), losses := [] }

theorem u30933 : Upper (D 6) (R 6) [10,33,192,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30934 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 196 25 274 100 100 228 356), lower := (rows 11 35 196 25 274 32 64 128 256), losses := [] }

theorem u30934 : Upper (D 6) (R 6) [10,33,192,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30935 : Route 9 := (fun mask => (mask,id))

def c30935 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30935 : Upper (D 6) (R 6) [10,33,192,17,260] 13 := by
  apply FastRouting.sound _ _ [10,33,192,17,260] 13 (by decide) (choices 1) [2,4,64] r30935 c30935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12844
  · exact u12845
  · exact u12846

def b30936 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 25 304 102 70 198 326), lower := (rows 11 35 196 25 304 32 64 128 256), losses := [] }

theorem u30936 : Upper (D 6) (R 6) [10,33,192,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30937 : Route 9 := (fun mask => (mask,id))

def c30937 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30937 : Upper (D 6) (R 6) [10,33,192,17,320] 13 := by
  apply FastRouting.sound _ _ [10,33,192,17,320] 13 (by decide) (choices 1) [2,4] r30937 c30937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12847
  · exact u12848

def b30938 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 28 19 356 356 484 356), lower := (rows 11 35 196 28 19 32 64 128 256), losses := [] }

theorem u30938 : Upper (D 6) (R 6) [10,33,192,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30939 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 196 28 21 354 354 482 354), lower := (rows 11 35 196 28 21 32 64 128 256), losses := [] }

theorem u30939 : Upper (D 6) (R 6) [10,33,192,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30940 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 196 28 22 353 353 481 353), lower := (rows 11 35 196 28 22 32 64 128 256), losses := [] }

theorem u30940 : Upper (D 6) (R 6) [10,33,192,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30941 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 196 28 49 358 326 454 326), lower := (rows 11 35 196 28 49 32 64 128 256), losses := [] }

theorem u30941 : Upper (D 6) (R 6) [10,33,192,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30942 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 196 28 50 357 325 453 325), lower := (rows 11 35 196 28 50 32 64 128 256), losses := [] }

theorem u30942 : Upper (D 6) (R 6) [10,33,192,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30943 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 196 28 52 355 323 451 323), lower := (rows 11 35 196 28 52 32 64 128 256), losses := [] }

theorem u30943 : Upper (D 6) (R 6) [10,33,192,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30944 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 484, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 11 35 196 28 81 294 358 422 294), lower := (rows 11 35 196 28 81 32 64 128 256), losses := [] }

theorem u30944 : Upper (D 6) (R 6) [10,33,192,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30945 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 35 196 28 82 293 357 421 293), lower := (rows 11 35 196 28 82 32 64 128 256), losses := [] }

theorem u30945 : Upper (D 6) (R 6) [10,33,192,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30946 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 196 28 84 291 355 419 291), lower := (rows 11 35 196 28 84 32 64 128 256), losses := [] }

theorem u30946 : Upper (D 6) (R 6) [10,33,192,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30947 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 35 196 28 112 295 327 391 263), lower := (rows 11 35 196 28 112 32 64 128 256), losses := [] }

theorem u30947 : Upper (D 6) (R 6) [10,33,192,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30948 : Route 9 := (fun mask => (mask,id))

def c30948 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30948 : Upper (D 6) (R 6) [10,33,192,20,257] 13 := by
  apply FastRouting.sound _ _ [10,33,192,20,257] 13 (by decide) (choices 1) [2,4,64] r30948 c30948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12849
  · exact u12850
  · exact u12851

def r30949 : Route 9 := (fun mask => (mask,id))

def c30949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30949 : Upper (D 6) (R 6) [10,33,192,20,258] 13 := by
  apply FastRouting.sound _ _ [10,33,192,20,258] 13 (by decide) (choices 1) [1,4,64] r30949 c30949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12852
  · exact u12853
  · exact u12854

def b30950 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 196 28 276 99 99 227 355), lower := (rows 11 35 196 28 276 32 64 128 256), losses := [] }

theorem u30950 : Upper (D 6) (R 6) [10,33,192,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30951 : Route 9 := (fun mask => (mask,id))

def c30951 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30951 : Upper (D 6) (R 6) [10,33,192,20,288] 13 := by
  apply FastRouting.sound _ _ [10,33,192,20,288] 13 (by decide) (choices 1) [1,2,4,64] r30951 c30951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12855
  · exact u12856
  · exact u12857
  · exact u12858

def r30952 : Route 9 := (fun mask => (mask,id))

def c30952 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30952 : Upper (D 6) (R 6) [10,33,192,20,320] 13 := by
  apply FastRouting.sound _ _ [10,33,192,20,320] 13 (by decide) (choices 1) [1,2,4] r30952 c30952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12859
  · exact u12860
  · exact u12861

def b30953 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 73 22 308 372 436 308), lower := (rows 11 35 196 73 22 32 64 128 256), losses := [] }

theorem u30953 : Upper (D 6) (R 6) [10,33,192,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30954 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 196 73 50 308 340 404 276), lower := (rows 11 35 196 73 50 32 64 128 256), losses := [] }

theorem u30954 : Upper (D 6) (R 6) [10,33,192,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30955 : Route 9 := (fun mask => (mask,id))

def c30955 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30955 : Upper (D 6) (R 6) [10,33,192,65,36] 13 := by
  apply FastRouting.sound _ _ [10,33,192,65,36] 13 (by decide) (choices 1) [2,4,16,256] r30955 c30955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12862
  · exact u12863
  · exact u12864
  · exact u12865

def b30956 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 73 274 52 116 180 308), lower := (rows 11 35 196 73 274 32 64 128 256), losses := [] }

theorem u30956 : Upper (D 6) (R 6) [10,33,192,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30957 : Route 9 := (fun mask => (mask,id))

def c30957 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30957 : Upper (D 6) (R 6) [10,33,192,65,260] 13 := by
  apply FastRouting.sound _ _ [10,33,192,65,260] 13 (by decide) (choices 1) [2,4,16] r30957 c30957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12866
  · exact u12867
  · exact u12868

def r30958 : Route 9 := (fun mask => (mask,id))

def c30958 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30958 : Upper (D 6) (R 6) [10,33,192,65,288] 13 := by
  apply FastRouting.sound _ _ [10,33,192,65,288] 13 (by decide) (choices 1) [2,4,16] r30958 c30958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12869
  · exact u12870
  · exact u12871

def b30959 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 88 19 292 356 420 292), lower := (rows 11 35 196 88 19 32 64 128 256), losses := [] }

theorem u30959 : Upper (D 6) (R 6) [10,33,192,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30959
end Delivery.IrregularNine14.P06
