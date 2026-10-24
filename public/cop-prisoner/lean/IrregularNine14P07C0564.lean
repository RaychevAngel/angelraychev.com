import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0300
import IrregularNine14P07C0301
import IrregularNine14P07C0302

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33840 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 176 370 338 466 338), lower := (rows 35 67 13 140 176 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 35 67 131 259), good := (rows 498 498 508 156 176 32 64 128 256) }] }

theorem u33840 : Upper (D 7) (R 7) [34,65,9,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33841 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 291, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 208 306 370 434 306), lower := (rows 35 67 13 140 208 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 35 67 131 259), good := (rows 498 498 508 156 208 32 64 128 256) }] }

theorem u33841 : Upper (D 7) (R 7) [34,65,9,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33842 : Route 9 := (fun mask => (mask,id))

def c33842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33842 : Upper (D 7) (R 7) [34,65,9,132,258] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,258] 13 (by decide) (choices 1) [16,64,128] r33842 c33842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18018
  · exact u18019
  · exact u18020

def r33843 : Route 9 := (fun mask => (mask,id))

def c33843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33843 : Upper (D 7) (R 7) [34,65,9,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,288] 13 (by decide) (choices 1) [2,16,64,128] r33843 c33843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18021
  · exact u18022
  · exact u18023
  · exact u18024

def r33844 : Route 9 := (fun mask => (mask,id))

def c33844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33844 : Upper (D 7) (R 7) [34,65,9,132,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,320] 13 (by decide) (choices 1) [2,16,128] r33844 c33844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18025
  · exact u18026
  · exact u18027

def b33845 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 400 114 114 242 370), lower := (rows 35 67 13 140 400 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 35 67 131 259), good := (rows 498 498 508 156 400 32 64 128 256) }] }

theorem u33845 : Upper (D 7) (R 7) [34,65,9,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33846 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 67 13 152 50 484 452 452 452), lower := (rows 35 67 13 152 50 32 64 128 256), losses := [] }

theorem u33846 : Upper (D 7) (R 7) [34,65,9,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33847 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,5),(4,0)], upper := (rows 35 67 13 152 52 482 450 450 450), lower := (rows 35 67 13 152 52 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 152 60 32 64 128 256) },{ target := 5, region := (rows 1 7 4 24 16 0 87 151 279), good := (rows 451 451 463 472 478 0 64 128 256) }] }

theorem u33847 : Upper (D 7) (R 7) [34,65,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33848 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 67 13 152 82 420 484 420 420), lower := (rows 35 67 13 152 82 32 64 128 256), losses := [] }

theorem u33848 : Upper (D 7) (R 7) [34,65,9,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33849 : Route 9 := (fun mask => (mask,id))

def c33849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33849 : Upper (D 7) (R 7) [34,65,9,144,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,68] 13 (by decide) (choices 1) [2,128,256] r33849 c33849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18028
  · exact u18029
  · exact u18030

def b33850 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 3, targets := 128 },{ cop := 2, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 67 13 152 112 422 454 390 390), lower := (rows 35 67 13 152 112 32 64 128 256), losses := [{ target := 7, region := (rows 17 18 12 8 16 32 64 0 256), good := (rows 35 67 13 31 115 32 64 0 256) }] }

theorem u33850 : Upper (D 7) (R 7) [34,65,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33851 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 13 152 146 356 356 484 356), lower := (rows 35 67 13 152 146 32 64 128 256), losses := [] }

theorem u33851 : Upper (D 7) (R 7) [34,65,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33852 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 13 152 148 354 354 482 354), lower := (rows 35 67 13 152 148 32 64 128 256), losses := [] }

theorem u33852 : Upper (D 7) (R 7) [34,65,9,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33853 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 13 152 176 358 326 454 326), lower := (rows 35 67 13 152 176 32 64 128 256), losses := [] }

theorem u33853 : Upper (D 7) (R 7) [34,65,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33854 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 13 152 208 294 358 422 294), lower := (rows 35 67 13 152 208 32 64 128 256), losses := [] }

theorem u33854 : Upper (D 7) (R 7) [34,65,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33855 : Route 9 := (fun mask => (mask,id))

def c33855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33855 : Upper (D 7) (R 7) [34,65,9,144,258] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,258] 13 (by decide) (choices 1) [4,64,128] r33855 c33855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18031
  · exact u18032
  · exact u18033

def r33856 : Route 9 := (fun mask => (mask,id))

def c33856 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33856 : Upper (D 7) (R 7) [34,65,9,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,260] 13 (by decide) (choices 1) [2,64,128] r33856 c33856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18034
  · exact u18035
  · exact u18036

def r33857 : Route 9 := (fun mask => (mask,id))

def c33857 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33857 : Upper (D 7) (R 7) [34,65,9,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,288] 13 (by decide) (choices 1) [2,4,64,128] r33857 c33857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18037
  · exact u18038
  · exact u18039
  · exact u18040

def r33858 : Route 9 := (fun mask => (mask,id))

def c33858 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33858 : Upper (D 7) (R 7) [34,65,9,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,320] 13 (by decide) (choices 1) [2,4,128] r33858 c33858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18041
  · exact u18042
  · exact u18043

def b33859 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 13 152 400 102 102 230 358), lower := (rows 35 67 13 152 400 32 64 128 256), losses := [] }

theorem u33859 : Upper (D 7) (R 7) [34,65,9,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33860 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 67 13 168 82 436 468 404 404), lower := (rows 35 67 13 168 82 32 64 128 256), losses := [] }

theorem u33860 : Upper (D 7) (R 7) [34,65,9,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33861 : Route 9 := (fun mask => (mask,id))

def c33861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u33861 : Upper (D 7) (R 7) [34,65,9,160,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,68] 13 (by decide) (choices 1) [2,16,128,256] r33861 c33861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18044
  · exact u18045
  · exact u18046
  · exact u18047

def r33862 : Route 9 := (fun mask => (mask,id))

def c33862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u33862 : Upper (D 7) (R 7) [34,65,9,160,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,130] 13 (by decide) (choices 1) [4,16,64,256] r33862 c33862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18048
  · exact u18049
  · exact u18050
  · exact u18051

def b33863 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 67 13 168 148 370 338 466 338), lower := (rows 35 67 13 168 148 32 64 128 256), losses := [] }

theorem u33863 : Upper (D 7) (R 7) [34,65,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33864 : Route 9 := (fun mask => (mask,id))

def c33864 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33864 : Upper (D 7) (R 7) [34,65,9,160,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,192] 13 (by decide) (choices 1) [2,4,16,256] r33864 c33864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18052
  · exact u18053
  · exact u18054
  · exact u18055

def r33865 : Route 9 := (fun mask => (mask,id))

def c33865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33865 : Upper (D 7) (R 7) [34,65,9,160,258] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,258] 13 (by decide) (choices 1) [4,16,64,128] r33865 c33865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18056
  · exact u18057
  · exact u18058
  · exact u18059

def r33866 : Route 9 := (fun mask => (mask,id))

def c33866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33866 : Upper (D 7) (R 7) [34,65,9,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,260] 13 (by decide) (choices 1) [2,16,64,128] r33866 c33866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18060
  · exact u18061
  · exact u18062
  · exact u18063

def r33867 : Route 9 := (fun mask => (mask,id))

def c33867 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33867 : Upper (D 7) (R 7) [34,65,9,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,320] 13 (by decide) (choices 1) [2,4,16,128] r33867 c33867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18064
  · exact u18065
  · exact u18066
  · exact u18067

def r33868 : Route 9 := (fun mask => (mask,id))

def c33868 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33868 : Upper (D 7) (R 7) [34,65,9,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,384] 13 (by decide) (choices 1) [2,4,16,64] r33868 c33868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18068
  · exact u18069
  · exact u18070
  · exact u18071

def b33869 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 67 13 200 50 436 468 404 404), lower := (rows 35 67 13 200 50 32 64 128 256), losses := [] }

theorem u33869 : Upper (D 7) (R 7) [34,65,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33870 : Route 9 := (fun mask => (mask,id))

def c33870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u33870 : Upper (D 7) (R 7) [34,65,9,192,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,36] 13 (by decide) (choices 1) [2,16,128,256] r33870 c33870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18072
  · exact u18073
  · exact u18074
  · exact u18075

def r33871 : Route 9 := (fun mask => (mask,id))

def c33871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33871 : Upper (D 7) (R 7) [34,65,9,192,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,130] 13 (by decide) (choices 1) [4,16,256] r33871 c33871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18076
  · exact u18077
  · exact u18078

def r33872 : Route 9 := (fun mask => (mask,id))

def c33872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33872 : Upper (D 7) (R 7) [34,65,9,192,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,132] 13 (by decide) (choices 1) [2,16,256] r33872 c33872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18079
  · exact u18080
  · exact u18081

def r33873 : Route 9 := (fun mask => (mask,id))

def c33873 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33873 : Upper (D 7) (R 7) [34,65,9,192,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,160] 13 (by decide) (choices 1) [2,4,16,256] r33873 c33873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18082
  · exact u18083
  · exact u18084
  · exact u18085

def r33874 : Route 9 := (fun mask => (mask,id))

def c33874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33874 : Upper (D 7) (R 7) [34,65,9,192,258] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,258] 13 (by decide) (choices 1) [4,16,128] r33874 c33874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18086
  · exact u18087
  · exact u18088

def r33875 : Route 9 := (fun mask => (mask,id))

def c33875 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33875 : Upper (D 7) (R 7) [34,65,9,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,260] 13 (by decide) (choices 1) [2,16,128] r33875 c33875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18089
  · exact u18090
  · exact u18091

def r33876 : Route 9 := (fun mask => (mask,id))

def c33876 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33876 : Upper (D 7) (R 7) [34,65,9,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,288] 13 (by decide) (choices 1) [2,4,16,128] r33876 c33876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18092
  · exact u18093
  · exact u18094
  · exact u18095

def r33877 : Route 9 := (fun mask => (mask,id))

def c33877 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33877 : Upper (D 7) (R 7) [34,65,9,192,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,384] 13 (by decide) (choices 1) [2,4,16] r33877 c33877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18096
  · exact u18097
  · exact u18098

def r33878 : Route 9 := (fun mask => (mask,id))

def c33878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33878 : Upper (D 7) (R 7) [34,65,9,258,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,36] 13 (by decide) (choices 1) [16,64,128] r33878 c33878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18099
  · exact u18100
  · exact u18101

def r33879 : Route 9 := (fun mask => (mask,id))

def c33879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33879 : Upper (D 7) (R 7) [34,65,9,258,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,68] 13 (by decide) (choices 1) [16,128] r33879 c33879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18102
  · exact u18103

def b33880 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 67 13 266 112 180 212 148 404), lower := (rows 35 67 13 266 112 32 64 128 256), losses := [] }

theorem u33880 : Upper (D 7) (R 7) [34,65,9,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33881 : Route 9 := (fun mask => (mask,id))

def c33881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33881 : Upper (D 7) (R 7) [34,65,9,258,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,132] 13 (by decide) (choices 1) [16,64,128] r33881 c33881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18104
  · exact u18105
  · exact u18106

def r33882 : Route 9 := (fun mask => (mask,id))

def c33882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33882 : Upper (D 7) (R 7) [34,65,9,258,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,160] 13 (by decide) (choices 1) [4,16,64,128] r33882 c33882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18107
  · exact u18108
  · exact u18109
  · exact u18110

def r33883 : Route 9 := (fun mask => (mask,id))

def c33883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33883 : Upper (D 7) (R 7) [34,65,9,258,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,192] 13 (by decide) (choices 1) [4,16,128] r33883 c33883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18111
  · exact u18112
  · exact u18113

def b33884 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 67 13 268 50 240 208 208 464), lower := (rows 35 67 13 268 50 32 64 128 256), losses := [] }

theorem u33884 : Upper (D 7) (R 7) [34,65,9,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33885 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 1, region := 16, targets := 32 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 35 67 13 268 82 176 240 176 432), lower := (rows 35 67 13 268 82 32 64 128 256), losses := [] }

theorem u33885 : Upper (D 7) (R 7) [34,65,9,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33886 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 3, targets := 128 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 268 112 178 210 146 402), lower := (rows 35 67 13 268 112 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 35 67 131 259), good := (rows 498 498 508 284 112 32 64 128 256) }] }

theorem u33886 : Upper (D 7) (R 7) [34,65,9,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33887 : Route 9 := (fun mask => (mask,id))

def c33887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33887 : Upper (D 7) (R 7) [34,65,9,260,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,130] 13 (by decide) (choices 1) [16,64,128] r33887 c33887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18114
  · exact u18115
  · exact u18116

def r33888 : Route 9 := (fun mask => (mask,id))

def c33888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33888 : Upper (D 7) (R 7) [34,65,9,260,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,160] 13 (by decide) (choices 1) [2,16,64,128] r33888 c33888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18117
  · exact u18118
  · exact u18119
  · exact u18120

def r33889 : Route 9 := (fun mask => (mask,id))

def c33889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33889 : Upper (D 7) (R 7) [34,65,9,260,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,192] 13 (by decide) (choices 1) [2,16,128] r33889 c33889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18121
  · exact u18122
  · exact u18123

def b33890 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 67 13 280 50 228 196 196 452), lower := (rows 35 67 13 280 50 32 64 128 256), losses := [] }

theorem u33890 : Upper (D 7) (R 7) [34,65,9,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33891 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(3,5),(4,0)], upper := (rows 35 67 13 280 52 226 194 194 450), lower := (rows 35 67 13 280 52 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 280 60 32 64 128 256) },{ target := 5, region := (rows 1 7 4 24 16 0 87 151 279), good := (rows 451 451 463 472 478 0 64 128 256) }] }

theorem u33891 : Upper (D 7) (R 7) [34,65,9,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33892 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 67 13 280 82 164 228 164 420), lower := (rows 35 67 13 280 82 32 64 128 256), losses := [] }

theorem u33892 : Upper (D 7) (R 7) [34,65,9,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33893 : Route 9 := (fun mask => (mask,id))

def c33893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33893 : Upper (D 7) (R 7) [34,65,9,272,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,68] 13 (by decide) (choices 1) [2,128] r33893 c33893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18124
  · exact u18125

def b33894 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 3, targets := 128 },{ cop := 2, region := 194, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 67 13 280 112 166 198 134 390), lower := (rows 35 67 13 280 112 32 64 128 256), losses := [{ target := 7, region := (rows 17 18 12 8 16 32 64 0 256), good := (rows 35 67 13 287 115 32 64 0 256) }] }

theorem u33894 : Upper (D 7) (R 7) [34,65,9,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33895 : Route 9 := (fun mask => (mask,id))

def c33895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33895 : Upper (D 7) (R 7) [34,65,9,272,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,130] 13 (by decide) (choices 1) [4,64,128] r33895 c33895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18126
  · exact u18127
  · exact u18128

def r33896 : Route 9 := (fun mask => (mask,id))

def c33896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33896 : Upper (D 7) (R 7) [34,65,9,272,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,132] 13 (by decide) (choices 1) [2,64,128] r33896 c33896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18129
  · exact u18130
  · exact u18131

def r33897 : Route 9 := (fun mask => (mask,id))

def c33897 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33897 : Upper (D 7) (R 7) [34,65,9,272,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,160] 13 (by decide) (choices 1) [2,4,64,128] r33897 c33897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18132
  · exact u18133
  · exact u18134
  · exact u18135

def r33898 : Route 9 := (fun mask => (mask,id))

def c33898 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33898 : Upper (D 7) (R 7) [34,65,9,272,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,192] 13 (by decide) (choices 1) [2,4,128] r33898 c33898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18136
  · exact u18137
  · exact u18138

def b33899 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 67 13 296 82 180 212 148 404), lower := (rows 35 67 13 296 82 32 64 128 256), losses := [] }

theorem u33899 : Upper (D 7) (R 7) [34,65,9,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33899
end Delivery.IrregularNine14.P07
