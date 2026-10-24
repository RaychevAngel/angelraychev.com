import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0208
import IrregularNine14P08C0213
import IrregularNine14P08C0214
import IrregularNine14P08C0215

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20880 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 504 488 488 488 488), lower := (rows 97 7 37 26 16 32 64 128 256), losses := [] }

theorem u20880 : Upper (D 8) (R 8) [96,5,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20881 : PairBound 9 := { available := 472, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 42 472 504 472 472 472), lower := (rows 97 7 37 42 16 32 64 128 256), losses := [] }

theorem u20881 : Upper (D 8) (R 8) [96,5,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20882 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 440 440 504 440 440), lower := (rows 97 7 37 74 16 32 64 128 256), losses := [] }

theorem u20882 : Upper (D 8) (R 8) [96,5,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20883 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 504 504 504 504 504), lower := (rows 97 7 37 138 16 32 64 128 256), losses := [] }

theorem u20883 : Upper (D 8) (R 8) [96,5,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20884 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 168 474 506 474 474 474), lower := (rows 97 7 37 168 16 32 64 128 256), losses := [] }

theorem u20884 : Upper (D 8) (R 8) [96,5,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20885 : PairBound 9 := { available := 442, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 442 442 506 442 442), lower := (rows 97 7 37 200 16 32 64 128 256), losses := [] }

theorem u20885 : Upper (D 8) (R 8) [96,5,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20886 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 266 248 248 248 248 504), lower := (rows 97 7 37 266 16 32 64 128 256), losses := [] }

theorem u20886 : Upper (D 8) (R 8) [96,5,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20887 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 296 218 250 218 218 474), lower := (rows 97 7 37 296 16 32 64 128 256), losses := [] }

theorem u20887 : Upper (D 8) (R 8) [96,5,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20888 : PairBound 9 := { available := 186, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 328 186 186 250 186 442), lower := (rows 97 7 37 328 16 32 64 128 256), losses := [] }

theorem u20888 : Upper (D 8) (R 8) [96,5,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20889 : PairBound 9 := { available := 250, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 392 250 250 250 250 506), lower := (rows 97 7 37 392 16 32 64 128 256), losses := [] }

theorem u20889 : Upper (D 8) (R 8) [96,5,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20890 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 504 504 504 504 504), lower := (rows 97 7 38 137 16 32 64 128 256), losses := [] }

theorem u20890 : Upper (D 8) (R 8) [96,5,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20891 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 168 473 505 473 473 473), lower := (rows 97 7 38 168 16 32 64 128 256), losses := [] }

theorem u20891 : Upper (D 8) (R 8) [96,5,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20892 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 441 441 505 441 441), lower := (rows 97 7 38 200 16 32 64 128 256), losses := [] }

theorem u20892 : Upper (D 8) (R 8) [96,5,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20893 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 265 248 248 248 248 504), lower := (rows 97 7 38 265 16 32 64 128 256), losses := [] }

theorem u20893 : Upper (D 8) (R 8) [96,5,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20894 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 296 217 249 217 217 473), lower := (rows 97 7 38 296 16 32 64 128 256), losses := [] }

theorem u20894 : Upper (D 8) (R 8) [96,5,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20895 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 328 185 185 249 185 441), lower := (rows 97 7 38 328 16 32 64 128 256), losses := [] }

theorem u20895 : Upper (D 8) (R 8) [96,5,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20896 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 392 249 249 249 249 505), lower := (rows 97 7 38 392 16 32 64 128 256), losses := [] }

theorem u20896 : Upper (D 8) (R 8) [96,5,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20897 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 25 498 482 482 482 482), lower := (rows 97 7 44 25 16 32 64 128 256), losses := [] }

theorem u20897 : Upper (D 8) (R 8) [96,5,40,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20898 : Route 9 := (fun mask => (mask,id))

def c20898 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20898 : Upper (D 8) (R 8) [96,5,40,18] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20898 c20898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12809
  · exact u12810
  · exact u12811
  · exact u12812
  · exact u12813
  · exact u12814
  · exact u12815
  · exact u12816
  · exact u12817
  · exact u12818

def b20899 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 41 466 498 466 466 466), lower := (rows 97 7 44 41 16 32 64 128 256), losses := [] }

theorem u20899 : Upper (D 8) (R 8) [96,5,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20900 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 42 465 497 465 465 465), lower := (rows 97 7 44 42 16 32 64 128 256), losses := [] }

theorem u20900 : Upper (D 8) (R 8) [96,5,40,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20901 : PairBound 9 := { available := 451, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 56 467 483 451 451 451), lower := (rows 97 7 44 56 16 32 64 128 256), losses := [] }

theorem u20901 : Upper (D 8) (R 8) [96,5,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20902 : PairBound 9 := { available := 434, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 73 434 434 498 434 434), lower := (rows 97 7 44 73 16 32 64 128 256), losses := [] }

theorem u20902 : Upper (D 8) (R 8) [96,5,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20903 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 433 433 497 433 433), lower := (rows 97 7 44 74 16 32 64 128 256), losses := [] }

theorem u20903 : Upper (D 8) (R 8) [96,5,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20904 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 88 435 419 483 419 419), lower := (rows 97 7 44 88 16 32 64 128 256), losses := [] }

theorem u20904 : Upper (D 8) (R 8) [96,5,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20905 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 104 403 435 467 403 403), lower := (rows 97 7 44 104 16 32 64 128 256), losses := [] }

theorem u20905 : Upper (D 8) (R 8) [96,5,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20906 : PairBound 9 := { available := 498, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 498 498 498 498 498), lower := (rows 97 7 44 137 16 32 64 128 256), losses := [] }

theorem u20906 : Upper (D 8) (R 8) [96,5,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20907 : Route 9 := (fun mask => (mask,id))

def c20907 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20907 : Upper (D 8) (R 8) [96,5,40,130] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20907 c20907
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12871
  · exact u12872
  · exact u12873
  · exact u12874
  · exact u12875
  · exact u12876
  · exact u12877
  · exact u12878
  · exact u12879
  · exact u12880

theorem m20908_3 : Upper (D 8) (R 8) [96,5,40,144,3] 13 :=
  permutation_upper _ _ _ [96,5,9,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12518

def r20908 : Route 9 := (fun mask => (mask,id))

def c20908 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20908 : Upper (D 8) (R 8) [96,5,40,144] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r20908 c20908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20908_3
  · exact u12881
  · exact u12882
  · exact u12883
  · exact u12884
  · exact u12885
  · exact u12886
  · exact u12887
  · exact u12888
  · exact u12889
  · exact u12890
  · exact u12891
  · exact u12892
  · exact u12893
  · exact u12894

def b20909 : PairBound 9 := { available := 467, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 467 499 467 467 467), lower := (rows 97 7 44 168 16 32 64 128 256), losses := [] }

theorem u20909 : Upper (D 8) (R 8) [96,5,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20910 : PairBound 9 := { available := 435, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 435 435 499 435 435), lower := (rows 97 7 44 200 16 32 64 128 256), losses := [] }

theorem u20910 : Upper (D 8) (R 8) [96,5,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20911 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 265 242 242 242 242 498), lower := (rows 97 7 44 265 16 32 64 128 256), losses := [] }

theorem u20911 : Upper (D 8) (R 8) [96,5,40,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20912 : Route 9 := (fun mask => (mask,id))

def c20912 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20912 : Upper (D 8) (R 8) [96,5,40,258] 13 := by
  apply FastRouting.sound _ _ [96,5,40,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20912 c20912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12916
  · exact u12917
  · exact u12918
  · exact u12919
  · exact u12920
  · exact u12921

theorem m20913_3 : Upper (D 8) (R 8) [96,5,40,272,3] 13 :=
  permutation_upper _ _ _ [96,5,9,48,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12520

def r20913 : Route 9 := (fun mask => (mask,id))

def c20913 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20913 : Upper (D 8) (R 8) [96,5,40,272] 13 := by
  apply FastRouting.sound _ _ [96,5,40,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r20913 c20913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20913_3
  · exact u12922
  · exact u12923
  · exact u12924
  · exact u12925
  · exact u12926
  · exact u12927
  · exact u12928
  · exact u12929
  · exact u12930

def b20914 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 296 211 243 211 211 467), lower := (rows 97 7 44 296 16 32 64 128 256), losses := [] }

theorem u20914 : Upper (D 8) (R 8) [96,5,40,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20915 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 328 179 179 243 179 435), lower := (rows 97 7 44 328 16 32 64 128 256), losses := [] }

theorem u20915 : Upper (D 8) (R 8) [96,5,40,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20916_3 : Upper (D 8) (R 8) [96,5,40,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,48,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12522

def r20916 : Route 9 := (fun mask => (mask,id))

def c20916 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20916 : Upper (D 8) (R 8) [96,5,40,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r20916 c20916
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20916_3
  · exact u12939
  · exact u12940
  · exact u12941
  · exact u12942
  · exact u12943
  · exact u12944
  · exact u12945
  · exact u12946
  · exact u12947

theorem m20917_9 : Upper (D 8) (R 8) [96,5,48,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12800

theorem m20917_65 : Upper (D 8) (R 8) [96,5,48,34,65] 13 :=
  permutation_upper _ _ _ [96,5,40,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12838

theorem m20917_72 : Upper (D 8) (R 8) [96,5,48,34,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12849

theorem m20917_129 : Upper (D 8) (R 8) [96,5,48,34,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12862

theorem m20917_136 : Upper (D 8) (R 8) [96,5,48,34,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12882

theorem m20917_192 : Upper (D 8) (R 8) [96,5,48,34,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12903

theorem m20917_257 : Upper (D 8) (R 8) [96,5,48,34,257] 13 :=
  permutation_upper _ _ _ [96,5,40,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12911

theorem m20917_264 : Upper (D 8) (R 8) [96,5,48,34,264] 13 :=
  permutation_upper _ _ _ [96,5,40,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12923

theorem m20917_320 : Upper (D 8) (R 8) [96,5,48,34,320] 13 :=
  permutation_upper _ _ _ [96,5,40,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12935

theorem m20917_384 : Upper (D 8) (R 8) [96,5,48,34,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12940

def r20917 : Route 9 := (fun mask => (mask,id))

def c20917 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u20917 : Upper (D 8) (R 8) [96,5,48,34] 13 := by
  apply FastRouting.sound _ _ [96,5,48,34] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r20917 c20917
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20917_9
  · exact m20917_65
  · exact m20917_72
  · exact m20917_129
  · exact m20917_136
  · exact m20917_192
  · exact m20917_257
  · exact m20917_264
  · exact m20917_320
  · exact m20917_384

theorem m20918_9 : Upper (D 8) (R 8) [96,5,48,66,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12801

theorem m20918_33 : Upper (D 8) (R 8) [96,5,48,66,33] 13 :=
  permutation_upper _ _ _ [96,5,40,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12819

theorem m20918_40 : Upper (D 8) (R 8) [96,5,48,66,40] 13 :=
  permutation_upper _ _ _ [96,5,40,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12830

theorem m20918_129 : Upper (D 8) (R 8) [96,5,48,66,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12863

theorem m20918_136 : Upper (D 8) (R 8) [96,5,48,66,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12884

theorem m20918_160 : Upper (D 8) (R 8) [96,5,48,66,160] 13 :=
  permutation_upper _ _ _ [96,5,40,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12895

theorem m20918_257 : Upper (D 8) (R 8) [96,5,48,66,257] 13 :=
  permutation_upper _ _ _ [96,5,40,257,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12912

theorem m20918_264 : Upper (D 8) (R 8) [96,5,48,66,264] 13 :=
  permutation_upper _ _ _ [96,5,40,272,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12925

theorem m20918_288 : Upper (D 8) (R 8) [96,5,48,66,288] 13 :=
  permutation_upper _ _ _ [96,5,40,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12931

theorem m20918_384 : Upper (D 8) (R 8) [96,5,48,66,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12942

def r20918 : Route 9 := (fun mask => (mask,id))

def c20918 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20918 : Upper (D 8) (R 8) [96,5,48,66] 13 := by
  apply FastRouting.sound _ _ [96,5,48,66] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r20918 c20918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20918_9
  · exact m20918_33
  · exact m20918_40
  · exact m20918_129
  · exact m20918_136
  · exact m20918_160
  · exact m20918_257
  · exact m20918_264
  · exact m20918_288
  · exact m20918_384

theorem m20919_10 : Upper (D 8) (R 8) [96,5,48,129,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12812

theorem m20919_34 : Upper (D 8) (R 8) [96,5,48,129,34] 13 :=
  permutation_upper _ _ _ [96,5,40,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12825

theorem m20919_40 : Upper (D 8) (R 8) [96,5,48,129,40] 13 :=
  permutation_upper _ _ _ [96,5,40,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12831

theorem m20919_66 : Upper (D 8) (R 8) [96,5,48,129,66] 13 :=
  permutation_upper _ _ _ [96,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12844

theorem m20919_72 : Upper (D 8) (R 8) [96,5,48,129,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12850

theorem m20919_96 : Upper (D 8) (R 8) [96,5,48,129,96] 13 :=
  permutation_upper _ _ _ [96,5,40,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12857

theorem m20919_130 : Upper (D 8) (R 8) [96,5,48,129,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12874

theorem m20919_136 : Upper (D 8) (R 8) [96,5,48,129,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12886

theorem m20919_160 : Upper (D 8) (R 8) [96,5,48,129,160] 13 :=
  permutation_upper _ _ _ [96,5,40,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12896

theorem m20919_192 : Upper (D 8) (R 8) [96,5,48,129,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12904

theorem m20919_258 : Upper (D 8) (R 8) [96,5,48,129,258] 13 :=
  permutation_upper _ _ _ [96,5,40,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12919

theorem m20919_264 : Upper (D 8) (R 8) [96,5,48,129,264] 13 :=
  permutation_upper _ _ _ [96,5,40,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12927

theorem m20919_288 : Upper (D 8) (R 8) [96,5,48,129,288] 13 :=
  permutation_upper _ _ _ [96,5,40,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12932

theorem m20919_320 : Upper (D 8) (R 8) [96,5,48,129,320] 13 :=
  permutation_upper _ _ _ [96,5,40,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12936

theorem m20919_384 : Upper (D 8) (R 8) [96,5,48,129,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12944

def r20919 : Route 9 := (fun mask => (mask,id))

def c20919 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u20919 : Upper (D 8) (R 8) [96,5,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,48,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192,258,264,288,320,384] r20919 c20919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20919_10
  · exact m20919_34
  · exact m20919_40
  · exact m20919_66
  · exact m20919_72
  · exact m20919_96
  · exact m20919_130
  · exact m20919_136
  · exact m20919_160
  · exact m20919_192
  · exact m20919_258
  · exact m20919_264
  · exact m20919_288
  · exact m20919_320
  · exact m20919_384

theorem m20920_9 : Upper (D 8) (R 8) [96,5,48,130,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12802

theorem m20920_33 : Upper (D 8) (R 8) [96,5,48,130,33] 13 :=
  permutation_upper _ _ _ [96,5,40,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12820

theorem m20920_40 : Upper (D 8) (R 8) [96,5,48,130,40] 13 :=
  permutation_upper _ _ _ [96,5,40,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12832

theorem m20920_65 : Upper (D 8) (R 8) [96,5,48,130,65] 13 :=
  permutation_upper _ _ _ [96,5,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12839

theorem m20920_72 : Upper (D 8) (R 8) [96,5,48,130,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12851

theorem m20920_96 : Upper (D 8) (R 8) [96,5,48,130,96] 13 :=
  permutation_upper _ _ _ [96,5,40,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12858

theorem m20920_129 : Upper (D 8) (R 8) [96,5,48,130,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12864

theorem m20920_136 : Upper (D 8) (R 8) [96,5,48,130,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12887

theorem m20920_160 : Upper (D 8) (R 8) [96,5,48,130,160] 13 :=
  permutation_upper _ _ _ [96,5,40,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12897

theorem m20920_192 : Upper (D 8) (R 8) [96,5,48,130,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12905

theorem m20920_257 : Upper (D 8) (R 8) [96,5,48,130,257] 13 :=
  permutation_upper _ _ _ [96,5,40,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12913

theorem m20920_264 : Upper (D 8) (R 8) [96,5,48,130,264] 13 :=
  permutation_upper _ _ _ [96,5,40,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12928

theorem m20920_288 : Upper (D 8) (R 8) [96,5,48,130,288] 13 :=
  permutation_upper _ _ _ [96,5,40,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12933

theorem m20920_320 : Upper (D 8) (R 8) [96,5,48,130,320] 13 :=
  permutation_upper _ _ _ [96,5,40,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12937

theorem m20920_384 : Upper (D 8) (R 8) [96,5,48,130,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12945

def r20920 : Route 9 := (fun mask => (mask,id))

def c20920 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u20920 : Upper (D 8) (R 8) [96,5,48,130] 13 := by
  apply FastRouting.sound _ _ [96,5,48,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r20920 c20920
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20920_9
  · exact m20920_33
  · exact m20920_40
  · exact m20920_65
  · exact m20920_72
  · exact m20920_96
  · exact m20920_129
  · exact m20920_136
  · exact m20920_160
  · exact m20920_192
  · exact m20920_257
  · exact m20920_264
  · exact m20920_288
  · exact m20920_320
  · exact m20920_384

theorem m20921_3 : Upper (D 8) (R 8) [96,5,48,160,3] 13 :=
  permutation_upper _ _ _ [96,5,9,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12512

theorem m20921_9 : Upper (D 8) (R 8) [96,5,48,160,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12803

theorem m20921_10 : Upper (D 8) (R 8) [96,5,48,160,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12813

theorem m20921_65 : Upper (D 8) (R 8) [96,5,48,160,65] 13 :=
  permutation_upper _ _ _ [96,5,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12840

theorem m20921_66 : Upper (D 8) (R 8) [96,5,48,160,66] 13 :=
  permutation_upper _ _ _ [96,5,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12845

theorem m20921_72 : Upper (D 8) (R 8) [96,5,48,160,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12852

theorem m20921_129 : Upper (D 8) (R 8) [96,5,48,160,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12865

theorem m20921_130 : Upper (D 8) (R 8) [96,5,48,160,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12875

theorem m20921_136 : Upper (D 8) (R 8) [96,5,48,160,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12888

theorem m20921_192 : Upper (D 8) (R 8) [96,5,48,160,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12906

theorem m20921_257 : Upper (D 8) (R 8) [96,5,48,160,257] 13 :=
  permutation_upper _ _ _ [96,5,40,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12914

theorem m20921_258 : Upper (D 8) (R 8) [96,5,48,160,258] 13 :=
  permutation_upper _ _ _ [96,5,40,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12920

theorem m20921_264 : Upper (D 8) (R 8) [96,5,48,160,264] 13 :=
  permutation_upper _ _ _ [96,5,40,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12929

theorem m20921_320 : Upper (D 8) (R 8) [96,5,48,160,320] 13 :=
  permutation_upper _ _ _ [96,5,40,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12938

theorem m20921_384 : Upper (D 8) (R 8) [96,5,48,160,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12946

def r20921 : Route 9 := (fun mask => (mask,id))

def c20921 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u20921 : Upper (D 8) (R 8) [96,5,48,160] 13 := by
  apply FastRouting.sound _ _ [96,5,48,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r20921 c20921
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20921_3
  · exact m20921_9
  · exact m20921_10
  · exact m20921_65
  · exact m20921_66
  · exact m20921_72
  · exact m20921_129
  · exact m20921_130
  · exact m20921_136
  · exact m20921_192
  · exact m20921_257
  · exact m20921_258
  · exact m20921_264
  · exact m20921_320
  · exact m20921_384

theorem m20922_3 : Upper (D 8) (R 8) [96,5,48,192,3] 13 :=
  permutation_upper _ _ _ [96,5,9,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12513

theorem m20922_9 : Upper (D 8) (R 8) [96,5,48,192,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12804

theorem m20922_10 : Upper (D 8) (R 8) [96,5,48,192,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12814

theorem m20922_33 : Upper (D 8) (R 8) [96,5,48,192,33] 13 :=
  permutation_upper _ _ _ [96,5,40,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12821

theorem m20922_34 : Upper (D 8) (R 8) [96,5,48,192,34] 13 :=
  permutation_upper _ _ _ [96,5,40,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12826

theorem m20922_40 : Upper (D 8) (R 8) [96,5,48,192,40] 13 :=
  permutation_upper _ _ _ [96,5,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12833

theorem m20922_129 : Upper (D 8) (R 8) [96,5,48,192,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12866

theorem m20922_130 : Upper (D 8) (R 8) [96,5,48,192,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12876

theorem m20922_136 : Upper (D 8) (R 8) [96,5,48,192,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12889

theorem m20922_160 : Upper (D 8) (R 8) [96,5,48,192,160] 13 :=
  permutation_upper _ _ _ [96,5,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12898

theorem m20922_257 : Upper (D 8) (R 8) [96,5,48,192,257] 13 :=
  permutation_upper _ _ _ [96,5,40,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12915

theorem m20922_258 : Upper (D 8) (R 8) [96,5,48,192,258] 13 :=
  permutation_upper _ _ _ [96,5,40,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12921

theorem m20922_264 : Upper (D 8) (R 8) [96,5,48,192,264] 13 :=
  permutation_upper _ _ _ [96,5,40,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12930

theorem m20922_288 : Upper (D 8) (R 8) [96,5,48,192,288] 13 :=
  permutation_upper _ _ _ [96,5,40,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12934

theorem m20922_384 : Upper (D 8) (R 8) [96,5,48,192,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12947

def r20922 : Route 9 := (fun mask => (mask,id))

def c20922 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20922 : Upper (D 8) (R 8) [96,5,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,48,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,257,258,264,288,384] r20922 c20922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20922_3
  · exact m20922_9
  · exact m20922_10
  · exact m20922_33
  · exact m20922_34
  · exact m20922_40
  · exact m20922_129
  · exact m20922_130
  · exact m20922_136
  · exact m20922_160
  · exact m20922_257
  · exact m20922_258
  · exact m20922_264
  · exact m20922_288
  · exact m20922_384

theorem m20923_10 : Upper (D 8) (R 8) [96,5,48,257,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12815

theorem m20923_34 : Upper (D 8) (R 8) [96,5,48,257,34] 13 :=
  permutation_upper _ _ _ [96,5,40,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12827

theorem m20923_40 : Upper (D 8) (R 8) [96,5,48,257,40] 13 :=
  permutation_upper _ _ _ [96,5,40,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12834

theorem m20923_66 : Upper (D 8) (R 8) [96,5,48,257,66] 13 :=
  permutation_upper _ _ _ [96,5,40,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12846

theorem m20923_72 : Upper (D 8) (R 8) [96,5,48,257,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12853

theorem m20923_96 : Upper (D 8) (R 8) [96,5,48,257,96] 13 :=
  permutation_upper _ _ _ [96,5,40,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12859

theorem m20923_130 : Upper (D 8) (R 8) [96,5,48,257,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12877

theorem m20923_136 : Upper (D 8) (R 8) [96,5,48,257,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12890

theorem m20923_160 : Upper (D 8) (R 8) [96,5,48,257,160] 13 :=
  permutation_upper _ _ _ [96,5,40,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12899

theorem m20923_192 : Upper (D 8) (R 8) [96,5,48,257,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12907

def r20923 : Route 9 := (fun mask => (mask,id))

def c20923 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20923 : Upper (D 8) (R 8) [96,5,48,257] 13 := by
  apply FastRouting.sound _ _ [96,5,48,257] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r20923 c20923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20923_10
  · exact m20923_34
  · exact m20923_40
  · exact m20923_66
  · exact m20923_72
  · exact m20923_96
  · exact m20923_130
  · exact m20923_136
  · exact m20923_160
  · exact m20923_192

theorem m20924_9 : Upper (D 8) (R 8) [96,5,48,258,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12805

theorem m20924_33 : Upper (D 8) (R 8) [96,5,48,258,33] 13 :=
  permutation_upper _ _ _ [96,5,40,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12822

theorem m20924_40 : Upper (D 8) (R 8) [96,5,48,258,40] 13 :=
  permutation_upper _ _ _ [96,5,40,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12835

theorem m20924_65 : Upper (D 8) (R 8) [96,5,48,258,65] 13 :=
  permutation_upper _ _ _ [96,5,40,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12841

theorem m20924_72 : Upper (D 8) (R 8) [96,5,48,258,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12854

theorem m20924_96 : Upper (D 8) (R 8) [96,5,48,258,96] 13 :=
  permutation_upper _ _ _ [96,5,40,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12860

theorem m20924_129 : Upper (D 8) (R 8) [96,5,48,258,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12867

theorem m20924_136 : Upper (D 8) (R 8) [96,5,48,258,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12891

theorem m20924_160 : Upper (D 8) (R 8) [96,5,48,258,160] 13 :=
  permutation_upper _ _ _ [96,5,40,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12900

theorem m20924_192 : Upper (D 8) (R 8) [96,5,48,258,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12908

def r20924 : Route 9 := (fun mask => (mask,id))

def c20924 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20924 : Upper (D 8) (R 8) [96,5,48,258] 13 := by
  apply FastRouting.sound _ _ [96,5,48,258] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20924 c20924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20924_9
  · exact m20924_33
  · exact m20924_40
  · exact m20924_65
  · exact m20924_72
  · exact m20924_96
  · exact m20924_129
  · exact m20924_136
  · exact m20924_160
  · exact m20924_192

theorem m20925_3 : Upper (D 8) (R 8) [96,5,48,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,34,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12514

theorem m20925_9 : Upper (D 8) (R 8) [96,5,48,288,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12806

theorem m20925_10 : Upper (D 8) (R 8) [96,5,48,288,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12816

theorem m20925_65 : Upper (D 8) (R 8) [96,5,48,288,65] 13 :=
  permutation_upper _ _ _ [96,5,40,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12842

theorem m20925_66 : Upper (D 8) (R 8) [96,5,48,288,66] 13 :=
  permutation_upper _ _ _ [96,5,40,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12847

theorem m20925_72 : Upper (D 8) (R 8) [96,5,48,288,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12855

theorem m20925_129 : Upper (D 8) (R 8) [96,5,48,288,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12868

theorem m20925_130 : Upper (D 8) (R 8) [96,5,48,288,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12878

theorem m20925_136 : Upper (D 8) (R 8) [96,5,48,288,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12892

theorem m20925_192 : Upper (D 8) (R 8) [96,5,48,288,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12909

def r20925 : Route 9 := (fun mask => (mask,id))

def c20925 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20925 : Upper (D 8) (R 8) [96,5,48,288] 13 := by
  apply FastRouting.sound _ _ [96,5,48,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r20925 c20925
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20925_3
  · exact m20925_9
  · exact m20925_10
  · exact m20925_65
  · exact m20925_66
  · exact m20925_72
  · exact m20925_129
  · exact m20925_130
  · exact m20925_136
  · exact m20925_192

theorem m20926_3 : Upper (D 8) (R 8) [96,5,48,320,3] 13 :=
  permutation_upper _ _ _ [96,5,9,34,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12515

theorem m20926_9 : Upper (D 8) (R 8) [96,5,48,320,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12807

theorem m20926_10 : Upper (D 8) (R 8) [96,5,48,320,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12817

theorem m20926_33 : Upper (D 8) (R 8) [96,5,48,320,33] 13 :=
  permutation_upper _ _ _ [96,5,40,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12823

theorem m20926_34 : Upper (D 8) (R 8) [96,5,48,320,34] 13 :=
  permutation_upper _ _ _ [96,5,40,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12828

theorem m20926_40 : Upper (D 8) (R 8) [96,5,48,320,40] 13 :=
  permutation_upper _ _ _ [96,5,40,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12836

theorem m20926_129 : Upper (D 8) (R 8) [96,5,48,320,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12869

theorem m20926_130 : Upper (D 8) (R 8) [96,5,48,320,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12879

theorem m20926_136 : Upper (D 8) (R 8) [96,5,48,320,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12893

theorem m20926_160 : Upper (D 8) (R 8) [96,5,48,320,160] 13 :=
  permutation_upper _ _ _ [96,5,40,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12901

def r20926 : Route 9 := (fun mask => (mask,id))

def c20926 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20926 : Upper (D 8) (R 8) [96,5,48,320] 13 := by
  apply FastRouting.sound _ _ [96,5,48,320] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r20926 c20926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20926_3
  · exact m20926_9
  · exact m20926_10
  · exact m20926_33
  · exact m20926_34
  · exact m20926_40
  · exact m20926_129
  · exact m20926_130
  · exact m20926_136
  · exact m20926_160

theorem m20927_3 : Upper (D 8) (R 8) [96,5,48,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,34,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12516

theorem m20927_9 : Upper (D 8) (R 8) [96,5,48,384,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12808

theorem m20927_10 : Upper (D 8) (R 8) [96,5,48,384,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12818

theorem m20927_33 : Upper (D 8) (R 8) [96,5,48,384,33] 13 :=
  permutation_upper _ _ _ [96,5,40,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12824

theorem m20927_34 : Upper (D 8) (R 8) [96,5,48,384,34] 13 :=
  permutation_upper _ _ _ [96,5,40,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12829

theorem m20927_40 : Upper (D 8) (R 8) [96,5,48,384,40] 13 :=
  permutation_upper _ _ _ [96,5,40,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12837

theorem m20927_65 : Upper (D 8) (R 8) [96,5,48,384,65] 13 :=
  permutation_upper _ _ _ [96,5,40,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12843

theorem m20927_66 : Upper (D 8) (R 8) [96,5,48,384,66] 13 :=
  permutation_upper _ _ _ [96,5,40,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12848

theorem m20927_72 : Upper (D 8) (R 8) [96,5,48,384,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12856

theorem m20927_96 : Upper (D 8) (R 8) [96,5,48,384,96] 13 :=
  permutation_upper _ _ _ [96,5,40,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12861

theorem m20927_129 : Upper (D 8) (R 8) [96,5,48,384,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12870

theorem m20927_130 : Upper (D 8) (R 8) [96,5,48,384,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12880

theorem m20927_136 : Upper (D 8) (R 8) [96,5,48,384,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12894

theorem m20927_160 : Upper (D 8) (R 8) [96,5,48,384,160] 13 :=
  permutation_upper _ _ _ [96,5,40,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12902

theorem m20927_192 : Upper (D 8) (R 8) [96,5,48,384,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12910

def r20927 : Route 9 := (fun mask => (mask,id))

def c20927 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20927 : Upper (D 8) (R 8) [96,5,48,384] 13 := by
  apply FastRouting.sound _ _ [96,5,48,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r20927 c20927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20927_3
  · exact m20927_9
  · exact m20927_10
  · exact m20927_33
  · exact m20927_34
  · exact m20927_40
  · exact m20927_65
  · exact m20927_66
  · exact m20927_72
  · exact m20927_96
  · exact m20927_129
  · exact m20927_130
  · exact m20927_136
  · exact m20927_160
  · exact m20927_192

def b20928 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 26 440 424 488 424 424), lower := (rows 97 7 69 26 16 32 64 128 256), losses := [] }

theorem u20928 : Upper (D 8) (R 8) [96,5,65,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20929 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 69 42 440 440 504 440 440), lower := (rows 97 7 69 42 16 32 64 128 256), losses := [] }

theorem u20929 : Upper (D 8) (R 8) [96,5,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20930 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 138 440 440 504 440 440), lower := (rows 97 7 69 138 16 32 64 128 256), losses := [] }

theorem u20930 : Upper (D 8) (R 8) [96,5,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20931 : PairBound 9 := { available := 442, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 168 442 442 506 442 442), lower := (rows 97 7 69 168 16 32 64 128 256), losses := [] }

theorem u20931 : Upper (D 8) (R 8) [96,5,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20932 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 266 184 184 248 184 440), lower := (rows 97 7 69 266 16 32 64 128 256), losses := [] }

theorem u20932 : Upper (D 8) (R 8) [96,5,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20933 : PairBound 9 := { available := 186, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 296 186 186 250 186 442), lower := (rows 97 7 69 296 16 32 64 128 256), losses := [] }

theorem u20933 : Upper (D 8) (R 8) [96,5,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20934 : PairBound 9 := { available := 186, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 392 186 186 250 186 442), lower := (rows 97 7 69 392 16 32 64 128 256), losses := [] }

theorem u20934 : Upper (D 8) (R 8) [96,5,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20935 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 137 440 440 504 440 440), lower := (rows 97 7 70 137 16 32 64 128 256), losses := [] }

theorem u20935 : Upper (D 8) (R 8) [96,5,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20936 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 168 441 441 505 441 441), lower := (rows 97 7 70 168 16 32 64 128 256), losses := [] }

theorem u20936 : Upper (D 8) (R 8) [96,5,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20937 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 265 184 184 248 184 440), lower := (rows 97 7 70 265 16 32 64 128 256), losses := [] }

theorem u20937 : Upper (D 8) (R 8) [96,5,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20938 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 296 185 185 249 185 441), lower := (rows 97 7 70 296 16 32 64 128 256), losses := [] }

theorem u20938 : Upper (D 8) (R 8) [96,5,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20939 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 70 392 185 185 249 185 441), lower := (rows 97 7 70 392 16 32 64 128 256), losses := [] }

theorem u20939 : Upper (D 8) (R 8) [96,5,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u20939
end Delivery.IrregularNine14.P08
