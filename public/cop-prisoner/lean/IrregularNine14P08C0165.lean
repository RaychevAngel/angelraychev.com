import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0044

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9900 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 152 84 161 225 161 417), lower := (rows 35 322 44 152 84 32 64 128 256), losses := [] }

theorem u9900 : Upper (D 8) (R 8) [34,320,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9901 : Route 9 := (fun mask => (mask,id))

def c9901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9901 : Upper (D 8) (R 8) [34,320,40,144,96] 13 := by
  apply FastRouting.sound _ _ [34,320,40,144,96] 13 (by decide) (choices 1) [1,4,128] r9901 c9901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2658
  · exact u2659
  · exact u2660

def b9902 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 152 145 101 101 229 357), lower := (rows 35 322 44 152 145 32 64 128 256), losses := [] }

theorem u9902 : Upper (D 8) (R 8) [34,320,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9903 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 152 148 97 97 225 353), lower := (rows 35 322 44 152 148 32 64 128 256), losses := [] }

theorem u9903 : Upper (D 8) (R 8) [34,320,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9904 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 152 176 101 69 197 325), lower := (rows 35 322 44 152 176 32 64 128 256), losses := [] }

theorem u9904 : Upper (D 8) (R 8) [34,320,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9905 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 152 208 37 101 165 293), lower := (rows 35 322 44 152 208 32 64 128 256), losses := [] }

theorem u9905 : Upper (D 8) (R 8) [34,320,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9906 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 168 84 177 209 145 401), lower := (rows 35 322 44 168 84 32 64 128 256), losses := [] }

theorem u9906 : Upper (D 8) (R 8) [34,320,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9907 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 168 145 117 85 213 341), lower := (rows 35 322 44 168 145 32 64 128 256), losses := [] }

theorem u9907 : Upper (D 8) (R 8) [34,320,40,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9908 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 168 148 113 81 209 337), lower := (rows 35 322 44 168 148 32 64 128 256), losses := [] }

theorem u9908 : Upper (D 8) (R 8) [34,320,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9909 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 168 208 53 85 149 277), lower := (rows 35 322 44 168 208 32 64 128 256), losses := [] }

theorem u9909 : Upper (D 8) (R 8) [34,320,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9910 : Route 9 := (fun mask => (mask,id))

def c9910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9910 : Upper (D 8) (R 8) [34,320,40,192,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,129] 13 (by decide) (choices 1) [1,4,16] r9910 c9910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2661
  · exact u2662
  · exact u2663

def b9911 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 200 148 49 113 177 305), lower := (rows 35 322 44 200 148 32 64 128 256), losses := [] }

theorem u9911 : Upper (D 8) (R 8) [34,320,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9912 : Route 9 := (fun mask => (mask,id))

def c9912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9912 : Upper (D 8) (R 8) [34,320,40,192,160] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,160] 13 (by decide) (choices 1) [1,4,16] r9912 c9912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2664
  · exact u2665
  · exact u2666

def b9913 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 137 148 56 120 184 312), lower := (rows 35 322 69 137 148 32 64 128 256), losses := [] }

theorem u9913 : Upper (D 8) (R 8) [34,320,65,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9914 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 137 176 60 124 188 316), lower := (rows 35 322 69 137 176 32 64 128 256), losses := [] }

theorem u9914 : Upper (D 8) (R 8) [34,320,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9915 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 140 176 57 121 185 313), lower := (rows 35 322 69 140 176 32 64 128 256), losses := [] }

theorem u9915 : Upper (D 8) (R 8) [34,320,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9916 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 322 76 137 145 52 116 180 308), lower := (rows 35 322 76 137 145 32 64 128 256), losses := [] }

theorem u9916 : Upper (D 8) (R 8) [34,320,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9917 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 137 148 49 113 177 305), lower := (rows 35 322 76 137 148 32 64 128 256), losses := [] }

theorem u9917 : Upper (D 8) (R 8) [34,320,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9918 : Route 9 := (fun mask => (mask,id))

def c9918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9918 : Upper (D 8) (R 8) [34,320,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129,160] 13 (by decide) (choices 1) [1,4,16] r9918 c9918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2667
  · exact u2668
  · exact u2669

def b9919 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 140 145 49 113 177 305), lower := (rows 35 322 76 140 145 32 64 128 256), losses := [] }

theorem u9919 : Upper (D 8) (R 8) [34,320,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9920 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 140 176 49 113 177 305), lower := (rows 35 322 76 140 176 32 64 128 256), losses := [] }

theorem u9920 : Upper (D 8) (R 8) [34,320,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9921 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 152 145 37 101 165 293), lower := (rows 35 322 76 152 145 32 64 128 256), losses := [] }

theorem u9921 : Upper (D 8) (R 8) [34,320,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9922 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 152 148 33 97 161 289), lower := (rows 35 322 76 152 148 32 64 128 256), losses := [] }

theorem u9922 : Upper (D 8) (R 8) [34,320,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9923 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 152 176 37 101 165 293), lower := (rows 35 322 76 152 176 32 64 128 256), losses := [] }

theorem u9923 : Upper (D 8) (R 8) [34,320,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9924 : Route 9 := (fun mask => (mask,id))

def c9924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9924 : Upper (D 8) (R 8) [34,320,72,160,129] 13 := by
  apply FastRouting.sound _ _ [34,320,72,160,129] 13 (by decide) (choices 1) [1,4,16] r9924 c9924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2670
  · exact u2671
  · exact u2672

def b9925 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 168 148 49 113 177 305), lower := (rows 35 322 76 168 148 32 64 128 256), losses := [] }

theorem u9925 : Upper (D 8) (R 8) [34,320,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9926 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 322 76 168 176 53 85 149 277), lower := (rows 35 322 76 168 176 32 64 128 256), losses := [] }

theorem u9926 : Upper (D 8) (R 8) [34,320,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9927 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 322 100 137 145 60 124 188 316), lower := (rows 35 322 100 137 145 32 64 128 256), losses := [] }

theorem u9927 : Upper (D 8) (R 8) [34,320,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9928 : Route 9 := (fun mask => (mask,id))

def c9928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9928 : Upper (D 8) (R 8) [34,320,96,129,132] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129,132] 13 (by decide) (choices 1) [1,8,16] r9928 c9928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2673
  · exact u2674
  · exact u2675

def b9929 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 322 100 137 152 53 117 181 309), lower := (rows 35 322 100 137 152 32 64 128 256), losses := [] }

theorem u9929 : Upper (D 8) (R 8) [34,320,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9930 : Route 9 := (fun mask => (mask,id))

def c9930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9930 : Upper (D 8) (R 8) [34,320,96,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129,160] 13 (by decide) (choices 1) [1,4,8,16] r9930 c9930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2676
  · exact u2677
  · exact u2678
  · exact u2679

def b9931 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 322 100 140 152 49 113 177 305), lower := (rows 35 322 100 140 152 32 64 128 256), losses := [] }

theorem u9931 : Upper (D 8) (R 8) [34,320,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9932 : Route 9 := (fun mask => (mask,id))

def c9932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9932 : Upper (D 8) (R 8) [34,320,96,132,160] 13 := by
  apply FastRouting.sound _ _ [34,320,96,132,160] 13 (by decide) (choices 1) [1,8,16] r9932 c9932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2680
  · exact u2681
  · exact u2682

def b9933 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 322 100 152 152 37 101 165 293), lower := (rows 35 322 100 152 152 32 64 128 256), losses := [] }

theorem u9933 : Upper (D 8) (R 8) [34,320,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9934 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 100 152 176 45 77 141 269), lower := (rows 35 322 100 152 176 32 64 128 256), losses := [] }

theorem u9934 : Upper (D 8) (R 8) [34,320,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9935 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 41 176 480 480 480 480), lower := (rows 67 7 28 41 176 32 64 128 256), losses := [] }

theorem u9935 : Upper (D 8) (R 8) [66,5,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9936 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 41 304 224 224 224 480), lower := (rows 67 7 28 41 304 32 64 128 256), losses := [] }

theorem u9936 : Upper (D 8) (R 8) [66,5,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9937 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 41 400 224 224 224 480), lower := (rows 67 7 28 41 400 32 64 128 256), losses := [] }

theorem u9937 : Upper (D 8) (R 8) [66,5,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9938 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 28 73 176 416 480 416 416), lower := (rows 67 7 28 73 176 32 64 128 256), losses := [] }

theorem u9938 : Upper (D 8) (R 8) [66,5,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9939 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 28 73 304 160 224 160 416), lower := (rows 67 7 28 73 304 32 64 128 256), losses := [] }

theorem u9939 : Upper (D 8) (R 8) [66,5,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9940 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 28 73 400 160 224 160 416), lower := (rows 67 7 28 73 400 32 64 128 256), losses := [] }

theorem u9940 : Upper (D 8) (R 8) [66,5,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9941 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 28 104 176 417 481 417 417), lower := (rows 67 7 28 104 176 32 64 128 256), losses := [] }

theorem u9941 : Upper (D 8) (R 8) [66,5,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9942 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 28 104 304 161 225 161 417), lower := (rows 67 7 28 104 304 32 64 128 256), losses := [] }

theorem u9942 : Upper (D 8) (R 8) [66,5,24,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9943 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 28 104 400 161 225 161 417), lower := (rows 67 7 28 104 400 32 64 128 256), losses := [] }

theorem u9943 : Upper (D 8) (R 8) [66,5,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9944 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 28 137 176 352 352 480 352), lower := (rows 67 7 28 137 176 32 64 128 256), losses := [] }

theorem u9944 : Upper (D 8) (R 8) [66,5,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9945 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 137 304 224 224 224 480), lower := (rows 67 7 28 137 304 32 64 128 256), losses := [] }

theorem u9945 : Upper (D 8) (R 8) [66,5,24,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9946 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 28 137 400 96 96 224 352), lower := (rows 67 7 28 137 400 32 64 128 256), losses := [] }

theorem u9946 : Upper (D 8) (R 8) [66,5,24,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9947 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 168 176 353 353 481 353), lower := (rows 67 7 28 168 176 32 64 128 256), losses := [] }

theorem u9947 : Upper (D 8) (R 8) [66,5,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9948 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 28 168 208 289 353 417 289), lower := (rows 67 7 28 168 208 32 64 128 256), losses := [] }

theorem u9948 : Upper (D 8) (R 8) [66,5,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9949 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 168 273 224 224 224 480), lower := (rows 67 7 28 168 273 32 64 128 256), losses := [] }

theorem u9949 : Upper (D 8) (R 8) [66,5,24,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9950 : Route 9 := (fun mask => (mask,id))

def c9950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9950 : Upper (D 8) (R 8) [66,5,24,160,288] 13 := by
  apply FastRouting.sound _ _ [66,5,24,160,288] 13 (by decide) (choices 1) [1,64,128] r9950 c9950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2683
  · exact u2684
  · exact u2685

def b9951 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 7 28 168 336 161 225 161 417), lower := (rows 67 7 28 168 336 32 64 128 256), losses := [] }

theorem u9951 : Upper (D 8) (R 8) [66,5,24,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9952 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 28 168 400 97 97 225 353), lower := (rows 67 7 28 168 400 32 64 128 256), losses := [] }

theorem u9952 : Upper (D 8) (R 8) [66,5,24,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9953 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 28 200 304 161 225 161 417), lower := (rows 67 7 28 200 304 32 64 128 256), losses := [] }

theorem u9953 : Upper (D 8) (R 8) [66,5,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9954 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 28 200 400 33 97 161 289), lower := (rows 67 7 28 200 400 32 64 128 256), losses := [] }

theorem u9954 : Upper (D 8) (R 8) [66,5,24,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9955 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 152 49 480 480 480 480), lower := (rows 67 7 44 152 49 32 64 128 256), losses := [] }

theorem u9955 : Upper (D 8) (R 8) [66,5,40,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9956 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 44 152 81 416 480 416 416), lower := (rows 67 7 44 152 81 32 64 128 256), losses := [] }

theorem u9956 : Upper (D 8) (R 8) [66,5,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9957 : Route 9 := (fun mask => (mask,id))

def c9957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u9957 : Upper (D 8) (R 8) [66,5,40,144,96] 13 := by
  apply FastRouting.sound _ _ [66,5,40,144,96] 13 (by decide) (choices 1) [1,128,256] r9957 c9957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2686
  · exact u2687
  · exact u2688

def b9958 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 152 145 352 352 480 352), lower := (rows 67 7 44 152 145 32 64 128 256), losses := [] }

theorem u9958 : Upper (D 8) (R 8) [66,5,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9959 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 152 176 353 353 481 353), lower := (rows 67 7 44 152 176 32 64 128 256), losses := [] }

theorem u9959 : Upper (D 8) (R 8) [66,5,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9959
end Delivery.IrregularNine14.P08
