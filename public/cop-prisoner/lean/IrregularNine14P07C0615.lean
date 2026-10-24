import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0380
import IrregularNine14P07C0381

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36900 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 22 137 49 482 450 450 450), lower := (rows 37 74 22 137 49 32 64 128 256), losses := [] }

theorem u36900 : Upper (D 7) (R 7) [36,72,18,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36901 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 22 137 50 481 449 449 449), lower := (rows 37 74 22 137 50 32 64 128 256), losses := [] }

theorem u36901 : Upper (D 7) (R 7) [36,72,18,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36902 : Route 9 := (fun mask => (mask,id))

def c36902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36902 : Upper (D 7) (R 7) [36,72,18,129,65] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,65] 13 (by decide) (choices 1) [2,128,256] r36902 c36902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22816
  · exact u22817
  · exact u22818

def b36903 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 37 74 22 137 82 417 481 417 417), lower := (rows 37 74 22 137 82 32 64 128 256), losses := [] }

theorem u36903 : Upper (D 7) (R 7) [36,72,18,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36904 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(1,5),(3,5),(3,6)], upper := (rows 37 74 22 137 112 419 451 387 387), lower := (rows 37 74 22 137 112 32 64 128 256), losses := [] }

theorem u36904 : Upper (D 7) (R 7) [36,72,18,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36905 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 74 22 137 145 354 354 482 354), lower := (rows 37 74 22 137 145 32 64 128 256), losses := [] }

theorem u36905 : Upper (D 7) (R 7) [36,72,18,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36906 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 4, targets := 97 },{ cop := 2, region := 353, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,6)], upper := (rows 37 74 22 137 146 353 353 481 353), lower := (rows 37 74 22 137 146 32 64 128 256), losses := [] }

theorem u36906 : Upper (D 7) (R 7) [36,72,18,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36907 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 353, targets := 128 },{ cop := 3, region := 322, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(3,5)], upper := (rows 37 74 22 137 176 355 323 451 323), lower := (rows 37 74 22 137 176 32 64 128 256), losses := [] }

theorem u36907 : Upper (D 7) (R 7) [36,72,18,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36908 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 2, region := 289, targets := 128 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,6)], upper := (rows 37 74 22 137 208 291 355 419 291), lower := (rows 37 74 22 137 208 32 64 128 256), losses := [] }

theorem u36908 : Upper (D 7) (R 7) [36,72,18,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36909 : Route 9 := (fun mask => (mask,id))

def c36909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36909 : Upper (D 7) (R 7) [36,72,18,129,257] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,257] 13 (by decide) (choices 1) [2,64,128] r36909 c36909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22819
  · exact u22820
  · exact u22821

def b36910 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 74 22 137 274 225 225 225 481), lower := (rows 37 74 22 137 274 32 64 128 256), losses := [] }

theorem u36910 : Upper (D 7) (R 7) [36,72,18,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36911 : Route 9 := (fun mask => (mask,id))

def c36911 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36911 : Upper (D 7) (R 7) [36,72,18,129,288] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,288] 13 (by decide) (choices 1) [1,2,64,128] r36911 c36911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22822
  · exact u22823
  · exact u22824
  · exact u22825

def r36912 : Route 9 := (fun mask => (mask,id))

def c36912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36912 : Upper (D 7) (R 7) [36,72,18,129,320] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,320] 13 (by decide) (choices 1) [1,2,128] r36912 c36912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22826
  · exact u22827
  · exact u22828

def r36913 : Route 9 := (fun mask => (mask,id))

def c36913 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36913 : Upper (D 7) (R 7) [36,72,18,129,384] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,384] 13 (by decide) (choices 1) [1,2,64] r36913 c36913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22829
  · exact u22830
  · exact u22831

def b36914 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 74 22 138 49 481 449 449 449), lower := (rows 37 74 22 138 49 32 64 128 256), losses := [] }

theorem u36914 : Upper (D 7) (R 7) [36,72,18,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36915 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 74 22 138 81 417 481 417 417), lower := (rows 37 74 22 138 81 32 64 128 256), losses := [] }

theorem u36915 : Upper (D 7) (R 7) [36,72,18,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36916 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 37 74 22 138 112 417 449 385 385), lower := (rows 37 74 22 138 112 32 64 128 256), losses := [] }

theorem u36916 : Upper (D 7) (R 7) [36,72,18,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36917 : Route 9 := (fun mask => (mask,id))

def c36917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36917 : Upper (D 7) (R 7) [36,72,18,130,129] 13 := by
  apply FastRouting.sound _ _ [36,72,18,130,129] 13 (by decide) (choices 1) [1,64,256] r36917 c36917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22832
  · exact u22833
  · exact u22834

def b36918 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 37 74 22 138 176 353 321 449 321), lower := (rows 37 74 22 138 176 32 64 128 256), losses := [] }

theorem u36918 : Upper (D 7) (R 7) [36,72,18,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36919 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 14, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 74 22 138 208 289 353 417 289), lower := (rows 37 74 22 138 208 32 64 128 256), losses := [] }

theorem u36919 : Upper (D 7) (R 7) [36,72,18,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36920 : Route 9 := (fun mask => (mask,id))

def c36920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36920 : Upper (D 7) (R 7) [36,72,18,130,257] 13 := by
  apply FastRouting.sound _ _ [36,72,18,130,257] 13 (by decide) (choices 1) [1,64,128] r36920 c36920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22835
  · exact u22836
  · exact u22837

def b36921 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 37 74 22 138 304 225 193 193 449), lower := (rows 37 74 22 138 304 32 64 128 256), losses := [] }

theorem u36921 : Upper (D 7) (R 7) [36,72,18,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36922 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 74 22 138 336 161 225 161 417), lower := (rows 37 74 22 138 336 32 64 128 256), losses := [] }

theorem u36922 : Upper (D 7) (R 7) [36,72,18,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36923 : Route 9 := (fun mask => (mask,id))

def c36923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36923 : Upper (D 7) (R 7) [36,72,18,130,384] 13 := by
  apply FastRouting.sound _ _ [36,72,18,130,384] 13 (by decide) (choices 1) [1,64] r36923 c36923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22838
  · exact u22839

def b36924 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 193 },{ cop := 2, region := 481, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 37 74 22 168 19 481 449 449 449), lower := (rows 37 74 22 168 19 32 64 128 256), losses := [] }

theorem u36924 : Upper (D 7) (R 7) [36,72,18,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36925 : Route 9 := (fun mask => (mask,id))

def c36925 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36925 : Upper (D 7) (R 7) [36,72,18,160,65] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,65] 13 (by decide) (choices 1) [1,2,128,256] r36925 c36925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22840
  · exact u22841
  · exact u22842
  · exact u22843

def b36926 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 37 74 22 168 82 417 449 385 385), lower := (rows 37 74 22 168 82 32 64 128 256), losses := [] }

theorem u36926 : Upper (D 7) (R 7) [36,72,18,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36927 : Route 9 := (fun mask => (mask,id))

def c36927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36927 : Upper (D 7) (R 7) [36,72,18,160,129] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,129] 13 (by decide) (choices 1) [1,2,64,256] r36927 c36927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22844
  · exact u22845
  · exact u22846
  · exact u22847

def b36928 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 4, targets := 97 },{ cop := 2, region := 353, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,6)], upper := (rows 37 74 22 168 146 353 321 449 321), lower := (rows 37 74 22 168 146 32 64 128 256), losses := [] }

theorem u36928 : Upper (D 7) (R 7) [36,72,18,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36929 : Route 9 := (fun mask => (mask,id))

def c36929 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36929 : Upper (D 7) (R 7) [36,72,18,160,192] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,192] 13 (by decide) (choices 1) [1,2,256] r36929 c36929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22848
  · exact u22849
  · exact u22850

def r36930 : Route 9 := (fun mask => (mask,id))

def c36930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36930 : Upper (D 7) (R 7) [36,72,18,160,257] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,257] 13 (by decide) (choices 1) [1,2,64,128] r36930 c36930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22851
  · exact u22852
  · exact u22853
  · exact u22854

def b36931 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 74 22 168 274 225 193 193 449), lower := (rows 37 74 22 168 274 32 64 128 256), losses := [] }

theorem u36931 : Upper (D 7) (R 7) [36,72,18,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36932 : Route 9 := (fun mask => (mask,id))

def c36932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36932 : Upper (D 7) (R 7) [36,72,18,160,320] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,320] 13 (by decide) (choices 1) [1,2,128] r36932 c36932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22855
  · exact u22856
  · exact u22857

def r36933 : Route 9 := (fun mask => (mask,id))

def c36933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36933 : Upper (D 7) (R 7) [36,72,18,160,384] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,384] 13 (by decide) (choices 1) [1,2,64] r36933 c36933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22858
  · exact u22859
  · exact u22860

def b36934 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 22 265 19 224 224 224 480), lower := (rows 37 74 22 265 19 32 64 128 256), losses := [] }

theorem u36934 : Upper (D 7) (R 7) [36,72,18,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36935 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 22 265 49 226 194 194 450), lower := (rows 37 74 22 265 49 32 64 128 256), losses := [] }

theorem u36935 : Upper (D 7) (R 7) [36,72,18,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36936 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 22 265 50 225 193 193 449), lower := (rows 37 74 22 265 50 32 64 128 256), losses := [] }

theorem u36936 : Upper (D 7) (R 7) [36,72,18,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36937 : Route 9 := (fun mask => (mask,id))

def c36937 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36937 : Upper (D 7) (R 7) [36,72,18,257,65] 13 := by
  apply FastRouting.sound _ _ [36,72,18,257,65] 13 (by decide) (choices 1) [2,128] r36937 c36937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22861
  · exact u22862

def b36938 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 37 74 22 265 82 161 225 161 417), lower := (rows 37 74 22 265 82 32 64 128 256), losses := [] }

theorem u36938 : Upper (D 7) (R 7) [36,72,18,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36939 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(1,5),(3,5),(3,6)], upper := (rows 37 74 22 265 112 163 195 131 387), lower := (rows 37 74 22 265 112 32 64 128 256), losses := [] }

theorem u36939 : Upper (D 7) (R 7) [36,72,18,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36940 : Route 9 := (fun mask => (mask,id))

def c36940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36940 : Upper (D 7) (R 7) [36,72,18,257,129] 13 := by
  apply FastRouting.sound _ _ [36,72,18,257,129] 13 (by decide) (choices 1) [2,64,128] r36940 c36940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22863
  · exact u22864
  · exact u22865

def b36941 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 74 22 265 146 225 225 225 481), lower := (rows 37 74 22 265 146 32 64 128 256), losses := [] }

theorem u36941 : Upper (D 7) (R 7) [36,72,18,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36942 : Route 9 := (fun mask => (mask,id))

def c36942 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36942 : Upper (D 7) (R 7) [36,72,18,257,160] 13 := by
  apply FastRouting.sound _ _ [36,72,18,257,160] 13 (by decide) (choices 1) [1,2,64,128] r36942 c36942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22866
  · exact u22867
  · exact u22868
  · exact u22869

def r36943 : Route 9 := (fun mask => (mask,id))

def c36943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36943 : Upper (D 7) (R 7) [36,72,18,257,192] 13 := by
  apply FastRouting.sound _ _ [36,72,18,257,192] 13 (by decide) (choices 1) [1,2,128] r36943 c36943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22870
  · exact u22871
  · exact u22872

def b36944 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 74 22 266 49 225 193 193 449), lower := (rows 37 74 22 266 49 32 64 128 256), losses := [] }

theorem u36944 : Upper (D 7) (R 7) [36,72,18,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36945 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 74 22 266 81 161 225 161 417), lower := (rows 37 74 22 266 81 32 64 128 256), losses := [] }

theorem u36945 : Upper (D 7) (R 7) [36,72,18,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36946 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 37 74 22 266 112 161 193 129 385), lower := (rows 37 74 22 266 112 32 64 128 256), losses := [] }

theorem u36946 : Upper (D 7) (R 7) [36,72,18,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36947 : Route 9 := (fun mask => (mask,id))

def c36947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36947 : Upper (D 7) (R 7) [36,72,18,258,129] 13 := by
  apply FastRouting.sound _ _ [36,72,18,258,129] 13 (by decide) (choices 1) [1,64,128] r36947 c36947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22873
  · exact u22874
  · exact u22875

def b36948 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 37 74 22 266 176 225 193 193 449), lower := (rows 37 74 22 266 176 32 64 128 256), losses := [] }

theorem u36948 : Upper (D 7) (R 7) [36,72,18,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36949 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 74 22 266 208 161 225 161 417), lower := (rows 37 74 22 266 208 32 64 128 256), losses := [] }

theorem u36949 : Upper (D 7) (R 7) [36,72,18,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36950 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 193 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 37 74 22 296 19 225 193 193 449), lower := (rows 37 74 22 296 19 32 64 128 256), losses := [] }

theorem u36950 : Upper (D 7) (R 7) [36,72,18,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36951 : Route 9 := (fun mask => (mask,id))

def c36951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36951 : Upper (D 7) (R 7) [36,72,18,288,65] 13 := by
  apply FastRouting.sound _ _ [36,72,18,288,65] 13 (by decide) (choices 1) [1,2,128] r36951 c36951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22876
  · exact u22877
  · exact u22878

def b36952 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 37 74 22 296 82 161 193 129 385), lower := (rows 37 74 22 296 82 32 64 128 256), losses := [] }

theorem u36952 : Upper (D 7) (R 7) [36,72,18,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36953 : Route 9 := (fun mask => (mask,id))

def c36953 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36953 : Upper (D 7) (R 7) [36,72,18,288,129] 13 := by
  apply FastRouting.sound _ _ [36,72,18,288,129] 13 (by decide) (choices 1) [1,2,64,128] r36953 c36953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22879
  · exact u22880
  · exact u22881
  · exact u22882

def b36954 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 74 22 296 146 225 193 193 449), lower := (rows 37 74 22 296 146 32 64 128 256), losses := [] }

theorem u36954 : Upper (D 7) (R 7) [36,72,18,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36955 : Route 9 := (fun mask => (mask,id))

def c36955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36955 : Upper (D 7) (R 7) [36,72,18,288,192] 13 := by
  apply FastRouting.sound _ _ [36,72,18,288,192] 13 (by decide) (choices 1) [1,2,128] r36955 c36955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22883
  · exact u22884
  · exact u22885

def b36956 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 74 22 392 19 225 225 225 481), lower := (rows 37 74 22 392 19 32 64 128 256), losses := [] }

theorem u36956 : Upper (D 7) (R 7) [36,72,18,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36957 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 22 392 49 227 195 195 451), lower := (rows 37 74 22 392 49 32 64 128 256), losses := [] }

theorem u36957 : Upper (D 7) (R 7) [36,72,18,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36958 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 22 392 50 225 193 193 449), lower := (rows 37 74 22 392 50 32 64 128 256), losses := [] }

theorem u36958 : Upper (D 7) (R 7) [36,72,18,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36959 : Route 9 := (fun mask => (mask,id))

def c36959 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36959 : Upper (D 7) (R 7) [36,72,18,384,65] 13 := by
  apply FastRouting.sound _ _ [36,72,18,384,65] 13 (by decide) (choices 1) [1,2,128] r36959 c36959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22886
  · exact u22887
  · exact u22888

#print axioms u36959
end Delivery.IrregularNine14.P07
