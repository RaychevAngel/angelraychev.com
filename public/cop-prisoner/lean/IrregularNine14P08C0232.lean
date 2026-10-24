import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0078
import IrregularNine14P08C0079

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13920 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 265 81 162 226 162 418), lower := (rows 97 14 52 265 81 32 64 128 256), losses := [] }

theorem u13920 : Upper (D 8) (R 8) [96,12,48,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13921 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 52 265 82 161 225 161 417), lower := (rows 97 14 52 265 82 32 64 128 256), losses := [] }

theorem u13921 : Upper (D 8) (R 8) [96,12,48,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13922 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 265 112 163 195 131 387), lower := (rows 97 14 52 265 112 32 64 128 256), losses := [] }

theorem u13922 : Upper (D 8) (R 8) [96,12,48,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13923 : Route 9 := (fun mask => (mask,id))

def c13923 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13923 : Upper (D 8) (R 8) [96,12,48,257,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,257,129] 13 (by decide) (choices 1) [2,64,128] r13923 c13923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4719
  · exact u4720
  · exact u4721

def r13924 : Route 9 := (fun mask => (mask,id))

def c13924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13924 : Upper (D 8) (R 8) [96,12,48,257,130] 13 := by
  apply FastRouting.sound _ _ [96,12,48,257,130] 13 (by decide) (choices 1) [1,64,128] r13924 c13924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4722
  · exact u4723
  · exact u4724

def b13925 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 265 176 227 195 195 451), lower := (rows 97 14 52 265 176 32 64 128 256), losses := [] }

theorem u13925 : Upper (D 8) (R 8) [96,12,48,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13926 : Route 9 := (fun mask => (mask,id))

def c13926 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13926 : Upper (D 8) (R 8) [96,12,48,257,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,257,192] 13 (by decide) (choices 1) [1,2,128] r13926 c13926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4725
  · exact u4726
  · exact u4727

def b13927 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 266 49 225 193 193 449), lower := (rows 97 14 52 266 49 32 64 128 256), losses := [] }

theorem u13927 : Upper (D 8) (R 8) [96,12,48,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13928 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 266 81 161 225 161 417), lower := (rows 97 14 52 266 81 32 64 128 256), losses := [] }

theorem u13928 : Upper (D 8) (R 8) [96,12,48,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13929 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 266 112 161 193 129 385), lower := (rows 97 14 52 266 112 32 64 128 256), losses := [] }

theorem u13929 : Upper (D 8) (R 8) [96,12,48,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13930 : Route 9 := (fun mask => (mask,id))

def c13930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13930 : Upper (D 8) (R 8) [96,12,48,258,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,258,129] 13 (by decide) (choices 1) [1,64,128] r13930 c13930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4728
  · exact u4729
  · exact u4730

def b13931 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 266 176 225 193 193 449), lower := (rows 97 14 52 266 176 32 64 128 256), losses := [] }

theorem u13931 : Upper (D 8) (R 8) [96,12,48,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13932 : Route 9 := (fun mask => (mask,id))

def c13932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13932 : Upper (D 8) (R 8) [96,12,48,258,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,258,192] 13 (by decide) (choices 1) [1,128] r13932 c13932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4731
  · exact u4732

def b13933 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 296 81 163 195 131 387), lower := (rows 97 14 52 296 81 32 64 128 256), losses := [] }

theorem u13933 : Upper (D 8) (R 8) [96,12,48,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13934 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 52 296 82 161 193 129 385), lower := (rows 97 14 52 296 82 32 64 128 256), losses := [] }

theorem u13934 : Upper (D 8) (R 8) [96,12,48,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13935 : Route 9 := (fun mask => (mask,id))

def c13935 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13935 : Upper (D 8) (R 8) [96,12,48,288,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,288,129] 13 (by decide) (choices 1) [1,2,64,128] r13935 c13935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4733
  · exact u4734
  · exact u4735
  · exact u4736

def r13936 : Route 9 := (fun mask => (mask,id))

def c13936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13936 : Upper (D 8) (R 8) [96,12,48,288,130] 13 := by
  apply FastRouting.sound _ _ [96,12,48,288,130] 13 (by decide) (choices 1) [1,64,128] r13936 c13936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4737
  · exact u4738
  · exact u4739

def r13937 : Route 9 := (fun mask => (mask,id))

def c13937 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13937 : Upper (D 8) (R 8) [96,12,48,288,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,288,192] 13 (by decide) (choices 1) [1,2,128] r13937 c13937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4740
  · exact u4741
  · exact u4742

def b13938 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 328 49 163 195 131 387), lower := (rows 97 14 52 328 49 32 64 128 256), losses := [] }

theorem u13938 : Upper (D 8) (R 8) [96,12,48,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13939 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 328 50 161 193 129 385), lower := (rows 97 14 52 328 50 32 64 128 256), losses := [] }

theorem u13939 : Upper (D 8) (R 8) [96,12,48,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13940 : Route 9 := (fun mask => (mask,id))

def c13940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13940 : Upper (D 8) (R 8) [96,12,48,320,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,320,129] 13 (by decide) (choices 1) [1,2,128] r13940 c13940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4743
  · exact u4744
  · exact u4745

def r13941 : Route 9 := (fun mask => (mask,id))

def c13941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13941 : Upper (D 8) (R 8) [96,12,48,320,130] 13 := by
  apply FastRouting.sound _ _ [96,12,48,320,130] 13 (by decide) (choices 1) [1,128] r13941 c13941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4746
  · exact u4747

def b13942 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 328 176 163 195 131 387), lower := (rows 97 14 52 328 176 32 64 128 256), losses := [] }

theorem u13942 : Upper (D 8) (R 8) [96,12,48,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13943 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 392 49 227 195 195 451), lower := (rows 97 14 52 392 49 32 64 128 256), losses := [] }

theorem u13943 : Upper (D 8) (R 8) [96,12,48,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13944 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 392 50 225 193 193 449), lower := (rows 97 14 52 392 50 32 64 128 256), losses := [] }

theorem u13944 : Upper (D 8) (R 8) [96,12,48,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13945 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 392 81 163 227 163 419), lower := (rows 97 14 52 392 81 32 64 128 256), losses := [] }

theorem u13945 : Upper (D 8) (R 8) [96,12,48,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13946 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 52 392 82 161 225 161 417), lower := (rows 97 14 52 392 82 32 64 128 256), losses := [] }

theorem u13946 : Upper (D 8) (R 8) [96,12,48,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13947 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 392 112 163 195 131 387), lower := (rows 97 14 52 392 112 32 64 128 256), losses := [] }

theorem u13947 : Upper (D 8) (R 8) [96,12,48,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13948 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 392 145 99 99 227 355), lower := (rows 97 14 52 392 145 32 64 128 256), losses := [] }

theorem u13948 : Upper (D 8) (R 8) [96,12,48,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13949 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 392 146 97 97 225 353), lower := (rows 97 14 52 392 146 32 64 128 256), losses := [] }

theorem u13949 : Upper (D 8) (R 8) [96,12,48,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13950 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 392 176 99 67 195 323), lower := (rows 97 14 52 392 176 32 64 128 256), losses := [] }

theorem u13950 : Upper (D 8) (R 8) [96,12,48,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13951 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 392 208 35 99 163 291), lower := (rows 97 14 52 392 208 32 64 128 256), losses := [] }

theorem u13951 : Upper (D 8) (R 8) [96,12,48,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13952 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 137 50 432 496 432 432), lower := (rows 97 14 69 137 50 32 64 128 256), losses := [] }

theorem u13952 : Upper (D 8) (R 8) [96,12,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13953 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 137 176 306 370 434 306), lower := (rows 97 14 69 137 176 32 64 128 256), losses := [] }

theorem u13953 : Upper (D 8) (R 8) [96,12,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13954 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 137 274 176 240 176 432), lower := (rows 97 14 69 137 274 32 64 128 256), losses := [] }

theorem u13954 : Upper (D 8) (R 8) [96,12,65,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13955 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 137 304 178 242 178 434), lower := (rows 97 14 69 137 304 32 64 128 256), losses := [] }

theorem u13955 : Upper (D 8) (R 8) [96,12,65,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13956 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 137 400 50 114 178 306), lower := (rows 97 14 69 137 400 32 64 128 256), losses := [] }

theorem u13956 : Upper (D 8) (R 8) [96,12,65,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13957 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 138 273 176 240 176 432), lower := (rows 97 14 69 138 273 32 64 128 256), losses := [] }

theorem u13957 : Upper (D 8) (R 8) [96,12,65,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13958 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 138 304 177 241 177 433), lower := (rows 97 14 69 138 304 32 64 128 256), losses := [] }

theorem u13958 : Upper (D 8) (R 8) [96,12,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13959 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 152 50 417 481 417 417), lower := (rows 97 14 69 152 50 32 64 128 256), losses := [] }

theorem u13959 : Upper (D 8) (R 8) [96,12,65,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13960 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 152 273 162 226 162 418), lower := (rows 97 14 69 152 273 32 64 128 256), losses := [] }

theorem u13960 : Upper (D 8) (R 8) [96,12,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13961 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 152 274 161 225 161 417), lower := (rows 97 14 69 152 274 32 64 128 256), losses := [] }

theorem u13961 : Upper (D 8) (R 8) [96,12,65,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13962 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 152 304 163 227 163 419), lower := (rows 97 14 69 152 304 32 64 128 256), losses := [] }

theorem u13962 : Upper (D 8) (R 8) [96,12,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13963 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 168 50 433 465 401 401), lower := (rows 97 14 69 168 50 32 64 128 256), losses := [] }

theorem u13963 : Upper (D 8) (R 8) [96,12,65,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13964 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 168 145 306 370 434 306), lower := (rows 97 14 69 168 145 32 64 128 256), losses := [] }

theorem u13964 : Upper (D 8) (R 8) [96,12,65,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13965 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 168 273 178 242 178 434), lower := (rows 97 14 69 168 273 32 64 128 256), losses := [] }

theorem u13965 : Upper (D 8) (R 8) [96,12,65,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13966 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 168 274 177 241 177 433), lower := (rows 97 14 69 168 274 32 64 128 256), losses := [] }

theorem u13966 : Upper (D 8) (R 8) [96,12,65,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13967 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 168 304 179 211 147 403), lower := (rows 97 14 69 168 304 32 64 128 256), losses := [] }

theorem u13967 : Upper (D 8) (R 8) [96,12,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13968 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 168 400 51 115 179 307), lower := (rows 97 14 69 168 400 32 64 128 256), losses := [] }

theorem u13968 : Upper (D 8) (R 8) [96,12,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13969 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 265 50 176 240 176 432), lower := (rows 97 14 69 265 50 32 64 128 256), losses := [] }

theorem u13969 : Upper (D 8) (R 8) [96,12,65,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13970 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 265 146 176 240 176 432), lower := (rows 97 14 69 265 146 32 64 128 256), losses := [] }

theorem u13970 : Upper (D 8) (R 8) [96,12,65,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13971 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 265 176 178 242 178 434), lower := (rows 97 14 69 265 176 32 64 128 256), losses := [] }

theorem u13971 : Upper (D 8) (R 8) [96,12,65,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13972 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 266 145 176 240 176 432), lower := (rows 97 14 69 266 145 32 64 128 256), losses := [] }

theorem u13972 : Upper (D 8) (R 8) [96,12,65,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13973 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 266 176 177 241 177 433), lower := (rows 97 14 69 266 176 32 64 128 256), losses := [] }

theorem u13973 : Upper (D 8) (R 8) [96,12,65,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13974 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 280 50 161 225 161 417), lower := (rows 97 14 69 280 50 32 64 128 256), losses := [] }

theorem u13974 : Upper (D 8) (R 8) [96,12,65,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13975 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 280 145 162 226 162 418), lower := (rows 97 14 69 280 145 32 64 128 256), losses := [] }

theorem u13975 : Upper (D 8) (R 8) [96,12,65,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13976 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 280 146 161 225 161 417), lower := (rows 97 14 69 280 146 32 64 128 256), losses := [] }

theorem u13976 : Upper (D 8) (R 8) [96,12,65,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13977 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 280 176 163 227 163 419), lower := (rows 97 14 69 280 176 32 64 128 256), losses := [] }

theorem u13977 : Upper (D 8) (R 8) [96,12,65,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13978 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 296 50 177 209 145 401), lower := (rows 97 14 69 296 50 32 64 128 256), losses := [] }

theorem u13978 : Upper (D 8) (R 8) [96,12,65,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13979 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 296 145 178 242 178 434), lower := (rows 97 14 69 296 145 32 64 128 256), losses := [] }

theorem u13979 : Upper (D 8) (R 8) [96,12,65,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13979
end Delivery.IrregularNine14.P08
