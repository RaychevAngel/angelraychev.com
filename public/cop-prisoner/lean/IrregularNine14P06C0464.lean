import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0149
import IrregularNine14P06C0150

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27840 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 360, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 56 22 352 352 480 352), lower := (rows 7 11 133 56 22 32 64 128 256), losses := [] }

theorem u27840 : Upper (D 6) (R 6) [6,9,129,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27841 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 56 50 356 324 452 324), lower := (rows 7 11 133 56 50 32 64 128 256), losses := [] }

theorem u27841 : Upper (D 6) (R 6) [6,9,129,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27842 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 133 56 52 354 322 450 322), lower := (rows 7 11 133 56 52 32 64 128 256), losses := [] }

theorem u27842 : Upper (D 6) (R 6) [6,9,129,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27843 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 56 82 356 356 484 356), lower := (rows 7 11 133 56 82 32 64 128 256), losses := [] }

theorem u27843 : Upper (D 6) (R 6) [6,9,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27844 : Route 9 := (fun mask => (mask,id))

def c27844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27844 : Upper (D 6) (R 6) [6,9,129,48,68] 13 := by
  apply FastRouting.sound _ _ [6,9,129,48,68] 13 (by decide) (choices 1) [2,64,256] r27844 c27844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8975
  · exact u8976
  · exact u8977

def b27845 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 56 112 358 326 454 326), lower := (rows 7 11 133 56 112 32 64 128 256), losses := [] }

theorem u27845 : Upper (D 6) (R 6) [6,9,129,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27846 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 56 274 100 100 228 356), lower := (rows 7 11 133 56 274 32 64 128 256), losses := [] }

theorem u27846 : Upper (D 6) (R 6) [6,9,129,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27847 : Route 9 := (fun mask => (mask,id))

def c27847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27847 : Upper (D 6) (R 6) [6,9,129,48,260] 13 := by
  apply FastRouting.sound _ _ [6,9,129,48,260] 13 (by decide) (choices 1) [2,64] r27847 c27847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8978
  · exact u8979

def b27848 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 56 304 102 70 198 326), lower := (rows 7 11 133 56 304 32 64 128 256), losses := [] }

theorem u27848 : Upper (D 6) (R 6) [6,9,129,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27849 : Route 9 := (fun mask => (mask,id))

def c27849 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27849 : Upper (D 6) (R 6) [6,9,129,48,320] 13 := by
  apply FastRouting.sound _ _ [6,9,129,48,320] 13 (by decide) (choices 1) [2,4,64] r27849 c27849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8980
  · exact u8981
  · exact u8982

def b27850 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 104 22 368 368 496 368), lower := (rows 7 11 133 104 22 32 64 128 256), losses := [] }

theorem u27850 : Upper (D 6) (R 6) [6,9,129,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27851 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 11 133 104 50 372 340 468 340), lower := (rows 7 11 133 104 50 32 64 128 256), losses := [] }

theorem u27851 : Upper (D 6) (R 6) [6,9,129,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27852 : Route 9 := (fun mask => (mask,id))

def c27852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u27852 : Upper (D 6) (R 6) [6,9,129,96,36] 13 := by
  apply FastRouting.sound _ _ [6,9,129,96,36] 13 (by decide) (choices 1) [2,16,64,256] r27852 c27852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8983
  · exact u8984
  · exact u8985
  · exact u8986

def b27853 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 133 104 112 310 342 406 278), lower := (rows 7 11 133 104 112 32 64 128 256), losses := [] }

theorem u27853 : Upper (D 6) (R 6) [6,9,129,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27854 : Route 9 := (fun mask => (mask,id))

def c27854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27854 : Upper (D 6) (R 6) [6,9,129,96,258] 13 := by
  apply FastRouting.sound _ _ [6,9,129,96,258] 13 (by decide) (choices 1) [4,16,64] r27854 c27854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8987
  · exact u8988
  · exact u8989

def r27855 : Route 9 := (fun mask => (mask,id))

def c27855 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27855 : Upper (D 6) (R 6) [6,9,129,96,260] 13 := by
  apply FastRouting.sound _ _ [6,9,129,96,260] 13 (by decide) (choices 1) [2,16,64] r27855 c27855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8990
  · exact u8991
  · exact u8992

def r27856 : Route 9 := (fun mask => (mask,id))

def c27856 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27856 : Upper (D 6) (R 6) [6,9,129,96,288] 13 := by
  apply FastRouting.sound _ _ [6,9,129,96,288] 13 (by decide) (choices 1) [2,4,16,64] r27856 c27856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8993
  · exact u8994
  · exact u8995
  · exact u8996

def b27857 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 360, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 280 22 96 96 224 352), lower := (rows 7 11 133 280 22 32 64 128 256), losses := [] }

theorem u27857 : Upper (D 6) (R 6) [6,9,129,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27858 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 280 50 100 100 228 356), lower := (rows 7 11 133 280 50 32 64 128 256), losses := [] }

theorem u27858 : Upper (D 6) (R 6) [6,9,129,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27859 : Route 9 := (fun mask => (mask,id))

def c27859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27859 : Upper (D 6) (R 6) [6,9,129,272,36] 13 := by
  apply FastRouting.sound _ _ [6,9,129,272,36] 13 (by decide) (choices 1) [2,64] r27859 c27859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8997
  · exact u8998

def r27860 : Route 9 := (fun mask => (mask,id))

def c27860 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27860 : Upper (D 6) (R 6) [6,9,129,272,96] 13 := by
  apply FastRouting.sound _ _ [6,9,129,272,96] 13 (by decide) (choices 1) [2,4,64] r27860 c27860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8999
  · exact u9000
  · exact u9001

def b27861 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 296 22 112 112 240 368), lower := (rows 7 11 133 296 22 32 64 128 256), losses := [] }

theorem u27861 : Upper (D 6) (R 6) [6,9,129,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27862 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 11 133 296 50 116 84 212 340), lower := (rows 7 11 133 296 50 32 64 128 256), losses := [] }

theorem u27862 : Upper (D 6) (R 6) [6,9,129,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27863 : Route 9 := (fun mask => (mask,id))

def c27863 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27863 : Upper (D 6) (R 6) [6,9,129,288,36] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,36] 13 (by decide) (choices 1) [2,16,64] r27863 c27863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9002
  · exact u9003
  · exact u9004

def r27864 : Route 9 := (fun mask => (mask,id))

def c27864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27864 : Upper (D 6) (R 6) [6,9,129,288,66] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,66] 13 (by decide) (choices 1) [4,16,64] r27864 c27864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9005
  · exact u9006
  · exact u9007

def r27865 : Route 9 := (fun mask => (mask,id))

def c27865 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27865 : Upper (D 6) (R 6) [6,9,129,288,68] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,68] 13 (by decide) (choices 1) [2,16,64] r27865 c27865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9008
  · exact u9009
  · exact u9010

def r27866 : Route 9 := (fun mask => (mask,id))

def c27866 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27866 : Upper (D 6) (R 6) [6,9,129,288,96] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,96] 13 (by decide) (choices 1) [2,4,16,64] r27866 c27866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9011
  · exact u9012
  · exact u9013
  · exact u9014

def b27867 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 148 42 21 352 352 480 352), lower := (rows 7 11 148 42 21 32 64 128 256), losses := [] }

theorem u27867 : Upper (D 6) (R 6) [6,9,144,34,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27868 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 10, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 148 42 49 356 324 452 324), lower := (rows 7 11 148 42 49 32 64 128 256), losses := [] }

theorem u27868 : Upper (D 6) (R 6) [6,9,144,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27869 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 148 42 52 353 321 449 321), lower := (rows 7 11 148 42 52 32 64 128 256), losses := [] }

theorem u27869 : Upper (D 6) (R 6) [6,9,144,34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27870 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 360, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 11 148 42 81 356 356 484 356), lower := (rows 7 11 148 42 81 32 64 128 256), losses := [] }

theorem u27870 : Upper (D 6) (R 6) [6,9,144,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27871 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 148 42 84 353 353 481 353), lower := (rows 7 11 148 42 84 32 64 128 256), losses := [] }

theorem u27871 : Upper (D 6) (R 6) [6,9,144,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27872 : Route 9 := (fun mask => (mask,id))

def c27872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27872 : Upper (D 6) (R 6) [6,9,144,34,96] 13 := by
  apply FastRouting.sound _ _ [6,9,144,34,96] 13 (by decide) (choices 1) [1,4,64,256] r27872 c27872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9015
  · exact u9016
  · exact u9017
  · exact u9018

def b27873 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 11 148 42 273 100 100 228 356), lower := (rows 7 11 148 42 273 32 64 128 256), losses := [] }

theorem u27873 : Upper (D 6) (R 6) [6,9,144,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27874 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 148 42 276 97 97 225 353), lower := (rows 7 11 148 42 276 32 64 128 256), losses := [] }

theorem u27874 : Upper (D 6) (R 6) [6,9,144,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27875 : Route 9 := (fun mask => (mask,id))

def c27875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27875 : Upper (D 6) (R 6) [6,9,144,34,288] 13 := by
  apply FastRouting.sound _ _ [6,9,144,34,288] 13 (by decide) (choices 1) [1,4,64] r27875 c27875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9019
  · exact u9020
  · exact u9021

def r27876 : Route 9 := (fun mask => (mask,id))

def c27876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27876 : Upper (D 6) (R 6) [6,9,144,34,320] 13 := by
  apply FastRouting.sound _ _ [6,9,144,34,320] 13 (by decide) (choices 1) [1,4,64] r27876 c27876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9022
  · exact u9023
  · exact u9024

def b27877 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 104 19 356 356 484 356), lower := (rows 7 11 148 104 19 32 64 128 256), losses := [] }

theorem u27877 : Upper (D 6) (R 6) [6,9,144,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27878 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 148 104 21 354 354 482 354), lower := (rows 7 11 148 104 21 32 64 128 256), losses := [] }

theorem u27878 : Upper (D 6) (R 6) [6,9,144,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27879 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 11 148 104 22 353 353 481 353), lower := (rows 7 11 148 104 22 32 64 128 256), losses := [] }

theorem u27879 : Upper (D 6) (R 6) [6,9,144,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27880 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 360, targets := 1 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 7 11 148 104 49 358 326 454 326), lower := (rows 7 11 148 104 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 156 104 508 32 64 128 256) },{ target := 5, region := (rows 1 2 20 8 16 0 65 129 257), good := (rows 455 459 148 72 469 0 64 128 256) }] }

theorem u27880 : Upper (D 6) (R 6) [6,9,144,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27881 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 453, targets := 32 },{ cop := 0, region := 360, targets := 2 }], pairs := [(0,5),(2,5),(3,1)], upper := (rows 7 11 148 104 50 357 325 453 325), lower := (rows 7 11 148 104 50 32 64 128 256), losses := [] }

theorem u27881 : Upper (D 6) (R 6) [6,9,144,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27882 : Route 9 := (fun mask => (mask,id))

def c27882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27882 : Upper (D 6) (R 6) [6,9,144,96,36] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,36] 13 (by decide) (choices 1) [1,2,64,256] r27882 c27882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9025
  · exact u9026
  · exact u9027
  · exact u9028

def b27883 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 148 104 112 295 327 391 263), lower := (rows 7 11 148 104 112 32 64 128 256), losses := [] }

theorem u27883 : Upper (D 6) (R 6) [6,9,144,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27884 : Route 9 := (fun mask => (mask,id))

def c27884 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27884 : Upper (D 6) (R 6) [6,9,144,96,257] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,257] 13 (by decide) (choices 1) [2,4,64] r27884 c27884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9029
  · exact u9030
  · exact u9031

def r27885 : Route 9 := (fun mask => (mask,id))

def c27885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27885 : Upper (D 6) (R 6) [6,9,144,96,258] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,258] 13 (by decide) (choices 1) [1,4,64] r27885 c27885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9032
  · exact u9033
  · exact u9034

def r27886 : Route 9 := (fun mask => (mask,id))

def c27886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27886 : Upper (D 6) (R 6) [6,9,144,96,260] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,260] 13 (by decide) (choices 1) [1,2,64] r27886 c27886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9035
  · exact u9036
  · exact u9037

def r27887 : Route 9 := (fun mask => (mask,id))

def c27887 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27887 : Upper (D 6) (R 6) [6,9,144,96,288] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,288] 13 (by decide) (choices 1) [1,2,4,64] r27887 c27887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9038
  · exact u9039
  · exact u9040
  · exact u9041

def b27888 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 148 266 21 96 96 224 352), lower := (rows 7 11 148 266 21 32 64 128 256), losses := [] }

theorem u27888 : Upper (D 6) (R 6) [6,9,144,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27889 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 360, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 11 148 266 49 100 100 228 356), lower := (rows 7 11 148 266 49 32 64 128 256), losses := [] }

theorem u27889 : Upper (D 6) (R 6) [6,9,144,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27890 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 148 266 52 97 97 225 353), lower := (rows 7 11 148 266 52 32 64 128 256), losses := [] }

theorem u27890 : Upper (D 6) (R 6) [6,9,144,258,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27891 : Route 9 := (fun mask => (mask,id))

def c27891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27891 : Upper (D 6) (R 6) [6,9,144,258,96] 13 := by
  apply FastRouting.sound _ _ [6,9,144,258,96] 13 (by decide) (choices 1) [1,4,64] r27891 c27891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9042
  · exact u9043
  · exact u9044

def b27892 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 296 19 100 100 228 356), lower := (rows 7 11 148 296 19 32 64 128 256), losses := [] }

theorem u27892 : Upper (D 6) (R 6) [6,9,144,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27893 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 148 296 21 98 98 226 354), lower := (rows 7 11 148 296 21 32 64 128 256), losses := [] }

theorem u27893 : Upper (D 6) (R 6) [6,9,144,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27894 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 11 148 296 22 97 97 225 353), lower := (rows 7 11 148 296 22 32 64 128 256), losses := [] }

theorem u27894 : Upper (D 6) (R 6) [6,9,144,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27895 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 360, targets := 1 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 7 11 148 296 49 102 70 198 326), lower := (rows 7 11 148 296 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 156 296 508 32 64 128 256) },{ target := 5, region := (rows 1 2 20 8 16 0 65 129 257), good := (rows 455 459 148 264 469 0 64 128 256) }] }

theorem u27895 : Upper (D 6) (R 6) [6,9,144,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27896 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 197, targets := 32 },{ cop := 0, region := 360, targets := 2 }], pairs := [(0,5),(2,5),(3,1)], upper := (rows 7 11 148 296 50 101 69 197 325), lower := (rows 7 11 148 296 50 32 64 128 256), losses := [] }

theorem u27896 : Upper (D 6) (R 6) [6,9,144,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27897 : Route 9 := (fun mask => (mask,id))

def c27897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27897 : Upper (D 6) (R 6) [6,9,144,288,36] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,36] 13 (by decide) (choices 1) [1,2,64] r27897 c27897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9045
  · exact u9046
  · exact u9047

def r27898 : Route 9 := (fun mask => (mask,id))

def c27898 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27898 : Upper (D 6) (R 6) [6,9,144,288,65] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,65] 13 (by decide) (choices 1) [2,4,64] r27898 c27898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9048
  · exact u9049
  · exact u9050

def r27899 : Route 9 := (fun mask => (mask,id))

def c27899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27899 : Upper (D 6) (R 6) [6,9,144,288,66] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,66] 13 (by decide) (choices 1) [1,4,64] r27899 c27899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9051
  · exact u9052
  · exact u9053

#print axioms u27899
end Delivery.IrregularNine14.P06
