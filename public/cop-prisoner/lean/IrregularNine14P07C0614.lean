import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0379
import IrregularNine14P07C0380

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36840 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 138 82 417 481 417 417), lower := (rows 37 74 21 138 82 32 64 128 256), losses := [] }

theorem u36840 : Upper (D 7) (R 7) [36,72,17,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36841 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 138 112 419 451 387 387), lower := (rows 37 74 21 138 112 32 64 128 256), losses := [] }

theorem u36841 : Upper (D 7) (R 7) [36,72,17,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36842 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 138 145 354 354 482 354), lower := (rows 37 74 21 138 145 32 64 128 256), losses := [] }

theorem u36842 : Upper (D 7) (R 7) [36,72,17,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36843 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 74 21 138 146 353 353 481 353), lower := (rows 37 74 21 138 146 32 64 128 256), losses := [] }

theorem u36843 : Upper (D 7) (R 7) [36,72,17,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36844 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 138 176 355 323 451 323), lower := (rows 37 74 21 138 176 32 64 128 256), losses := [] }

theorem u36844 : Upper (D 7) (R 7) [36,72,17,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36845 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 21 138 208 291 355 419 291), lower := (rows 37 74 21 138 208 32 64 128 256), losses := [] }

theorem u36845 : Upper (D 7) (R 7) [36,72,17,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36846 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 138 273 226 226 226 482), lower := (rows 37 74 21 138 273 32 64 128 256), losses := [] }

theorem u36846 : Upper (D 7) (R 7) [36,72,17,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36847 : Route 9 := (fun mask => (mask,id))

def c36847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36847 : Upper (D 7) (R 7) [36,72,17,130,258] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,258] 13 (by decide) (choices 1) [1,64,128] r36847 c36847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22757
  · exact u22758
  · exact u22759

def b36848 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 138 304 227 195 195 451), lower := (rows 37 74 21 138 304 32 64 128 256), losses := [] }

theorem u36848 : Upper (D 7) (R 7) [36,72,17,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36849 : Route 9 := (fun mask => (mask,id))

def c36849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36849 : Upper (D 7) (R 7) [36,72,17,130,320] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,320] 13 (by decide) (choices 1) [1,2,128] r36849 c36849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22760
  · exact u22761
  · exact u22762

def r36850 : Route 9 := (fun mask => (mask,id))

def c36850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36850 : Upper (D 7) (R 7) [36,72,17,130,384] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,384] 13 (by decide) (choices 1) [1,2,64] r36850 c36850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22763
  · exact u22764
  · exact u22765

def b36851 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 4, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 37 74 21 168 19 482 450 450 450), lower := (rows 37 74 21 168 19 32 64 128 256), losses := [] }

theorem u36851 : Upper (D 7) (R 7) [36,72,17,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36852 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 168 81 418 450 386 386), lower := (rows 37 74 21 168 81 32 64 128 256), losses := [] }

theorem u36852 : Upper (D 7) (R 7) [36,72,17,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36853 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 168 82 419 451 387 387), lower := (rows 37 74 21 168 82 32 64 128 256), losses := [] }

theorem u36853 : Upper (D 7) (R 7) [36,72,17,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36854 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 21, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 168 145 354 322 450 322), lower := (rows 37 74 21 168 145 32 64 128 256), losses := [] }

theorem u36854 : Upper (D 7) (R 7) [36,72,17,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36855 : Route 9 := (fun mask => (mask,id))

def c36855 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36855 : Upper (D 7) (R 7) [36,72,17,160,130] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,130] 13 (by decide) (choices 1) [1,2,64,256] r36855 c36855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22766
  · exact u22767
  · exact u22768
  · exact u22769

def r36856 : Route 9 := (fun mask => (mask,id))

def c36856 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36856 : Upper (D 7) (R 7) [36,72,17,160,192] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,192] 13 (by decide) (choices 1) [1,2,256] r36856 c36856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22770
  · exact u22771
  · exact u22772

def b36857 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 168 273 226 194 194 450), lower := (rows 37 74 21 168 273 32 64 128 256), losses := [] }

theorem u36857 : Upper (D 7) (R 7) [36,72,17,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36858 : Route 9 := (fun mask => (mask,id))

def c36858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36858 : Upper (D 7) (R 7) [36,72,17,160,258] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,258] 13 (by decide) (choices 1) [1,2,64,128] r36858 c36858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22773
  · exact u22774
  · exact u22775
  · exact u22776

def r36859 : Route 9 := (fun mask => (mask,id))

def c36859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36859 : Upper (D 7) (R 7) [36,72,17,160,320] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,320] 13 (by decide) (choices 1) [1,2,128] r36859 c36859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22777
  · exact u22778
  · exact u22779

def r36860 : Route 9 := (fun mask => (mask,id))

def c36860 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36860 : Upper (D 7) (R 7) [36,72,17,160,384] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,384] 13 (by decide) (choices 1) [1,2,64] r36860 c36860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22780
  · exact u22781
  · exact u22782

def b36861 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 265 50 226 194 194 450), lower := (rows 37 74 21 265 50 32 64 128 256), losses := [] }

theorem u36861 : Upper (D 7) (R 7) [36,72,17,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36862 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 1, region := 16, targets := 32 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 37 74 21 265 82 162 226 162 418), lower := (rows 37 74 21 265 82 32 64 128 256), losses := [] }

theorem u36862 : Upper (D 7) (R 7) [36,72,17,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36863 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 265 112 162 194 130 386), lower := (rows 37 74 21 265 112 32 64 128 256), losses := [] }

theorem u36863 : Upper (D 7) (R 7) [36,72,17,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36864 : Route 9 := (fun mask => (mask,id))

def c36864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36864 : Upper (D 7) (R 7) [36,72,17,257,130] 13 := by
  apply FastRouting.sound _ _ [36,72,17,257,130] 13 (by decide) (choices 1) [2,64,128] r36864 c36864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22783
  · exact u22784
  · exact u22785

def b36865 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 265 176 226 194 194 450), lower := (rows 37 74 21 265 176 32 64 128 256), losses := [] }

theorem u36865 : Upper (D 7) (R 7) [36,72,17,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36866 : Route 9 := (fun mask => (mask,id))

def c36866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36866 : Upper (D 7) (R 7) [36,72,17,257,192] 13 := by
  apply FastRouting.sound _ _ [36,72,17,257,192] 13 (by decide) (choices 1) [2,128] r36866 c36866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22786
  · exact u22787

def b36867 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 0, region := 458, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 266 19 224 224 224 480), lower := (rows 37 74 21 266 19 32 64 128 256), losses := [] }

theorem u36867 : Upper (D 7) (R 7) [36,72,17,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36868 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 21, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 266 49 226 194 194 450), lower := (rows 37 74 21 266 49 32 64 128 256), losses := [] }

theorem u36868 : Upper (D 7) (R 7) [36,72,17,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36869 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 266 50 225 193 193 449), lower := (rows 37 74 21 266 50 32 64 128 256), losses := [] }

theorem u36869 : Upper (D 7) (R 7) [36,72,17,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36870 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 266 81 162 226 162 418), lower := (rows 37 74 21 266 81 32 64 128 256), losses := [] }

theorem u36870 : Upper (D 7) (R 7) [36,72,17,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36871 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 266 82 161 225 161 417), lower := (rows 37 74 21 266 82 32 64 128 256), losses := [] }

theorem u36871 : Upper (D 7) (R 7) [36,72,17,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36872 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 266 112 163 195 131 387), lower := (rows 37 74 21 266 112 32 64 128 256), losses := [] }

theorem u36872 : Upper (D 7) (R 7) [36,72,17,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36873 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 266 145 226 226 226 482), lower := (rows 37 74 21 266 145 32 64 128 256), losses := [] }

theorem u36873 : Upper (D 7) (R 7) [36,72,17,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36874 : Route 9 := (fun mask => (mask,id))

def c36874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36874 : Upper (D 7) (R 7) [36,72,17,258,130] 13 := by
  apply FastRouting.sound _ _ [36,72,17,258,130] 13 (by decide) (choices 1) [1,64,128] r36874 c36874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22788
  · exact u22789
  · exact u22790

def b36875 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 266 176 227 195 195 451), lower := (rows 37 74 21 266 176 32 64 128 256), losses := [] }

theorem u36875 : Upper (D 7) (R 7) [36,72,17,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36876 : Route 9 := (fun mask => (mask,id))

def c36876 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36876 : Upper (D 7) (R 7) [36,72,17,258,192] 13 := by
  apply FastRouting.sound _ _ [36,72,17,258,192] 13 (by decide) (choices 1) [1,2,128] r36876 c36876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22791
  · exact u22792
  · exact u22793

def b36877 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 37 74 21 296 19 226 194 194 450), lower := (rows 37 74 21 296 19 32 64 128 256), losses := [] }

theorem u36877 : Upper (D 7) (R 7) [36,72,17,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36878 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 296 81 162 194 130 386), lower := (rows 37 74 21 296 81 32 64 128 256), losses := [] }

theorem u36878 : Upper (D 7) (R 7) [36,72,17,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36879 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 296 82 163 195 131 387), lower := (rows 37 74 21 296 82 32 64 128 256), losses := [] }

theorem u36879 : Upper (D 7) (R 7) [36,72,17,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36880 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 296 145 226 194 194 450), lower := (rows 37 74 21 296 145 32 64 128 256), losses := [] }

theorem u36880 : Upper (D 7) (R 7) [36,72,17,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36881 : Route 9 := (fun mask => (mask,id))

def c36881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36881 : Upper (D 7) (R 7) [36,72,17,288,130] 13 := by
  apply FastRouting.sound _ _ [36,72,17,288,130] 13 (by decide) (choices 1) [1,2,64,128] r36881 c36881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22794
  · exact u22795
  · exact u22796
  · exact u22797

def r36882 : Route 9 := (fun mask => (mask,id))

def c36882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36882 : Upper (D 7) (R 7) [36,72,17,288,192] 13 := by
  apply FastRouting.sound _ _ [36,72,17,288,192] 13 (by decide) (choices 1) [1,2,128] r36882 c36882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22798
  · exact u22799
  · exact u22800

def b36883 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 392 19 226 226 226 482), lower := (rows 37 74 21 392 19 32 64 128 256), losses := [] }

theorem u36883 : Upper (D 7) (R 7) [36,72,17,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36884 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 21, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 392 49 226 194 194 450), lower := (rows 37 74 21 392 49 32 64 128 256), losses := [] }

theorem u36884 : Upper (D 7) (R 7) [36,72,17,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36885 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 392 50 227 195 195 451), lower := (rows 37 74 21 392 50 32 64 128 256), losses := [] }

theorem u36885 : Upper (D 7) (R 7) [36,72,17,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36886 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 392 81 162 226 162 418), lower := (rows 37 74 21 392 81 32 64 128 256), losses := [] }

theorem u36886 : Upper (D 7) (R 7) [36,72,17,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36887 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 392 82 163 227 163 419), lower := (rows 37 74 21 392 82 32 64 128 256), losses := [] }

theorem u36887 : Upper (D 7) (R 7) [36,72,17,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36888 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 392 112 163 195 131 387), lower := (rows 37 74 21 392 112 32 64 128 256), losses := [] }

theorem u36888 : Upper (D 7) (R 7) [36,72,17,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36889 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 21 392 145 98 98 226 354), lower := (rows 37 74 21 392 145 32 64 128 256), losses := [] }

theorem u36889 : Upper (D 7) (R 7) [36,72,17,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36890 : Route 9 := (fun mask => (mask,id))

def c36890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36890 : Upper (D 7) (R 7) [36,72,17,384,130] 13 := by
  apply FastRouting.sound _ _ [36,72,17,384,130] 13 (by decide) (choices 1) [1,2,64] r36890 c36890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22801
  · exact u22802
  · exact u22803

def b36891 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 392 176 99 67 195 323), lower := (rows 37 74 21 392 176 32 64 128 256), losses := [] }

theorem u36891 : Upper (D 7) (R 7) [36,72,17,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36892 : Route 9 := (fun mask => (mask,id))

def c36892 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36892 : Upper (D 7) (R 7) [36,72,17,384,192] 13 := by
  apply FastRouting.sound _ _ [36,72,17,384,192] 13 (by decide) (choices 1) [1,2] r36892 c36892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22804
  · exact u22805

def b36893 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 74 22 42 81 417 449 385 385), lower := (rows 37 74 22 42 81 32 64 128 256), losses := [] }

theorem u36893 : Upper (D 7) (R 7) [36,72,18,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36894 : Route 9 := (fun mask => (mask,id))

def c36894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u36894 : Upper (D 7) (R 7) [36,72,18,34,129] 13 := by
  apply FastRouting.sound _ _ [36,72,18,34,129] 13 (by decide) (choices 1) [1,64,128,256] r36894 c36894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22806
  · exact u22807
  · exact u22808
  · exact u22809

def b36895 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 74 22 42 208 417 449 385 385), lower := (rows 37 74 22 42 208 32 64 128 256), losses := [] }

theorem u36895 : Upper (D 7) (R 7) [36,72,18,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36896 : Route 9 := (fun mask => (mask,id))

def c36896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36896 : Upper (D 7) (R 7) [36,72,18,34,257] 13 := by
  apply FastRouting.sound _ _ [36,72,18,34,257] 13 (by decide) (choices 1) [1,64,128] r36896 c36896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22810
  · exact u22811
  · exact u22812

def b36897 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 74 22 42 336 161 193 129 385), lower := (rows 37 74 22 42 336 32 64 128 256), losses := [] }

theorem u36897 : Upper (D 7) (R 7) [36,72,18,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36898 : Route 9 := (fun mask => (mask,id))

def c36898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36898 : Upper (D 7) (R 7) [36,72,18,34,384] 13 := by
  apply FastRouting.sound _ _ [36,72,18,34,384] 13 (by decide) (choices 1) [1,64,128] r36898 c36898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22813
  · exact u22814
  · exact u22815

def b36899 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 2, region := 481, targets := 2 }], pairs := [(0,1),(2,5),(2,6),(2,7)], upper := (rows 37 74 22 137 19 480 480 480 480), lower := (rows 37 74 22 137 19 32 64 128 256), losses := [] }

theorem u36899 : Upper (D 7) (R 7) [36,72,18,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36899
end Delivery.IrregularNine14.P07
