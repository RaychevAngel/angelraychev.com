import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0171
import IrregularNine14P07C0172

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r27840 : Route 9 := (fun mask => (mask,id))

def c27840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27840 : Upper (D 7) (R 7) [36,320,136,3,192,16] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,192,16] 13 (by decide) (choices 1) [1,2,32] r27840 c27840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10291
  · exact u10292
  · exact u10293

def b27841 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 140 25 50 33 194 194 450), lower := (rows 37 322 140 25 50 33 64 128 256), losses := [] }

theorem u27841 : Upper (D 7) (R 7) [36,320,136,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27842 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 322 140 25 50 34 193 193 449), lower := (rows 37 322 140 25 50 34 64 128 256), losses := [] }

theorem u27842 : Upper (D 7) (R 7) [36,320,136,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27843 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 141, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 322 140 25 50 96 195 131 387), lower := (rows 37 322 140 25 50 96 64 128 256), losses := [] }

theorem u27843 : Upper (D 7) (R 7) [36,320,136,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27844 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 25 50 160 67 195 323), lower := (rows 37 322 140 25 50 160 64 128 256), losses := [] }

theorem u27844 : Upper (D 7) (R 7) [36,320,136,17,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27845 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 140 25 112 33 194 130 386), lower := (rows 37 322 140 25 112 33 64 128 256), losses := [] }

theorem u27845 : Upper (D 7) (R 7) [36,320,136,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27846 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 48, targets := 129 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,0),(4,7)], upper := (rows 37 322 140 25 112 34 195 131 387), lower := (rows 37 322 140 25 112 34 64 128 256), losses := [] }

theorem u27846 : Upper (D 7) (R 7) [36,320,136,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27847 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 25 112 160 67 131 259), lower := (rows 37 322 140 25 112 160 64 128 256), losses := [] }

theorem u27847 : Upper (D 7) (R 7) [36,320,136,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27848 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 140 25 146 33 98 226 354), lower := (rows 37 322 140 25 146 33 64 128 256), losses := [] }

theorem u27848 : Upper (D 7) (R 7) [36,320,136,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27849 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 37 322 140 25 146 34 97 225 353), lower := (rows 37 322 140 25 146 34 64 128 256), losses := [] }

theorem u27849 : Upper (D 7) (R 7) [36,320,136,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27850 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 37 322 140 25 146 96 99 163 291), lower := (rows 37 322 140 25 146 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 24 16 98 64 128 256), good := (rows 37 352 140 29 189 96 96 128 256) }] }

theorem u27850 : Upper (D 7) (R 7) [36,320,136,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27851 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 140 25 208 33 98 162 290), lower := (rows 37 322 140 25 208 33 64 128 256), losses := [] }

theorem u27851 : Upper (D 7) (R 7) [36,320,136,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27852 : Route 9 := (fun mask => (mask,id))

def c27852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27852 : Upper (D 7) (R 7) [36,320,136,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,320,136,17,192,2] 13 (by decide) (choices 1) [1,2,32] r27852 c27852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10294
  · exact u10295
  · exact u10296

def b27853 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 140 26 81 33 226 162 418), lower := (rows 37 322 140 26 81 33 64 128 256), losses := [] }

theorem u27853 : Upper (D 7) (R 7) [36,320,136,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27854 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(2,6),(4,1)], upper := (rows 37 322 140 26 81 34 225 161 417), lower := (rows 37 322 140 26 81 34 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 354 45 58 81 34 64 0 256) }] }

theorem u27854 : Upper (D 7) (R 7) [36,320,136,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27855 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 26 81 160 99 163 291), lower := (rows 37 322 140 26 81 160 64 128 256), losses := [] }

theorem u27855 : Upper (D 7) (R 7) [36,320,136,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27856 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 140 26 112 33 195 131 387), lower := (rows 37 322 140 26 112 33 64 128 256), losses := [] }

theorem u27856 : Upper (D 7) (R 7) [36,320,136,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27857 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 322 140 26 112 34 193 129 385), lower := (rows 37 322 140 26 112 34 64 128 256), losses := [] }

theorem u27857 : Upper (D 7) (R 7) [36,320,136,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27858 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 26 112 160 67 131 259), lower := (rows 37 322 140 26 112 160 64 128 256), losses := [] }

theorem u27858 : Upper (D 7) (R 7) [36,320,136,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27859 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 140 26 145 33 98 226 354), lower := (rows 37 322 140 26 145 33 64 128 256), losses := [] }

theorem u27859 : Upper (D 7) (R 7) [36,320,136,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27860 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,1)], upper := (rows 37 322 140 26 145 34 97 225 353), lower := (rows 37 322 140 26 145 34 64 128 256), losses := [] }

theorem u27860 : Upper (D 7) (R 7) [36,320,136,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27861 : Route 9 := (fun mask => (mask,id))

def c27861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27861 : Upper (D 7) (R 7) [36,320,136,18,129,64] 13 := by
  apply FastRouting.sound _ _ [36,320,136,18,129,64] 13 (by decide) (choices 1) [1,2,32] r27861 c27861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10297
  · exact u10298
  · exact u10299

def b27862 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 140 26 176 33 67 195 323), lower := (rows 37 322 140 26 176 33 64 128 256), losses := [] }

theorem u27862 : Upper (D 7) (R 7) [36,320,136,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27863 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,1)], upper := (rows 37 322 140 26 176 34 65 193 321), lower := (rows 37 322 140 26 176 34 64 128 256), losses := [] }

theorem u27863 : Upper (D 7) (R 7) [36,320,136,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27864 : Route 9 := (fun mask => (mask,id))

def c27864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27864 : Upper (D 7) (R 7) [36,320,136,18,160,64] 13 := by
  apply FastRouting.sound _ _ [36,320,136,18,160,64] 13 (by decide) (choices 1) [1,2] r27864 c27864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10300
  · exact u10301

def b27865 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 140 42 19 33 208 208 464), lower := (rows 37 322 140 42 19 33 64 128 256), losses := [] }

theorem u27865 : Upper (D 7) (R 7) [36,320,136,34,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27866 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 322 140 42 19 48 193 193 449), lower := (rows 37 322 140 42 19 48 64 128 256), losses := [] }

theorem u27866 : Upper (D 7) (R 7) [36,320,136,34,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27866 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27867 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 149, targets := 64 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,6)], upper := (rows 37 322 140 42 19 96 209 145 401), lower := (rows 37 322 140 42 19 96 64 128 256), losses := [] }

theorem u27867 : Upper (D 7) (R 7) [36,320,136,34,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27868 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 338, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 42 19 160 81 209 337), lower := (rows 37 322 140 42 19 160 64 128 256), losses := [] }

theorem u27868 : Upper (D 7) (R 7) [36,320,136,34,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27869 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 140 42 81 33 210 146 402), lower := (rows 37 322 140 42 81 33 64 128 256), losses := [] }

theorem u27869 : Upper (D 7) (R 7) [36,320,136,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27870 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 140 42 81 34 209 145 401), lower := (rows 37 322 140 42 81 34 64 128 256), losses := [] }

theorem u27870 : Upper (D 7) (R 7) [36,320,136,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27871 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 133, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 37 322 140 42 81 48 195 131 387), lower := (rows 37 322 140 42 81 48 64 128 256), losses := [] }

theorem u27871 : Upper (D 7) (R 7) [36,320,136,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27871 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27872 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 338, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 42 81 160 83 147 275), lower := (rows 37 322 140 42 81 160 64 128 256), losses := [] }

theorem u27872 : Upper (D 7) (R 7) [36,320,136,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27873 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 140 42 146 33 81 209 337), lower := (rows 37 322 140 42 146 33 64 128 256), losses := [] }

theorem u27873 : Upper (D 7) (R 7) [36,320,136,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27874 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 140 42 146 48 65 193 321), lower := (rows 37 322 140 42 146 48 64 128 256), losses := [] }

theorem u27874 : Upper (D 7) (R 7) [36,320,136,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27874 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27875 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 149, targets := 64 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,6)], upper := (rows 37 322 140 42 146 96 81 145 273), lower := (rows 37 322 140 42 146 96 64 128 256), losses := [] }

theorem u27875 : Upper (D 7) (R 7) [36,320,136,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27876 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 140 42 208 33 83 147 275), lower := (rows 37 322 140 42 208 33 64 128 256), losses := [] }

theorem u27876 : Upper (D 7) (R 7) [36,320,136,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27877 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 140 42 208 34 81 145 273), lower := (rows 37 322 140 42 208 34 64 128 256), losses := [] }

theorem u27877 : Upper (D 7) (R 7) [36,320,136,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27878 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 37 322 140 42 208 48 67 131 259), lower := (rows 37 322 140 42 208 48 64 128 256), losses := [] }

theorem u27878 : Upper (D 7) (R 7) [36,320,136,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27878 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27879 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 140 56 19 33 194 194 450), lower := (rows 37 322 140 56 19 33 64 128 256), losses := [] }

theorem u27879 : Upper (D 7) (R 7) [36,320,136,48,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27880 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(3,7)], upper := (rows 37 322 140 56 19 34 193 193 449), lower := (rows 37 322 140 56 19 34 64 128 256), losses := [] }

theorem u27880 : Upper (D 7) (R 7) [36,320,136,48,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27881 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 37 322 140 56 19 96 195 131 387), lower := (rows 37 322 140 56 19 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 98 64 128 256), good := (rows 36 354 140 56 58 96 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 98 64 128 256), good := (rows 37 352 140 56 57 96 96 128 256) }] }

theorem u27881 : Upper (D 7) (R 7) [36,320,136,48,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27882 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 56 19 160 67 195 323), lower := (rows 37 322 140 56 19 160 64 128 256), losses := [] }

theorem u27882 : Upper (D 7) (R 7) [36,320,136,48,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27883 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 140 56 81 33 194 130 386), lower := (rows 37 322 140 56 81 33 64 128 256), losses := [] }

theorem u27883 : Upper (D 7) (R 7) [36,320,136,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27884 : Route 9 := (fun mask => (mask,id))

def c27884 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27884 : Upper (D 7) (R 7) [36,320,136,48,65,2] 13 := by
  apply FastRouting.sound _ _ [36,320,136,48,65,2] 13 (by decide) (choices 1) [1,2,128] r27884 c27884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10302
  · exact u10303
  · exact u10304

def b27885 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 56 81 160 67 131 259), lower := (rows 37 322 140 56 81 160 64 128 256), losses := [] }

theorem u27885 : Upper (D 7) (R 7) [36,320,136,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27886 : Route 9 := (fun mask => (mask,id))

def c27886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u27886 : Upper (D 7) (R 7) [36,320,136,65,3,2] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,3,2] 13 (by decide) (choices 1) [16,32,128] r27886 c27886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10305
  · exact u10306
  · exact u10307

def r27887 : Route 9 := (fun mask => (mask,id))

def c27887 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27887 : Upper (D 7) (R 7) [36,320,136,65,3,16] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,3,16] 13 (by decide) (choices 1) [2,32,128] r27887 c27887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10308
  · exact u10309
  · exact u10310

def b27888 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 73 19 160 114 178 306), lower := (rows 37 322 140 73 19 160 64 128 256), losses := [] }

theorem u27888 : Upper (D 7) (R 7) [36,320,136,65,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27889 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 140 73 50 33 210 146 402), lower := (rows 37 322 140 73 50 33 64 128 256), losses := [] }

theorem u27889 : Upper (D 7) (R 7) [36,320,136,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27890 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 322 140 73 50 34 209 145 401), lower := (rows 37 322 140 73 50 34 64 128 256), losses := [] }

theorem u27890 : Upper (D 7) (R 7) [36,320,136,65,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27891 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 140 73 50 48 195 131 387), lower := (rows 37 322 140 73 50 48 64 128 256), losses := [] }

theorem u27891 : Upper (D 7) (R 7) [36,320,136,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27891 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27892 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 73 50 160 83 147 275), lower := (rows 37 322 140 73 50 160 64 128 256), losses := [] }

theorem u27892 : Upper (D 7) (R 7) [36,320,136,65,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27893 : Route 9 := (fun mask => (mask,id))

def c27893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27893 : Upper (D 7) (R 7) [36,320,136,65,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,129,2] 13 (by decide) (choices 1) [2,16,32] r27893 c27893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10311
  · exact u10312
  · exact u10313

def b27894 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 140 73 145 48 98 162 290), lower := (rows 37 322 140 73 145 48 64 128 256), losses := [] }

theorem u27894 : Upper (D 7) (R 7) [36,320,136,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27894 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27895 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 140 73 146 33 114 178 306), lower := (rows 37 322 140 73 146 33 64 128 256), losses := [] }

theorem u27895 : Upper (D 7) (R 7) [36,320,136,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27896 : Route 9 := (fun mask => (mask,id))

def c27896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27896 : Upper (D 7) (R 7) [36,320,136,65,130,2] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,130,2] 13 (by decide) (choices 1) [1,16,32] r27896 c27896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10314
  · exact u10315
  · exact u10316

def r27897 : Route 9 := (fun mask => (mask,id))

def c27897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27897 : Upper (D 7) (R 7) [36,320,136,65,130,16] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,130,16] 13 (by decide) (choices 1) [1,2,32] r27897 c27897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10317
  · exact u10318
  · exact u10319

def b27898 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 140 73 176 33 82 146 274), lower := (rows 37 322 140 73 176 33 64 128 256), losses := [] }

theorem u27898 : Upper (D 7) (R 7) [36,320,136,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27899 : Route 9 := (fun mask => (mask,id))

def c27899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27899 : Upper (D 7) (R 7) [36,320,136,65,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65,160,2] 13 (by decide) (choices 1) [1,2,16] r27899 c27899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10320
  · exact u10321
  · exact u10322

#print axioms u27899
end Delivery.IrregularNine14.P07
