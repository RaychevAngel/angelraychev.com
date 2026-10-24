import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0004

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3840 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 168 336 34 65 130 386), lower := (rows 13 98 21 168 336 34 65 128 256), losses := [] }

theorem u3840 : Upper (D 7) (R 7) [12,96,17,160,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3841 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 21 168 336 34 66 129 385), lower := (rows 13 98 21 168 336 34 66 128 256), losses := [] }

theorem u3841 : Upper (D 7) (R 7) [12,96,17,160,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3842 : Route 9 := (fun mask => (mask,id))

def c3842 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3842 : Upper (D 7) (R 7) [12,96,17,160,320,2,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,320,2,128] 13 (by decide) (choices 1) [1,2] r3842 c3842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u260
  · exact u261

def b3843 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 168 400 34 65 194 322), lower := (rows 13 98 21 168 400 34 65 128 256), losses := [] }

theorem u3843 : Upper (D 7) (R 7) [12,96,17,160,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3844 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 21 168 400 34 66 193 321), lower := (rows 13 98 21 168 400 34 66 128 256), losses := [] }

theorem u3844 : Upper (D 7) (R 7) [12,96,17,160,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3845 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 21 266 146 33 96 192 448), lower := (rows 13 98 21 266 146 33 96 128 256), losses := [] }

theorem u3845 : Upper (D 7) (R 7) [12,96,17,258,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3846 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,0)], upper := (rows 13 98 21 266 146 33 192 224 352), lower := (rows 13 98 21 266 146 33 192 128 256), losses := [] }

theorem u3846 : Upper (D 7) (R 7) [12,96,17,258,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3847 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 266 146 96 192 161 289), lower := (rows 13 98 21 266 146 96 192 128 256), losses := [] }

theorem u3847 : Upper (D 7) (R 7) [12,96,17,258,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3848 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 266 176 34 65 192 448), lower := (rows 13 98 21 266 176 34 65 128 256), losses := [] }

theorem u3848 : Upper (D 7) (R 7) [12,96,17,258,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3849 : Route 9 := (fun mask => (mask,id))

def c3849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3849 : Upper (D 7) (R 7) [12,96,17,258,160,2,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,258,160,2,128] 13 (by decide) (choices 1) [1,64] r3849 c3849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u262
  · exact u263

def b3850 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 296 146 34 65 192 448), lower := (rows 13 98 21 296 146 34 65 128 256), losses := [] }

theorem u3850 : Upper (D 7) (R 7) [12,96,17,288,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3851 : Route 9 := (fun mask => (mask,id))

def c3851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3851 : Upper (D 7) (R 7) [12,96,17,288,130,2,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,130,2,128] 13 (by decide) (choices 1) [1,64] r3851 c3851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u264
  · exact u265

def b3852 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 21 296 146 160 65 194 322), lower := (rows 13 98 21 296 146 160 65 128 256), losses := [] }

theorem u3852 : Upper (D 7) (R 7) [12,96,17,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3853 : Route 9 := (fun mask => (mask,id))

def c3853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3853 : Upper (D 7) (R 7) [12,96,17,288,130,128,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,130,128,2] 13 (by decide) (choices 1) [1,64] r3853 c3853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u266
  · exact u267

def b3854 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 296 208 34 65 130 386), lower := (rows 13 98 21 296 208 34 65 128 256), losses := [] }

theorem u3854 : Upper (D 7) (R 7) [12,96,17,288,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3855 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 21 296 208 34 66 129 385), lower := (rows 13 98 21 296 208 34 66 128 256), losses := [] }

theorem u3855 : Upper (D 7) (R 7) [12,96,17,288,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3856 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 21 296 208 34 192 131 259), lower := (rows 13 98 21 296 208 34 192 128 256), losses := [] }

theorem u3856 : Upper (D 7) (R 7) [12,96,17,288,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3857 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 21 296 208 160 65 130 258), lower := (rows 13 98 21 296 208 160 65 128 256), losses := [] }

theorem u3857 : Upper (D 7) (R 7) [12,96,17,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3858 : Route 9 := (fun mask => (mask,id))

def c3858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3858 : Upper (D 7) (R 7) [12,96,17,288,192,128,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,192,128,2] 13 (by decide) (choices 1) [1,2] r3858 c3858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u268
  · exact u269

def b3859 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 392 146 33 66 224 352), lower := (rows 13 98 21 392 146 33 66 128 256), losses := [] }

theorem u3859 : Upper (D 7) (R 7) [12,96,17,384,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3860 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 21 392 146 34 96 193 321), lower := (rows 13 98 21 392 146 34 96 128 256), losses := [] }

theorem u3860 : Upper (D 7) (R 7) [12,96,17,384,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3861 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 392 176 34 65 194 322), lower := (rows 13 98 21 392 176 34 65 128 256), losses := [] }

theorem u3861 : Upper (D 7) (R 7) [12,96,17,384,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3862 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 21 392 176 34 66 193 321), lower := (rows 13 98 21 392 176 34 66 128 256), losses := [] }

theorem u3862 : Upper (D 7) (R 7) [12,96,17,384,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3863 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 13 98 22 41 208 288 65 130 386), lower := (rows 13 98 22 41 208 288 65 128 256), losses := [] }

theorem u3863 : Upper (D 7) (R 7) [12,96,18,33,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3863 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3864 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 13 98 22 41 208 288 66 129 385), lower := (rows 13 98 22 41 208 288 66 128 256), losses := [] }

theorem u3864 : Upper (D 7) (R 7) [12,96,18,33,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3864 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3865 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 22 41 208 288 192 131 259), lower := (rows 13 98 22 41 208 288 192 128 256), losses := [] }

theorem u3865 : Upper (D 7) (R 7) [12,96,18,33,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3865 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3866 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,0)], upper := (rows 13 98 22 41 273 160 66 192 448), lower := (rows 13 98 22 41 273 160 66 128 256), losses := [{ target := 1, region := (rows 5 0 4 13 20 230 64 194 322), good := (rows 61 480 445 41 281 160 480 160 256) }] }

theorem u3866 : Upper (D 7) (R 7) [12,96,18,33,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3867 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 22 41 273 160 192 194 322), lower := (rows 13 98 22 41 273 160 192 128 256), losses := [] }

theorem u3867 : Upper (D 7) (R 7) [12,96,18,33,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3868 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 438, targets := 1 },{ cop := 1, region := 404, targets := 32 }], pairs := [(1,0),(2,0),(2,5),(4,0)], upper := (rows 13 98 22 41 336 160 65 130 386), lower := (rows 13 98 22 41 336 160 65 128 256), losses := [] }

theorem u3868 : Upper (D 7) (R 7) [12,96,18,33,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3869 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 169, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 22 41 336 160 66 129 385), lower := (rows 13 98 22 41 336 160 66 128 256), losses := [] }

theorem u3869 : Upper (D 7) (R 7) [12,96,18,33,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3870 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 22 41 336 160 192 131 259), lower := (rows 13 98 22 41 336 160 192 128 256), losses := [] }

theorem u3870 : Upper (D 7) (R 7) [12,96,18,33,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3871 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,0)], upper := (rows 13 98 22 137 273 34 192 224 352), lower := (rows 13 98 22 137 273 34 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 20 32 238 162 290), good := (rows 93 480 477 201 273 480 192 192 256) }] }

theorem u3871 : Upper (D 7) (R 7) [12,96,18,129,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3872 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 137 273 96 192 162 290), lower := (rows 13 98 22 137 273 96 192 128 256), losses := [] }

theorem u3872 : Upper (D 7) (R 7) [12,96,18,129,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3873 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 },{ cop := 1, region := 276, targets := 128 }], pairs := [(1,0),(2,0),(2,7),(4,0)], upper := (rows 13 98 22 137 304 160 65 194 322), lower := (rows 13 98 22 137 304 160 65 128 256), losses := [] }

theorem u3873 : Upper (D 7) (R 7) [12,96,18,129,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3874 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 70, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 22 137 304 160 66 193 321), lower := (rows 13 98 22 137 304 160 66 128 256), losses := [] }

theorem u3874 : Upper (D 7) (R 7) [12,96,18,129,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3875 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 13 98 22 137 400 33 66 224 352), lower := (rows 13 98 22 137 400 33 66 128 256), losses := [] }

theorem u3875 : Upper (D 7) (R 7) [12,96,18,129,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3876 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 22 137 400 34 96 193 321), lower := (rows 13 98 22 137 400 34 96 128 256), losses := [] }

theorem u3876 : Upper (D 7) (R 7) [12,96,18,129,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3877 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 22 138 273 33 96 192 448), lower := (rows 13 98 22 138 273 33 96 128 256), losses := [] }

theorem u3877 : Upper (D 7) (R 7) [12,96,18,130,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3878 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 202, targets := 1 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,7),(1,0),(3,0),(4,1)], upper := (rows 13 98 22 138 273 33 192 224 352), lower := (rows 13 98 22 138 273 33 192 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 24 57 64 0 258), good := (rows 61 354 310 319 305 33 64 0 256) }] }

theorem u3878 : Upper (D 7) (R 7) [12,96,18,130,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3879 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 138 273 96 192 161 289), lower := (rows 13 98 22 138 273 96 192 128 256), losses := [] }

theorem u3879 : Upper (D 7) (R 7) [12,96,18,130,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3880 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(2,0),(3,0),(4,0)], upper := (rows 13 98 22 138 304 33 65 192 448), lower := (rows 13 98 22 138 304 33 65 128 256), losses := [] }

theorem u3880 : Upper (D 7) (R 7) [12,96,18,130,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3881 : Route 9 := (fun mask => (mask,id))

def c3881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3881 : Upper (D 7) (R 7) [12,96,18,130,288,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,288,1,128] 13 (by decide) (choices 1) [1,64] r3881 c3881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u270
  · exact u271

def b3882 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(0,7),(3,5),(4,1)], upper := (rows 13 98 22 138 304 160 65 193 321), lower := (rows 13 98 22 138 304 160 65 128 256), losses := [{ target := 7, region := (rows 9 2 14 8 18 32 73 0 329), good := (rows 333 374 22 351 304 32 321 0 256) }] }

theorem u3882 : Upper (D 7) (R 7) [12,96,18,130,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3883 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 496, targets := 2 }], pairs := [(2,0),(3,0),(4,0),(4,1)], upper := (rows 13 98 22 138 400 33 65 224 352), lower := (rows 13 98 22 138 400 33 65 128 256), losses := [] }

theorem u3883 : Upper (D 7) (R 7) [12,96,18,130,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3884 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 22 138 400 33 96 193 321), lower := (rows 13 98 22 138 400 33 96 128 256), losses := [] }

theorem u3884 : Upper (D 7) (R 7) [12,96,18,130,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3885 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 22 168 81 288 65 130 386), lower := (rows 13 98 22 168 81 288 65 128 256), losses := [] }

theorem u3885 : Upper (D 7) (R 7) [12,96,18,160,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3885 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3886 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 13 98 22 168 81 288 66 129 385), lower := (rows 13 98 22 168 81 288 66 128 256), losses := [] }

theorem u3886 : Upper (D 7) (R 7) [12,96,18,160,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3886 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3887 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 290, targets := 128 }], pairs := [(0,6),(1,7),(3,6)], upper := (rows 13 98 22 168 81 288 192 131 259), lower := (rows 13 98 22 168 81 288 192 128 256), losses := [] }

theorem u3887 : Upper (D 7) (R 7) [12,96,18,160,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3887 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3888 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 358, targets := 128 },{ cop := 6, region := 290, targets := 1 }], pairs := [(1,0),(1,7),(2,7)], upper := (rows 13 98 22 168 145 288 65 194 322), lower := (rows 13 98 22 168 145 288 65 128 256), losses := [] }

theorem u3888 : Upper (D 7) (R 7) [12,96,18,160,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3888 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3889 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7)], upper := (rows 13 98 22 168 145 288 66 193 321), lower := (rows 13 98 22 168 145 288 66 128 256), losses := [] }

theorem u3889 : Upper (D 7) (R 7) [12,96,18,160,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3889 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3890 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 404, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,0)], upper := (rows 13 98 22 168 208 33 65 386 258), lower := (rows 13 98 22 168 208 33 65 128 256), losses := [] }

theorem u3890 : Upper (D 7) (R 7) [12,96,18,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3891 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 22 168 208 33 66 385 257), lower := (rows 13 98 22 168 208 33 66 128 256), losses := [] }

theorem u3891 : Upper (D 7) (R 7) [12,96,18,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3892 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 0, region := 354, targets := 128 }], pairs := [(0,6),(1,7),(3,6)], upper := (rows 13 98 22 168 208 33 320 131 259), lower := (rows 13 98 22 168 208 33 320 128 256), losses := [] }

theorem u3892 : Upper (D 7) (R 7) [12,96,18,160,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3892 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3893 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 102, targets := 128 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 22 168 273 33 66 192 448), lower := (rows 13 98 22 168 273 33 66 128 256), losses := [] }

theorem u3893 : Upper (D 7) (R 7) [12,96,18,160,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3894 : Route 9 := (fun mask => (mask,id))

def c3894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3894 : Upper (D 7) (R 7) [12,96,18,160,257,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,257,1,128] 13 (by decide) (choices 1) [2,64] r3894 c3894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u272
  · exact u273

def b3895 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 404, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,0)], upper := (rows 13 98 22 168 336 33 65 130 386), lower := (rows 13 98 22 168 336 33 65 128 256), losses := [] }

theorem u3895 : Upper (D 7) (R 7) [12,96,18,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3896 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 169, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 22 168 336 33 66 129 385), lower := (rows 13 98 22 168 336 33 66 128 256), losses := [] }

theorem u3896 : Upper (D 7) (R 7) [12,96,18,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3897 : Route 9 := (fun mask => (mask,id))

def c3897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3897 : Upper (D 7) (R 7) [12,96,18,160,320,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,320,1,128] 13 (by decide) (choices 1) [1,2] r3897 c3897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u274
  · exact u275

def b3898 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 404, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,0)], upper := (rows 13 98 22 168 400 33 65 194 322), lower := (rows 13 98 22 168 400 33 65 128 256), losses := [] }

theorem u3898 : Upper (D 7) (R 7) [12,96,18,160,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3899 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,5),(4,5)], upper := (rows 13 98 22 168 400 33 66 193 321), lower := (rows 13 98 22 168 400 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 6 8 49 0 70 129 257), good := (rows 477 86 86 152 400 401 70 128 256) }] }

theorem u3899 : Upper (D 7) (R 7) [12,96,18,160,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3899
end Delivery.IrregularNine14.P07
