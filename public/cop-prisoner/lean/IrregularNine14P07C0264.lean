import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0056
import IrregularNine14P07C0057

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15840 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 200 273 34 240 176 432), lower := (rows 13 35 70 200 273 34 64 128 256), losses := [] }

theorem u15840 : Upper (D 7) (R 7) [12,33,66,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15841 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 13 35 70 200 273 48 226 162 418), lower := (rows 13 35 70 200 273 48 64 128 256), losses := [] }

theorem u15841 : Upper (D 7) (R 7) [12,33,66,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15841 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15842 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 340, targets := 128 }], pairs := [(1,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 70 200 273 160 114 178 306), lower := (rows 13 35 70 200 273 160 64 128 256), losses := [] }

theorem u15842 : Upper (D 7) (R 7) [12,33,66,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15843 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 200 274 33 240 176 432), lower := (rows 13 35 70 200 274 33 64 128 256), losses := [] }

theorem u15843 : Upper (D 7) (R 7) [12,33,66,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15844 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 200, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 13 35 70 200 274 48 225 161 417), lower := (rows 13 35 70 200 274 48 64 128 256), losses := [] }

theorem u15844 : Upper (D 7) (R 7) [12,33,66,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15844 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15845 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 340, targets := 128 }], pairs := [(1,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 70 200 274 160 113 177 305), lower := (rows 13 35 70 200 274 160 64 128 256), losses := [] }

theorem u15845 : Upper (D 7) (R 7) [12,33,66,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15846 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 200 304 33 210 146 402), lower := (rows 13 35 70 200 304 33 64 128 256), losses := [] }

theorem u15846 : Upper (D 7) (R 7) [12,33,66,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15847 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 200 304 34 209 145 401), lower := (rows 13 35 70 200 304 34 64 128 256), losses := [] }

theorem u15847 : Upper (D 7) (R 7) [12,33,66,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15848 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 13 35 70 200 304 48 195 131 387), lower := (rows 13 35 70 200 304 48 64 128 256), losses := [] }

theorem u15848 : Upper (D 7) (R 7) [12,33,66,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15848 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15849 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 340, targets := 128 }], pairs := [(1,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 70 200 304 160 83 147 275), lower := (rows 13 35 70 200 304 160 64 128 256), losses := [] }

theorem u15849 : Upper (D 7) (R 7) [12,33,66,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15850 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 200 400 33 114 178 306), lower := (rows 13 35 70 200 400 33 64 128 256), losses := [] }

theorem u15850 : Upper (D 7) (R 7) [12,33,66,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15851 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 200 400 34 113 177 305), lower := (rows 13 35 70 200 400 34 64 128 256), losses := [] }

theorem u15851 : Upper (D 7) (R 7) [12,33,66,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15852 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 68, targets := 128 }], pairs := [(1,6),(2,7),(4,6)], upper := (rows 13 35 70 200 400 48 99 163 291), lower := (rows 13 35 70 200 400 48 64 128 256), losses := [] }

theorem u15852 : Upper (D 7) (R 7) [12,33,66,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15852 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15853 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 70 265 112 34 208 144 400), lower := (rows 13 35 70 265 112 34 64 128 256), losses := [] }

theorem u15853 : Upper (D 7) (R 7) [12,33,66,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15854 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 265 112 48 194 130 386), lower := (rows 13 35 70 265 112 48 64 128 256), losses := [] }

theorem u15854 : Upper (D 7) (R 7) [12,33,66,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15854 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15855 : Route 9 := (fun mask => (mask,id))

def c15855 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15855 : Upper (D 7) (R 7) [12,33,66,257,96,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,257,96,128] 13 (by decide) (choices 1) [2,16,128] r15855 c15855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3402
  · exact u3403
  · exact u3404

def b15856 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 456, targets := 2 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 13 35 70 265 146 48 224 224 480), lower := (rows 13 35 70 265 146 48 64 128 256), losses := [] }

theorem u15856 : Upper (D 7) (R 7) [12,33,66,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15856 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15857 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 70 265 146 96 240 176 432), lower := (rows 13 35 70 265 146 96 64 128 256), losses := [] }

theorem u15857 : Upper (D 7) (R 7) [12,33,66,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15858 : Route 9 := (fun mask => (mask,id))

def c15858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15858 : Upper (D 7) (R 7) [12,33,66,257,130,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,257,130,128] 13 (by decide) (choices 1) [16,32] r15858 c15858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3405
  · exact u3406

def b15859 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 70 265 176 34 208 208 464), lower := (rows 13 35 70 265 176 34 64 128 256), losses := [] }

theorem u15859 : Upper (D 7) (R 7) [12,33,66,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15860 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 265 176 48 194 194 450), lower := (rows 13 35 70 265 176 48 64 128 256), losses := [] }

theorem u15860 : Upper (D 7) (R 7) [12,33,66,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15860 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15861 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 70 265 176 96 210 146 402), lower := (rows 13 35 70 265 176 96 64 128 256), losses := [] }

theorem u15861 : Upper (D 7) (R 7) [12,33,66,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15862 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 265 176 160 82 210 338), lower := (rows 13 35 70 265 176 160 64 128 256), losses := [] }

theorem u15862 : Upper (D 7) (R 7) [12,33,66,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15863 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 70 265 208 34 240 176 432), lower := (rows 13 35 70 265 208 34 64 128 256), losses := [] }

theorem u15863 : Upper (D 7) (R 7) [12,33,66,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15864 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,0),(3,6),(4,0)], upper := (rows 13 35 70 265 208 48 226 162 418), lower := (rows 13 35 70 265 208 48 64 128 256), losses := [] }

theorem u15864 : Upper (D 7) (R 7) [12,33,66,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15864 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15865 : Route 9 := (fun mask => (mask,id))

def c15865 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15865 : Upper (D 7) (R 7) [12,33,66,257,192,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,257,192,128] 13 (by decide) (choices 1) [2,16,32] r15865 c15865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3407
  · exact u3408
  · exact u3409

def b15866 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 13 35 70 266 81 48 224 160 416), lower := (rows 13 35 70 266 81 48 64 128 256), losses := [] }

theorem u15866 : Upper (D 7) (R 7) [12,33,66,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15866 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15867 : Route 9 := (fun mask => (mask,id))

def c15867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u15867 : Upper (D 7) (R 7) [12,33,66,258,65,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,65,128] 13 (by decide) (choices 1) [16,32,128] r15867 c15867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3410
  · exact u3411
  · exact u3412

def b15868 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 266 112 33 208 144 400), lower := (rows 13 35 70 266 112 33 64 128 256), losses := [] }

theorem u15868 : Upper (D 7) (R 7) [12,33,66,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15869 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 266 112 48 193 129 385), lower := (rows 13 35 70 266 112 48 64 128 256), losses := [] }

theorem u15869 : Upper (D 7) (R 7) [12,33,66,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15869 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15870 : Route 9 := (fun mask => (mask,id))

def c15870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15870 : Upper (D 7) (R 7) [12,33,66,258,96,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,96,128] 13 (by decide) (choices 1) [1,16,128] r15870 c15870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3413
  · exact u3414
  · exact u3415

def b15871 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 13 35 70 266 145 48 224 224 480), lower := (rows 13 35 70 266 145 48 64 128 256), losses := [] }

theorem u15871 : Upper (D 7) (R 7) [12,33,66,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15871 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15872 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,6),(3,6),(4,1),(4,6)], upper := (rows 13 35 70 266 145 96 240 176 432), lower := (rows 13 35 70 266 145 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 22 32 0 130 258), good := (rows 29 443 415 410 145 32 0 128 256) }] }

theorem u15872 : Upper (D 7) (R 7) [12,33,66,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15873 : Route 9 := (fun mask => (mask,id))

def c15873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15873 : Upper (D 7) (R 7) [12,33,66,258,129,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,129,128] 13 (by decide) (choices 1) [16,32] r15873 c15873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3416
  · exact u3417

def b15874 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 266 176 33 208 208 464), lower := (rows 13 35 70 266 176 33 64 128 256), losses := [] }

theorem u15874 : Upper (D 7) (R 7) [12,33,66,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15875 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 266 176 48 193 193 449), lower := (rows 13 35 70 266 176 48 64 128 256), losses := [] }

theorem u15875 : Upper (D 7) (R 7) [12,33,66,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15875 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15876 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,6),(3,6),(4,1),(4,6)], upper := (rows 13 35 70 266 176 96 209 145 401), lower := (rows 13 35 70 266 176 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 18 32 0 134 262), good := (rows 397 443 415 410 176 32 0 128 256) }] }

theorem u15876 : Upper (D 7) (R 7) [12,33,66,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15877 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 266 176 160 81 209 337), lower := (rows 13 35 70 266 176 160 64 128 256), losses := [] }

theorem u15877 : Upper (D 7) (R 7) [12,33,66,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15878 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 266 208 33 240 176 432), lower := (rows 13 35 70 266 208 33 64 128 256), losses := [] }

theorem u15878 : Upper (D 7) (R 7) [12,33,66,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15879 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 392, targets := 64 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 13 35 70 266 208 48 225 161 417), lower := (rows 13 35 70 266 208 48 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 16 48 0 130 258), good := (rows 13 427 399 394 176 48 0 128 256) }] }

theorem u15879 : Upper (D 7) (R 7) [12,33,66,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15879 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15880 : Route 9 := (fun mask => (mask,id))

def c15880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15880 : Upper (D 7) (R 7) [12,33,66,258,192,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,192,128] 13 (by decide) (choices 1) [1,16,32] r15880 c15880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3418
  · exact u3419
  · exact u3420

def b15881 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 472, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,1),(3,6),(4,1)], upper := (rows 13 35 70 280 81 34 224 160 416), lower := (rows 13 35 70 280 81 34 64 128 256), losses := [] }

theorem u15881 : Upper (D 7) (R 7) [12,33,66,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15882 : Route 9 := (fun mask => (mask,id))

def c15882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15882 : Upper (D 7) (R 7) [12,33,66,272,65,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,65,128] 13 (by decide) (choices 1) [2,32,128] r15882 c15882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3421
  · exact u3422
  · exact u3423

def b15883 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 280 112 33 194 130 386), lower := (rows 13 35 70 280 112 33 64 128 256), losses := [] }

theorem u15883 : Upper (D 7) (R 7) [12,33,66,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15884 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 472, targets := 2 },{ cop := 2, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 13 35 70 280 112 34 193 129 385), lower := (rows 13 35 70 280 112 34 64 128 256), losses := [] }

theorem u15884 : Upper (D 7) (R 7) [12,33,66,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15885 : Route 9 := (fun mask => (mask,id))

def c15885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15885 : Upper (D 7) (R 7) [12,33,66,272,96,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,96,128] 13 (by decide) (choices 1) [1,2,128] r15885 c15885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3424
  · exact u3425
  · exact u3426

def b15886 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 280 145 34 224 224 480), lower := (rows 13 35 70 280 145 34 64 128 256), losses := [] }

theorem u15886 : Upper (D 7) (R 7) [12,33,66,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15887 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(0,6),(2,0),(3,6),(4,6)], upper := (rows 13 35 70 280 145 96 226 162 418), lower := (rows 13 35 70 280 145 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 22 32 0 130 258), good := (rows 29 443 415 280 145 32 0 128 256) }] }

theorem u15887 : Upper (D 7) (R 7) [12,33,66,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15888 : Route 9 := (fun mask => (mask,id))

def c15888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15888 : Upper (D 7) (R 7) [12,33,66,272,129,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,129,128] 13 (by decide) (choices 1) [2,32] r15888 c15888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3427
  · exact u3428

def b15889 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 280 146 33 224 224 480), lower := (rows 13 35 70 280 146 33 64 128 256), losses := [] }

theorem u15889 : Upper (D 7) (R 7) [12,33,66,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15890 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,6)], upper := (rows 13 35 70 280 146 96 225 161 417), lower := (rows 13 35 70 280 146 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 119 67 131 259), good := (rows 493 481 484 312 504 96 96 128 256) },{ target := 6, region := (rows 5 2 4 30 22 32 0 130 258), good := (rows 29 443 415 280 410 32 0 128 256) }] }

theorem u15890 : Upper (D 7) (R 7) [12,33,66,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15891 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 68, targets := 128 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 13 35 70 280 146 160 97 225 353), lower := (rows 13 35 70 280 146 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 183 67 131 259), good := (rows 493 481 484 312 504 160 64 160 256) },{ target := 7, region := (rows 25 2 22 24 16 32 66 0 258), good := (rows 13 359 326 285 351 32 64 0 256) }] }

theorem u15891 : Upper (D 7) (R 7) [12,33,66,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15892 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 280 176 33 194 194 450), lower := (rows 13 35 70 280 176 33 64 128 256), losses := [] }

theorem u15892 : Upper (D 7) (R 7) [12,33,66,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15893 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 280 176 34 193 193 449), lower := (rows 13 35 70 280 176 34 64 128 256), losses := [] }

theorem u15893 : Upper (D 7) (R 7) [12,33,66,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15894 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 1, region := 196, targets := 32 }], pairs := [(0,6),(2,5),(3,6),(4,6)], upper := (rows 13 35 70 280 176 96 195 131 387), lower := (rows 13 35 70 280 176 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 18 32 0 134 262), good := (rows 397 443 415 280 176 32 0 128 256) }] }

theorem u15894 : Upper (D 7) (R 7) [12,33,66,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15895 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 280 176 160 67 195 323), lower := (rows 13 35 70 280 176 160 64 128 256), losses := [] }

theorem u15895 : Upper (D 7) (R 7) [12,33,66,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15896 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 280 208 33 226 162 418), lower := (rows 13 35 70 280 208 33 64 128 256), losses := [] }

theorem u15896 : Upper (D 7) (R 7) [12,33,66,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15897 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 472, targets := 2 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 280 208 34 225 161 417), lower := (rows 13 35 70 280 208 34 64 128 256), losses := [] }

theorem u15897 : Upper (D 7) (R 7) [12,33,66,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15898 : Route 9 := (fun mask => (mask,id))

def c15898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15898 : Upper (D 7) (R 7) [12,33,66,272,192,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,192,128] 13 (by decide) (choices 1) [1,2,32] r15898 c15898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3429
  · exact u3430
  · exact u3431

def b15899 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 70 296 145 34 208 208 464), lower := (rows 13 35 70 296 145 34 64 128 256), losses := [] }

theorem u15899 : Upper (D 7) (R 7) [12,33,66,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15899
end Delivery.IrregularNine14.P07
