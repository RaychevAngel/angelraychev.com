import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0086

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18840 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 392 176 48 67 195 323), lower := (rows 35 70 13 392 176 48 64 128 256), losses := [] }

theorem u18840 : Upper (D 7) (R 7) [34,68,9,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18840 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18841 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 392 176 96 83 147 275), lower := (rows 35 70 13 392 176 96 64 128 256), losses := [] }

theorem u18841 : Upper (D 7) (R 7) [34,68,9,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18842 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 392 208 33 114 178 306), lower := (rows 35 70 13 392 208 33 64 128 256), losses := [] }

theorem u18842 : Upper (D 7) (R 7) [34,68,9,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18843 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 392 208 34 113 177 305), lower := (rows 35 70 13 392 208 34 64 128 256), losses := [] }

theorem u18843 : Upper (D 7) (R 7) [34,68,9,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18844 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(1,7),(2,6),(3,6)], upper := (rows 35 70 13 392 208 48 99 163 291), lower := (rows 35 70 13 392 208 48 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 48 65 0 257), good := (rows 355 70 335 264 112 48 64 0 256) }] }

theorem u18844 : Upper (D 7) (R 7) [34,68,9,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18844 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18845 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 14 25 208 33 480 416 416), lower := (rows 35 70 14 25 208 33 64 128 256), losses := [] }

theorem u18845 : Upper (D 7) (R 7) [34,68,10,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18846 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,7),(3,1),(4,1)], upper := (rows 35 70 14 25 208 160 353 417 289), lower := (rows 35 70 14 25 208 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 32 65 0 257), good := (rows 355 70 14 351 80 32 64 0 256) }] }

theorem u18846 : Upper (D 7) (R 7) [34,68,10,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18847 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 70 14 25 208 288 225 161 417), lower := (rows 35 70 14 25 208 288 64 128 256), losses := [] }

theorem u18847 : Upper (D 7) (R 7) [34,68,10,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18847 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18848 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 14 25 336 33 224 160 416), lower := (rows 35 70 14 25 336 33 64 128 256), losses := [] }

theorem u18848 : Upper (D 7) (R 7) [34,68,10,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18849 : Route 9 := (fun mask => (mask,id))

def c18849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18849 : Upper (D 7) (R 7) [34,68,10,17,320,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,17,320,128] 13 (by decide) (choices 1) [1,32,128] r18849 c18849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5175
  · exact u5176
  · exact u5177

def b18850 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 25 400 33 224 224 480), lower := (rows 35 70 14 25 400 33 64 128 256), losses := [] }

theorem u18850 : Upper (D 7) (R 7) [34,68,10,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18851 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 25 400 96 225 161 417), lower := (rows 35 70 14 25 400 96 64 128 256), losses := [] }

theorem u18851 : Upper (D 7) (R 7) [34,68,10,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18852 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(1,7),(2,7),(3,1),(4,1)], upper := (rows 35 70 14 25 400 160 97 225 353), lower := (rows 35 70 14 25 400 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 32 65 0 257), good := (rows 355 70 14 351 272 32 64 0 256) }] }

theorem u18852 : Upper (D 7) (R 7) [34,68,10,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18853 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 56 400 33 193 193 449), lower := (rows 35 70 14 56 400 33 64 128 256), losses := [] }

theorem u18853 : Upper (D 7) (R 7) [34,68,10,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18854 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 56 400 96 193 129 385), lower := (rows 35 70 14 56 400 96 64 128 256), losses := [] }

theorem u18854 : Upper (D 7) (R 7) [34,68,10,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18855 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 14 56 400 160 65 193 321), lower := (rows 35 70 14 56 400 160 64 128 256), losses := [] }

theorem u18855 : Upper (D 7) (R 7) [34,68,10,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18856 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 137 81 48 480 416 416), lower := (rows 35 70 14 137 81 48 64 128 256), losses := [] }

theorem u18856 : Upper (D 7) (R 7) [34,68,10,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18856 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18857 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 },{ cop := 4, region := 424, targets := 64 }], pairs := [(3,1),(3,6),(4,1),(4,7)], upper := (rows 35 70 14 137 81 160 368 432 304), lower := (rows 35 70 14 137 81 160 64 128 256), losses := [] }

theorem u18857 : Upper (D 7) (R 7) [34,68,10,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18858 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 4, region := 424, targets := 64 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 70 14 137 81 288 240 176 432), lower := (rows 35 70 14 137 81 288 64 128 256), losses := [] }

theorem u18858 : Upper (D 7) (R 7) [34,68,10,129,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18858 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18859 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 137 112 33 464 400 400), lower := (rows 35 70 14 137 112 33 64 128 256), losses := [] }

theorem u18859 : Upper (D 7) (R 7) [34,68,10,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18860 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 14 137 112 48 449 385 385), lower := (rows 35 70 14 137 112 48 64 128 256), losses := [] }

theorem u18860 : Upper (D 7) (R 7) [34,68,10,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18860 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18861 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 137 112 160 337 401 273), lower := (rows 35 70 14 137 112 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 35 7 47 169 48 160 0 160 256) }] }

theorem u18861 : Upper (D 7) (R 7) [34,68,10,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18862 : Route 9 := (fun mask => (mask,id))

def c18862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18862 : Upper (D 7) (R 7) [34,68,10,129,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,96,256] 13 (by decide) (choices 1) [1,16,128] r18862 c18862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5178
  · exact u5179
  · exact u5180

def b18863 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 137 176 33 336 464 336), lower := (rows 35 70 14 137 176 33 64 128 256), losses := [] }

theorem u18863 : Upper (D 7) (R 7) [34,68,10,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18864 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 14 137 176 48 321 449 321), lower := (rows 35 70 14 137 176 48 64 128 256), losses := [] }

theorem u18864 : Upper (D 7) (R 7) [34,68,10,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18864 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18865 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 137 176 96 337 401 273), lower := (rows 35 70 14 137 176 96 64 128 256), losses := [] }

theorem u18865 : Upper (D 7) (R 7) [34,68,10,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18866 : Route 9 := (fun mask => (mask,id))

def c18866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18866 : Upper (D 7) (R 7) [34,68,10,129,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,160,256] 13 (by decide) (choices 1) [1,16] r18866 c18866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5181
  · exact u5182

def b18867 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 137 208 33 368 432 304), lower := (rows 35 70 14 137 208 33 64 128 256), losses := [] }

theorem u18867 : Upper (D 7) (R 7) [34,68,10,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18868 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 137 208 48 353 417 289), lower := (rows 35 70 14 137 208 48 64 128 256), losses := [] }

theorem u18868 : Upper (D 7) (R 7) [34,68,10,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18868 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18869 : Route 9 := (fun mask => (mask,id))

def c18869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18869 : Upper (D 7) (R 7) [34,68,10,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129,192,256] 13 (by decide) (choices 1) [1,16,32] r18869 c18869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5183
  · exact u5184
  · exact u5185

def b18870 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 35 70 14 137 273 48 224 224 480), lower := (rows 35 70 14 137 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 113 177 305), good := (rows 482 70 14 462 496 496 64 128 256) }] }

theorem u18870 : Upper (D 7) (R 7) [34,68,10,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18870 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18871 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 137 273 96 240 176 432), lower := (rows 35 70 14 137 273 96 64 128 256), losses := [] }

theorem u18871 : Upper (D 7) (R 7) [34,68,10,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18872 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 137 273 160 112 240 368), lower := (rows 35 70 14 137 273 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 35 7 47 169 273 160 0 160 256) }] }

theorem u18872 : Upper (D 7) (R 7) [34,68,10,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18873 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 137 304 33 208 208 464), lower := (rows 35 70 14 137 304 33 64 128 256), losses := [] }

theorem u18873 : Upper (D 7) (R 7) [34,68,10,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18874 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 14 137 304 48 193 193 449), lower := (rows 35 70 14 137 304 48 64 128 256), losses := [] }

theorem u18874 : Upper (D 7) (R 7) [34,68,10,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18874 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18875 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 137 304 96 209 145 401), lower := (rows 35 70 14 137 304 96 64 128 256), losses := [] }

theorem u18875 : Upper (D 7) (R 7) [34,68,10,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18876 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 137 304 160 81 209 337), lower := (rows 35 70 14 137 304 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 35 7 47 169 304 160 0 160 256) }] }

theorem u18876 : Upper (D 7) (R 7) [34,68,10,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18877 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 137 336 33 240 176 432), lower := (rows 35 70 14 137 336 33 64 128 256), losses := [] }

theorem u18877 : Upper (D 7) (R 7) [34,68,10,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18878 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 137 336 48 225 161 417), lower := (rows 35 70 14 137 336 48 64 128 256), losses := [] }

theorem u18878 : Upper (D 7) (R 7) [34,68,10,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18878 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18879 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 137 336 160 113 177 305), lower := (rows 35 70 14 137 336 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 35 7 47 169 272 160 0 160 256) }] }

theorem u18879 : Upper (D 7) (R 7) [34,68,10,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18880 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 137 400 33 112 240 368), lower := (rows 35 70 14 137 400 33 64 128 256), losses := [] }

theorem u18880 : Upper (D 7) (R 7) [34,68,10,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18881 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(1,7),(3,1),(4,1)], upper := (rows 35 70 14 137 400 48 97 225 353), lower := (rows 35 70 14 137 400 48 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 48 65 0 257), good := (rows 355 70 14 335 304 48 64 0 256) }] }

theorem u18881 : Upper (D 7) (R 7) [34,68,10,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18881 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18882 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 137 400 96 113 177 305), lower := (rows 35 70 14 137 400 96 64 128 256), losses := [] }

theorem u18882 : Upper (D 7) (R 7) [34,68,10,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18883 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 152 112 33 449 385 385), lower := (rows 35 70 14 152 112 33 64 128 256), losses := [] }

theorem u18883 : Upper (D 7) (R 7) [34,68,10,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18884 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 152 112 160 321 385 257), lower := (rows 35 70 14 152 112 160 64 128 256), losses := [] }

theorem u18884 : Upper (D 7) (R 7) [34,68,10,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18885 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 70 14 152 112 288 193 129 385), lower := (rows 35 70 14 152 112 288 64 128 256), losses := [] }

theorem u18885 : Upper (D 7) (R 7) [34,68,10,144,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18885 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18886 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 152 273 33 224 224 480), lower := (rows 35 70 14 152 273 33 64 128 256), losses := [] }

theorem u18886 : Upper (D 7) (R 7) [34,68,10,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18887 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 152 273 96 225 161 417), lower := (rows 35 70 14 152 273 96 64 128 256), losses := [] }

theorem u18887 : Upper (D 7) (R 7) [34,68,10,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18888 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 152 273 160 97 225 353), lower := (rows 35 70 14 152 273 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 35 7 47 184 273 160 0 160 256) }] }

theorem u18888 : Upper (D 7) (R 7) [34,68,10,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18889 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 152 304 33 193 193 449), lower := (rows 35 70 14 152 304 33 64 128 256), losses := [] }

theorem u18889 : Upper (D 7) (R 7) [34,68,10,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18890 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 152 304 96 193 129 385), lower := (rows 35 70 14 152 304 96 64 128 256), losses := [] }

theorem u18890 : Upper (D 7) (R 7) [34,68,10,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18891 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 152 304 160 65 193 321), lower := (rows 35 70 14 152 304 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 35 7 47 184 304 160 0 160 256) }] }

theorem u18891 : Upper (D 7) (R 7) [34,68,10,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18892 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 152 336 33 225 161 417), lower := (rows 35 70 14 152 336 33 64 128 256), losses := [] }

theorem u18892 : Upper (D 7) (R 7) [34,68,10,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18893 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 336, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 152 336 160 97 161 289), lower := (rows 35 70 14 152 336 160 64 128 256), losses := [] }

theorem u18893 : Upper (D 7) (R 7) [34,68,10,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18894 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 168 145 33 336 464 336), lower := (rows 35 70 14 168 145 33 64 128 256), losses := [] }

theorem u18894 : Upper (D 7) (R 7) [34,68,10,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18895 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 14 168 145 48 321 449 321), lower := (rows 35 70 14 168 145 48 64 128 256), losses := [] }

theorem u18895 : Upper (D 7) (R 7) [34,68,10,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18895 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18896 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 168 145 96 337 401 273), lower := (rows 35 70 14 168 145 96 64 128 256), losses := [] }

theorem u18896 : Upper (D 7) (R 7) [34,68,10,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18897 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 35 70 14 168 145 288 81 209 337), lower := (rows 35 70 14 168 145 288 64 128 256), losses := [] }

theorem u18897 : Upper (D 7) (R 7) [34,68,10,160,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18897 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18898 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 168 208 33 337 401 273), lower := (rows 35 70 14 168 208 33 64 128 256), losses := [] }

theorem u18898 : Upper (D 7) (R 7) [34,68,10,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18899 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 14 168 208 48 321 385 257), lower := (rows 35 70 14 168 208 48 64 128 256), losses := [] }

theorem u18899 : Upper (D 7) (R 7) [34,68,10,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18899 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18899
end Delivery.IrregularNine14.P07
