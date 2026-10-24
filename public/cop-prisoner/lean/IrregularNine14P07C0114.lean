import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6840 : Route 9 := (fun mask => (mask,id))

def c6840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6840 : Upper (D 7) (R 7) [36,40,80,192,384,2,1] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,384,2,1] 13 (by decide) (choices 1) [1,2] r6840 c6840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u504
  · exact u505

def b6841 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 400, targets := 98 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,6)], upper := (rows 37 42 84 200 400 34 66 129 257), lower := (rows 37 42 84 200 400 34 66 128 256), losses := [] }

theorem u6841 : Upper (D 7) (R 7) [36,40,80,192,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6842 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 2, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 84 328 19 160 65 130 386), lower := (rows 37 42 84 328 19 160 65 128 256), losses := [] }

theorem u6842 : Upper (D 7) (R 7) [36,40,80,320,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6843 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 42 84 328 19 160 66 129 385), lower := (rows 37 42 84 328 19 160 66 128 256), losses := [] }

theorem u6843 : Upper (D 7) (R 7) [36,40,80,320,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6844 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(0,1),(1,0),(2,5),(3,5)], upper := (rows 37 42 84 328 19 160 192 131 259), lower := (rows 37 42 84 328 19 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 100 106 116 362 18 224 224 224 256) },{ target := 1, region := (rows 5 0 4 8 16 224 224 128 256), good := (rows 101 104 117 360 17 224 224 224 256) }] }

theorem u6844 : Upper (D 7) (R 7) [36,40,80,320,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6845 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 328 145 34 65 130 386), lower := (rows 37 42 84 328 145 34 65 128 256), losses := [] }

theorem u6845 : Upper (D 7) (R 7) [36,40,80,320,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6846 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 42 84 328 145 34 66 129 385), lower := (rows 37 42 84 328 145 34 66 128 256), losses := [] }

theorem u6846 : Upper (D 7) (R 7) [36,40,80,320,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6847 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 37 42 84 328 145 34 192 131 259), lower := (rows 37 42 84 328 145 34 192 128 256), losses := [] }

theorem u6847 : Upper (D 7) (R 7) [36,40,80,320,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6848 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 84 328 146 33 65 130 386), lower := (rows 37 42 84 328 146 33 65 128 256), losses := [] }

theorem u6848 : Upper (D 7) (R 7) [36,40,80,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6849 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 2 },{ cop := 4, region := 68, targets := 33 }], pairs := [(0,1),(2,0),(2,5),(3,1)], upper := (rows 37 42 84 328 146 33 66 129 385), lower := (rows 37 42 84 328 146 33 66 128 256), losses := [] }

theorem u6849 : Upper (D 7) (R 7) [36,40,80,320,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6850 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 37 42 84 328 146 33 192 131 259), lower := (rows 37 42 84 328 146 33 192 128 256), losses := [] }

theorem u6850 : Upper (D 7) (R 7) [36,40,80,320,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6851 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 68, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 42 84 392 145 34 65 194 322), lower := (rows 37 42 84 392 145 34 65 128 256), losses := [] }

theorem u6851 : Upper (D 7) (R 7) [36,40,80,384,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6852 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(2,5)], upper := (rows 37 42 84 392 145 34 66 193 321), lower := (rows 37 42 84 392 145 34 66 128 256), losses := [{ target := 5, region := (rows 1 2 5 25 17 0 98 129 257), good := (rows 477 74 92 392 413 66 66 128 256) }] }

theorem u6852 : Upper (D 7) (R 7) [36,40,80,384,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6853 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 3, region := 114, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(4,7)], upper := (rows 37 42 196 265 82 34 65 144 400), lower := (rows 37 42 196 265 82 34 65 128 256), losses := [] }

theorem u6853 : Upper (D 7) (R 7) [36,40,192,257,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6854 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 42 196 265 82 34 80 129 385), lower := (rows 37 42 196 265 82 34 80 128 256), losses := [] }

theorem u6854 : Upper (D 7) (R 7) [36,40,192,257,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6854 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6855 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 265 82 34 192 145 273), lower := (rows 37 42 196 265 82 34 192 128 256), losses := [] }

theorem u6855 : Upper (D 7) (R 7) [36,40,192,257,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6856 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 3, region := 114, targets := 128 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 37 42 196 265 82 48 65 130 386), lower := (rows 37 42 196 265 82 48 65 128 256), losses := [] }

theorem u6856 : Upper (D 7) (R 7) [36,40,192,257,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6856 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6857 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 42 196 265 82 48 66 129 385), lower := (rows 37 42 196 265 82 48 66 128 256), losses := [] }

theorem u6857 : Upper (D 7) (R 7) [36,40,192,257,66,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6857 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6858 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 42 196 265 82 48 192 131 259), lower := (rows 37 42 196 265 82 48 192 128 256), losses := [] }

theorem u6858 : Upper (D 7) (R 7) [36,40,192,257,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6858 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6859 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 196 280 82 33 65 130 386), lower := (rows 37 42 196 280 82 33 65 128 256), losses := [] }

theorem u6859 : Upper (D 7) (R 7) [36,40,192,272,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6860 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 42 196 280 82 33 66 129 385), lower := (rows 37 42 196 280 82 33 66 128 256), losses := [] }

theorem u6860 : Upper (D 7) (R 7) [36,40,192,272,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6861 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 280 82 33 192 131 259), lower := (rows 37 42 196 280 82 33 192 128 256), losses := [] }

theorem u6861 : Upper (D 7) (R 7) [36,40,192,272,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6862 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 37 42 196 328 19 48 65 130 386), lower := (rows 37 42 196 328 19 48 65 128 256), losses := [{ target := 0, region := (rows 0 3 76 76 16 48 64 211 339), good := (rows 430 430 460 460 434 432 462 128 256) }] }

theorem u6862 : Upper (D 7) (R 7) [36,40,192,320,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6862 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6863 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(0,1),(2,5),(3,5)], upper := (rows 37 42 196 328 19 48 66 129 385), lower := (rows 37 42 196 328 19 48 66 128 256), losses := [{ target := 1, region := (rows 3 0 76 76 16 48 64 211 339), good := (rows 429 429 460 460 433 432 461 128 256) }] }

theorem u6863 : Upper (D 7) (R 7) [36,40,192,320,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6863 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6864 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 42 196 328 19 48 192 131 259), lower := (rows 37 42 196 328 19 48 192 128 256), losses := [] }

theorem u6864 : Upper (D 7) (R 7) [36,40,192,320,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6864 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6865 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 144, targets := 97 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,6)], upper := (rows 37 42 196 328 146 33 65 146 274), lower := (rows 37 42 196 328 146 33 65 128 256), losses := [] }

theorem u6865 : Upper (D 7) (R 7) [36,40,192,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6866 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 42 196 328 146 33 66 145 273), lower := (rows 37 42 196 328 146 33 66 128 256), losses := [] }

theorem u6866 : Upper (D 7) (R 7) [36,40,192,320,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6867 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 42 196 328 146 33 80 131 259), lower := (rows 37 42 196 328 146 33 80 128 256), losses := [] }

theorem u6867 : Upper (D 7) (R 7) [36,40,192,320,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6867 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6868 : Route 9 := (fun mask => (mask,id))

def c6868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6868 : Upper (D 7) (R 7) [36,40,192,320,130,2,1] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320,130,2,1] 13 (by decide) (choices 1) [1,16] r6868 c6868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u506
  · exact u507

def b6869 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 42 196 328 146 34 80 129 257), lower := (rows 37 42 196 328 146 34 80 128 256), losses := [] }

theorem u6869 : Upper (D 7) (R 7) [36,40,192,320,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6869 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6870 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 42 196 328 146 48 65 131 259), lower := (rows 37 42 196 328 146 48 65 128 256), losses := [] }

theorem u6870 : Upper (D 7) (R 7) [36,40,192,320,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6870 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6871 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(1,7),(2,0),(3,7)], upper := (rows 37 42 196 328 146 48 66 129 257), lower := (rows 37 42 196 328 146 48 66 128 256), losses := [] }

theorem u6871 : Upper (D 7) (R 7) [36,40,192,320,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6871 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6872 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,0),(4,0),(4,5)], upper := (rows 37 74 7 25 274 160 96 192 448), lower := (rows 37 74 7 25 274 160 96 128 256), losses := [] }

theorem u6872 : Upper (D 7) (R 7) [36,72,3,17,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6873 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 74 7 25 274 160 192 224 352), lower := (rows 37 74 7 25 274 160 192 128 256), losses := [{ target := 6, region := (rows 3 2 22 24 16 224 0 128 256), good := (rows 37 47 7 29 287 160 160 160 256) }] }

theorem u6873 : Upper (D 7) (R 7) [36,72,3,17,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6874 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 7 25 400 160 66 224 352), lower := (rows 37 74 7 25 400 160 66 128 256), losses := [] }

theorem u6874 : Upper (D 7) (R 7) [36,72,3,17,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6875 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,5),(4,0),(4,5)], upper := (rows 37 74 7 25 400 160 96 194 322), lower := (rows 37 74 7 25 400 160 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 13 22 0 64 130 258), good := (rows 29 474 415 25 400 128 64 128 256) }] }

theorem u6875 : Upper (D 7) (R 7) [36,72,3,17,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6876 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 26 176 288 65 192 448), lower := (rows 37 74 7 26 176 288 65 128 256), losses := [] }

theorem u6876 : Upper (D 7) (R 7) [36,72,3,18,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6876 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6877 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 7 26 176 288 192 193 321), lower := (rows 37 74 7 26 176 288 192 128 256), losses := [] }

theorem u6877 : Upper (D 7) (R 7) [36,72,3,18,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6877 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6878 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 26 304 160 65 192 448), lower := (rows 37 74 7 26 304 160 65 128 256), losses := [] }

theorem u6878 : Upper (D 7) (R 7) [36,72,3,18,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6879 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 7 26 304 160 192 193 321), lower := (rows 37 74 7 26 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 224 224 128 256), good := (rows 100 106 6 26 378 224 224 224 256) }] }

theorem u6879 : Upper (D 7) (R 7) [36,72,3,18,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6880 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 56 146 288 65 192 448), lower := (rows 37 74 7 56 146 288 65 128 256), losses := [] }

theorem u6880 : Upper (D 7) (R 7) [36,72,3,48,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6880 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6881 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 293, targets := 128 },{ cop := 2, region := 481, targets := 2 }], pairs := [(0,1),(0,7),(2,7)], upper := (rows 37 74 7 56 146 288 192 193 321), lower := (rows 37 74 7 56 146 288 192 128 256), losses := [] }

theorem u6881 : Upper (D 7) (R 7) [36,72,3,48,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6881 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6882 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 442, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 7 56 274 160 65 192 448), lower := (rows 37 74 7 56 274 160 65 128 256), losses := [] }

theorem u6882 : Upper (D 7) (R 7) [36,72,3,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6883 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 225, targets := 2 },{ cop := 2, region := 464, targets := 32 }], pairs := [(0,1),(1,0),(1,5),(4,5)], upper := (rows 37 74 7 56 274 160 192 193 321), lower := (rows 37 74 7 56 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 100 106 6 122 274 224 224 224 256) },{ target := 5, region := (rows 1 10 4 8 20 0 229 133 261), good := (rows 469 74 471 90 274 192 192 192 256) }] }

theorem u6883 : Upper (D 7) (R 7) [36,72,3,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6884 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 442, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 7 56 336 160 65 130 386), lower := (rows 37 74 7 56 336 160 65 128 256), losses := [] }

theorem u6884 : Upper (D 7) (R 7) [36,72,3,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6885 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 74 7 56 336 160 66 129 385), lower := (rows 37 74 7 56 336 160 66 128 256), losses := [] }

theorem u6885 : Upper (D 7) (R 7) [36,72,3,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6886 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 464, targets := 32 }], pairs := [(0,6),(1,0),(2,6),(4,5)], upper := (rows 37 74 7 56 336 160 192 131 259), lower := (rows 37 74 7 56 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 26 4 24 16 224 224 128 256), good := (rows 100 106 6 122 378 224 224 224 256) }] }

theorem u6886 : Upper (D 7) (R 7) [36,72,3,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6887 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 74 7 137 112 288 66 144 400), lower := (rows 37 74 7 137 112 288 66 128 256), losses := [] }

theorem u6887 : Upper (D 7) (R 7) [36,72,3,129,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6887 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6888 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 74 7 137 112 288 80 130 386), lower := (rows 37 74 7 137 112 288 80 128 256), losses := [] }

theorem u6888 : Upper (D 7) (R 7) [36,72,3,129,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6888 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6889 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 7 137 112 288 192 146 274), lower := (rows 37 74 7 137 112 288 192 128 256), losses := [] }

theorem u6889 : Upper (D 7) (R 7) [36,72,3,129,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6889 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6890 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 74 7 137 176 288 66 208 336), lower := (rows 37 74 7 137 176 288 66 128 256), losses := [] }

theorem u6890 : Upper (D 7) (R 7) [36,72,3,129,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6890 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6891 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 74 7 137 176 288 80 194 322), lower := (rows 37 74 7 137 176 288 80 128 256), losses := [] }

theorem u6891 : Upper (D 7) (R 7) [36,72,3,129,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6891 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6892 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 74 7 137 208 48 66 416 288), lower := (rows 37 74 7 137 208 48 66 128 256), losses := [] }

theorem u6892 : Upper (D 7) (R 7) [36,72,3,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6892 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6893 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 392, targets := 96 },{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 37 74 7 137 208 48 96 386 258), lower := (rows 37 74 7 137 208 48 96 128 256), losses := [] }

theorem u6893 : Upper (D 7) (R 7) [36,72,3,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6893 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6894 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 37 74 7 137 208 48 320 162 290), lower := (rows 37 74 7 137 208 48 320 128 256), losses := [] }

theorem u6894 : Upper (D 7) (R 7) [36,72,3,129,192,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6894 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6895 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 74 7 137 208 288 66 176 304), lower := (rows 37 74 7 137 208 288 66 128 256), losses := [] }

theorem u6895 : Upper (D 7) (R 7) [36,72,3,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6895 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6896 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 74 7 137 208 288 80 162 290), lower := (rows 37 74 7 137 208 288 80 128 256), losses := [] }

theorem u6896 : Upper (D 7) (R 7) [36,72,3,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6896 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6897 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 74 7 137 208 288 96 146 274), lower := (rows 37 74 7 137 208 288 96 128 256), losses := [] }

theorem u6897 : Upper (D 7) (R 7) [36,72,3,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6897 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6898 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 74 7 137 336 48 66 160 416), lower := (rows 37 74 7 137 336 48 66 128 256), losses := [] }

theorem u6898 : Upper (D 7) (R 7) [36,72,3,129,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6898 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6899 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 112, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 37 74 7 137 336 48 96 130 386), lower := (rows 37 74 7 137 336 48 96 128 256), losses := [] }

theorem u6899 : Upper (D 7) (R 7) [36,72,3,129,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6899 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6899
end Delivery.IrregularNine14.P07
