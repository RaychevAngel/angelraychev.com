import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0014
import IrregularNine14P09C0015

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3840 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 14 84 104 145 33 448 384 384), lower := (rows 35 14 84 104 145 33 64 128 256), losses := [] }

theorem u3840 : Upper (D 9) (R 9) [34,12,80,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3840 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3841 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(2,5),(3,7),(4,5),(4,6)], upper := (rows 35 14 84 104 145 160 321 385 257), lower := (rows 35 14 84 104 145 160 64 128 256), losses := [] }

theorem u3841 : Upper (D 9) (R 9) [34,12,80,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3841 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3842 : Route 9 := (fun mask => (mask,id))

def c3842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3842 : Upper (D 9) (R 9) [34,12,80,96,129,256] 13 := by
  apply FastRouting.sound _ _ [34,12,80,96,129,256] 13 (by decide) (choices 1) [1,128,256] r3842 c3842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u875
  · exact u876
  · exact u877

def b3843 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 14 84 104 400 33 449 385 385), lower := (rows 35 14 84 104 400 33 64 128 256), losses := [] }

theorem u3843 : Upper (D 9) (R 9) [34,12,80,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3843 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3844 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(2,5),(3,7),(4,5),(4,6)], upper := (rows 35 14 84 104 400 160 321 385 257), lower := (rows 35 14 84 104 400 160 64 128 256), losses := [] }

theorem u3844 : Upper (D 9) (R 9) [34,12,80,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3844 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3845 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 320 },{ cop := 4, region := 40, targets := 64 }], pairs := [(0,6),(0,8),(2,5),(3,6),(4,5)], upper := (rows 35 14 84 168 145 33 320 448 320), lower := (rows 35 14 84 168 145 33 64 128 256), losses := [] }

theorem u3845 : Upper (D 9) (R 9) [34,12,80,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3845 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3846 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(2,5),(3,6),(4,5),(4,6)], upper := (rows 35 14 84 168 145 96 321 385 257), lower := (rows 35 14 84 168 145 96 64 128 256), losses := [] }

theorem u3846 : Upper (D 9) (R 9) [34,12,80,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3846 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3847 : Route 9 := (fun mask => (mask,id))

def c3847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3847 : Upper (D 9) (R 9) [34,12,80,160,129,256] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160,129,256] 13 (by decide) (choices 1) [1,256] r3847 c3847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u878
  · exact u879

def b3848 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(2,5),(4,5)], upper := (rows 35 14 84 168 273 33 448 448 448), lower := (rows 35 14 84 168 273 33 64 128 256), losses := [] }

theorem u3848 : Upper (D 9) (R 9) [34,12,80,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3848 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3849 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(2,5),(3,6),(4,5),(4,6)], upper := (rows 35 14 84 168 273 96 449 385 385), lower := (rows 35 14 84 168 273 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 47 116 40 273 96 96 0 256) }] }

theorem u3849 : Upper (D 9) (R 9) [34,12,80,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3849 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3850 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 14 84 168 273 160 321 449 321), lower := (rows 35 14 84 168 273 160 64 128 256), losses := [] }

theorem u3850 : Upper (D 9) (R 9) [34,12,80,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3850 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3851 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 200, targets := 256 },{ cop := 4, region := 196, targets := 256 }], pairs := [(1,8),(2,5),(2,8),(3,8),(4,5)], upper := (rows 35 14 84 168 273 288 193 193 449), lower := (rows 35 14 84 168 273 288 64 128 256), losses := [{ target := 8, region := (rows 1 18 20 9 16 32 81 145 0), good := (rows 235 14 214 168 223 32 64 128 0) }] }

theorem u3851 : Upper (D 9) (R 9) [34,12,80,160,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3851 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3852 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 320 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(2,5),(4,5)], upper := (rows 35 14 84 168 400 33 321 449 321), lower := (rows 35 14 84 168 400 33 64 128 256), losses := [] }

theorem u3852 : Upper (D 9) (R 9) [34,12,80,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3852 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3853 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(2,5),(3,6),(4,5),(4,6)], upper := (rows 35 14 84 168 400 96 321 385 257), lower := (rows 35 14 84 168 400 96 64 128 256), losses := [] }

theorem u3853 : Upper (D 9) (R 9) [34,12,80,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3853 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3854 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 40, targets := 65 },{ cop := 0, region := 200, targets := 256 }], pairs := [(2,5),(3,0),(3,6),(3,8),(4,5)], upper := (rows 35 14 84 168 400 288 65 193 321), lower := (rows 35 14 84 168 400 288 64 128 256), losses := [] }

theorem u3854 : Upper (D 9) (R 9) [34,12,80,160,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3854 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3855 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 84 200 145 33 352 416 288), lower := (rows 35 14 84 200 145 33 64 128 256), losses := [] }

theorem u3855 : Upper (D 9) (R 9) [34,12,80,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3855 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3856 : Route 9 := (fun mask => (mask,id))

def c3856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3856 : Upper (D 9) (R 9) [34,12,80,192,129,256] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,129,256] 13 (by decide) (choices 1) [1,32,256] r3856 c3856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u880
  · exact u881
  · exact u882

def b3857 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 84 200 176 33 321 385 257), lower := (rows 35 14 84 200 176 33 64 128 256), losses := [] }

theorem u3857 : Upper (D 9) (R 9) [34,12,80,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3857 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3858 : Route 9 := (fun mask => (mask,id))

def c3858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3858 : Upper (D 9) (R 9) [34,12,80,192,160,256] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,160,256] 13 (by decide) (choices 1) [1,256] r3858 c3858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u883
  · exact u884

def b3859 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,6)], upper := (rows 35 14 84 200 273 33 480 416 416), lower := (rows 35 14 84 200 273 33 64 128 256), losses := [] }

theorem u3859 : Upper (D 9) (R 9) [34,12,80,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3859 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3860 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(2,7),(4,6),(4,7)], upper := (rows 35 14 84 200 273 160 353 417 289), lower := (rows 35 14 84 200 273 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 8 16 168 64 128 0), good := (rows 35 47 84 232 17 160 64 160 0) }] }

theorem u3860 : Upper (D 9) (R 9) [34,12,80,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3860 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3861 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 256 }], pairs := [(0,6),(1,8),(2,8),(3,8),(4,6)], upper := (rows 35 14 84 200 273 288 225 161 417), lower := (rows 35 14 84 200 273 288 64 128 256), losses := [{ target := 8, region := (rows 1 22 20 25 16 32 65 129 0), good := (rows 235 14 94 200 223 32 64 128 0) }] }

theorem u3861 : Upper (D 9) (R 9) [34,12,80,192,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3861 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3862 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,6)], upper := (rows 35 14 84 200 304 33 449 385 385), lower := (rows 35 14 84 200 304 33 64 128 256), losses := [] }

theorem u3862 : Upper (D 9) (R 9) [34,12,80,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3862 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3863 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,6),(2,7),(3,5),(4,6),(4,7)], upper := (rows 35 14 84 200 304 160 321 385 257), lower := (rows 35 14 84 200 304 160 64 128 256), losses := [] }

theorem u3863 : Upper (D 9) (R 9) [34,12,80,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3863 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3864 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 84 200 304 288 193 129 385), lower := (rows 35 14 84 200 304 288 64 128 256), losses := [] }

theorem u3864 : Upper (D 9) (R 9) [34,12,80,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3864 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3865 : Route 9 := (fun mask => (mask,id))

def c3865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3865 : Upper (D 9) (R 9) [34,12,80,192,384,1] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,384,1] 13 (by decide) (choices 1) [1,32,256] r3865 c3865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u885
  · exact u886
  · exact u887

def r3866 : Route 9 := (fun mask => (mask,id))

def c3866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3866 : Upper (D 9) (R 9) [34,12,80,192,384,256] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,384,256] 13 (by decide) (choices 1) [1,32] r3866 c3866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u888
  · exact u889

def b3867 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 33, targets := 320 },{ cop := 0, region := 456, targets := 1 },{ cop := 1, region := 33, targets := 128 },{ cop := 4, region := 356, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(2,7),(3,0)], upper := (rows 35 14 84 392 145 33 352 480 352), lower := (rows 35 14 84 392 145 33 64 128 256), losses := [] }

theorem u3867 : Upper (D 9) (R 9) [34,12,80,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3867 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3868 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 353, targets := 128 },{ cop := 4, region := 356, targets := 128 }], pairs := [(0,7),(1,6),(2,7),(3,6),(4,6)], upper := (rows 35 14 84 392 145 96 353 417 289), lower := (rows 35 14 84 392 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 25 17 32 0 129 257), good := (rows 443 14 30 392 409 32 0 128 256) }] }

theorem u3868 : Upper (D 9) (R 9) [34,12,80,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3868 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3869 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 212, targets := 256 },{ cop := 1, region := 353, targets := 128 },{ cop := 4, region := 356, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(2,8),(4,8)], upper := (rows 35 14 84 392 145 288 97 225 353), lower := (rows 35 14 84 392 145 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 296 0 128 256), good := (rows 35 47 20 424 145 288 0 128 288) }] }

theorem u3869 : Upper (D 9) (R 9) [34,12,80,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3869 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3870 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 33, targets := 320 },{ cop := 0, region := 456, targets := 32 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,5),(3,5)], upper := (rows 35 14 84 392 176 33 321 449 321), lower := (rows 35 14 84 392 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 22 20 57 16 0 97 161 289), good := (rows 459 14 94 392 478 457 64 128 256) }] }

theorem u3870 : Upper (D 9) (R 9) [34,12,80,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3870 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3871 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 392, targets := 32 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(3,6),(4,6)], upper := (rows 35 14 84 392 176 96 321 385 257), lower := (rows 35 14 84 392 176 96 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 8 16 100 64 128 0), good := (rows 35 47 116 136 176 96 96 128 0) }] }

theorem u3871 : Upper (D 9) (R 9) [34,12,80,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3871 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3872 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 256 },{ cop := 3, region := 48, targets := 65 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,8),(3,5),(4,0),(4,6),(4,8)], upper := (rows 35 14 84 392 176 288 65 193 321), lower := (rows 35 14 84 392 176 288 64 128 256), losses := [] }

theorem u3872 : Upper (D 9) (R 9) [34,12,80,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3872 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3873 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 100 200 273 33 464 400 400), lower := (rows 35 14 100 200 273 33 64 128 256), losses := [] }

theorem u3873 : Upper (D 9) (R 9) [34,12,96,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3873 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3874 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 14 100 200 273 48 449 385 385), lower := (rows 35 14 100 200 273 48 64 128 256), losses := [] }

theorem u3874 : Upper (D 9) (R 9) [34,12,96,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3874 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3875 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 35 14 100 200 273 160 337 401 273), lower := (rows 35 14 100 200 273 160 64 128 256), losses := [] }

theorem u3875 : Upper (D 9) (R 9) [34,12,96,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3875 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3876 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,6),(3,5),(3,8),(4,5),(4,6)], upper := (rows 35 14 100 200 273 288 209 145 401), lower := (rows 35 14 100 200 273 288 64 128 256), losses := [] }

theorem u3876 : Upper (D 9) (R 9) [34,12,96,192,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3876 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3877 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 100 200 400 33 337 401 273), lower := (rows 35 14 100 200 400 33 64 128 256), losses := [] }

theorem u3877 : Upper (D 9) (R 9) [34,12,96,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3877 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3878 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 14 100 200 400 48 321 385 257), lower := (rows 35 14 100 200 400 48 64 128 256), losses := [] }

theorem u3878 : Upper (D 9) (R 9) [34,12,96,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3878 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3879 : Route 9 := (fun mask => (mask,id))

def c3879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3879 : Upper (D 9) (R 9) [34,12,96,192,384,256] 13 := by
  apply FastRouting.sound _ _ [34,12,96,192,384,256] 13 (by decide) (choices 1) [1,16] r3879 c3879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u890
  · exact u891

def b3880 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 14 100 392 81 33 464 400 400), lower := (rows 35 14 100 392 81 33 64 128 256), losses := [] }

theorem u3880 : Upper (D 9) (R 9) [34,12,96,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3880 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3881 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 35 14 100 392 81 48 449 385 385), lower := (rows 35 14 100 392 81 48 64 128 256), losses := [] }

theorem u3881 : Upper (D 9) (R 9) [34,12,96,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3881 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3882 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 340, targets := 128 },{ cop := 4, region := 392, targets := 64 }], pairs := [(2,7),(3,5),(3,6),(4,5),(4,7)], upper := (rows 35 14 100 392 81 160 337 401 273), lower := (rows 35 14 100 392 81 160 64 128 256), losses := [] }

theorem u3882 : Upper (D 9) (R 9) [34,12,96,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3882 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3883 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 14 100 392 145 33 336 464 336), lower := (rows 35 14 100 392 145 33 64 128 256), losses := [] }

theorem u3883 : Upper (D 9) (R 9) [34,12,96,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3883 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3884 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 324, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 14 100 392 145 48 321 449 321), lower := (rows 35 14 100 392 145 48 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 57 17 0 81 145 273), good := (rows 475 14 78 392 473 472 64 128 256) }] }

theorem u3884 : Upper (D 9) (R 9) [34,12,96,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3884 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3885 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 35 14 100 392 145 96 337 401 273), lower := (rows 35 14 100 392 145 96 64 128 256), losses := [] }

theorem u3885 : Upper (D 9) (R 9) [34,12,96,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3885 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3886 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 212, targets := 256 },{ cop := 4, region := 356, targets := 128 }], pairs := [(2,7),(2,8),(3,5),(4,5),(4,8)], upper := (rows 35 14 100 392 145 288 81 209 337), lower := (rows 35 14 100 392 145 288 64 128 256), losses := [] }

theorem u3886 : Upper (D 9) (R 9) [34,12,96,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3886 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3887 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 14 100 392 208 33 337 401 273), lower := (rows 35 14 100 392 208 33 64 128 256), losses := [] }

theorem u3887 : Upper (D 9) (R 9) [34,12,96,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3887 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3888 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 35 14 100 392 208 48 321 385 257), lower := (rows 35 14 100 392 208 48 64 128 256), losses := [] }

theorem u3888 : Upper (D 9) (R 9) [34,12,96,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3888 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3889 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 212, targets := 256 }], pairs := [(0,6),(2,8),(3,5),(4,5),(4,8)], upper := (rows 35 14 100 392 208 288 81 145 273), lower := (rows 35 14 100 392 208 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 296 0 128 256), good := (rows 35 47 36 424 144 288 0 128 288) }] }

theorem u3889 : Upper (D 9) (R 9) [34,12,96,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3889 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3890 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(3,7),(4,6)], upper := (rows 35 14 196 328 145 33 368 432 304), lower := (rows 35 14 196 328 145 33 64 128 256), losses := [] }

theorem u3890 : Upper (D 9) (R 9) [34,12,192,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3890 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3891 : Route 9 := (fun mask => (mask,id))

def c3891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3891 : Upper (D 9) (R 9) [34,12,192,320,129,16] 13 := by
  apply FastRouting.sound _ _ [34,12,192,320,129,16] 13 (by decide) (choices 1) [1,32,256] r3891 c3891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u892
  · exact u893
  · exact u894

def b3892 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 212, targets := 256 },{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(2,8),(3,7),(4,6),(4,8)], upper := (rows 35 14 196 328 145 288 113 177 305), lower := (rows 35 14 196 328 145 288 64 128 256), losses := [] }

theorem u3892 : Upper (D 9) (R 9) [34,12,192,320,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3892 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3893 : Route 9 := (fun mask => (mask,id))

def c3893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3893 : Upper (D 9) (R 9) [34,12,192,320,160,1] 13 := by
  apply FastRouting.sound _ _ [34,12,192,320,160,1] 13 (by decide) (choices 1) [1,16,256] r3893 c3893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u895
  · exact u896
  · exact u897

def b3894 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 14 196 328 176 48 321 385 257), lower := (rows 35 14 196 328 176 48 64 128 256), losses := [] }

theorem u3894 : Upper (D 9) (R 9) [34,12,192,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3894 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3895 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 256 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,8),(4,6),(4,8)], upper := (rows 35 14 196 328 176 288 81 145 273), lower := (rows 35 14 196 328 176 288 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 296 64 0 256), good := (rows 35 47 68 360 48 288 64 0 288) }] }

theorem u3895 : Upper (D 9) (R 9) [34,12,192,320,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3895 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3896 : Route 9 := (fun mask => (mask,id))

def c3896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3896 : Upper (D 9) (R 9) [34,12,192,320,384,1] 13 := by
  apply FastRouting.sound _ _ [34,12,192,320,384,1] 13 (by decide) (choices 1) [1,16,32] r3896 c3896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u898
  · exact u899
  · exact u900

def b3897 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 },{ cop := 0, region := 196, targets := 256 }], pairs := [(0,6),(2,8),(3,7),(4,6)], upper := (rows 35 14 196 328 400 48 97 161 289), lower := (rows 35 14 196 328 400 48 64 128 256), losses := [] }

theorem u3897 : Upper (D 9) (R 9) [34,12,192,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3897 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3898 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 28 176 96 448 384 384), lower := (rows 35 67 13 28 176 96 64 128 256), losses := [] }

theorem u3898 : Upper (D 9) (R 9) [34,65,9,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3898 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3899 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,7)], upper := (rows 35 67 13 28 176 160 320 448 320), lower := (rows 35 67 13 28 176 160 64 128 256), losses := [] }

theorem u3899 : Upper (D 9) (R 9) [34,65,9,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3899 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3899
end Delivery.IrregularNine14.P09
