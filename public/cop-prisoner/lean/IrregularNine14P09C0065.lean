import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0015

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3900 : Route 9 := (fun mask => (mask,id))

def c3900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3900 : Upper (D 9) (R 9) [34,65,9,20,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,160,256] 13 (by decide) (choices 1) [128,256] r3900 c3900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u901
  · exact u902

def b3901 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 35 67 13 28 208 160 352 416 288), lower := (rows 35 67 13 28 208 160 64 128 256), losses := [] }

theorem u3901 : Upper (D 9) (R 9) [34,65,9,20,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3901 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3902 : Route 9 := (fun mask => (mask,id))

def c3902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3902 : Upper (D 9) (R 9) [34,65,9,20,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,192,256] 13 (by decide) (choices 1) [32,128,256] r3902 c3902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u903
  · exact u904
  · exact u905

def b3903 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 28 400 96 480 416 416), lower := (rows 35 67 13 28 400 96 64 128 256), losses := [] }

theorem u3903 : Upper (D 9) (R 9) [34,65,9,20,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3903 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3904 : Route 9 := (fun mask => (mask,id))

def c3904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3904 : Upper (D 9) (R 9) [34,65,9,20,384,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,384,128] 13 (by decide) (choices 1) [32,256] r3904 c3904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u906
  · exact u907

def b3905 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 56 148 96 448 384 384), lower := (rows 35 67 13 56 148 96 64 128 256), losses := [] }

theorem u3905 : Upper (D 9) (R 9) [34,65,9,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3905 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3906 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 35 67 13 56 148 160 320 448 320), lower := (rows 35 67 13 56 148 160 64 128 256), losses := [] }

theorem u3906 : Upper (D 9) (R 9) [34,65,9,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3906 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3907 : Route 9 := (fun mask => (mask,id))

def c3907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3907 : Upper (D 9) (R 9) [34,65,9,48,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,132,256] 13 (by decide) (choices 1) [128,256] r3907 c3907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u908
  · exact u909

def b3908 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 56 208 36 448 384 384), lower := (rows 35 67 13 56 208 36 64 128 256), losses := [] }

theorem u3908 : Upper (D 9) (R 9) [34,65,9,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3908 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3909 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 56 208 160 324 388 260), lower := (rows 35 67 13 56 208 160 64 128 256), losses := [] }

theorem u3909 : Upper (D 9) (R 9) [34,65,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3909 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3910 : Route 9 := (fun mask => (mask,id))

def c3910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3910 : Upper (D 9) (R 9) [34,65,9,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,192,256] 13 (by decide) (choices 1) [4,128,256] r3910 c3910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u910
  · exact u911
  · exact u912

def b3911 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 56 400 36 448 448 448), lower := (rows 35 67 13 56 400 36 64 128 256), losses := [] }

theorem u3911 : Upper (D 9) (R 9) [34,65,9,48,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3911 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3912 : PairBound 9 := { available := 388, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 56 400 96 452 388 388), lower := (rows 35 67 13 56 400 96 64 128 256), losses := [] }

theorem u3912 : Upper (D 9) (R 9) [34,65,9,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3912 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3913 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 35 67 13 56 400 160 324 452 324), lower := (rows 35 67 13 56 400 160 64 128 256), losses := [] }

theorem u3913 : Upper (D 9) (R 9) [34,65,9,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3913 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3914 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 323, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 88 148 160 352 416 288), lower := (rows 35 67 13 88 148 160 64 128 256), losses := [] }

theorem u3914 : Upper (D 9) (R 9) [34,65,9,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3914 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3915 : Route 9 := (fun mask => (mask,id))

def c3915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3915 : Upper (D 9) (R 9) [34,65,9,80,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,132,256] 13 (by decide) (choices 1) [32,128,256] r3915 c3915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u913
  · exact u914
  · exact u915

def b3916 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 88 176 36 448 384 384), lower := (rows 35 67 13 88 176 36 64 128 256), losses := [] }

theorem u3916 : Upper (D 9) (R 9) [34,65,9,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3916 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3917 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 67 13 88 176 160 324 388 260), lower := (rows 35 67 13 88 176 160 64 128 256), losses := [] }

theorem u3917 : Upper (D 9) (R 9) [34,65,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3917 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3918 : Route 9 := (fun mask => (mask,id))

def c3918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3918 : Upper (D 9) (R 9) [34,65,9,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,160,256] 13 (by decide) (choices 1) [4,128,256] r3918 c3918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u916
  · exact u917
  · exact u918

def b3919 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 88 400 36 480 416 416), lower := (rows 35 67 13 88 400 36 64 128 256), losses := [] }

theorem u3919 : Upper (D 9) (R 9) [34,65,9,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3919 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3920 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,8),(1,8),(3,0),(4,0),(4,6)], upper := (rows 35 67 13 88 400 160 356 420 292), lower := (rows 35 67 13 88 400 160 64 128 256), losses := [{ target := 8, region := (rows 9 10 12 8 16 176 64 128 0), good := (rows 35 67 15 127 176 160 64 160 0) }] }

theorem u3920 : Upper (D 9) (R 9) [34,65,9,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3920 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3921 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 456, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(3,5)], upper := (rows 35 67 13 140 176 48 320 448 320), lower := (rows 35 67 13 140 176 48 64 128 256), losses := [] }

theorem u3921 : Upper (D 9) (R 9) [34,65,9,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3921 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3922 : PairBound 9 := { available := 272, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 140 176 96 336 400 272), lower := (rows 35 67 13 140 176 96 64 128 256), losses := [] }

theorem u3922 : Upper (D 9) (R 9) [34,65,9,132,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3922 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3923 : Route 9 := (fun mask => (mask,id))

def c3923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3923 : Upper (D 9) (R 9) [34,65,9,132,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,160,256] 13 (by decide) (choices 1) [16,256] r3923 c3923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u919
  · exact u920

def b3924 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 140 208 48 352 416 288), lower := (rows 35 67 13 140 208 48 64 128 256), losses := [] }

theorem u3924 : Upper (D 9) (R 9) [34,65,9,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3924 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3925 : Route 9 := (fun mask => (mask,id))

def c3925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3925 : Upper (D 9) (R 9) [34,65,9,132,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,192,256] 13 (by decide) (choices 1) [16,32,256] r3925 c3925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u921
  · exact u922
  · exact u923

def b3926 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 456, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(3,5)], upper := (rows 35 67 13 140 304 48 448 448 448), lower := (rows 35 67 13 140 304 48 64 128 256), losses := [] }

theorem u3926 : Upper (D 9) (R 9) [34,65,9,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3926 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3927 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 140 304 96 464 400 400), lower := (rows 35 67 13 140 304 96 64 128 256), losses := [] }

theorem u3927 : Upper (D 9) (R 9) [34,65,9,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3927 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3928 : PairBound 9 := { available := 336, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0),(4,7)], upper := (rows 35 67 13 140 304 160 336 464 336), lower := (rows 35 67 13 140 304 160 64 128 256), losses := [] }

theorem u3928 : Upper (D 9) (R 9) [34,65,9,132,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3928 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3929 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 35 67 13 140 304 288 208 208 464), lower := (rows 35 67 13 140 304 288 64 128 256), losses := [] }

theorem u3929 : Upper (D 9) (R 9) [34,65,9,132,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3929 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3930 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 140 336 48 480 416 416), lower := (rows 35 67 13 140 336 48 64 128 256), losses := [] }

theorem u3930 : Upper (D 9) (R 9) [34,65,9,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3930 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3931 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0),(4,7)], upper := (rows 35 67 13 140 336 160 368 432 304), lower := (rows 35 67 13 140 336 160 64 128 256), losses := [] }

theorem u3931 : Upper (D 9) (R 9) [34,65,9,132,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3931 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3932 : Route 9 := (fun mask => (mask,id))

def c3932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3932 : Upper (D 9) (R 9) [34,65,9,132,320,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,320,256] 13 (by decide) (choices 1) [16,32,128] r3932 c3932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u924
  · exact u925
  · exact u926

def b3933 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 400 48 352 480 352), lower := (rows 35 67 13 140 400 48 64 128 256), losses := [] }

theorem u3933 : Upper (D 9) (R 9) [34,65,9,132,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3933 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3934 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 140 400 96 368 432 304), lower := (rows 35 67 13 140 400 96 64 128 256), losses := [] }

theorem u3934 : Upper (D 9) (R 9) [34,65,9,132,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3934 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3935 : Route 9 := (fun mask => (mask,id))

def c3935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3935 : Upper (D 9) (R 9) [34,65,9,132,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,384,256] 13 (by decide) (choices 1) [16,32] r3935 c3935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u927
  · exact u928

def b3936 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 152 52 96 448 384 384), lower := (rows 35 67 13 152 52 96 64 128 256), losses := [] }

theorem u3936 : Upper (D 9) (R 9) [34,65,9,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3936 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3937 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 323, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 152 52 160 320 448 320), lower := (rows 35 67 13 152 52 160 64 128 256), losses := [] }

theorem u3937 : Upper (D 9) (R 9) [34,65,9,144,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3937 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3938 : Route 9 := (fun mask => (mask,id))

def c3938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3938 : Upper (D 9) (R 9) [34,65,9,144,36,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,36,256] 13 (by decide) (choices 1) [128,256] r3938 c3938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u929
  · exact u930

def b3939 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 323, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 152 84 160 352 416 288), lower := (rows 35 67 13 152 84 160 64 128 256), losses := [] }

theorem u3939 : Upper (D 9) (R 9) [34,65,9,144,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3939 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3940 : Route 9 := (fun mask => (mask,id))

def c3940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3940 : Upper (D 9) (R 9) [34,65,9,144,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,68,256] 13 (by decide) (choices 1) [32,128,256] r3940 c3940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u931
  · exact u932
  · exact u933

def b3941 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 152 276 96 480 416 416), lower := (rows 35 67 13 152 276 96 64 128 256), losses := [] }

theorem u3941 : Upper (D 9) (R 9) [34,65,9,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3941 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3942 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0),(4,7)], upper := (rows 35 67 13 152 276 160 352 480 352), lower := (rows 35 67 13 152 276 160 64 128 256), losses := [{ target := 7, region := (rows 33 39 4 8 20 32 97 0 289), good := (rows 355 323 351 24 278 355 64 0 256) }] }

theorem u3942 : Upper (D 9) (R 9) [34,65,9,144,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3942 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3943 : Route 9 := (fun mask => (mask,id))

def c3943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3943 : Upper (D 9) (R 9) [34,65,9,144,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,260,256] 13 (by decide) (choices 1) [32,128] r3943 c3943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u934
  · exact u935

def b3944 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 450, targets := 32 },{ cop := 4, region := 200, targets := 32 }], pairs := [(1,5),(3,0),(3,5),(4,0)], upper := (rows 35 67 13 152 304 36 448 448 448), lower := (rows 35 67 13 152 304 36 64 128 256), losses := [] }

theorem u3944 : Upper (D 9) (R 9) [34,65,9,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3944 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3945 : PairBound 9 := { available := 388, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 152 304 96 452 388 388), lower := (rows 35 67 13 152 304 96 64 128 256), losses := [] }

theorem u3945 : Upper (D 9) (R 9) [34,65,9,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3945 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3946 : Route 9 := (fun mask => (mask,id))

def c3946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3946 : Upper (D 9) (R 9) [34,65,9,144,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,288,128] 13 (by decide) (choices 1) [4,256] r3946 c3946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u936
  · exact u937

def b3947 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 13 152 304 288 196 196 452), lower := (rows 35 67 13 152 304 288 64 128 256), losses := [] }

theorem u3947 : Upper (D 9) (R 9) [34,65,9,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3947 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3948 : Route 9 := (fun mask => (mask,id))

def c3948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3948 : Upper (D 9) (R 9) [34,65,9,144,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,320,4] 13 (by decide) (choices 1) [32,128,256] r3948 c3948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u938
  · exact u939
  · exact u940

def r3949 : Route 9 := (fun mask => (mask,id))

def c3949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3949 : Upper (D 9) (R 9) [34,65,9,144,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,320,128] 13 (by decide) (choices 1) [4,32,256] r3949 c3949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u941
  · exact u942
  · exact u943

def b3950 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 35 67 13 152 336 288 228 164 420), lower := (rows 35 67 13 152 336 288 64 128 256), losses := [{ target := 7, region := (rows 25 18 12 8 16 304 64 0 256), good := (rows 35 67 13 63 371 288 64 0 288) }] }

theorem u3950 : Upper (D 9) (R 9) [34,65,9,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3950 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3951 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 168 208 36 336 400 272), lower := (rows 35 67 13 168 208 36 64 128 256), losses := [] }

theorem u3951 : Upper (D 9) (R 9) [34,65,9,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3951 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3952 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 168 208 48 324 388 260), lower := (rows 35 67 13 168 208 48 64 128 256), losses := [] }

theorem u3952 : Upper (D 9) (R 9) [34,65,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3952 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3953 : Route 9 := (fun mask => (mask,id))

def c3953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3953 : Upper (D 9) (R 9) [34,65,9,160,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,192,256] 13 (by decide) (choices 1) [4,16,256] r3953 c3953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u944
  · exact u945
  · exact u946

def b3954 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 168 276 48 448 448 448), lower := (rows 35 67 13 168 276 48 64 128 256), losses := [] }

theorem u3954 : Upper (D 9) (R 9) [34,65,9,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3954 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3955 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 168 276 96 464 400 400), lower := (rows 35 67 13 168 276 96 64 128 256), losses := [] }

theorem u3955 : Upper (D 9) (R 9) [34,65,9,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3955 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3956 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 13 168 276 160 336 464 336), lower := (rows 35 67 13 168 276 160 64 128 256), losses := [] }

theorem u3956 : Upper (D 9) (R 9) [34,65,9,160,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3956 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3957 : Route 9 := (fun mask => (mask,id))

def c3957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3957 : Upper (D 9) (R 9) [34,65,9,160,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,260,256] 13 (by decide) (choices 1) [16,128] r3957 c3957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u947
  · exact u948

def b3958 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 168 336 36 464 400 400), lower := (rows 35 67 13 168 336 36 64 128 256), losses := [] }

theorem u3958 : Upper (D 9) (R 9) [34,65,9,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3958 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3959 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 168 336 48 452 388 388), lower := (rows 35 67 13 168 336 48 64 128 256), losses := [] }

theorem u3959 : Upper (D 9) (R 9) [34,65,9,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3959 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3959
end Delivery.IrregularNine14.P09
