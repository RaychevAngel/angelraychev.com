import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3900 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 1, region := 112, targets := 1 }], pairs := [(2,1),(2,6),(4,0)], upper := (rows 11 134 37 328 112 36 66 145 273), lower := (rows 11 134 37 328 112 36 66 128 256), losses := [] }

theorem u3900 : Upper (D 6) (R 6) [10,132,33,320,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3901 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 328 112 36 80 131 259), lower := (rows 11 134 37 328 112 36 80 128 256), losses := [] }

theorem u3901 : Upper (D 6) (R 6) [10,132,33,320,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3901 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3902 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 134 38 25 84 96 65 416 288), lower := (rows 11 134 38 25 84 96 65 128 256), losses := [] }

theorem u3902 : Upper (D 6) (R 6) [10,132,34,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3903 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 38 25 84 96 96 385 257), lower := (rows 11 134 38 25 84 96 96 128 256), losses := [] }

theorem u3903 : Upper (D 6) (R 6) [10,132,34,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3904 : Route 9 := (fun mask => (mask,id))

def c3904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3904 : Upper (D 6) (R 6) [10,132,34,17,68,64,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,68,64,256] 13 (by decide) (choices 1) [1,32] r3904 c3904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u274
  · exact u275

def b3905 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 38 25 84 288 65 224 352), lower := (rows 11 134 38 25 84 288 65 128 256), losses := [] }

theorem u3905 : Upper (D 6) (R 6) [10,132,34,17,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3905 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3906 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 25 84 288 96 193 321), lower := (rows 11 134 38 25 84 288 96 128 256), losses := [] }

theorem u3906 : Upper (D 6) (R 6) [10,132,34,17,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3906 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3907 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 25 112 288 65 196 324), lower := (rows 11 134 38 25 112 288 65 128 256), losses := [] }

theorem u3907 : Upper (D 6) (R 6) [10,132,34,17,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3907 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3908 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 38 25 112 288 68 193 321), lower := (rows 11 134 38 25 112 288 68 128 256), losses := [] }

theorem u3908 : Upper (D 6) (R 6) [10,132,34,17,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3908 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3909 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 25 276 96 65 224 352), lower := (rows 11 134 38 25 276 96 65 128 256), losses := [] }

theorem u3909 : Upper (D 6) (R 6) [10,132,34,17,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3910 : Route 9 := (fun mask => (mask,id))

def c3910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3910 : Upper (D 6) (R 6) [10,132,34,17,260,64,32] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,260,64,32] 13 (by decide) (choices 1) [1,64] r3910 c3910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u276
  · exact u277

def b3911 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 25 304 96 65 196 324), lower := (rows 11 134 38 25 304 96 65 128 256), losses := [] }

theorem u3911 : Upper (D 6) (R 6) [10,132,34,17,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3912 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 38 25 304 96 68 193 321), lower := (rows 11 134 38 25 304 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 25 103 70 129 257), good := (rows 505 228 100 441 304 96 100 128 256) }] }

theorem u3912 : Upper (D 6) (R 6) [10,132,34,17,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3913 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 25 336 96 65 164 292), lower := (rows 11 134 38 25 336 96 65 128 256), losses := [] }

theorem u3913 : Upper (D 6) (R 6) [10,132,34,17,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3914 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 38 25 336 96 68 161 289), lower := (rows 11 134 38 25 336 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 119 70 137 265), good := (rows 505 228 100 441 368 96 100 128 256) }] }

theorem u3914 : Upper (D 6) (R 6) [10,132,34,17,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3915 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 134 38 25 336 96 96 133 261), lower := (rows 11 134 38 25 336 96 96 128 256), losses := [] }

theorem u3915 : Upper (D 6) (R 6) [10,132,34,17,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3916 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 28 81 96 65 416 288), lower := (rows 11 134 38 28 81 96 65 128 256), losses := [] }

theorem u3916 : Upper (D 6) (R 6) [10,132,34,20,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3917 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 387, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 38 28 81 96 96 385 257), lower := (rows 11 134 38 28 81 96 96 128 256), losses := [] }

theorem u3917 : Upper (D 6) (R 6) [10,132,34,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3918 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 28 81 96 320 161 289), lower := (rows 11 134 38 28 81 96 320 128 256), losses := [] }

theorem u3918 : Upper (D 6) (R 6) [10,132,34,20,65,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3918 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3919 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 28 273 96 65 224 352), lower := (rows 11 134 38 28 273 96 65 128 256), losses := [] }

theorem u3919 : Upper (D 6) (R 6) [10,132,34,20,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3920 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 28 273 96 96 193 321), lower := (rows 11 134 38 28 273 96 96 128 256), losses := [] }

theorem u3920 : Upper (D 6) (R 6) [10,132,34,20,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3921 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 38 28 336 96 65 161 289), lower := (rows 11 134 38 28 336 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 113 113 65 193 321), good := (rows 505 140 60 60 496 496 497 128 256) }] }

theorem u3921 : Upper (D 6) (R 6) [10,132,34,20,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3922 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 38 28 336 96 96 129 257), lower := (rows 11 134 38 28 336 96 96 128 256), losses := [] }

theorem u3922 : Upper (D 6) (R 6) [10,132,34,20,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3923 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 56 81 288 65 196 324), lower := (rows 11 134 38 56 81 288 65 128 256), losses := [] }

theorem u3923 : Upper (D 6) (R 6) [10,132,34,48,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3923 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3924 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 134 38 56 81 288 68 193 321), lower := (rows 11 134 38 56 81 288 68 128 256), losses := [] }

theorem u3924 : Upper (D 6) (R 6) [10,132,34,48,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3924 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3925 : PairBound 9 := { available := 65, camps := [], pairs := [(3,1),(3,2)], upper := (rows 11 134 38 56 84 288 65 193 321), lower := (rows 11 134 38 56 84 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 369 65 193 321), good := (rows 489 132 36 56 508 288 481 128 288) },{ target := 2, region := (rows 1 2 0 24 16 369 65 193 321), good := (rows 491 130 34 56 504 288 481 128 288) }] }

theorem u3925 : Upper (D 6) (R 6) [10,132,34,48,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3925 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3926 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 104, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 38 56 273 96 65 196 324), lower := (rows 11 134 38 56 273 96 65 128 256), losses := [] }

theorem u3926 : Upper (D 6) (R 6) [10,132,34,48,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3927 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 56 273 96 68 193 321), lower := (rows 11 134 38 56 273 96 68 128 256), losses := [{ target := 0, region := (rows 0 130 135 24 16 255 215 128 256), good := (rows 110 230 102 120 380 96 100 230 256) }] }

theorem u3927 : Upper (D 6) (R 6) [10,132,34,48,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3928 : Route 9 := (fun mask => (mask,id))

def c3928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3928 : Upper (D 6) (R 6) [10,132,34,48,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,260,64,1] 13 (by decide) (choices 1) [1,64] r3928 c3928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u278
  · exact u279

def b3929 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 56 336 33 65 196 324), lower := (rows 11 134 38 56 336 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 97 97 132 260), good := (rows 105 412 508 120 376 97 97 128 256) }] }

theorem u3929 : Upper (D 6) (R 6) [10,132,34,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3930 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 56 336 33 68 193 321), lower := (rows 11 134 38 56 336 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 41 17 33 70 129 257), good := (rows 505 196 108 56 336 441 68 128 256) }] }

theorem u3930 : Upper (D 6) (R 6) [10,132,34,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3931 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 418, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 134 38 73 84 288 65 176 304), lower := (rows 11 134 38 73 84 288 65 128 256), losses := [] }

theorem u3931 : Upper (D 6) (R 6) [10,132,34,65,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3931 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3932 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5)], upper := (rows 11 134 38 73 84 288 80 161 289), lower := (rows 11 134 38 73 84 288 80 128 256), losses := [] }

theorem u3932 : Upper (D 6) (R 6) [10,132,34,65,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3932 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3933 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 73 84 288 96 145 273), lower := (rows 11 134 38 73 84 288 96 128 256), losses := [] }

theorem u3933 : Upper (D 6) (R 6) [10,132,34,65,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3933 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3934 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 134 38 73 112 288 65 148 276), lower := (rows 11 134 38 73 112 288 65 128 256), losses := [] }

theorem u3934 : Upper (D 6) (R 6) [10,132,34,65,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3934 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3935 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 38 73 112 288 68 145 273), lower := (rows 11 134 38 73 112 288 68 128 256), losses := [] }

theorem u3935 : Upper (D 6) (R 6) [10,132,34,65,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3935 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3936 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 89, targets := 4 }], pairs := [(0,2)], upper := (rows 11 134 38 73 112 288 80 133 261), lower := (rows 11 134 38 73 112 288 80 128 256), losses := [] }

theorem u3936 : Upper (D 6) (R 6) [10,132,34,65,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3936 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3937 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 3, region := 304, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 134 38 73 273 96 68 176 304), lower := (rows 11 134 38 73 273 96 68 128 256), losses := [] }

theorem u3937 : Upper (D 6) (R 6) [10,132,34,65,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3938 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 134 38 73 273 96 80 164 292), lower := (rows 11 134 38 73 273 96 80 128 256), losses := [] }

theorem u3938 : Upper (D 6) (R 6) [10,132,34,65,257,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3938 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3939 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 38 73 273 96 96 148 276), lower := (rows 11 134 38 73 273 96 96 128 256), losses := [] }

theorem u3939 : Upper (D 6) (R 6) [10,132,34,65,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3940 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 73 276 96 65 176 304), lower := (rows 11 134 38 73 276 96 65 128 256), losses := [] }

theorem u3940 : Upper (D 6) (R 6) [10,132,34,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3941 : Route 9 := (fun mask => (mask,id))

def c3941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3941 : Upper (D 6) (R 6) [10,132,34,65,260,64,16] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,260,64,16] 13 (by decide) (choices 1) [1,32] r3941 c3941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u280
  · exact u281

def b3942 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 38 73 276 96 96 145 273), lower := (rows 11 134 38 73 276 96 96 128 256), losses := [] }

theorem u3942 : Upper (D 6) (R 6) [10,132,34,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3943 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 73 304 96 65 148 276), lower := (rows 11 134 38 73 304 96 65 128 256), losses := [] }

theorem u3943 : Upper (D 6) (R 6) [10,132,34,65,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3944 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 3, region := 304, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 134 38 73 304 96 68 145 273), lower := (rows 11 134 38 73 304 96 68 128 256), losses := [] }

theorem u3944 : Upper (D 6) (R 6) [10,132,34,65,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3945 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 38 73 304 96 80 133 261), lower := (rows 11 134 38 73 304 96 80 128 256), losses := [] }

theorem u3945 : Upper (D 6) (R 6) [10,132,34,65,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3945 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3946 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 134 38 73 336 48 65 164 292), lower := (rows 11 134 38 73 336 48 65 128 256), losses := [] }

theorem u3946 : Upper (D 6) (R 6) [10,132,34,65,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3946 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3947 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 38 73 336 48 68 161 289), lower := (rows 11 134 38 73 336 48 68 128 256), losses := [] }

theorem u3947 : Upper (D 6) (R 6) [10,132,34,65,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3947 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3948 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 38 73 336 48 96 133 261), lower := (rows 11 134 38 73 336 48 96 128 256), losses := [] }

theorem u3948 : Upper (D 6) (R 6) [10,132,34,65,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3948 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3949 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 88 49 288 65 196 324), lower := (rows 11 134 38 88 49 288 65 128 256), losses := [] }

theorem u3949 : Upper (D 6) (R 6) [10,132,34,80,33,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3949 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3950 : PairBound 9 := { available := 65, camps := [], pairs := [(3,1),(4,1)], upper := (rows 11 134 38 88 49 288 68 193 321), lower := (rows 11 134 38 88 49 288 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 305 70 129 257), good := (rows 505 196 100 120 441 288 68 128 288) }] }

theorem u3950 : Upper (D 6) (R 6) [10,132,34,80,33,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3950 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3951 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 88 273 96 65 164 292), lower := (rows 11 134 38 88 273 96 65 128 256), losses := [] }

theorem u3951 : Upper (D 6) (R 6) [10,132,34,80,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3952 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 88 273 96 68 161 289), lower := (rows 11 134 38 88 273 96 68 128 256), losses := [{ target := 0, region := (rows 0 130 135 24 16 255 215 128 256), good := (rows 110 230 102 120 380 96 100 230 256) }] }

theorem u3952 : Upper (D 6) (R 6) [10,132,34,80,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3953 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 38 88 273 96 96 133 261), lower := (rows 11 134 38 88 273 96 96 128 256), losses := [] }

theorem u3953 : Upper (D 6) (R 6) [10,132,34,80,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3954 : Route 9 := (fun mask => (mask,id))

def c3954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3954 : Upper (D 6) (R 6) [10,132,34,80,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,260,64,1] 13 (by decide) (choices 1) [1,32] r3954 c3954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u282
  · exact u283

def b3955 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 38 88 276 96 96 129 257), lower := (rows 11 134 38 88 276 96 96 128 256), losses := [] }

theorem u3955 : Upper (D 6) (R 6) [10,132,34,80,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3956 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 88 304 33 65 196 324), lower := (rows 11 134 38 88 304 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 97 97 132 260), good := (rows 105 412 508 120 376 97 97 128 256) }] }

theorem u3956 : Upper (D 6) (R 6) [10,132,34,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3957 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 88 304 33 68 193 321), lower := (rows 11 134 38 88 304 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 13 49 33 70 129 257), good := (rows 505 204 124 88 304 441 76 128 256) }] }

theorem u3957 : Upper (D 6) (R 6) [10,132,34,80,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3958 : Route 9 := (fun mask => (mask,id))

def c3958 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3958 : Upper (D 6) (R 6) [10,132,34,80,288,64,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,288,64,1] 13 (by decide) (choices 1) [1,4] r3958 c3958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u284
  · exact u285

def b3959 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 38 88 304 96 68 129 257), lower := (rows 11 134 38 88 304 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 111 70 129 257), good := (rows 505 228 100 120 304 96 100 128 256) }] }

theorem u3959 : Upper (D 6) (R 6) [10,132,34,80,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3959
end Delivery.IrregularNine14.P06
