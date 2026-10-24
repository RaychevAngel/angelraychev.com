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

def b3900 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 4, region := 70, targets := 128 }], pairs := [(0,5),(1,7),(2,7),(3,5)], upper := (rows 13 98 22 266 49 160 65 192 448), lower := (rows 13 98 22 266 49 160 65 128 256), losses := [] }

theorem u3900 : Upper (D 7) (R 7) [12,96,18,258,33,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3901 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 22 266 49 160 192 193 321), lower := (rows 13 98 22 266 49 160 192 128 256), losses := [] }

theorem u3901 : Upper (D 7) (R 7) [12,96,18,258,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3902 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 22 266 145 33 96 192 448), lower := (rows 13 98 22 266 145 33 96 128 256), losses := [] }

theorem u3902 : Upper (D 7) (R 7) [12,96,18,258,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3903 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 458, targets := 1 },{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,1)], upper := (rows 13 98 22 266 145 33 192 224 352), lower := (rows 13 98 22 266 145 33 192 128 256), losses := [] }

theorem u3903 : Upper (D 7) (R 7) [12,96,18,258,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3904 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 266 145 96 192 161 289), lower := (rows 13 98 22 266 145 96 192 128 256), losses := [] }

theorem u3904 : Upper (D 7) (R 7) [12,96,18,258,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3905 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(3,0),(4,0)], upper := (rows 13 98 22 266 176 33 65 192 448), lower := (rows 13 98 22 266 176 33 65 128 256), losses := [] }

theorem u3905 : Upper (D 7) (R 7) [12,96,18,258,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3906 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 4, region := 70, targets := 1 }], pairs := [(0,5),(1,0),(2,0),(3,5)], upper := (rows 13 98 22 266 176 33 192 193 321), lower := (rows 13 98 22 266 176 33 192 128 256), losses := [] }

theorem u3906 : Upper (D 7) (R 7) [12,96,18,258,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3907 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 22 296 81 160 65 130 386), lower := (rows 13 98 22 296 81 160 65 128 256), losses := [] }

theorem u3907 : Upper (D 7) (R 7) [12,96,18,288,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3908 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 22 296 81 160 66 129 385), lower := (rows 13 98 22 296 81 160 66 128 256), losses := [] }

theorem u3908 : Upper (D 7) (R 7) [12,96,18,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3909 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 22 296 81 160 192 131 259), lower := (rows 13 98 22 296 81 160 192 128 256), losses := [] }

theorem u3909 : Upper (D 7) (R 7) [12,96,18,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3910 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 102, targets := 128 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 22 296 145 33 66 192 448), lower := (rows 13 98 22 296 145 33 66 128 256), losses := [] }

theorem u3910 : Upper (D 7) (R 7) [12,96,18,288,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3911 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 458, targets := 1 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,5)], upper := (rows 13 98 22 296 145 33 192 194 322), lower := (rows 13 98 22 296 145 33 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 215 134 262), good := (rows 477 450 470 264 209 81 192 192 256) }] }

theorem u3911 : Upper (D 7) (R 7) [12,96,18,288,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3912 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 426, targets := 1 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,5)], upper := (rows 13 98 22 296 145 160 65 194 322), lower := (rows 13 98 22 296 145 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 81 134 262), good := (rows 477 450 470 264 209 128 81 128 256) }] }

theorem u3912 : Upper (D 7) (R 7) [12,96,18,288,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3913 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(4,5)], upper := (rows 13 98 22 296 145 160 66 193 321), lower := (rows 13 98 22 296 145 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 70 129 257), good := (rows 477 66 86 264 401 128 66 128 256) }] }

theorem u3913 : Upper (D 7) (R 7) [12,96,18,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3914 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 148, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,0)], upper := (rows 13 98 22 296 208 33 65 130 386), lower := (rows 13 98 22 296 208 33 65 128 256), losses := [] }

theorem u3914 : Upper (D 7) (R 7) [12,96,18,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3915 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 22 296 208 33 66 129 385), lower := (rows 13 98 22 296 208 33 66 128 256), losses := [] }

theorem u3915 : Upper (D 7) (R 7) [12,96,18,288,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3916 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 22 296 208 33 192 131 259), lower := (rows 13 98 22 296 208 33 192 128 256), losses := [] }

theorem u3916 : Upper (D 7) (R 7) [12,96,18,288,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3917 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 102, targets := 128 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 22 392 145 33 66 224 352), lower := (rows 13 98 22 392 145 33 66 128 256), losses := [] }

theorem u3917 : Upper (D 7) (R 7) [12,96,18,384,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3918 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 22 392 145 34 96 193 321), lower := (rows 13 98 22 392 145 34 96 128 256), losses := [] }

theorem u3918 : Upper (D 7) (R 7) [12,96,18,384,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3919 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 37 88 145 288 66 130 386), lower := (rows 13 98 37 88 145 288 66 128 256), losses := [] }

theorem u3919 : Upper (D 7) (R 7) [12,96,33,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3919 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3920 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 37 88 145 288 192 130 258), lower := (rows 13 98 37 88 145 288 192 128 256), losses := [] }

theorem u3920 : Upper (D 7) (R 7) [12,96,33,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3920 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3921 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 88 146 288 65 130 386), lower := (rows 13 98 37 88 146 288 65 128 256), losses := [] }

theorem u3921 : Upper (D 7) (R 7) [12,96,33,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3921 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3922 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 13 98 37 88 146 288 66 129 385), lower := (rows 13 98 37 88 146 288 66 128 256), losses := [] }

theorem u3922 : Upper (D 7) (R 7) [12,96,33,80,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3922 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3923 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 37 88 146 288 192 131 259), lower := (rows 13 98 37 88 146 288 192 128 256), losses := [] }

theorem u3923 : Upper (D 7) (R 7) [12,96,33,80,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3923 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3924 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(0,6),(1,0),(1,7),(3,0)], upper := (rows 13 98 37 88 273 160 66 130 386), lower := (rows 13 98 37 88 273 160 66 128 256), losses := [{ target := 6, region := (rows 9 2 13 8 24 234 0 194 322), good := (rows 61 418 37 445 277 160 418 160 256) }] }

theorem u3924 : Upper (D 7) (R 7) [12,96,33,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3925 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 37 88 273 160 192 130 258), lower := (rows 13 98 37 88 273 160 192 128 256), losses := [] }

theorem u3925 : Upper (D 7) (R 7) [12,96,33,80,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3926 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 37 88 274 160 65 130 386), lower := (rows 13 98 37 88 274 160 65 128 256), losses := [] }

theorem u3926 : Upper (D 7) (R 7) [12,96,33,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3927 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 88 274 160 66 129 385), lower := (rows 13 98 37 88 274 160 66 128 256), losses := [] }

theorem u3927 : Upper (D 7) (R 7) [12,96,33,80,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3928 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 37 88 274 160 192 131 259), lower := (rows 13 98 37 88 274 160 192 128 256), losses := [] }

theorem u3928 : Upper (D 7) (R 7) [12,96,33,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3929 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 82, targets := 128 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 13 98 37 138 81 288 66 144 400), lower := (rows 13 98 37 138 81 288 66 128 256), losses := [] }

theorem u3929 : Upper (D 7) (R 7) [12,96,33,130,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3929 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3930 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 13 98 37 138 81 288 80 130 386), lower := (rows 13 98 37 138 81 288 80 128 256), losses := [] }

theorem u3930 : Upper (D 7) (R 7) [12,96,33,130,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3930 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3931 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 37 138 81 288 192 146 274), lower := (rows 13 98 37 138 81 288 192 128 256), losses := [] }

theorem u3931 : Upper (D 7) (R 7) [12,96,33,130,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3931 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3932 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 138 208 288 65 146 274), lower := (rows 13 98 37 138 208 288 65 128 256), losses := [] }

theorem u3932 : Upper (D 7) (R 7) [12,96,33,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3932 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3933 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 3, region := 80, targets := 1 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 37 138 208 288 66 145 273), lower := (rows 13 98 37 138 208 288 66 128 256), losses := [] }

theorem u3933 : Upper (D 7) (R 7) [12,96,33,130,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3933 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3934 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 13 98 37 138 208 288 80 131 259), lower := (rows 13 98 37 138 208 288 80 128 256), losses := [] }

theorem u3934 : Upper (D 7) (R 7) [12,96,33,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3934 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3935 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 138 274 48 65 192 448), lower := (rows 13 98 37 138 274 48 65 128 256), losses := [] }

theorem u3935 : Upper (D 7) (R 7) [12,96,33,130,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3935 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3936 : Route 9 := (fun mask => (mask,id))

def c3936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3936 : Upper (D 7) (R 7) [12,96,33,130,258,16,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,258,16,128] 13 (by decide) (choices 1) [1,64] r3936 c3936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u276
  · exact u277

def b3937 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 138 400 48 65 194 322), lower := (rows 13 98 37 138 400 48 65 128 256), losses := [] }

theorem u3937 : Upper (D 7) (R 7) [12,96,33,130,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3937 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3938 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 37 138 400 48 66 193 321), lower := (rows 13 98 37 138 400 48 66 128 256), losses := [] }

theorem u3938 : Upper (D 7) (R 7) [12,96,33,130,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3938 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3939 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 82, targets := 128 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 13 98 37 152 81 288 66 130 386), lower := (rows 13 98 37 152 81 288 66 128 256), losses := [] }

theorem u3939 : Upper (D 7) (R 7) [12,96,33,144,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3939 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3940 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 37 152 81 288 192 130 258), lower := (rows 13 98 37 152 81 288 192 128 256), losses := [] }

theorem u3940 : Upper (D 7) (R 7) [12,96,33,144,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3940 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3941 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 200 146 288 65 146 274), lower := (rows 13 98 37 200 146 288 65 128 256), losses := [] }

theorem u3941 : Upper (D 7) (R 7) [12,96,33,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3941 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3942 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 72, targets := 1 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 37 200 146 288 66 145 273), lower := (rows 13 98 37 200 146 288 66 128 256), losses := [] }

theorem u3942 : Upper (D 7) (R 7) [12,96,33,192,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3942 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3943 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 13 98 37 200 146 288 80 131 259), lower := (rows 13 98 37 200 146 288 80 128 256), losses := [] }

theorem u3943 : Upper (D 7) (R 7) [12,96,33,192,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3943 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3944 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 200 274 48 65 130 386), lower := (rows 13 98 37 200 274 48 65 128 256), losses := [] }

theorem u3944 : Upper (D 7) (R 7) [12,96,33,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3944 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3945 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 37 200 274 48 66 129 385), lower := (rows 13 98 37 200 274 48 66 128 256), losses := [] }

theorem u3945 : Upper (D 7) (R 7) [12,96,33,192,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3945 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3946 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 37 200 274 48 192 131 259), lower := (rows 13 98 37 200 274 48 192 128 256), losses := [] }

theorem u3946 : Upper (D 7) (R 7) [12,96,33,192,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3946 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3947 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 98 37 200 400 48 65 130 258), lower := (rows 13 98 37 200 400 48 65 128 256), losses := [] }

theorem u3947 : Upper (D 7) (R 7) [12,96,33,192,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3947 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3948 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 37 200 400 48 66 131 259), lower := (rows 13 98 37 200 400 48 66 128 256), losses := [] }

theorem u3948 : Upper (D 7) (R 7) [12,96,33,192,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3948 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3949 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 32 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 265 146 160 66 208 336), lower := (rows 13 98 37 265 146 160 66 128 256), losses := [] }

theorem u3949 : Upper (D 7) (R 7) [12,96,33,257,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3950 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 37 265 146 160 80 194 322), lower := (rows 13 98 37 265 146 160 80 128 256), losses := [] }

theorem u3950 : Upper (D 7) (R 7) [12,96,33,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3950 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3951 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 32 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 265 208 160 66 146 274), lower := (rows 13 98 37 265 208 160 66 128 256), losses := [] }

theorem u3951 : Upper (D 7) (R 7) [12,96,33,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3952 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 265 208 160 80 130 258), lower := (rows 13 98 37 265 208 160 80 128 256), losses := [] }

theorem u3952 : Upper (D 7) (R 7) [12,96,33,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3952 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3953 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 82, targets := 128 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 37 266 81 160 66 144 400), lower := (rows 13 98 37 266 81 160 66 128 256), losses := [] }

theorem u3953 : Upper (D 7) (R 7) [12,96,33,258,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3954 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 13 98 37 266 81 160 80 130 386), lower := (rows 13 98 37 266 81 160 80 128 256), losses := [] }

theorem u3954 : Upper (D 7) (R 7) [12,96,33,258,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3954 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3955 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 37 266 81 160 192 146 274), lower := (rows 13 98 37 266 81 160 192 128 256), losses := [] }

theorem u3955 : Upper (D 7) (R 7) [12,96,33,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3956 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 266 146 48 65 192 448), lower := (rows 13 98 37 266 146 48 65 128 256), losses := [] }

theorem u3956 : Upper (D 7) (R 7) [12,96,33,258,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3956 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3957 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 37 266 146 48 192 193 321), lower := (rows 13 98 37 266 146 48 192 128 256), losses := [] }

theorem u3957 : Upper (D 7) (R 7) [12,96,33,258,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3957 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3958 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 37 266 146 160 65 208 336), lower := (rows 13 98 37 266 146 160 65 128 256), losses := [] }

theorem u3958 : Upper (D 7) (R 7) [12,96,33,258,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3959 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 37 266 146 160 80 193 321), lower := (rows 13 98 37 266 146 160 80 128 256), losses := [] }

theorem u3959 : Upper (D 7) (R 7) [12,96,33,258,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3959 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3959
end Delivery.IrregularNine14.P07
