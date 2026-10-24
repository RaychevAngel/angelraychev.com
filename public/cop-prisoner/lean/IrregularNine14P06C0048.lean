import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0003

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2880 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 296 84 33 80 193 321), lower := (rows 11 38 134 296 84 33 80 128 256), losses := [] }

theorem u2880 : Upper (D 6) (R 6) [10,36,130,288,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2880 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2881 : Route 9 := (fun mask => (mask,id))

def c2881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2881 : Upper (D 6) (R 6) [10,36,130,320,5,64,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,5,64,1] 13 (by decide) (choices 1) [16,32] r2881 c2881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u202
  · exact u203

def b2882 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 360, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 38 134 328 21 96 80 161 289), lower := (rows 11 38 134 328 21 96 80 128 256), losses := [] }

theorem u2882 : Upper (D 6) (R 6) [10,36,130,320,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2882 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2883 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 148, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 134 328 21 96 96 145 273), lower := (rows 11 38 134 328 21 96 96 128 256), losses := [] }

theorem u2883 : Upper (D 6) (R 6) [10,36,130,320,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2884 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 6 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 38 134 328 81 33 68 176 304), lower := (rows 11 38 134 328 81 33 68 128 256), losses := [] }

theorem u2884 : Upper (D 6) (R 6) [10,36,130,320,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2885 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 134 328 81 33 80 164 292), lower := (rows 11 38 134 328 81 33 80 128 256), losses := [] }

theorem u2885 : Upper (D 6) (R 6) [10,36,130,320,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2885 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2886 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 11 38 134 328 81 33 96 148 276), lower := (rows 11 38 134 328 81 33 96 128 256), losses := [] }

theorem u2886 : Upper (D 6) (R 6) [10,36,130,320,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2887 : PairBound 9 := { available := 48, camps := [], pairs := [(3,1),(3,2),(4,1)], upper := (rows 11 38 134 328 84 33 65 176 304), lower := (rows 11 38 134 328 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 123 18 97 97 147 275), good := (rows 505 508 412 360 508 489 489 128 256) },{ target := 2, region := (rows 1 2 0 24 16 97 97 144 272), good := (rows 107 98 130 360 504 97 97 128 256) }] }

theorem u2887 : Upper (D 6) (R 6) [10,36,130,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2888 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 328 84 33 80 161 289), lower := (rows 11 38 134 328 84 33 80 128 256), losses := [] }

theorem u2888 : Upper (D 6) (R 6) [10,36,130,320,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2888 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2889 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 11 38 134 328 84 33 96 145 273), lower := (rows 11 38 134 328 84 33 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 41 22 33 99 129 257), good := (rows 505 124 212 328 84 489 104 128 256) }] }

theorem u2889 : Upper (D 6) (R 6) [10,36,130,320,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2890 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 134 328 112 33 65 148 276), lower := (rows 11 38 134 328 112 33 65 128 256), losses := [] }

theorem u2890 : Upper (D 6) (R 6) [10,36,130,320,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2891 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 11 38 134 328 112 33 68 145 273), lower := (rows 11 38 134 328 112 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 27 19 33 70 161 289), good := (rows 505 508 220 328 504 441 68 128 256) }] }

theorem u2891 : Upper (D 6) (R 6) [10,36,130,320,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2892 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 134 328 112 33 80 133 261), lower := (rows 11 38 134 328 112 33 80 128 256), losses := [] }

theorem u2892 : Upper (D 6) (R 6) [10,36,130,320,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2892 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2893 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 148 73 274 96 65 164 292), lower := (rows 11 38 148 73 274 96 65 128 256), losses := [] }

theorem u2893 : Upper (D 6) (R 6) [10,36,144,65,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2894 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 73 274 96 68 161 289), lower := (rows 11 38 148 73 274 96 68 128 256), losses := [] }

theorem u2894 : Upper (D 6) (R 6) [10,36,144,65,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2895 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 148 73 274 96 96 133 261), lower := (rows 11 38 148 73 274 96 96 128 256), losses := [] }

theorem u2895 : Upper (D 6) (R 6) [10,36,144,65,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2896 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 148 73 276 96 65 162 290), lower := (rows 11 38 148 73 276 96 65 128 256), losses := [] }

theorem u2896 : Upper (D 6) (R 6) [10,36,144,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2897 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 1, region := 73, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 38 148 73 276 96 66 161 289), lower := (rows 11 38 148 73 276 96 66 128 256), losses := [] }

theorem u2897 : Upper (D 6) (R 6) [10,36,144,65,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2898 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 148 73 276 96 96 131 259), lower := (rows 11 38 148 73 276 96 96 128 256), losses := [] }

theorem u2898 : Upper (D 6) (R 6) [10,36,144,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2899 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 148 73 304 96 65 134 262), lower := (rows 11 38 148 73 304 96 65 128 256), losses := [] }

theorem u2899 : Upper (D 6) (R 6) [10,36,144,65,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2900 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 1, region := 73, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 38 148 73 304 96 66 133 261), lower := (rows 11 38 148 73 304 96 66 128 256), losses := [] }

theorem u2900 : Upper (D 6) (R 6) [10,36,144,65,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2901 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 73 304 96 68 131 259), lower := (rows 11 38 148 73 304 96 68 128 256), losses := [] }

theorem u2901 : Upper (D 6) (R 6) [10,36,144,65,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2902 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 166, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 148 73 336 34 65 164 292), lower := (rows 11 38 148 73 336 34 65 128 256), losses := [] }

theorem u2902 : Upper (D 6) (R 6) [10,36,144,65,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2903 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 73 336 34 68 161 289), lower := (rows 11 38 148 73 336 34 68 128 256), losses := [] }

theorem u2903 : Upper (D 6) (R 6) [10,36,144,65,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2904 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 404, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 148 73 336 34 96 133 261), lower := (rows 11 38 148 73 336 34 96 128 256), losses := [] }

theorem u2904 : Upper (D 6) (R 6) [10,36,144,65,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2905 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 38 148 76 273 96 65 162 290), lower := (rows 11 38 148 76 273 96 65 128 256), losses := [] }

theorem u2905 : Upper (D 6) (R 6) [10,36,144,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2906 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 76 273 96 66 161 289), lower := (rows 11 38 148 76 273 96 66 128 256), losses := [] }

theorem u2906 : Upper (D 6) (R 6) [10,36,144,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2907 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 148 76 273 96 96 131 259), lower := (rows 11 38 148 76 273 96 96 128 256), losses := [] }

theorem u2907 : Upper (D 6) (R 6) [10,36,144,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2908 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 38 148 76 274 96 65 161 289), lower := (rows 11 38 148 76 274 96 65 128 256), losses := [] }

theorem u2908 : Upper (D 6) (R 6) [10,36,144,68,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2909 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 148 76 274 96 96 129 257), lower := (rows 11 38 148 76 274 96 96 128 256), losses := [] }

theorem u2909 : Upper (D 6) (R 6) [10,36,144,68,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2910 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 104 274 33 65 196 324), lower := (rows 11 38 148 104 274 33 65 128 256), losses := [] }

theorem u2910 : Upper (D 6) (R 6) [10,36,144,96,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2911 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 148 104 274 33 68 193 321), lower := (rows 11 38 148 104 274 33 68 128 256), losses := [] }

theorem u2911 : Upper (D 6) (R 6) [10,36,144,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2912 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 104 336 33 65 134 262), lower := (rows 11 38 148 104 336 33 65 128 256), losses := [] }

theorem u2912 : Upper (D 6) (R 6) [10,36,144,96,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2913 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 148 104 336 33 66 133 261), lower := (rows 11 38 148 104 336 33 66 128 256), losses := [] }

theorem u2913 : Upper (D 6) (R 6) [10,36,144,96,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2914 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 148 104 336 33 68 131 259), lower := (rows 11 38 148 104 336 33 68 128 256), losses := [] }

theorem u2914 : Upper (D 6) (R 6) [10,36,144,96,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2915 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 132, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 148 296 82 33 65 196 324), lower := (rows 11 38 148 296 82 33 65 128 256), losses := [] }

theorem u2915 : Upper (D 6) (R 6) [10,36,144,288,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2916 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 148 296 82 33 68 193 321), lower := (rows 11 38 148 296 82 33 68 128 256), losses := [] }

theorem u2916 : Upper (D 6) (R 6) [10,36,144,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2917 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 38 148 328 21 96 65 162 290), lower := (rows 11 38 148 328 21 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 20 72 16 104 64 131 259), good := (rows 426 422 148 360 404 104 488 128 256) }] }

theorem u2917 : Upper (D 6) (R 6) [10,36,144,320,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2918 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 148 328 21 96 66 161 289), lower := (rows 11 38 148 328 21 96 66 128 256), losses := [] }

theorem u2918 : Upper (D 6) (R 6) [10,36,144,320,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2919 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 148, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 148 328 21 96 96 131 259), lower := (rows 11 38 148 328 21 96 96 128 256), losses := [] }

theorem u2919 : Upper (D 6) (R 6) [10,36,144,320,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2920 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 38 148 328 82 33 65 164 292), lower := (rows 11 38 148 328 82 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 32 64 130 258), good := (rows 394 422 156 328 478 32 64 128 256) }] }

theorem u2920 : Upper (D 6) (R 6) [10,36,144,320,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2921 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 11 38 148 328 82 33 68 161 289), lower := (rows 11 38 148 328 82 33 68 128 256), losses := [] }

theorem u2921 : Upper (D 6) (R 6) [10,36,144,320,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2922 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 38 148 328 82 33 96 133 261), lower := (rows 11 38 148 328 82 33 96 128 256), losses := [] }

theorem u2922 : Upper (D 6) (R 6) [10,36,144,320,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2923 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2),(4,1)], upper := (rows 11 38 148 328 84 33 65 162 290), lower := (rows 11 38 148 328 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 18 97 97 128 256), good := (rows 121 116 148 360 116 97 97 128 256) }] }

theorem u2923 : Upper (D 6) (R 6) [10,36,144,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2924 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 11 38 148 328 84 33 66 161 289), lower := (rows 11 38 148 328 84 33 66 128 256), losses := [] }

theorem u2924 : Upper (D 6) (R 6) [10,36,144,320,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2925 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 11 38 148 328 84 33 96 131 259), lower := (rows 11 38 148 328 84 33 96 128 256), losses := [] }

theorem u2925 : Upper (D 6) (R 6) [10,36,144,320,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2926 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 148 328 112 33 65 134 262), lower := (rows 11 38 148 328 112 33 65 128 256), losses := [] }

theorem u2926 : Upper (D 6) (R 6) [10,36,144,320,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2927 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 1, region := 329, targets := 32 }], pairs := [(0,5),(4,0),(4,2)], upper := (rows 11 38 148 328 112 33 66 133 261), lower := (rows 11 38 148 328 112 33 66 128 256), losses := [] }

theorem u2927 : Upper (D 6) (R 6) [10,36,144,320,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2928 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(3,5),(4,0)], upper := (rows 11 38 148 328 112 33 68 131 259), lower := (rows 11 38 148 328 112 33 68 128 256), losses := [] }

theorem u2928 : Upper (D 6) (R 6) [10,36,144,320,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2929 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 196 25 112 288 65 134 262), lower := (rows 11 38 196 25 112 288 65 128 256), losses := [] }

theorem u2929 : Upper (D 6) (R 6) [10,36,192,17,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2929 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2930 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 196 25 112 288 66 133 261), lower := (rows 11 38 196 25 112 288 66 128 256), losses := [] }

theorem u2930 : Upper (D 6) (R 6) [10,36,192,17,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2930 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2931 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 38 196 25 112 288 68 131 259), lower := (rows 11 38 196 25 112 288 68 128 256), losses := [] }

theorem u2931 : Upper (D 6) (R 6) [10,36,192,17,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2931 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2932 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 25 336 34 65 164 292), lower := (rows 11 38 196 25 336 34 65 128 256), losses := [] }

theorem u2932 : Upper (D 6) (R 6) [10,36,192,17,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2933 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 38 196 25 336 34 68 161 289), lower := (rows 11 38 196 25 336 34 68 128 256), losses := [] }

theorem u2933 : Upper (D 6) (R 6) [10,36,192,17,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2934 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 196 25 336 34 96 133 261), lower := (rows 11 38 196 25 336 34 96 128 256), losses := [] }

theorem u2934 : Upper (D 6) (R 6) [10,36,192,17,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2935 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 196 56 336 33 65 134 262), lower := (rows 11 38 196 56 336 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 97 97 128 256), good := (rows 105 100 228 120 376 97 97 128 256) }] }

theorem u2935 : Upper (D 6) (R 6) [10,36,192,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2936 : Route 9 := (fun mask => (mask,id))

def c2936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2936 : Upper (D 6) (R 6) [10,36,192,48,320,1,2] 13 := by
  apply FastRouting.sound _ _ [10,36,192,48,320,1,2] 13 (by decide) (choices 1) [1,4] r2936 c2936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u204
  · exact u205

def b2937 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 56 336 33 68 131 259), lower := (rows 11 38 196 56 336 33 68 128 256), losses := [] }

theorem u2937 : Upper (D 6) (R 6) [10,36,192,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2938 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 38 196 73 274 48 65 164 292), lower := (rows 11 38 196 73 274 48 65 128 256), losses := [] }

theorem u2938 : Upper (D 6) (R 6) [10,36,192,65,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2938 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2939 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 38 196 73 274 48 68 161 289), lower := (rows 11 38 196 73 274 48 68 128 256), losses := [] }

theorem u2939 : Upper (D 6) (R 6) [10,36,192,65,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2939 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2939
end Delivery.IrregularNine14.P06
