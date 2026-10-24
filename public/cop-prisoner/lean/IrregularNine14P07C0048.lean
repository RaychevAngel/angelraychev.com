import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0003

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2880 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 44 73 208 160 65 146 274), lower := (rows 7 290 44 73 208 160 65 128 256), losses := [] }

theorem u2880 : Upper (D 7) (R 7) [6,288,40,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2881 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 290 44 73 208 160 66 145 273), lower := (rows 7 290 44 73 208 160 66 128 256), losses := [] }

theorem u2881 : Upper (D 7) (R 7) [6,288,40,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2882 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 290 44 73 208 160 80 131 259), lower := (rows 7 290 44 73 208 160 80 128 256), losses := [] }

theorem u2882 : Upper (D 7) (R 7) [6,288,40,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2882 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2883 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 290 44 74 145 160 65 208 336), lower := (rows 7 290 44 74 145 160 65 128 256), losses := [] }

theorem u2883 : Upper (D 7) (R 7) [6,288,40,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2884 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 290 44 74 145 160 80 193 321), lower := (rows 7 290 44 74 145 160 80 128 256), losses := [] }

theorem u2884 : Upper (D 7) (R 7) [6,288,40,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2884 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2885 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 290 44 74 208 160 65 145 273), lower := (rows 7 290 44 74 208 160 65 128 256), losses := [] }

theorem u2885 : Upper (D 7) (R 7) [6,288,40,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2886 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 290 44 74 208 160 80 129 257), lower := (rows 7 290 44 74 208 160 80 128 256), losses := [] }

theorem u2886 : Upper (D 7) (R 7) [6,288,40,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2886 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2887 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 290 44 88 146 33 65 192 448), lower := (rows 7 290 44 88 146 33 65 128 256), losses := [] }

theorem u2887 : Upper (D 7) (R 7) [6,288,40,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2888 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 290 44 88 146 33 192 193 321), lower := (rows 7 290 44 88 146 33 192 128 256), losses := [] }

theorem u2888 : Upper (D 7) (R 7) [6,288,40,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2889 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 172, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(4,5)], upper := (rows 7 290 44 200 81 33 66 144 400), lower := (rows 7 290 44 200 81 33 66 128 256), losses := [] }

theorem u2889 : Upper (D 7) (R 7) [6,288,40,192,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2890 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 290 44 200 81 33 80 130 386), lower := (rows 7 290 44 200 81 33 80 128 256), losses := [] }

theorem u2890 : Upper (D 7) (R 7) [6,288,40,192,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2890 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2891 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 290 44 200 81 33 192 146 274), lower := (rows 7 290 44 200 81 33 192 128 256), losses := [] }

theorem u2891 : Upper (D 7) (R 7) [6,288,40,192,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2892 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 136, targets := 35 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,0),(3,1),(3,5),(4,5)], upper := (rows 7 290 44 200 82 33 65 144 400), lower := (rows 7 290 44 200 82 33 65 128 256), losses := [] }

theorem u2892 : Upper (D 7) (R 7) [6,288,40,192,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2893 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 290 44 200 82 33 80 129 385), lower := (rows 7 290 44 200 82 33 80 128 256), losses := [] }

theorem u2893 : Upper (D 7) (R 7) [6,288,40,192,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2893 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2894 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 290 44 200 82 33 192 145 273), lower := (rows 7 290 44 200 82 33 192 128 256), losses := [] }

theorem u2894 : Upper (D 7) (R 7) [6,288,40,192,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2895 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 69 25 112 160 66 136 392), lower := (rows 7 290 69 25 112 160 66 128 256), losses := [] }

theorem u2895 : Upper (D 7) (R 7) [6,288,65,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2896 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 25 112 160 72 130 386), lower := (rows 7 290 69 25 112 160 72 128 256), losses := [] }

theorem u2896 : Upper (D 7) (R 7) [6,288,65,17,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2896 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2897 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 69 25 112 160 192 138 266), lower := (rows 7 290 69 25 112 160 192 128 256), losses := [] }

theorem u2897 : Upper (D 7) (R 7) [6,288,65,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2898 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 25 146 96 72 160 416), lower := (rows 7 290 69 25 146 96 72 128 256), losses := [] }

theorem u2898 : Upper (D 7) (R 7) [6,288,65,17,130,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2898 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2899 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 290 69 25 146 96 96 136 392), lower := (rows 7 290 69 25 146 96 96 128 256), losses := [] }

theorem u2899 : Upper (D 7) (R 7) [6,288,65,17,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2900 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 7 290 69 25 146 96 192 168 296), lower := (rows 7 290 69 25 146 96 192 128 256), losses := [] }

theorem u2900 : Upper (D 7) (R 7) [6,288,65,17,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2901 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 25 146 160 72 224 352), lower := (rows 7 290 69 25 146 160 72 128 256), losses := [] }

theorem u2901 : Upper (D 7) (R 7) [6,288,65,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2901 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2902 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 290 69 25 146 160 96 200 328), lower := (rows 7 290 69 25 146 160 96 128 256), losses := [] }

theorem u2902 : Upper (D 7) (R 7) [6,288,65,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2903 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 290 69 25 176 96 66 136 392), lower := (rows 7 290 69 25 176 96 66 128 256), losses := [] }

theorem u2903 : Upper (D 7) (R 7) [6,288,65,17,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2904 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 25 176 96 72 130 386), lower := (rows 7 290 69 25 176 96 72 128 256), losses := [] }

theorem u2904 : Upper (D 7) (R 7) [6,288,65,17,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2904 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2905 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 6, region := 48, targets := 2 }], pairs := [(1,0),(2,1),(4,0),(4,1)], upper := (rows 7 290 69 25 176 96 192 138 266), lower := (rows 7 290 69 25 176 96 192 128 256), losses := [{ target := 1, region := (rows 1 0 12 12 208 252 208 128 256), good := (rows 45 288 125 125 240 112 240 240 256) }] }

theorem u2905 : Upper (D 7) (R 7) [6,288,65,17,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2906 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 25 208 160 66 168 296), lower := (rows 7 290 69 25 208 160 66 128 256), losses := [] }

theorem u2906 : Upper (D 7) (R 7) [6,288,65,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2907 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 7 290 69 25 208 160 72 162 290), lower := (rows 7 290 69 25 208 160 72 128 256), losses := [] }

theorem u2907 : Upper (D 7) (R 7) [6,288,65,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2907 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2908 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 290 69 25 208 160 96 138 266), lower := (rows 7 290 69 25 208 160 96 128 256), losses := [] }

theorem u2908 : Upper (D 7) (R 7) [6,288,65,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2909 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 69 26 112 160 65 136 392), lower := (rows 7 290 69 26 112 160 65 128 256), losses := [] }

theorem u2909 : Upper (D 7) (R 7) [6,288,65,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2910 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 26 112 160 72 129 385), lower := (rows 7 290 69 26 112 160 72 128 256), losses := [] }

theorem u2910 : Upper (D 7) (R 7) [6,288,65,18,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2910 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2911 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 69 26 112 160 192 137 265), lower := (rows 7 290 69 26 112 160 192 128 256), losses := [] }

theorem u2911 : Upper (D 7) (R 7) [6,288,65,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2912 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 26 145 96 72 160 416), lower := (rows 7 290 69 26 145 96 72 128 256), losses := [] }

theorem u2912 : Upper (D 7) (R 7) [6,288,65,18,129,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2912 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2913 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 290 69 26 145 96 96 136 392), lower := (rows 7 290 69 26 145 96 96 128 256), losses := [] }

theorem u2913 : Upper (D 7) (R 7) [6,288,65,18,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2914 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 68, targets := 2 },{ cop := 4, region := 68, targets := 32 }], pairs := [(1,0),(2,1),(2,5),(3,0)], upper := (rows 7 290 69 26 145 96 192 168 296), lower := (rows 7 290 69 26 145 96 192 128 256), losses := [] }

theorem u2914 : Upper (D 7) (R 7) [6,288,65,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2915 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 26 145 160 72 224 352), lower := (rows 7 290 69 26 145 160 72 128 256), losses := [] }

theorem u2915 : Upper (D 7) (R 7) [6,288,65,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2915 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2916 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 7 290 69 26 145 160 96 200 328), lower := (rows 7 290 69 26 145 160 96 128 256), losses := [] }

theorem u2916 : Upper (D 7) (R 7) [6,288,65,18,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2917 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 290 69 26 152 96 65 160 416), lower := (rows 7 290 69 26 152 96 65 128 256), losses := [] }

theorem u2917 : Upper (D 7) (R 7) [6,288,65,18,136,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2918 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 290 69 26 152 96 96 129 385), lower := (rows 7 290 69 26 152 96 96 128 256), losses := [] }

theorem u2918 : Upper (D 7) (R 7) [6,288,65,18,136,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2919 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 263, targets := 128 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 7 290 69 26 152 96 192 161 289), lower := (rows 7 290 69 26 152 96 192 128 256), losses := [] }

theorem u2919 : Upper (D 7) (R 7) [6,288,65,18,136,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2920 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 290 69 26 176 96 65 136 392), lower := (rows 7 290 69 26 176 96 65 128 256), losses := [] }

theorem u2920 : Upper (D 7) (R 7) [6,288,65,18,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2921 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 26 176 96 72 129 385), lower := (rows 7 290 69 26 176 96 72 128 256), losses := [] }

theorem u2921 : Upper (D 7) (R 7) [6,288,65,18,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2921 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2922 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 197, targets := 32 },{ cop := 6, region := 48, targets := 3 }], pairs := [(0,5),(2,5),(4,0),(4,1)], upper := (rows 7 290 69 26 176 96 192 137 265), lower := (rows 7 290 69 26 176 96 192 128 256), losses := [] }

theorem u2922 : Upper (D 7) (R 7) [6,288,65,18,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2923 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 290 69 26 208 33 72 160 416), lower := (rows 7 290 69 26 208 33 72 128 256), losses := [] }

theorem u2923 : Upper (D 7) (R 7) [6,288,65,18,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2923 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2924 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 290 69 26 208 33 96 136 392), lower := (rows 7 290 69 26 208 33 96 128 256), losses := [] }

theorem u2924 : Upper (D 7) (R 7) [6,288,65,18,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2925 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 69 26 208 33 192 168 296), lower := (rows 7 290 69 26 208 33 192 128 256), losses := [] }

theorem u2925 : Upper (D 7) (R 7) [6,288,65,18,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2926 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 26 208 40 65 160 416), lower := (rows 7 290 69 26 208 40 65 128 256), losses := [] }

theorem u2926 : Upper (D 7) (R 7) [6,288,65,18,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2926 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2927 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 7 290 69 26 208 40 96 129 385), lower := (rows 7 290 69 26 208 40 96 128 256), losses := [] }

theorem u2927 : Upper (D 7) (R 7) [6,288,65,18,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2927 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2928 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 69 26 208 40 192 161 289), lower := (rows 7 290 69 26 208 40 192 128 256), losses := [] }

theorem u2928 : Upper (D 7) (R 7) [6,288,65,18,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2928 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2929 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 26 208 160 65 168 296), lower := (rows 7 290 69 26 208 160 65 128 256), losses := [] }

theorem u2929 : Upper (D 7) (R 7) [6,288,65,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2930 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 26 208 160 72 161 289), lower := (rows 7 290 69 26 208 160 72 128 256), losses := [] }

theorem u2930 : Upper (D 7) (R 7) [6,288,65,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2930 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2931 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,7),(2,7),(4,0),(4,1)], upper := (rows 7 290 69 26 208 160 96 137 265), lower := (rows 7 290 69 26 208 160 96 128 256), losses := [] }

theorem u2931 : Upper (D 7) (R 7) [6,288,65,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2932 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 69 41 88 160 66 144 400), lower := (rows 7 290 69 41 88 160 66 128 256), losses := [] }

theorem u2932 : Upper (D 7) (R 7) [6,288,65,33,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2933 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 84, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 7 290 69 41 88 160 80 130 386), lower := (rows 7 290 69 41 88 160 80 128 256), losses := [] }

theorem u2933 : Upper (D 7) (R 7) [6,288,65,33,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2933 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2934 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 466, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(2,1),(4,0)], upper := (rows 7 290 69 41 88 160 192 146 274), lower := (rows 7 290 69 41 88 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 12 12 28 224 224 128 256), good := (rows 29 352 125 125 124 224 224 224 256) }] }

theorem u2934 : Upper (D 7) (R 7) [6,288,65,33,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2935 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 41 146 160 72 208 336), lower := (rows 7 290 69 41 146 160 72 128 256), losses := [] }

theorem u2935 : Upper (D 7) (R 7) [6,288,65,33,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2935 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2936 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 41 146 160 80 200 328), lower := (rows 7 290 69 41 146 160 80 128 256), losses := [] }

theorem u2936 : Upper (D 7) (R 7) [6,288,65,33,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2936 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2937 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 41 152 160 66 208 336), lower := (rows 7 290 69 41 152 160 66 128 256), losses := [] }

theorem u2937 : Upper (D 7) (R 7) [6,288,65,33,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2938 : Route 9 := (fun mask => (mask,id))

def c2938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2938 : Upper (D 7) (R 7) [6,288,65,33,136,128,16] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,136,128,16] 13 (by decide) (choices 1) [2,64] r2938 c2938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u183
  · exact u184

def b2939 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 41 208 160 66 152 280), lower := (rows 7 290 69 41 208 160 66 128 256), losses := [] }

theorem u2939 : Upper (D 7) (R 7) [6,288,65,33,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2939
end Delivery.IrregularNine14.P07
