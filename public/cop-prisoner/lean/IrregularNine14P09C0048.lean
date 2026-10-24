import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2880 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,7)], upper := (rows 97 38 196 266 400 33 80 137 265), lower := (rows 97 38 196 266 400 33 80 128 256), losses := [] }

theorem u2880 : Upper (D 9) (R 9) [96,36,192,258,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2880 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2881 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 1, region := 65, targets := 384 }], pairs := [(0,7),(0,8),(2,5),(4,5)], upper := (rows 97 38 196 266 400 40 65 145 273), lower := (rows 97 38 196 266 400 40 65 128 256), losses := [] }

theorem u2881 : Upper (D 9) (R 9) [96,36,192,258,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2881 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2882 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 38 196 266 400 40 80 129 257), lower := (rows 97 38 196 266 400 40 80 128 256), losses := [] }

theorem u2882 : Upper (D 9) (R 9) [96,36,192,258,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2882 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2883 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 103, targets := 256 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 97 38 196 266 400 48 65 137 265), lower := (rows 97 38 196 266 400 48 65 128 256), losses := [] }

theorem u2883 : Upper (D 9) (R 9) [96,36,192,258,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2883 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2884 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 38 196 266 400 48 72 129 257), lower := (rows 97 38 196 266 400 48 72 128 256), losses := [] }

theorem u2884 : Upper (D 9) (R 9) [96,36,192,258,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2884 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2885 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 388 137 273 40 66 208 336), lower := (rows 97 38 388 137 273 40 66 128 256), losses := [] }

theorem u2885 : Upper (D 9) (R 9) [96,36,384,129,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2885 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2886 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,0),(2,0)], upper := (rows 97 38 388 137 273 40 80 194 322), lower := (rows 97 38 388 137 273 40 80 128 256), losses := [] }

theorem u2886 : Upper (D 9) (R 9) [96,36,384,129,257,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2886 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2887 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 1 },{ cop := 2, region := 105, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(4,0)], upper := (rows 97 38 388 137 274 33 72 208 336), lower := (rows 97 38 388 137 274 33 72 128 256), losses := [] }

theorem u2887 : Upper (D 9) (R 9) [96,36,384,129,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2887 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2888 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 0, region := 396, targets := 32 }], pairs := [(0,7),(1,7),(2,5),(4,7)], upper := (rows 97 38 388 137 274 33 80 200 328), lower := (rows 97 38 388 137 274 33 80 128 256), losses := [] }

theorem u2888 : Upper (D 9) (R 9) [96,36,384,129,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2888 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2889 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 388 137 280 33 66 208 336), lower := (rows 97 38 388 137 280 33 66 128 256), losses := [] }

theorem u2889 : Upper (D 9) (R 9) [96,36,384,129,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2889 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2890 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 4, region := 97, targets := 384 }], pairs := [(0,7),(0,8),(1,0),(2,0)], upper := (rows 97 38 388 137 280 33 80 194 322), lower := (rows 97 38 388 137 280 33 80 128 256), losses := [] }

theorem u2890 : Upper (D 9) (R 9) [96,36,384,129,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2890 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2891 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 1, region := 201, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,8)], upper := (rows 97 38 388 137 280 48 65 194 322), lower := (rows 97 38 388 137 280 48 65 128 256), losses := [] }

theorem u2891 : Upper (D 9) (R 9) [96,36,384,129,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2891 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2892 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 388 137 280 48 66 193 321), lower := (rows 97 38 388 137 280 48 66 128 256), losses := [] }

theorem u2892 : Upper (D 9) (R 9) [96,36,384,129,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2892 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2893 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 97 38 388 137 336 33 66 152 280), lower := (rows 97 38 388 137 336 33 66 128 256), losses := [] }

theorem u2893 : Upper (D 9) (R 9) [96,36,384,129,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2893 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2894 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 },{ cop := 2, region := 105, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(4,0)], upper := (rows 97 38 388 137 336 33 72 146 274), lower := (rows 97 38 388 137 336 33 72 128 256), losses := [] }

theorem u2894 : Upper (D 9) (R 9) [96,36,384,129,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2894 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2895 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 388 137 336 33 80 138 266), lower := (rows 97 38 388 137 336 33 80 128 256), losses := [] }

theorem u2895 : Upper (D 9) (R 9) [96,36,384,129,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2895 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2896 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 },{ cop := 2, region := 105, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(4,0)], upper := (rows 97 38 388 137 336 40 65 146 274), lower := (rows 97 38 388 137 336 40 65 128 256), losses := [] }

theorem u2896 : Upper (D 9) (R 9) [96,36,384,129,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2896 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2897 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 388 137 336 40 66 145 273), lower := (rows 97 38 388 137 336 40 66 128 256), losses := [] }

theorem u2897 : Upper (D 9) (R 9) [96,36,384,129,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2897 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2898 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 38 388 137 336 40 80 131 259), lower := (rows 97 38 388 137 336 40 80 128 256), losses := [] }

theorem u2898 : Upper (D 9) (R 9) [96,36,384,129,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2898 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2899 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 2, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 38 388 138 280 33 65 208 336), lower := (rows 97 38 388 138 280 33 65 128 256), losses := [] }

theorem u2899 : Upper (D 9) (R 9) [96,36,384,130,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2899 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2900 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 369, targets := 128 },{ cop := 0, region := 388, targets := 32 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(2,5),(4,7)], upper := (rows 97 38 388 138 280 33 80 193 321), lower := (rows 97 38 388 138 280 33 80 128 256), losses := [] }

theorem u2900 : Upper (D 9) (R 9) [96,36,384,130,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2900 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2901 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 38 388 138 336 33 65 152 280), lower := (rows 97 38 388 138 336 33 65 128 256), losses := [] }

theorem u2901 : Upper (D 9) (R 9) [96,36,384,130,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2901 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2902 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 0, region := 404, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(3,8)], upper := (rows 97 38 388 138 336 33 72 145 273), lower := (rows 97 38 388 138 336 33 72 128 256), losses := [] }

theorem u2902 : Upper (D 9) (R 9) [96,36,384,130,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2902 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2903 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 388 138 336 33 80 137 265), lower := (rows 97 38 388 138 336 33 80 128 256), losses := [] }

theorem u2903 : Upper (D 9) (R 9) [96,36,384,130,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2903 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2904 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 38 388 152 336 33 65 138 266), lower := (rows 97 38 388 152 336 33 65 128 256), losses := [] }

theorem u2904 : Upper (D 9) (R 9) [96,36,384,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2904 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2905 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 97 38 388 152 336 33 66 137 265), lower := (rows 97 38 388 152 336 33 66 128 256), losses := [] }

theorem u2905 : Upper (D 9) (R 9) [96,36,384,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2905 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2906 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 388 152 336 33 72 131 259), lower := (rows 97 38 388 152 336 33 72 128 256), losses := [] }

theorem u2906 : Upper (D 9) (R 9) [96,36,384,144,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2906 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2907 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 264, targets := 128 },{ cop := 0, region := 130, targets := 256 }], pairs := [(1,8),(2,0),(3,7)], upper := (rows 97 131 140 265 274 36 80 224 352), lower := (rows 97 131 140 265 274 36 80 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 44 82 129 257), good := (rows 480 466 172 428 338 36 80 128 256) }] }

theorem u2907 : Upper (D 9) (R 9) [96,129,136,257,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2907 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2908 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 131 140 265 274 36 96 208 336), lower := (rows 97 131 140 265 274 36 96 128 256), losses := [] }

theorem u2908 : Upper (D 9) (R 9) [96,129,136,257,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2908 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2909 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 227, targets := 256 },{ cop := 0, region := 264, targets := 128 }], pairs := [(0,8),(1,8),(3,7)], upper := (rows 97 131 140 265 276 34 80 224 352), lower := (rows 97 131 140 265 276 34 80 128 256), losses := [] }

theorem u2909 : Upper (D 9) (R 9) [96,129,136,257,260,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2909 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2910 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 131 140 265 276 34 96 208 336), lower := (rows 97 131 140 265 276 34 96 128 256), losses := [] }

theorem u2910 : Upper (D 9) (R 9) [96,129,136,257,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2910 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2911 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 131 140 265 276 48 96 194 322), lower := (rows 97 131 140 265 276 48 96 128 256), losses := [] }

theorem u2911 : Upper (D 9) (R 9) [96,129,136,257,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2911 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2912 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(3,7),(4,7)], upper := (rows 97 131 140 265 304 34 68 208 336), lower := (rows 97 131 140 265 304 34 68 128 256), losses := [] }

theorem u2912 : Upper (D 9) (R 9) [96,129,136,257,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2912 [(5,1),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2913 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 131 140 265 304 34 80 196 324), lower := (rows 97 131 140 265 304 34 80 128 256), losses := [] }

theorem u2913 : Upper (D 9) (R 9) [96,129,136,257,288,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2913 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2914 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(3,7),(4,7)], upper := (rows 97 131 140 265 304 36 66 208 336), lower := (rows 97 131 140 265 304 36 66 128 256), losses := [] }

theorem u2914 : Upper (D 9) (R 9) [96,129,136,257,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2914 [(5,2),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2915 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 131 140 265 304 36 80 194 322), lower := (rows 97 131 140 265 304 36 80 128 256), losses := [] }

theorem u2915 : Upper (D 9) (R 9) [96,129,136,257,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2915 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2916 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 131 140 266 276 33 80 224 352), lower := (rows 97 131 140 266 276 33 80 128 256), losses := [] }

theorem u2916 : Upper (D 9) (R 9) [96,129,136,258,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2916 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2917 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 131 140 266 276 33 96 208 336), lower := (rows 97 131 140 266 276 33 96 128 256), losses := [] }

theorem u2917 : Upper (D 9) (R 9) [96,129,136,258,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2917 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2918 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 131 140 266 304 33 68 208 336), lower := (rows 97 131 140 266 304 33 68 128 256), losses := [] }

theorem u2918 : Upper (D 9) (R 9) [96,129,136,258,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2918 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2919 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 97 131 140 266 304 33 80 196 324), lower := (rows 97 131 140 266 304 33 80 128 256), losses := [] }

theorem u2919 : Upper (D 9) (R 9) [96,129,136,258,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2919 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2920 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 396, targets := 1 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,7)], upper := (rows 97 131 140 268 274 33 80 224 352), lower := (rows 97 131 140 268 274 33 80 128 256), losses := [] }

theorem u2920 : Upper (D 9) (R 9) [96,129,136,260,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2920 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2921 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 131 140 268 274 33 96 208 336), lower := (rows 97 131 140 268 274 33 96 128 256), losses := [] }

theorem u2921 : Upper (D 9) (R 9) [96,129,136,260,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2921 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2922 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 97 131 140 268 304 33 66 208 336), lower := (rows 97 131 140 268 304 33 66 128 256), losses := [] }

theorem u2922 : Upper (D 9) (R 9) [96,129,136,260,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2922 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2923 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 97 131 140 268 304 33 80 194 322), lower := (rows 97 131 140 268 304 33 80 128 256), losses := [] }

theorem u2923 : Upper (D 9) (R 9) [96,129,136,260,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2923 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2924 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(1,5),(3,7),(4,5)], upper := (rows 97 131 140 296 273 34 68 208 336), lower := (rows 97 131 140 296 273 34 68 128 256), losses := [] }

theorem u2924 : Upper (D 9) (R 9) [96,129,136,288,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2924 [(5,1),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2925 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 396, targets := 1 },{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7),(2,0),(3,0)], upper := (rows 97 131 140 296 273 34 80 196 324), lower := (rows 97 131 140 296 273 34 80 128 256), losses := [] }

theorem u2925 : Upper (D 9) (R 9) [96,129,136,288,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2925 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2926 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(4,5)], upper := (rows 97 131 140 296 274 33 68 208 336), lower := (rows 97 131 140 296 274 33 68 128 256), losses := [] }

theorem u2926 : Upper (D 9) (R 9) [96,129,136,288,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2926 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2927 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 396, targets := 1 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(3,7)], upper := (rows 97 131 140 296 274 33 80 196 324), lower := (rows 97 131 140 296 274 33 80 128 256), losses := [] }

theorem u2927 : Upper (D 9) (R 9) [96,129,136,288,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2927 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2928 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(4,5)], upper := (rows 97 131 140 296 274 36 65 208 336), lower := (rows 97 131 140 296 274 36 65 128 256), losses := [] }

theorem u2928 : Upper (D 9) (R 9) [96,129,136,288,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2928 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2929 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 264, targets := 128 }], pairs := [(1,5),(3,7),(4,5)], upper := (rows 97 131 140 296 274 36 80 193 321), lower := (rows 97 131 140 296 274 36 80 128 256), losses := [] }

theorem u2929 : Upper (D 9) (R 9) [96,129,136,288,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2929 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2930 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 97 131 140 296 276 33 66 208 336), lower := (rows 97 131 140 296 276 33 66 128 256), losses := [] }

theorem u2930 : Upper (D 9) (R 9) [96,129,136,288,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2930 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2931 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,7)], upper := (rows 97 131 140 296 276 33 80 194 322), lower := (rows 97 131 140 296 276 33 80 128 256), losses := [] }

theorem u2931 : Upper (D 9) (R 9) [96,129,136,288,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2931 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2932 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 97 131 140 296 276 34 65 208 336), lower := (rows 97 131 140 296 276 34 65 128 256), losses := [] }

theorem u2932 : Upper (D 9) (R 9) [96,129,136,288,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2932 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2933 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 227, targets := 256 },{ cop := 0, region := 130, targets := 32 }], pairs := [(0,8),(1,5),(1,8)], upper := (rows 97 131 140 296 276 34 80 193 321), lower := (rows 97 131 140 296 276 34 80 128 256), losses := [] }

theorem u2933 : Upper (D 9) (R 9) [96,129,136,288,260,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2933 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2934 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 97 131 140 296 336 33 66 148 276), lower := (rows 97 131 140 296 336 33 66 128 256), losses := [] }

theorem u2934 : Upper (D 9) (R 9) [96,129,136,288,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2934 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2935 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(4,5)], upper := (rows 97 131 140 296 336 33 68 146 274), lower := (rows 97 131 140 296 336 33 68 128 256), losses := [] }

theorem u2935 : Upper (D 9) (R 9) [96,129,136,288,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2935 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2936 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 8, region := 113, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 131 140 296 336 33 80 134 262), lower := (rows 97 131 140 296 336 33 80 128 256), losses := [] }

theorem u2936 : Upper (D 9) (R 9) [96,129,136,288,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2936 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2937 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 97 131 140 296 336 34 65 148 276), lower := (rows 97 131 140 296 336 34 65 128 256), losses := [] }

theorem u2937 : Upper (D 9) (R 9) [96,129,136,288,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2937 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2938 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(1,5),(3,7),(4,5)], upper := (rows 97 131 140 296 336 34 68 145 273), lower := (rows 97 131 140 296 336 34 68 128 256), losses := [] }

theorem u2938 : Upper (D 9) (R 9) [96,129,136,288,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2938 [(5,1),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2939 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 140 296 336 34 80 133 261), lower := (rows 97 131 140 296 336 34 80 128 256), losses := [] }

theorem u2939 : Upper (D 9) (R 9) [96,129,136,288,320,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2939 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2939
end Delivery.IrregularNine14.P09
