import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0010

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7920 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 134 73 400 48 65 138 266), lower := (rows 37 98 134 73 400 48 65 128 256), losses := [] }

theorem u7920 : Upper (D 7) (R 7) [36,96,130,65,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7920 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7921 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 400, targets := 2 }], pairs := [(1,7),(3,7),(4,1)], upper := (rows 37 98 134 73 400 48 66 137 265), lower := (rows 37 98 134 73 400 48 66 128 256), losses := [] }

theorem u7921 : Upper (D 7) (R 7) [36,96,130,65,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7921 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7922 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 73 400 48 72 131 259), lower := (rows 37 98 134 73 400 48 72 128 256), losses := [] }

theorem u7922 : Upper (D 7) (R 7) [36,96,130,65,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7922 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7923 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 37 98 134 88 145 288 65 138 266), lower := (rows 37 98 134 88 145 288 65 128 256), losses := [] }

theorem u7923 : Upper (D 7) (R 7) [36,96,130,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7923 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7924 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 134 88 145 288 66 137 265), lower := (rows 37 98 134 88 145 288 66 128 256), losses := [] }

theorem u7924 : Upper (D 7) (R 7) [36,96,130,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7924 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7925 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 88 145 288 72 131 259), lower := (rows 37 98 134 88 145 288 72 128 256), losses := [] }

theorem u7925 : Upper (D 7) (R 7) [36,96,130,80,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7925 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7926 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 134 88 274 33 65 136 392), lower := (rows 37 98 134 88 274 33 65 128 256), losses := [] }

theorem u7926 : Upper (D 7) (R 7) [36,96,130,80,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7927 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 37 98 134 88 274 33 72 129 385), lower := (rows 37 98 134 88 274 33 72 128 256), losses := [] }

theorem u7927 : Upper (D 7) (R 7) [36,96,130,80,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7927 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7928 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 134 88 274 33 192 137 265), lower := (rows 37 98 134 88 274 33 192 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 196 128 256), good := (rows 102 98 198 88 274 34 192 192 256) }] }

theorem u7928 : Upper (D 7) (R 7) [36,96,130,80,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7929 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 134 88 400 33 65 138 266), lower := (rows 37 98 134 88 400 33 65 128 256), losses := [] }

theorem u7929 : Upper (D 7) (R 7) [36,96,130,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7930 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 88 400 33 66 137 265), lower := (rows 37 98 134 88 400 33 66 128 256), losses := [] }

theorem u7930 : Upper (D 7) (R 7) [36,96,130,80,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7931 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 37 98 134 88 400 33 72 131 259), lower := (rows 37 98 134 88 400 33 72 128 256), losses := [] }

theorem u7931 : Upper (D 7) (R 7) [36,96,130,80,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7931 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7932 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 370, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 134 137 273 48 66 200 328), lower := (rows 37 98 134 137 273 48 66 128 256), losses := [] }

theorem u7932 : Upper (D 7) (R 7) [36,96,130,129,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7932 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7933 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 132, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 37 98 134 137 273 48 72 194 322), lower := (rows 37 98 134 137 273 48 72 128 256), losses := [] }

theorem u7933 : Upper (D 7) (R 7) [36,96,130,129,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7933 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7934 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 132, targets := 33 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(2,0),(2,5)], upper := (rows 37 98 134 137 280 48 65 194 322), lower := (rows 37 98 134 137 280 48 65 128 256), losses := [] }

theorem u7934 : Upper (D 7) (R 7) [36,96,130,129,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7934 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7935 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 370, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 134 137 280 48 66 193 321), lower := (rows 37 98 134 137 280 48 66 128 256), losses := [] }

theorem u7935 : Upper (D 7) (R 7) [36,96,130,129,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7935 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7936 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 37 98 134 152 273 40 65 194 322), lower := (rows 37 98 134 152 273 40 65 128 256), losses := [] }

theorem u7936 : Upper (D 7) (R 7) [36,96,130,144,257,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7936 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7937 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 134 152 273 40 66 193 321), lower := (rows 37 98 134 152 273 40 66 128 256), losses := [] }

theorem u7937 : Upper (D 7) (R 7) [36,96,130,144,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7937 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7938 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 134 152 274 33 65 200 328), lower := (rows 37 98 134 152 274 33 65 128 256), losses := [] }

theorem u7938 : Upper (D 7) (R 7) [36,96,130,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7939 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 134 152 274 33 72 193 321), lower := (rows 37 98 134 152 274 33 72 128 256), losses := [] }

theorem u7939 : Upper (D 7) (R 7) [36,96,130,144,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7939 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7940 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(1,7),(2,5),(4,7)], upper := (rows 37 98 134 152 274 40 65 193 321), lower := (rows 37 98 134 152 274 40 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 14 18 0 65 193 321), good := (rows 461 478 158 152 286 8 449 128 256) }] }

theorem u7940 : Upper (D 7) (R 7) [36,96,130,144,258,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7940 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7941 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 134 152 336 33 65 138 266), lower := (rows 37 98 134 152 336 33 65 128 256), losses := [] }

theorem u7941 : Upper (D 7) (R 7) [36,96,130,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7942 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 152 336 33 66 137 265), lower := (rows 37 98 134 152 336 33 66 128 256), losses := [] }

theorem u7942 : Upper (D 7) (R 7) [36,96,130,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7943 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(2,6)], upper := (rows 37 98 134 152 336 33 72 131 259), lower := (rows 37 98 134 152 336 33 72 128 256), losses := [] }

theorem u7943 : Upper (D 7) (R 7) [36,96,130,144,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7943 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7944 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 72, targets := 33 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(3,0),(3,5)], upper := (rows 37 98 134 200 273 33 66 152 280), lower := (rows 37 98 134 200 273 33 66 128 256), losses := [] }

theorem u7944 : Upper (D 7) (R 7) [36,96,130,192,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7945 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 200 273 33 72 146 274), lower := (rows 37 98 134 200 273 33 72 128 256), losses := [] }

theorem u7945 : Upper (D 7) (R 7) [36,96,130,192,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7945 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7946 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 134 200 273 33 80 138 266), lower := (rows 37 98 134 200 273 33 80 128 256), losses := [] }

theorem u7946 : Upper (D 7) (R 7) [36,96,130,192,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7946 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7947 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 134 200 273 48 65 138 266), lower := (rows 37 98 134 200 273 48 65 128 256), losses := [] }

theorem u7947 : Upper (D 7) (R 7) [36,96,130,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7947 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7948 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 72, targets := 33 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 134 200 273 48 66 137 265), lower := (rows 37 98 134 200 273 48 66 128 256), losses := [] }

theorem u7948 : Upper (D 7) (R 7) [36,96,130,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7948 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7949 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 200 273 48 72 131 259), lower := (rows 37 98 134 200 273 48 72 128 256), losses := [] }

theorem u7949 : Upper (D 7) (R 7) [36,96,130,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7949 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7950 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 134 200 274 33 65 152 280), lower := (rows 37 98 134 200 274 33 65 128 256), losses := [] }

theorem u7950 : Upper (D 7) (R 7) [36,96,130,192,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7951 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 200 274 33 72 145 273), lower := (rows 37 98 134 200 274 33 72 128 256), losses := [] }

theorem u7951 : Upper (D 7) (R 7) [36,96,130,192,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7951 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7952 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 134 200 274 33 80 137 265), lower := (rows 37 98 134 200 274 33 80 128 256), losses := [] }

theorem u7952 : Upper (D 7) (R 7) [36,96,130,192,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7952 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7953 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(3,1),(3,5)], upper := (rows 37 98 134 200 274 48 65 137 265), lower := (rows 37 98 134 200 274 48 65 128 256), losses := [] }

theorem u7953 : Upper (D 7) (R 7) [36,96,130,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7953 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7954 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 200 274 48 72 129 257), lower := (rows 37 98 134 200 274 48 72 128 256), losses := [] }

theorem u7954 : Upper (D 7) (R 7) [36,96,130,192,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7954 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7955 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 134 200 280 33 65 146 274), lower := (rows 37 98 134 200 280 33 65 128 256), losses := [] }

theorem u7955 : Upper (D 7) (R 7) [36,96,130,192,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7956 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 33 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(3,0),(3,5)], upper := (rows 37 98 134 200 280 33 66 145 273), lower := (rows 37 98 134 200 280 33 66 128 256), losses := [] }

theorem u7956 : Upper (D 7) (R 7) [36,96,130,192,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7957 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(2,6)], upper := (rows 37 98 134 200 280 33 80 131 259), lower := (rows 37 98 134 200 280 33 80 128 256), losses := [] }

theorem u7957 : Upper (D 7) (R 7) [36,96,130,192,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7957 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7958 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 140 11 146 288 65 208 336), lower := (rows 37 98 140 11 146 288 65 128 256), losses := [] }

theorem u7958 : Upper (D 7) (R 7) [36,96,136,3,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7958 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7959 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 37 98 140 11 146 288 80 193 321), lower := (rows 37 98 140 11 146 288 80 128 256), losses := [] }

theorem u7959 : Upper (D 7) (R 7) [36,96,136,3,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7959 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7960 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 140 11 208 288 65 146 274), lower := (rows 37 98 140 11 208 288 65 128 256), losses := [] }

theorem u7960 : Upper (D 7) (R 7) [36,96,136,3,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7960 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7961 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 140 11 208 288 66 145 273), lower := (rows 37 98 140 11 208 288 66 128 256), losses := [] }

theorem u7961 : Upper (D 7) (R 7) [36,96,136,3,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7961 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7962 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 140 11 208 288 80 131 259), lower := (rows 37 98 140 11 208 288 80 128 256), losses := [] }

theorem u7962 : Upper (D 7) (R 7) [36,96,136,3,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7962 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7963 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 290, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 140 25 146 288 65 194 322), lower := (rows 37 98 140 25 146 288 65 128 256), losses := [] }

theorem u7963 : Upper (D 7) (R 7) [36,96,136,17,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7963 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7964 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 140 25 146 288 66 193 321), lower := (rows 37 98 140 25 146 288 66 128 256), losses := [] }

theorem u7964 : Upper (D 7) (R 7) [36,96,136,17,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7964 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7965 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 25 208 34 65 386 258), lower := (rows 37 98 140 25 208 34 65 128 256), losses := [] }

theorem u7965 : Upper (D 7) (R 7) [36,96,136,17,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7966 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 140 25 208 34 66 385 257), lower := (rows 37 98 140 25 208 34 66 128 256), losses := [] }

theorem u7966 : Upper (D 7) (R 7) [36,96,136,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7967 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 140 25 208 34 320 131 259), lower := (rows 37 98 140 25 208 34 320 128 256), losses := [] }

theorem u7967 : Upper (D 7) (R 7) [36,96,136,17,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7967 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7968 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 290, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 140 25 208 288 65 130 258), lower := (rows 37 98 140 25 208 288 65 128 256), losses := [] }

theorem u7968 : Upper (D 7) (R 7) [36,96,136,17,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7968 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7969 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 140 25 208 288 66 131 259), lower := (rows 37 98 140 25 208 288 66 128 256), losses := [] }

theorem u7969 : Upper (D 7) (R 7) [36,96,136,17,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7969 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7970 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 25 336 34 65 130 386), lower := (rows 37 98 140 25 336 34 65 128 256), losses := [] }

theorem u7970 : Upper (D 7) (R 7) [36,96,136,17,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7971 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 140 25 336 34 66 129 385), lower := (rows 37 98 140 25 336 34 66 128 256), losses := [] }

theorem u7971 : Upper (D 7) (R 7) [36,96,136,17,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7972 : Route 9 := (fun mask => (mask,id))

def c7972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7972 : Upper (D 7) (R 7) [36,96,136,17,320,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,320,2,128] 13 (by decide) (choices 1) [1,2] r7972 c7972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u618
  · exact u619

def b7973 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 25 400 34 65 194 322), lower := (rows 37 98 140 25 400 34 65 128 256), losses := [] }

theorem u7973 : Upper (D 7) (R 7) [36,96,136,17,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7974 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 140 25 400 34 66 193 321), lower := (rows 37 98 140 25 400 34 66 128 256), losses := [] }

theorem u7974 : Upper (D 7) (R 7) [36,96,136,17,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7975 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 140 26 81 288 65 130 386), lower := (rows 37 98 140 26 81 288 65 128 256), losses := [] }

theorem u7975 : Upper (D 7) (R 7) [36,96,136,18,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7975 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7976 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 140 26 81 288 66 129 385), lower := (rows 37 98 140 26 81 288 66 128 256), losses := [] }

theorem u7976 : Upper (D 7) (R 7) [36,96,136,18,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7976 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7977 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 290, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 98 140 26 81 288 192 131 259), lower := (rows 37 98 140 26 81 288 192 128 256), losses := [] }

theorem u7977 : Upper (D 7) (R 7) [36,96,136,18,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7977 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7978 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 140 73 146 288 65 146 274), lower := (rows 37 98 140 73 146 288 65 128 256), losses := [] }

theorem u7978 : Upper (D 7) (R 7) [36,96,136,65,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7978 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7979 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 140 73 146 288 66 145 273), lower := (rows 37 98 140 73 146 288 66 128 256), losses := [] }

theorem u7979 : Upper (D 7) (R 7) [36,96,136,65,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7979 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7979
end Delivery.IrregularNine14.P07
