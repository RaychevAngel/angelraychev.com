import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0014

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6960 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 76 56 146 160 97 161 289), lower := (rows 321 38 76 56 146 160 64 128 256), losses := [] }

theorem u6960 : Upper (D 8) (R 8) [320,36,72,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6961 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 321 38 76 137 176 33 114 178 306), lower := (rows 321 38 76 137 176 33 64 128 256), losses := [] }

theorem u6961 : Upper (D 8) (R 8) [320,36,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6962 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 38 76 137 176 34 113 177 305), lower := (rows 321 38 76 137 176 34 64 128 256), losses := [] }

theorem u6962 : Upper (D 8) (R 8) [320,36,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6962 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6963 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 38 76 137 176 48 99 163 291), lower := (rows 321 38 76 137 176 48 64 128 256), losses := [] }

theorem u6963 : Upper (D 8) (R 8) [320,36,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6963 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6964 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 321 38 76 168 145 33 114 178 306), lower := (rows 321 38 76 168 145 33 64 128 256), losses := [] }

theorem u6964 : Upper (D 8) (R 8) [320,36,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6965 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 38 76 168 145 34 113 177 305), lower := (rows 321 38 76 168 145 34 64 128 256), losses := [] }

theorem u6965 : Upper (D 8) (R 8) [320,36,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6965 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6966 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 38 76 168 145 48 99 163 291), lower := (rows 321 38 76 168 145 48 64 128 256), losses := [] }

theorem u6966 : Upper (D 8) (R 8) [320,36,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6966 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6967 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 321 38 133 56 208 33 106 170 298), lower := (rows 321 38 133 56 208 33 64 128 256), losses := [] }

theorem u6967 : Upper (D 8) (R 8) [320,36,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6968 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 321 38 133 56 208 34 105 169 297), lower := (rows 321 38 133 56 208 34 64 128 256), losses := [] }

theorem u6968 : Upper (D 8) (R 8) [320,36,129,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6968 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6969 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 38 133 56 208 40 99 163 291), lower := (rows 321 38 133 56 208 40 64 128 256), losses := [] }

theorem u6969 : Upper (D 8) (R 8) [320,36,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6969 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6970 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 321 38 133 74 176 33 120 184 312), lower := (rows 321 38 133 74 176 33 64 128 256), losses := [] }

theorem u6970 : Upper (D 8) (R 8) [320,36,129,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6971 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 38 133 74 176 40 113 177 305), lower := (rows 321 38 133 74 176 40 64 128 256), losses := [] }

theorem u6971 : Upper (D 8) (R 8) [320,36,129,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6971 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6972 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 321 38 133 74 176 48 105 169 297), lower := (rows 321 38 133 74 176 48 64 128 256), losses := [] }

theorem u6972 : Upper (D 8) (R 8) [320,36,129,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6972 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6973 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 321 38 133 88 176 33 106 170 298), lower := (rows 321 38 133 88 176 33 64 128 256), losses := [] }

theorem u6973 : Upper (D 8) (R 8) [320,36,129,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6974 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 321 38 133 88 176 34 105 169 297), lower := (rows 321 38 133 88 176 34 64 128 256), losses := [] }

theorem u6974 : Upper (D 8) (R 8) [320,36,129,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6974 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6975 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 38 133 88 176 40 99 163 291), lower := (rows 321 38 133 88 176 40 64 128 256), losses := [] }

theorem u6975 : Upper (D 8) (R 8) [320,36,129,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6975 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6976 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 321 38 133 104 152 33 114 178 306), lower := (rows 321 38 133 104 152 33 64 128 256), losses := [] }

theorem u6976 : Upper (D 8) (R 8) [320,36,129,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6977 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 38 133 104 152 34 113 177 305), lower := (rows 321 38 133 104 152 34 64 128 256), losses := [] }

theorem u6977 : Upper (D 8) (R 8) [320,36,129,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6977 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6978 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 38 133 104 152 48 99 163 291), lower := (rows 321 38 133 104 152 48 64 128 256), losses := [] }

theorem u6978 : Upper (D 8) (R 8) [320,36,129,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6978 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6979 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 321 38 133 104 176 33 90 154 282), lower := (rows 321 38 133 104 176 33 64 128 256), losses := [] }

theorem u6979 : Upper (D 8) (R 8) [320,36,129,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6980 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 321 38 133 104 176 34 89 153 281), lower := (rows 321 38 133 104 176 34 64 128 256), losses := [] }

theorem u6980 : Upper (D 8) (R 8) [320,36,129,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6980 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6981 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 321 38 133 104 176 40 83 147 275), lower := (rows 321 38 133 104 176 40 64 128 256), losses := [] }

theorem u6981 : Upper (D 8) (R 8) [320,36,129,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6981 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6982 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 321 38 133 104 176 48 75 139 267), lower := (rows 321 38 133 104 176 48 64 128 256), losses := [] }

theorem u6982 : Upper (D 8) (R 8) [320,36,129,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6982 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6983 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 321 38 140 104 145 33 114 178 306), lower := (rows 321 38 140 104 145 33 64 128 256), losses := [] }

theorem u6983 : Upper (D 8) (R 8) [320,36,136,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6984 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 38 140 104 145 34 113 177 305), lower := (rows 321 38 140 104 145 34 64 128 256), losses := [] }

theorem u6984 : Upper (D 8) (R 8) [320,36,136,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6984 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6985 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 38 140 104 145 48 99 163 291), lower := (rows 321 38 140 104 145 48 64 128 256), losses := [] }

theorem u6985 : Upper (D 8) (R 8) [320,36,136,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6985 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6986 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 321 38 140 104 176 33 83 147 275), lower := (rows 321 38 140 104 176 33 64 128 256), losses := [] }

theorem u6986 : Upper (D 8) (R 8) [320,36,136,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6987 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 321 38 140 104 176 34 81 145 273), lower := (rows 321 38 140 104 176 34 64 128 256), losses := [] }

theorem u6987 : Upper (D 8) (R 8) [320,36,136,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6987 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6988 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 321 38 140 104 176 48 67 131 259), lower := (rows 321 38 140 104 176 48 64 128 256), losses := [] }

theorem u6988 : Upper (D 8) (R 8) [320,36,136,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6988 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6989 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 52 104 49 480 448 448 448), lower := (rows 7 11 52 104 49 32 64 128 256), losses := [] }

theorem u6989 : Upper (D 8) (R 8) [6,9,48,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6990 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 81 416 480 416 416), lower := (rows 7 11 52 104 81 32 64 128 256), losses := [] }

theorem u6990 : Upper (D 8) (R 8) [6,9,48,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6991 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 112 417 449 385 385), lower := (rows 7 11 52 104 112 32 64 128 256), losses := [] }

theorem u6991 : Upper (D 8) (R 8) [6,9,48,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6992 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 104 145 480 480 480 480), lower := (rows 7 11 52 104 145 32 64 128 256), losses := [] }

theorem u6992 : Upper (D 8) (R 8) [6,9,48,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6993 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 104 176 481 449 449 449), lower := (rows 7 11 52 104 176 32 64 128 256), losses := [] }

theorem u6993 : Upper (D 8) (R 8) [6,9,48,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6994 : Route 9 := (fun mask => (mask,id))

def c6994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6994 : Upper (D 8) (R 8) [6,9,48,96,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192] 13 (by decide) (choices 1) [1,128,256] r6994 c6994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u860
  · exact u861
  · exact u862

def b6995 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 104 273 224 224 224 480), lower := (rows 7 11 52 104 273 32 64 128 256), losses := [] }

theorem u6995 : Upper (D 8) (R 8) [6,9,48,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6996 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 104 304 225 193 193 449), lower := (rows 7 11 52 104 304 32 64 128 256), losses := [] }

theorem u6996 : Upper (D 8) (R 8) [6,9,48,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6997 : Route 9 := (fun mask => (mask,id))

def c6997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6997 : Upper (D 8) (R 8) [6,9,48,96,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,320] 13 (by decide) (choices 1) [1,128] r6997 c6997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u863
  · exact u864

def r6998 : Route 9 := (fun mask => (mask,id))

def c6998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6998 : Upper (D 8) (R 8) [6,9,48,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,384] 13 (by decide) (choices 1) [1,64,128] r6998 c6998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u865
  · exact u866
  · exact u867

def b6999 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 49 480 480 480 480), lower := (rows 7 11 52 200 49 32 64 128 256), losses := [] }

theorem u6999 : Upper (D 8) (R 8) [6,9,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7000 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 81 416 480 416 416), lower := (rows 7 11 52 200 81 32 64 128 256), losses := [] }

theorem u7000 : Upper (D 8) (R 8) [6,9,48,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7001 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 112 417 481 417 417), lower := (rows 7 11 52 200 112 32 64 128 256), losses := [] }

theorem u7001 : Upper (D 8) (R 8) [6,9,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7002 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 52 200 208 289 353 417 289), lower := (rows 7 11 52 200 208 32 64 128 256), losses := [] }

theorem u7002 : Upper (D 8) (R 8) [6,9,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7003 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 273 224 224 224 480), lower := (rows 7 11 52 200 273 32 64 128 256), losses := [] }

theorem u7003 : Upper (D 8) (R 8) [6,9,48,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7004 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 304 225 225 225 481), lower := (rows 7 11 52 200 304 32 64 128 256), losses := [] }

theorem u7004 : Upper (D 8) (R 8) [6,9,48,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7005 : Route 9 := (fun mask => (mask,id))

def c7005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7005 : Upper (D 8) (R 8) [6,9,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320] 13 (by decide) (choices 1) [1,128] r7005 c7005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u868
  · exact u869

def b7006 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 52 296 49 224 192 192 448), lower := (rows 7 11 52 296 49 32 64 128 256), losses := [] }

theorem u7006 : Upper (D 8) (R 8) [6,9,48,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7007 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 296 81 224 224 224 480), lower := (rows 7 11 52 296 81 32 64 128 256), losses := [] }

theorem u7007 : Upper (D 8) (R 8) [6,9,48,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7008 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 296 112 225 193 193 449), lower := (rows 7 11 52 296 112 32 64 128 256), losses := [] }

theorem u7008 : Upper (D 8) (R 8) [6,9,48,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7009 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7009 : Upper (D 8) (R 8) [6,9,48,288,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,288,192] 13 (by decide) (choices 1) [1,64] r7009 c7009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u870
  · exact u871

def b7010 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 328 49 224 224 224 480), lower := (rows 7 11 52 328 49 32 64 128 256), losses := [] }

theorem u7010 : Upper (D 8) (R 8) [6,9,48,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7011 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 328 81 160 224 160 416), lower := (rows 7 11 52 328 81 32 64 128 256), losses := [] }

theorem u7011 : Upper (D 8) (R 8) [6,9,48,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7012 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 328 112 161 225 161 417), lower := (rows 7 11 52 328 112 32 64 128 256), losses := [] }

theorem u7012 : Upper (D 8) (R 8) [6,9,48,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7013 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 328 145 224 224 224 480), lower := (rows 7 11 52 328 145 32 64 128 256), losses := [] }

theorem u7013 : Upper (D 8) (R 8) [6,9,48,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7014 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 328 176 225 225 225 481), lower := (rows 7 11 52 328 176 32 64 128 256), losses := [] }

theorem u7014 : Upper (D 8) (R 8) [6,9,48,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7015 : Route 9 := (fun mask => (mask,id))

def c7015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7015 : Upper (D 8) (R 8) [6,9,48,320,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,192] 13 (by decide) (choices 1) [1,128] r7015 c7015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u872
  · exact u873

def b7016 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 49 480 480 480 480), lower := (rows 7 11 84 168 49 32 64 128 256), losses := [] }

theorem u7016 : Upper (D 8) (R 8) [6,9,80,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7017 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 168 81 416 480 416 416), lower := (rows 7 11 84 168 81 32 64 128 256), losses := [] }

theorem u7017 : Upper (D 8) (R 8) [6,9,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7018 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 168 112 417 481 417 417), lower := (rows 7 11 84 168 112 32 64 128 256), losses := [] }

theorem u7018 : Upper (D 8) (R 8) [6,9,80,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7019 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 145 352 352 480 352), lower := (rows 7 11 84 168 145 32 64 128 256), losses := [] }

theorem u7019 : Upper (D 8) (R 8) [6,9,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7019
end Delivery.IrregularNine14.P08
