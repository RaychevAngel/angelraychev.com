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

def b6960 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 7 296 208 160 66 145 273), lower := (rows 37 74 7 296 208 160 66 128 256), losses := [] }

theorem u6960 : Upper (D 7) (R 7) [36,72,3,288,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6961 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 7 296 208 160 80 131 259), lower := (rows 37 74 7 296 208 160 80 128 256), losses := [] }

theorem u6961 : Upper (D 7) (R 7) [36,72,3,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6961 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6962 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 7 392 145 48 66 224 352), lower := (rows 37 74 7 392 145 48 66 128 256), losses := [] }

theorem u6962 : Upper (D 7) (R 7) [36,72,3,384,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6962 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6963 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 7 392 145 48 96 194 322), lower := (rows 37 74 7 392 145 48 96 128 256), losses := [] }

theorem u6963 : Upper (D 7) (R 7) [36,72,3,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6963 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6964 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 7 392 208 48 65 162 290), lower := (rows 37 74 7 392 208 48 65 128 256), losses := [] }

theorem u6964 : Upper (D 7) (R 7) [36,72,3,384,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6964 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6965 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 74 7 392 208 48 66 161 289), lower := (rows 37 74 7 392 208 48 66 128 256), losses := [] }

theorem u6965 : Upper (D 7) (R 7) [36,72,3,384,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6965 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6966 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 392, targets := 96 },{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 37 74 7 392 208 48 96 131 259), lower := (rows 37 74 7 392 208 48 96 128 256), losses := [] }

theorem u6966 : Upper (D 7) (R 7) [36,72,3,384,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6966 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6967 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 21 42 146 288 65 192 448), lower := (rows 37 74 21 42 146 288 65 128 256), losses := [] }

theorem u6967 : Upper (D 7) (R 7) [36,72,17,34,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6967 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6968 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 357, targets := 2 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 37 74 21 42 146 288 192 193 321), lower := (rows 37 74 21 42 146 288 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 9 16 288 208 128 256), good := (rows 46 74 94 42 210 288 192 192 288) }] }

theorem u6968 : Upper (D 7) (R 7) [36,72,17,34,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6968 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6969 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 21 42 208 288 65 130 386), lower := (rows 37 74 21 42 208 288 65 128 256), losses := [] }

theorem u6969 : Upper (D 7) (R 7) [36,72,17,34,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6969 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6970 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 293, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 21 42 208 288 66 129 385), lower := (rows 37 74 21 42 208 288 66 128 256), losses := [] }

theorem u6970 : Upper (D 7) (R 7) [36,72,17,34,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6970 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6971 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 21 42 208 288 192 131 259), lower := (rows 37 74 21 42 208 288 192 128 256), losses := [] }

theorem u6971 : Upper (D 7) (R 7) [36,72,17,34,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6971 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6972 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 74, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 37 74 21 42 274 160 65 192 448), lower := (rows 37 74 21 42 274 160 65 128 256), losses := [] }

theorem u6972 : Upper (D 7) (R 7) [36,72,17,34,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6973 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 21 42 274 160 192 193 321), lower := (rows 37 74 21 42 274 160 192 128 256), losses := [] }

theorem u6973 : Upper (D 7) (R 7) [36,72,17,34,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6974 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 74, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 37 74 21 42 336 160 65 130 386), lower := (rows 37 74 21 42 336 160 65 128 256), losses := [] }

theorem u6974 : Upper (D 7) (R 7) [36,72,17,34,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6975 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 42 336 160 66 129 385), lower := (rows 37 74 21 42 336 160 66 128 256), losses := [] }

theorem u6975 : Upper (D 7) (R 7) [36,72,17,34,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6976 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 74, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 21 42 336 160 192 131 259), lower := (rows 37 74 21 42 336 160 192 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 224 224 128 256), good := (rows 101 104 21 104 373 224 224 224 256) }] }

theorem u6976 : Upper (D 7) (R 7) [36,72,17,34,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6977 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 66, targets := 160 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 74 21 137 274 160 66 224 352), lower := (rows 37 74 21 137 274 160 66 128 256), losses := [] }

theorem u6977 : Upper (D 7) (R 7) [36,72,17,129,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6978 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 272, targets := 32 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 137 274 160 96 194 322), lower := (rows 37 74 21 137 274 160 96 128 256), losses := [] }

theorem u6978 : Upper (D 7) (R 7) [36,72,17,129,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6979 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,0)], upper := (rows 37 74 21 137 336 34 66 160 416), lower := (rows 37 74 21 137 336 34 66 128 256), losses := [] }

theorem u6979 : Upper (D 7) (R 7) [36,72,17,129,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6980 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 74 21 137 336 34 96 130 386), lower := (rows 37 74 21 137 336 34 96 128 256), losses := [] }

theorem u6980 : Upper (D 7) (R 7) [36,72,17,129,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6981 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 21 137 336 34 192 162 290), lower := (rows 37 74 21 137 336 34 192 128 256), losses := [] }

theorem u6981 : Upper (D 7) (R 7) [36,72,17,129,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6982 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 66, targets := 160 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 74 21 137 336 160 66 162 290), lower := (rows 37 74 21 137 336 160 66 128 256), losses := [] }

theorem u6982 : Upper (D 7) (R 7) [36,72,17,129,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6983 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 272, targets := 32 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 137 336 160 96 130 258), lower := (rows 37 74 21 137 336 160 96 128 256), losses := [] }

theorem u6983 : Upper (D 7) (R 7) [36,72,17,129,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6984 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 66, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 74 21 137 400 34 66 224 352), lower := (rows 37 74 21 137 400 34 66 128 256), losses := [] }

theorem u6984 : Upper (D 7) (R 7) [36,72,17,129,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6985 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 74 21 137 400 34 96 194 322), lower := (rows 37 74 21 137 400 34 96 128 256), losses := [] }

theorem u6985 : Upper (D 7) (R 7) [36,72,17,129,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6986 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 66, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 74 21 137 400 96 66 162 290), lower := (rows 37 74 21 137 400 96 66 128 256), losses := [] }

theorem u6986 : Upper (D 7) (R 7) [36,72,17,129,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6987 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 1, region := 400, targets := 32 }], pairs := [(0,1),(2,1),(3,1),(4,5)], upper := (rows 37 74 21 137 400 96 96 130 258), lower := (rows 37 74 21 137 400 96 96 128 256), losses := [] }

theorem u6987 : Upper (D 7) (R 7) [36,72,17,129,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6988 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 21 138 274 160 65 224 352), lower := (rows 37 74 21 138 274 160 65 128 256), losses := [] }

theorem u6988 : Upper (D 7) (R 7) [36,72,17,130,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6989 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 21 138 274 160 96 193 321), lower := (rows 37 74 21 138 274 160 96 128 256), losses := [] }

theorem u6989 : Upper (D 7) (R 7) [36,72,17,130,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6990 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 6, region := 170, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 21 138 336 34 65 160 416), lower := (rows 37 74 21 138 336 34 65 128 256), losses := [] }

theorem u6990 : Upper (D 7) (R 7) [36,72,17,130,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6991 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 21 138 336 34 96 129 385), lower := (rows 37 74 21 138 336 34 96 128 256), losses := [] }

theorem u6991 : Upper (D 7) (R 7) [36,72,17,130,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6992 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 5, region := 469, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 21 138 336 34 192 161 289), lower := (rows 37 74 21 138 336 34 192 128 256), losses := [] }

theorem u6992 : Upper (D 7) (R 7) [36,72,17,130,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6993 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 168, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,0)], upper := (rows 37 74 21 138 336 160 65 162 290), lower := (rows 37 74 21 138 336 160 65 128 256), losses := [] }

theorem u6993 : Upper (D 7) (R 7) [36,72,17,130,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6994 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 138 336 160 66 161 289), lower := (rows 37 74 21 138 336 160 66 128 256), losses := [] }

theorem u6994 : Upper (D 7) (R 7) [36,72,17,130,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6995 : Route 9 := (fun mask => (mask,id))

def c6995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6995 : Upper (D 7) (R 7) [36,72,17,130,320,128,32] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,320,128,32] 13 (by decide) (choices 1) [1,2] r6995 c6995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u510
  · exact u511

def b6996 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 6, region := 170, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 21 138 400 34 65 224 352), lower := (rows 37 74 21 138 400 34 65 128 256), losses := [] }

theorem u6996 : Upper (D 7) (R 7) [36,72,17,130,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6997 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 21 138 400 34 96 193 321), lower := (rows 37 74 21 138 400 34 96 128 256), losses := [] }

theorem u6997 : Upper (D 7) (R 7) [36,72,17,130,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6998 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 21 138 400 96 65 162 290), lower := (rows 37 74 21 138 400 96 65 128 256), losses := [] }

theorem u6998 : Upper (D 7) (R 7) [36,72,17,130,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6999 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 405, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 138 400 96 66 161 289), lower := (rows 37 74 21 138 400 96 66 128 256), losses := [] }

theorem u6999 : Upper (D 7) (R 7) [36,72,17,130,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7000 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 21 138 400 96 96 131 259), lower := (rows 37 74 21 138 400 96 96 128 256), losses := [] }

theorem u7000 : Upper (D 7) (R 7) [36,72,17,130,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7001 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 21 168 146 288 65 194 322), lower := (rows 37 74 21 168 146 288 65 128 256), losses := [] }

theorem u7001 : Upper (D 7) (R 7) [36,72,17,160,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7001 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7002 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 74 21 168 146 288 66 193 321), lower := (rows 37 74 21 168 146 288 66 128 256), losses := [] }

theorem u7002 : Upper (D 7) (R 7) [36,72,17,160,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7002 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7003 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 85, targets := 2 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 21 168 208 34 65 386 258), lower := (rows 37 74 21 168 208 34 65 128 256), losses := [] }

theorem u7003 : Upper (D 7) (R 7) [36,72,17,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7004 : PairBound 9 := { available := 257, camps := [{ cop := 7, region := 122, targets := 1 },{ cop := 0, region := 392, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 74 21 168 208 34 66 385 257), lower := (rows 37 74 21 168 208 34 66 128 256), losses := [] }

theorem u7004 : Upper (D 7) (R 7) [36,72,17,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7005 : Route 9 := (fun mask => (mask,id))

def c7005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7005 : Upper (D 7) (R 7) [36,72,17,160,192,2,256] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,192,2,256] 13 (by decide) (choices 1) [1,2] r7005 c7005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u512
  · exact u513

def b7006 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 74 21 168 208 288 65 130 258), lower := (rows 37 74 21 168 208 288 65 128 256), losses := [] }

theorem u7006 : Upper (D 7) (R 7) [36,72,17,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7006 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7007 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 74 21 168 208 288 66 131 259), lower := (rows 37 74 21 168 208 288 66 128 256), losses := [] }

theorem u7007 : Upper (D 7) (R 7) [36,72,17,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7007 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7008 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 37 74 21 168 336 34 65 130 386), lower := (rows 37 74 21 168 336 34 65 128 256), losses := [] }

theorem u7008 : Upper (D 7) (R 7) [36,72,17,160,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7009 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 3, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,6)], upper := (rows 37 74 21 168 336 34 66 129 385), lower := (rows 37 74 21 168 336 34 66 128 256), losses := [] }

theorem u7009 : Upper (D 7) (R 7) [36,72,17,160,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7010 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 6, region := 42, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 21 168 336 34 192 131 259), lower := (rows 37 74 21 168 336 34 192 128 256), losses := [] }

theorem u7010 : Upper (D 7) (R 7) [36,72,17,160,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7011 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 37 74 21 168 400 34 65 194 322), lower := (rows 37 74 21 168 400 34 65 128 256), losses := [] }

theorem u7011 : Upper (D 7) (R 7) [36,72,17,160,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7012 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 3, region := 66, targets := 32 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 21 168 400 34 66 193 321), lower := (rows 37 74 21 168 400 34 66 128 256), losses := [] }

theorem u7012 : Upper (D 7) (R 7) [36,72,17,160,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7013 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 5, region := 138, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 74 21 168 400 96 65 130 258), lower := (rows 37 74 21 168 400 96 65 128 256), losses := [] }

theorem u7013 : Upper (D 7) (R 7) [36,72,17,160,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7014 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 3, region := 66, targets := 32 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 21 168 400 96 66 131 259), lower := (rows 37 74 21 168 400 96 66 128 256), losses := [] }

theorem u7014 : Upper (D 7) (R 7) [36,72,17,160,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7015 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,0)], upper := (rows 37 74 21 265 208 34 66 160 416), lower := (rows 37 74 21 265 208 34 66 128 256), losses := [] }

theorem u7015 : Upper (D 7) (R 7) [36,72,17,257,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7016 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 32 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 74 21 265 208 34 96 130 386), lower := (rows 37 74 21 265 208 34 96 128 256), losses := [] }

theorem u7016 : Upper (D 7) (R 7) [36,72,17,257,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7017 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 21 265 208 34 192 162 290), lower := (rows 37 74 21 265 208 34 192 128 256), losses := [] }

theorem u7017 : Upper (D 7) (R 7) [36,72,17,257,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7018 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 21 266 208 34 65 160 416), lower := (rows 37 74 21 266 208 34 65 128 256), losses := [] }

theorem u7018 : Upper (D 7) (R 7) [36,72,17,258,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7019 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 21 266 208 34 96 129 385), lower := (rows 37 74 21 266 208 34 96 128 256), losses := [] }

theorem u7019 : Upper (D 7) (R 7) [36,72,17,258,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7019
end Delivery.IrregularNine14.P07
