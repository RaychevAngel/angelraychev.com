import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0099

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20040 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 73 145 34 340 404 276), lower := (rows 35 70 44 73 145 34 64 128 256), losses := [] }

theorem u20040 : Upper (D 6) (R 6) [34,68,40,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20041 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 73 145 36 338 402 274), lower := (rows 35 70 44 73 145 36 64 128 256), losses := [] }

theorem u20041 : Upper (D 6) (R 6) [34,68,40,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20042 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 73 145 48 326 390 262), lower := (rows 35 70 44 73 145 48 64 128 256), losses := [] }

theorem u20042 : Upper (D 6) (R 6) [34,68,40,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20042 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20043 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 73 145 288 86 150 278), lower := (rows 35 70 44 73 145 288 64 128 256), losses := [] }

theorem u20043 : Upper (D 6) (R 6) [34,68,40,65,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20043 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20044 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 44 73 400 33 86 150 278), lower := (rows 35 70 44 73 400 33 64 128 256), losses := [] }

theorem u20044 : Upper (D 6) (R 6) [34,68,40,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20045 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 73 400 34 85 149 277), lower := (rows 35 70 44 73 400 34 64 128 256), losses := [] }

theorem u20045 : Upper (D 6) (R 6) [34,68,40,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20046 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 73 400 36 83 147 275), lower := (rows 35 70 44 73 400 36 64 128 256), losses := [] }

theorem u20046 : Upper (D 6) (R 6) [34,68,40,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20047 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 73 400 48 71 135 263), lower := (rows 35 70 44 73 400 48 64 128 256), losses := [] }

theorem u20047 : Upper (D 6) (R 6) [34,68,40,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20047 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20048 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 322, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 70 44 88 145 33 326 390 262), lower := (rows 35 70 44 88 145 33 64 128 256), losses := [] }

theorem u20048 : Upper (D 6) (R 6) [34,68,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20049 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 88 145 34 325 389 261), lower := (rows 35 70 44 88 145 34 64 128 256), losses := [] }

theorem u20049 : Upper (D 6) (R 6) [34,68,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20050 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 88 145 36 323 387 259), lower := (rows 35 70 44 88 145 36 64 128 256), losses := [] }

theorem u20050 : Upper (D 6) (R 6) [34,68,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20051 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 88 145 288 71 135 263), lower := (rows 35 70 44 88 145 288 64 128 256), losses := [] }

theorem u20051 : Upper (D 6) (R 6) [34,68,40,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20051 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20052 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 44 88 400 33 71 135 263), lower := (rows 35 70 44 88 400 33 64 128 256), losses := [] }

theorem u20052 : Upper (D 6) (R 6) [34,68,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20053 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 88 400 34 69 133 261), lower := (rows 35 70 44 88 400 34 64 128 256), losses := [] }

theorem u20053 : Upper (D 6) (R 6) [34,68,40,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20054 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 88 400 36 67 131 259), lower := (rows 35 70 44 88 400 36 64 128 256), losses := [] }

theorem u20054 : Upper (D 6) (R 6) [34,68,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20055 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 137 81 34 340 404 276), lower := (rows 35 70 44 137 81 34 64 128 256), losses := [] }

theorem u20055 : Upper (D 6) (R 6) [34,68,40,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20056 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 137 81 36 338 402 274), lower := (rows 35 70 44 137 81 36 64 128 256), losses := [] }

theorem u20056 : Upper (D 6) (R 6) [34,68,40,129,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20057 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 137 81 48 326 390 262), lower := (rows 35 70 44 137 81 48 64 128 256), losses := [] }

theorem u20057 : Upper (D 6) (R 6) [34,68,40,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20057 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20058 : Route 9 := (fun mask => (mask,id))

def c20058 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20058 : Upper (D 6) (R 6) [34,68,40,129,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,65,256] 13 (by decide) (choices 1) [2,4,16] r20058 c20058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5989
  · exact u5990
  · exact u5991

def b20059 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 137 273 34 84 212 340), lower := (rows 35 70 44 137 273 34 64 128 256), losses := [] }

theorem u20059 : Upper (D 6) (R 6) [34,68,40,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20060 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 137 273 36 82 210 338), lower := (rows 35 70 44 137 273 36 64 128 256), losses := [] }

theorem u20060 : Upper (D 6) (R 6) [34,68,40,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20061 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 44 137 273 48 70 198 326), lower := (rows 35 70 44 137 273 48 64 128 256), losses := [] }

theorem u20061 : Upper (D 6) (R 6) [34,68,40,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20061 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20062 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 137 273 96 86 150 278), lower := (rows 35 70 44 137 273 96 64 128 256), losses := [] }

theorem u20062 : Upper (D 6) (R 6) [34,68,40,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20063 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 44 137 274 33 84 212 340), lower := (rows 35 70 44 137 274 33 64 128 256), losses := [] }

theorem u20063 : Upper (D 6) (R 6) [34,68,40,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20064 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 137 274 36 81 209 337), lower := (rows 35 70 44 137 274 36 64 128 256), losses := [] }

theorem u20064 : Upper (D 6) (R 6) [34,68,40,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20065 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 44 137 274 48 69 197 325), lower := (rows 35 70 44 137 274 48 64 128 256), losses := [] }

theorem u20065 : Upper (D 6) (R 6) [34,68,40,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20065 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20066 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 137 274 96 85 149 277), lower := (rows 35 70 44 137 274 96 64 128 256), losses := [] }

theorem u20066 : Upper (D 6) (R 6) [34,68,40,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20067 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 44 137 276 33 82 210 338), lower := (rows 35 70 44 137 276 33 64 128 256), losses := [] }

theorem u20067 : Upper (D 6) (R 6) [34,68,40,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20068 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 137 276 34 81 209 337), lower := (rows 35 70 44 137 276 34 64 128 256), losses := [] }

theorem u20068 : Upper (D 6) (R 6) [34,68,40,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20069 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 200, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 137 276 48 67 195 323), lower := (rows 35 70 44 137 276 48 64 128 256), losses := [] }

theorem u20069 : Upper (D 6) (R 6) [34,68,40,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20069 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20070 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 137 276 96 83 147 275), lower := (rows 35 70 44 137 276 96 64 128 256), losses := [] }

theorem u20070 : Upper (D 6) (R 6) [34,68,40,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20071 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 44 137 336 33 86 150 278), lower := (rows 35 70 44 137 336 33 64 128 256), losses := [] }

theorem u20071 : Upper (D 6) (R 6) [34,68,40,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20072 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 137 336 34 85 149 277), lower := (rows 35 70 44 137 336 34 64 128 256), losses := [] }

theorem u20072 : Upper (D 6) (R 6) [34,68,40,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20073 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 137 336 36 83 147 275), lower := (rows 35 70 44 137 336 36 64 128 256), losses := [] }

theorem u20073 : Upper (D 6) (R 6) [34,68,40,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20074 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 137 336 48 71 135 263), lower := (rows 35 70 44 137 336 48 64 128 256), losses := [] }

theorem u20074 : Upper (D 6) (R 6) [34,68,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20074 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20075 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 44 138 21 33 336 464 336), lower := (rows 35 70 44 138 21 33 64 128 256), losses := [] }

theorem u20075 : Upper (D 6) (R 6) [34,68,40,130,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20076 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 44 138 21 48 321 449 321), lower := (rows 35 70 44 138 21 48 64 128 256), losses := [] }

theorem u20076 : Upper (D 6) (R 6) [34,68,40,130,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20076 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20077 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 138 21 96 337 401 273), lower := (rows 35 70 44 138 21 96 64 128 256), losses := [] }

theorem u20077 : Upper (D 6) (R 6) [34,68,40,130,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20078 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 44 138 21 288 81 209 337), lower := (rows 35 70 44 138 21 288 64 128 256), losses := [] }

theorem u20078 : Upper (D 6) (R 6) [34,68,40,130,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20078 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20079 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 44 138 81 33 340 404 276), lower := (rows 35 70 44 138 81 33 64 128 256), losses := [] }

theorem u20079 : Upper (D 6) (R 6) [34,68,40,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20080 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 138 81 36 337 401 273), lower := (rows 35 70 44 138 81 36 64 128 256), losses := [] }

theorem u20080 : Upper (D 6) (R 6) [34,68,40,130,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20081 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 138 81 48 325 389 261), lower := (rows 35 70 44 138 81 48 64 128 256), losses := [] }

theorem u20081 : Upper (D 6) (R 6) [34,68,40,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20081 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20082 : Route 9 := (fun mask => (mask,id))

def c20082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20082 : Upper (D 6) (R 6) [34,68,40,130,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,65,256] 13 (by decide) (choices 1) [1,4,16] r20082 c20082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5992
  · exact u5993
  · exact u5994

def b20083 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 44 138 273 33 84 212 340), lower := (rows 35 70 44 138 273 33 64 128 256), losses := [] }

theorem u20083 : Upper (D 6) (R 6) [34,68,40,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20084 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 138 273 36 81 209 337), lower := (rows 35 70 44 138 273 36 64 128 256), losses := [] }

theorem u20084 : Upper (D 6) (R 6) [34,68,40,130,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20085 : Route 9 := (fun mask => (mask,id))

def c20085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20085 : Upper (D 6) (R 6) [34,68,40,130,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,257,16] 13 (by decide) (choices 1) [1,4] r20085 c20085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5995
  · exact u5996

def b20086 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 138 273 96 85 149 277), lower := (rows 35 70 44 138 273 96 64 128 256), losses := [] }

theorem u20086 : Upper (D 6) (R 6) [34,68,40,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20087 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 44 138 276 33 81 209 337), lower := (rows 35 70 44 138 276 33 64 128 256), losses := [] }

theorem u20087 : Upper (D 6) (R 6) [34,68,40,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20088 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 138 276 48 65 193 321), lower := (rows 35 70 44 138 276 48 64 128 256), losses := [] }

theorem u20088 : Upper (D 6) (R 6) [34,68,40,130,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20088 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20089 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 138 276 96 81 145 273), lower := (rows 35 70 44 138 276 96 64 128 256), losses := [] }

theorem u20089 : Upper (D 6) (R 6) [34,68,40,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20090 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 44 138 336 33 85 149 277), lower := (rows 35 70 44 138 336 33 64 128 256), losses := [] }

theorem u20090 : Upper (D 6) (R 6) [34,68,40,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20091 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 138 336 36 81 145 273), lower := (rows 35 70 44 138 336 36 64 128 256), losses := [] }

theorem u20091 : Upper (D 6) (R 6) [34,68,40,130,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20092 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 138 336 48 69 133 261), lower := (rows 35 70 44 138 336 48 64 128 256), losses := [] }

theorem u20092 : Upper (D 6) (R 6) [34,68,40,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20092 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20093 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 2, region := 322, targets := 1 }], pairs := [(0,2),(1,0),(4,2)], upper := (rows 35 70 44 152 81 33 326 390 262), lower := (rows 35 70 44 152 81 33 64 128 256), losses := [] }

theorem u20093 : Upper (D 6) (R 6) [34,68,40,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20094 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 152 81 34 325 389 261), lower := (rows 35 70 44 152 81 34 64 128 256), losses := [] }

theorem u20094 : Upper (D 6) (R 6) [34,68,40,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20095 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 152 81 36 323 387 259), lower := (rows 35 70 44 152 81 36 64 128 256), losses := [] }

theorem u20095 : Upper (D 6) (R 6) [34,68,40,144,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20096 : Route 9 := (fun mask => (mask,id))

def c20096 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20096 : Upper (D 6) (R 6) [34,68,40,144,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,65,256] 13 (by decide) (choices 1) [1,2,4] r20096 c20096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5997
  · exact u5998
  · exact u5999

def b20097 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 44 152 273 33 70 198 326), lower := (rows 35 70 44 152 273 33 64 128 256), losses := [] }

theorem u20097 : Upper (D 6) (R 6) [34,68,40,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20098 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 152 273 34 69 197 325), lower := (rows 35 70 44 152 273 34 64 128 256), losses := [] }

theorem u20098 : Upper (D 6) (R 6) [34,68,40,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20099 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 152 273 36 67 195 323), lower := (rows 35 70 44 152 273 36 64 128 256), losses := [] }

theorem u20099 : Upper (D 6) (R 6) [34,68,40,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20099
end Delivery.IrregularNine14.P06
