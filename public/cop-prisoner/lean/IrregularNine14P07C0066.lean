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

def b3960 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 37 266 208 160 65 146 274), lower := (rows 13 98 37 266 208 160 65 128 256), losses := [] }

theorem u3960 : Upper (D 7) (R 7) [12,96,33,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3961 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 5, region := 82, targets := 1 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 266 208 160 66 145 273), lower := (rows 13 98 37 266 208 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 74 133 261), good := (rows 477 66 405 330 208 128 66 128 256) }] }

theorem u3961 : Upper (D 7) (R 7) [12,96,33,258,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3962 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 266 208 160 80 131 259), lower := (rows 13 98 37 266 208 160 80 128 256), losses := [] }

theorem u3962 : Upper (D 7) (R 7) [12,96,33,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3962 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3963 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 82, targets := 128 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 37 280 19 160 66 192 448), lower := (rows 13 98 37 280 19 160 66 128 256), losses := [] }

theorem u3963 : Upper (D 7) (R 7) [12,96,33,272,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3964 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 37 280 19 160 192 194 322), lower := (rows 13 98 37 280 19 160 192 128 256), losses := [] }

theorem u3964 : Upper (D 7) (R 7) [12,96,33,272,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3965 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 82, targets := 128 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 37 280 81 160 66 130 386), lower := (rows 13 98 37 280 81 160 66 128 256), losses := [] }

theorem u3965 : Upper (D 7) (R 7) [12,96,33,272,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3966 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 37 280 81 160 192 130 258), lower := (rows 13 98 37 280 81 160 192 128 256), losses := [] }

theorem u3966 : Upper (D 7) (R 7) [12,96,33,272,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3967 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 328 146 48 65 130 386), lower := (rows 13 98 37 328 146 48 65 128 256), losses := [] }

theorem u3967 : Upper (D 7) (R 7) [12,96,33,320,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3967 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3968 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 98 37 328 146 48 66 129 385), lower := (rows 13 98 37 328 146 48 66 128 256), losses := [] }

theorem u3968 : Upper (D 7) (R 7) [12,96,33,320,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3968 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3969 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 37 328 146 48 192 131 259), lower := (rows 13 98 37 328 146 48 192 128 256), losses := [] }

theorem u3969 : Upper (D 7) (R 7) [12,96,33,320,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3969 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3970 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 37 328 146 160 65 146 274), lower := (rows 13 98 37 328 146 160 65 128 256), losses := [] }

theorem u3970 : Upper (D 7) (R 7) [12,96,33,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3971 : Route 9 := (fun mask => (mask,id))

def c3971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3971 : Upper (D 7) (R 7) [12,96,33,320,130,128,2] 13 := by
  apply FastRouting.sound _ _ [12,96,33,320,130,128,2] 13 (by decide) (choices 1) [1,16] r3971 c3971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u278
  · exact u279

def b3972 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 37 328 146 160 80 131 259), lower := (rows 13 98 37 328 146 160 80 128 256), losses := [] }

theorem u3972 : Upper (D 7) (R 7) [12,96,33,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3972 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3973 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 392 146 34 65 208 336), lower := (rows 13 98 37 392 146 34 65 128 256), losses := [] }

theorem u3973 : Upper (D 7) (R 7) [12,96,33,384,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3974 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 98 37 392 146 34 80 193 321), lower := (rows 13 98 37 392 146 34 80 128 256), losses := [] }

theorem u3974 : Upper (D 7) (R 7) [12,96,33,384,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3974 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3975 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 37 392 146 48 65 194 322), lower := (rows 13 98 37 392 146 48 65 128 256), losses := [] }

theorem u3975 : Upper (D 7) (R 7) [12,96,33,384,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3975 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3976 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 98 37 392 146 48 66 193 321), lower := (rows 13 98 37 392 146 48 66 128 256), losses := [] }

theorem u3976 : Upper (D 7) (R 7) [12,96,33,384,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3976 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3977 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 392 208 34 65 146 274), lower := (rows 13 98 37 392 208 34 65 128 256), losses := [] }

theorem u3977 : Upper (D 7) (R 7) [12,96,33,384,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3978 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 37 392 208 34 66 145 273), lower := (rows 13 98 37 392 208 34 66 128 256), losses := [] }

theorem u3978 : Upper (D 7) (R 7) [12,96,33,384,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3979 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 392 208 34 80 131 259), lower := (rows 13 98 37 392 208 34 80 128 256), losses := [] }

theorem u3979 : Upper (D 7) (R 7) [12,96,33,384,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3979 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3980 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0)], upper := (rows 13 98 52 137 81 288 66 130 386), lower := (rows 13 98 52 137 81 288 66 128 256), losses := [] }

theorem u3980 : Upper (D 7) (R 7) [12,96,48,129,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3980 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3981 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 80, targets := 34 },{ cop := 4, region := 290, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 13 98 52 137 81 288 192 130 258), lower := (rows 13 98 52 137 81 288 192 128 256), losses := [] }

theorem u3981 : Upper (D 7) (R 7) [12,96,48,129,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3981 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3982 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 13 98 52 137 146 288 65 194 322), lower := (rows 13 98 52 137 146 288 65 128 256), losses := [] }

theorem u3982 : Upper (D 7) (R 7) [12,96,48,129,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3982 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3983 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(0,5),(1,0),(1,7)], upper := (rows 13 98 52 137 146 288 66 193 321), lower := (rows 13 98 52 137 146 288 66 128 256), losses := [{ target := 5, region := (rows 5 2 4 13 16 0 82 132 260), good := (rows 397 66 477 137 210 256 66 128 256) }] }

theorem u3983 : Upper (D 7) (R 7) [12,96,48,129,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3983 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3984 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 13 98 52 137 208 288 65 130 258), lower := (rows 13 98 52 137 208 288 65 128 256), losses := [] }

theorem u3984 : Upper (D 7) (R 7) [12,96,48,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3984 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3985 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 52 137 208 288 66 131 259), lower := (rows 13 98 52 137 208 288 66 128 256), losses := [{ target := 0, region := (rows 0 294 4 8 24 288 359 128 256), good := (rows 94 98 118 216 208 354 66 128 354) }] }

theorem u3985 : Upper (D 7) (R 7) [12,96,48,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3985 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3986 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 },{ cop := 1, region := 276, targets := 128 }], pairs := [(1,0),(2,0),(2,7),(4,0)], upper := (rows 13 98 52 137 274 160 65 194 322), lower := (rows 13 98 52 137 274 160 65 128 256), losses := [] }

theorem u3986 : Upper (D 7) (R 7) [12,96,48,129,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3987 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(0,5),(1,0),(1,7),(3,5)], upper := (rows 13 98 52 137 274 160 66 193 321), lower := (rows 13 98 52 137 274 160 66 128 256), losses := [{ target := 5, region := (rows 5 2 4 13 16 0 82 132 260), good := (rows 397 66 477 137 338 128 66 128 256) }] }

theorem u3987 : Upper (D 7) (R 7) [12,96,48,129,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3988 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 438, targets := 1 },{ cop := 1, region := 276, targets := 128 }], pairs := [(1,0),(2,0),(2,7),(4,0)], upper := (rows 13 98 52 137 336 160 65 130 258), lower := (rows 13 98 52 137 336 160 65 128 256), losses := [] }

theorem u3988 : Upper (D 7) (R 7) [12,96,48,129,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3989 : Route 9 := (fun mask => (mask,id))

def c3989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3989 : Upper (D 7) (R 7) [12,96,48,129,320,128,2] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,320,128,2] 13 (by decide) (choices 1) [1,2] r3989 c3989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u280
  · exact u281

def b3990 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 13 98 52 137 400 34 65 194 322), lower := (rows 13 98 52 137 400 34 65 128 256), losses := [] }

theorem u3990 : Upper (D 7) (R 7) [12,96,48,129,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3991 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 52 137 400 34 66 193 321), lower := (rows 13 98 52 137 400 34 66 128 256), losses := [] }

theorem u3991 : Upper (D 7) (R 7) [12,96,48,129,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3992 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 98 52 138 81 160 65 386 258), lower := (rows 13 98 52 138 81 160 65 128 256), losses := [] }

theorem u3992 : Upper (D 7) (R 7) [12,96,48,130,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3993 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 420, targets := 66 }], pairs := [(1,0),(1,7),(2,1),(2,6)], upper := (rows 13 98 52 138 81 160 66 385 257), lower := (rows 13 98 52 138 81 160 66 128 256), losses := [] }

theorem u3993 : Upper (D 7) (R 7) [12,96,48,130,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3994 : Route 9 := (fun mask => (mask,id))

def c3994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3994 : Upper (D 7) (R 7) [12,96,48,130,65,128,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,65,128,256] 13 (by decide) (choices 1) [1,2] r3994 c3994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u282
  · exact u283

def b3995 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 13 98 52 138 81 288 65 130 386), lower := (rows 13 98 52 138 81 288 65 128 256), losses := [] }

theorem u3995 : Upper (D 7) (R 7) [12,96,48,130,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3995 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3996 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 420, targets := 2 }], pairs := [(1,0),(1,7),(2,1)], upper := (rows 13 98 52 138 81 288 66 129 385), lower := (rows 13 98 52 138 81 288 66 128 256), losses := [] }

theorem u3996 : Upper (D 7) (R 7) [12,96,48,130,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3996 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3997 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 294, targets := 128 }], pairs := [(1,7),(2,7),(4,1)], upper := (rows 13 98 52 138 81 288 192 131 259), lower := (rows 13 98 52 138 81 288 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 288 200 128 256), good := (rows 93 96 52 200 81 288 192 192 288) }] }

theorem u3997 : Upper (D 7) (R 7) [12,96,48,130,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3997 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3998 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 358, targets := 128 },{ cop := 6, region := 290, targets := 1 }], pairs := [(1,0),(1,7),(2,7)], upper := (rows 13 98 52 138 145 288 65 194 322), lower := (rows 13 98 52 138 145 288 65 128 256), losses := [] }

theorem u3998 : Upper (D 7) (R 7) [12,96,48,130,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3998 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3999 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7)], upper := (rows 13 98 52 138 145 288 66 193 321), lower := (rows 13 98 52 138 145 288 66 128 256), losses := [] }

theorem u3999 : Upper (D 7) (R 7) [12,96,48,130,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3999 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4000 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,0),(3,0),(4,0)], upper := (rows 13 98 52 138 208 33 65 386 258), lower := (rows 13 98 52 138 208 33 65 128 256), losses := [] }

theorem u4000 : Upper (D 7) (R 7) [12,96,48,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4001 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 3, region := 80, targets := 33 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 52 138 208 33 66 385 257), lower := (rows 13 98 52 138 208 33 66 128 256), losses := [] }

theorem u4001 : Upper (D 7) (R 7) [12,96,48,130,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4002 : Route 9 := (fun mask => (mask,id))

def c4002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4002 : Upper (D 7) (R 7) [12,96,48,130,192,1,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,192,1,256] 13 (by decide) (choices 1) [1,2] r4002 c4002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u284
  · exact u285

def r4003 : Route 9 := (fun mask => (mask,id))

def c4003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4003 : Upper (D 7) (R 7) [12,96,48,130,192,256,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,192,256,1] 13 (by decide) (choices 1) [1,2] r4003 c4003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u286
  · exact u287

def b4004 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 3, region := 80, targets := 1 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 52 138 208 288 66 129 257), lower := (rows 13 98 52 138 208 288 66 128 256), losses := [] }

theorem u4004 : Upper (D 7) (R 7) [12,96,48,130,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4004 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4005 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 170, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(0,7),(1,0),(3,0),(3,5)], upper := (rows 13 98 52 138 273 160 65 194 322), lower := (rows 13 98 52 138 273 160 65 128 256), losses := [{ target := 7, region := (rows 9 6 6 8 89 32 89 0 271), good := (rows 351 374 374 351 337 32 337 0 256) }] }

theorem u4005 : Upper (D 7) (R 7) [12,96,48,130,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4006 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 5, region := 74, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,5)], upper := (rows 13 98 52 138 273 160 66 193 321), lower := (rows 13 98 52 138 273 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 74 129 257), good := (rows 477 66 20 202 401 128 66 128 256) }] }

theorem u4006 : Upper (D 7) (R 7) [12,96,48,130,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4007 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 52 138 274 33 65 192 448), lower := (rows 13 98 52 138 274 33 65 128 256), losses := [] }

theorem u4007 : Upper (D 7) (R 7) [12,96,48,130,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4008 : Route 9 := (fun mask => (mask,id))

def c4008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4008 : Upper (D 7) (R 7) [12,96,48,130,258,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,258,1,128] 13 (by decide) (choices 1) [1,64] r4008 c4008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u288
  · exact u289

def b4009 : PairBound 9 := { available := 65, camps := [], pairs := [(0,7),(2,1),(3,5),(4,5)], upper := (rows 13 98 52 138 274 160 65 193 321), lower := (rows 13 98 52 138 274 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 235 65 193 321), good := (rows 493 480 52 168 308 160 481 160 256) },{ target := 5, region := (rows 1 2 4 10 18 0 65 193 321), good := (rows 461 474 20 154 282 128 449 128 256) },{ target := 7, region := (rows 9 2 6 8 26 32 73 0 329), good := (rows 349 374 52 351 278 32 321 0 256) }] }

theorem u4009 : Upper (D 7) (R 7) [12,96,48,130,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4010 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 52 138 336 33 65 130 386), lower := (rows 13 98 52 138 336 33 65 128 256), losses := [] }

theorem u4010 : Upper (D 7) (R 7) [12,96,48,130,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4011 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 13 98 52 138 336 33 66 129 385), lower := (rows 13 98 52 138 336 33 66 128 256), losses := [{ target := 1, region := (rows 9 0 14 8 18 41 64 169 297), good := (rows 429 500 436 445 336 417 84 128 256) }] }

theorem u4011 : Upper (D 7) (R 7) [12,96,48,130,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4012 : Route 9 := (fun mask => (mask,id))

def c4012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4012 : Upper (D 7) (R 7) [12,96,48,130,320,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,320,1,128] 13 (by decide) (choices 1) [1,2] r4012 c4012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u290
  · exact u291

def r4013 : Route 9 := (fun mask => (mask,id))

def c4013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4013 : Upper (D 7) (R 7) [12,96,48,130,320,128,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,320,128,1] 13 (by decide) (choices 1) [1,2] r4013 c4013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u292
  · exact u293

def b4014 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 5, region := 74, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,5)], upper := (rows 13 98 52 138 336 160 66 129 257), lower := (rows 13 98 52 138 336 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 74 129 257), good := (rows 477 66 20 202 336 128 66 128 256) }] }

theorem u4014 : Upper (D 7) (R 7) [12,96,48,130,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4015 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 52 138 400 33 65 194 322), lower := (rows 13 98 52 138 400 33 65 128 256), losses := [] }

theorem u4015 : Upper (D 7) (R 7) [12,96,48,130,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4016 : Route 9 := (fun mask => (mask,id))

def c4016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4016 : Upper (D 7) (R 7) [12,96,48,130,384,1,2] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,384,1,2] 13 (by decide) (choices 1) [1,64] r4016 c4016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u294
  · exact u295

def b4017 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 72, targets := 34 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(3,1),(3,5)], upper := (rows 13 98 52 200 145 288 65 130 258), lower := (rows 13 98 52 200 145 288 65 128 256), losses := [] }

theorem u4017 : Upper (D 7) (R 7) [12,96,48,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4017 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4018 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7)], upper := (rows 13 98 52 200 145 288 66 131 259), lower := (rows 13 98 52 200 145 288 66 128 256), losses := [] }

theorem u4018 : Upper (D 7) (R 7) [12,96,48,192,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4018 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4019 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,0),(3,0),(4,0)], upper := (rows 13 98 52 200 146 33 65 386 258), lower := (rows 13 98 52 200 146 33 65 128 256), losses := [] }

theorem u4019 : Upper (D 7) (R 7) [12,96,48,192,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4019
end Delivery.IrregularNine14.P07
