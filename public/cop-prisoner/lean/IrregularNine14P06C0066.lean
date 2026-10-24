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

def b3960 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 104 84 33 65 400 272), lower := (rows 11 134 38 104 84 33 65 128 256), losses := [] }

theorem u3960 : Upper (D 6) (R 6) [10,132,34,96,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3961 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 134 38 104 84 33 80 385 257), lower := (rows 11 134 38 104 84 33 80 128 256), losses := [] }

theorem u3961 : Upper (D 6) (R 6) [10,132,34,96,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3961 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3962 : Route 9 := (fun mask => (mask,id))

def c3962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3962 : Upper (D 6) (R 6) [10,132,34,96,68,1,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,68,1,256] 13 (by decide) (choices 1) [1,16] r3962 c3962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u286
  · exact u287

def b3963 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 104 84 288 65 145 273), lower := (rows 11 134 38 104 84 288 65 128 256), losses := [] }

theorem u3963 : Upper (D 6) (R 6) [10,132,34,96,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3963 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3964 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 11 134 38 104 84 288 80 129 257), lower := (rows 11 134 38 104 84 288 80 128 256), losses := [] }

theorem u3964 : Upper (D 6) (R 6) [10,132,34,96,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3964 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3965 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 134 38 104 273 33 68 208 336), lower := (rows 11 134 38 104 273 33 68 128 256), losses := [] }

theorem u3965 : Upper (D 6) (R 6) [10,132,34,96,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3966 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 134, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 38 104 273 33 80 196 324), lower := (rows 11 134 38 104 273 33 80 128 256), losses := [] }

theorem u3966 : Upper (D 6) (R 6) [10,132,34,96,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3966 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3967 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 104 273 48 65 196 324), lower := (rows 11 134 38 104 273 48 65 128 256), losses := [] }

theorem u3967 : Upper (D 6) (R 6) [10,132,34,96,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3967 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3968 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 134 38 104 273 48 68 193 321), lower := (rows 11 134 38 104 273 48 68 128 256), losses := [] }

theorem u3968 : Upper (D 6) (R 6) [10,132,34,96,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3968 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3969 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 104 276 33 65 208 336), lower := (rows 11 134 38 104 276 33 65 128 256), losses := [] }

theorem u3969 : Upper (D 6) (R 6) [10,132,34,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3970 : Route 9 := (fun mask => (mask,id))

def c3970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3970 : Upper (D 6) (R 6) [10,132,34,96,260,1,16] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,260,1,16] 13 (by decide) (choices 1) [1,64] r3970 c3970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u288
  · exact u289

def b3971 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 104 336 33 65 148 276), lower := (rows 11 134 38 104 336 33 65 128 256), losses := [] }

theorem u3971 : Upper (D 6) (R 6) [10,132,34,96,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3972 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 134 38 104 336 33 68 145 273), lower := (rows 11 134 38 104 336 33 68 128 256), losses := [] }

theorem u3972 : Upper (D 6) (R 6) [10,132,34,96,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3973 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 38 104 336 33 80 133 261), lower := (rows 11 134 38 104 336 33 80 128 256), losses := [] }

theorem u3973 : Upper (D 6) (R 6) [10,132,34,96,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3973 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3974 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 38 265 49 96 68 208 336), lower := (rows 11 134 38 265 49 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 25 25 103 70 129 257), good := (rows 505 228 100 441 441 96 100 128 256) }] }

theorem u3974 : Upper (D 6) (R 6) [10,132,34,257,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3975 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 265 49 96 80 196 324), lower := (rows 11 134 38 265 49 96 80 128 256), losses := [] }

theorem u3975 : Upper (D 6) (R 6) [10,132,34,257,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3975 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3976 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 296, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 38 265 81 96 68 176 304), lower := (rows 11 134 38 265 81 96 68 128 256), losses := [] }

theorem u3976 : Upper (D 6) (R 6) [10,132,34,257,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3977 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 265 81 96 80 164 292), lower := (rows 11 134 38 265 81 96 80 128 256), losses := [] }

theorem u3977 : Upper (D 6) (R 6) [10,132,34,257,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3977 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3978 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 265 81 96 96 148 276), lower := (rows 11 134 38 265 81 96 96 128 256), losses := [] }

theorem u3978 : Upper (D 6) (R 6) [10,132,34,257,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3979 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 150, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 265 84 96 65 176 304), lower := (rows 11 134 38 265 84 96 65 128 256), losses := [] }

theorem u3979 : Upper (D 6) (R 6) [10,132,34,257,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3980 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 265 84 96 80 161 289), lower := (rows 11 134 38 265 84 96 80 128 256), losses := [] }

theorem u3980 : Upper (D 6) (R 6) [10,132,34,257,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3980 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3981 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 38 265 84 96 96 145 273), lower := (rows 11 134 38 265 84 96 96 128 256), losses := [] }

theorem u3981 : Upper (D 6) (R 6) [10,132,34,257,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3982 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 38 268 49 96 65 208 336), lower := (rows 11 134 38 268 49 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 81 113 81 241 369), good := (rows 505 140 428 268 497 496 497 128 256) }] }

theorem u3982 : Upper (D 6) (R 6) [10,132,34,260,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3983 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 268 49 96 80 193 321), lower := (rows 11 134 38 268 49 96 80 128 256), losses := [] }

theorem u3983 : Upper (D 6) (R 6) [10,132,34,260,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3983 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3984 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 268 81 96 65 176 304), lower := (rows 11 134 38 268 81 96 65 128 256), losses := [] }

theorem u3984 : Upper (D 6) (R 6) [10,132,34,260,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3985 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 268 81 96 80 161 289), lower := (rows 11 134 38 268 81 96 80 128 256), losses := [] }

theorem u3985 : Upper (D 6) (R 6) [10,132,34,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3985 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3986 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 268 81 96 96 145 273), lower := (rows 11 134 38 268 81 96 96 128 256), losses := [] }

theorem u3986 : Upper (D 6) (R 6) [10,132,34,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3987 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 38 280 21 96 65 224 352), lower := (rows 11 134 38 280 21 96 65 128 256), losses := [] }

theorem u3987 : Upper (D 6) (R 6) [10,132,34,272,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3988 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 38 280 21 96 96 193 321), lower := (rows 11 134 38 280 21 96 96 128 256), losses := [] }

theorem u3988 : Upper (D 6) (R 6) [10,132,34,272,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3989 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 280 49 96 65 196 324), lower := (rows 11 134 38 280 49 96 65 128 256), losses := [] }

theorem u3989 : Upper (D 6) (R 6) [10,132,34,272,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3990 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 38 280 49 96 68 193 321), lower := (rows 11 134 38 280 49 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 25 17 103 70 129 257), good := (rows 505 228 100 280 441 96 100 128 256) }] }

theorem u3990 : Upper (D 6) (R 6) [10,132,34,272,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3991 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 280 81 96 65 164 292), lower := (rows 11 134 38 280 81 96 65 128 256), losses := [] }

theorem u3991 : Upper (D 6) (R 6) [10,132,34,272,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3992 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 296, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 38 280 81 96 68 161 289), lower := (rows 11 134 38 280 81 96 68 128 256), losses := [] }

theorem u3992 : Upper (D 6) (R 6) [10,132,34,272,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3993 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 280 81 96 96 133 261), lower := (rows 11 134 38 280 81 96 96 128 256), losses := [] }

theorem u3993 : Upper (D 6) (R 6) [10,132,34,272,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3994 : Route 9 := (fun mask => (mask,id))

def c3994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3994 : Upper (D 6) (R 6) [10,132,34,272,68,64,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,68,64,1] 13 (by decide) (choices 1) [1,32] r3994 c3994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u290
  · exact u291

def b3995 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 38 280 84 96 96 129 257), lower := (rows 11 134 38 280 84 96 96 128 256), losses := [] }

theorem u3995 : Upper (D 6) (R 6) [10,132,34,272,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3996 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 280 112 33 65 196 324), lower := (rows 11 134 38 280 112 33 65 128 256), losses := [] }

theorem u3996 : Upper (D 6) (R 6) [10,132,34,272,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3997 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,0),(4,1)], upper := (rows 11 134 38 280 112 33 68 193 321), lower := (rows 11 134 38 280 112 33 68 128 256), losses := [] }

theorem u3997 : Upper (D 6) (R 6) [10,132,34,272,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3998 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 296, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(3,2)], upper := (rows 11 134 38 296 81 33 68 208 336), lower := (rows 11 134 38 296 81 33 68 128 256), losses := [] }

theorem u3998 : Upper (D 6) (R 6) [10,132,34,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3999 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 296 81 33 80 196 324), lower := (rows 11 134 38 296 81 33 80 128 256), losses := [] }

theorem u3999 : Upper (D 6) (R 6) [10,132,34,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3999 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4000 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 38 296 81 48 65 196 324), lower := (rows 11 134 38 296 81 48 65 128 256), losses := [] }

theorem u4000 : Upper (D 6) (R 6) [10,132,34,288,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4000 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4001 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 134 38 296 81 48 68 193 321), lower := (rows 11 134 38 296 81 48 68 128 256), losses := [] }

theorem u4001 : Upper (D 6) (R 6) [10,132,34,288,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4001 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4002 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 296 81 96 65 148 276), lower := (rows 11 134 38 296 81 96 65 128 256), losses := [] }

theorem u4002 : Upper (D 6) (R 6) [10,132,34,288,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4003 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 296, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 134 38 296 81 96 68 145 273), lower := (rows 11 134 38 296 81 96 68 128 256), losses := [] }

theorem u4003 : Upper (D 6) (R 6) [10,132,34,288,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4004 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 296 81 96 80 133 261), lower := (rows 11 134 38 296 81 96 80 128 256), losses := [] }

theorem u4004 : Upper (D 6) (R 6) [10,132,34,288,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4004 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4005 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 130, targets := 33 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(1,5),(2,6)], upper := (rows 11 134 38 296 84 33 65 208 336), lower := (rows 11 134 38 296 84 33 65 128 256), losses := [] }

theorem u4005 : Upper (D 6) (R 6) [10,132,34,288,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4006 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 38 296 84 33 80 193 321), lower := (rows 11 134 38 296 84 33 80 128 256), losses := [] }

theorem u4006 : Upper (D 6) (R 6) [10,132,34,288,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4006 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4007 : Route 9 := (fun mask => (mask,id))

def c4007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4007 : Upper (D 6) (R 6) [10,132,34,288,68,64,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288,68,64,1] 13 (by decide) (choices 1) [1,16] r4007 c4007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u292
  · exact u293

def b4008 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 296 84 96 80 129 257), lower := (rows 11 134 38 296 84 96 80 128 256), losses := [] }

theorem u4008 : Upper (D 6) (R 6) [10,132,34,288,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4008 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4009 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 6 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 134 38 328 81 33 68 176 304), lower := (rows 11 134 38 328 81 33 68 128 256), losses := [] }

theorem u4009 : Upper (D 6) (R 6) [10,132,34,320,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4010 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 134 38 328 81 33 80 164 292), lower := (rows 11 134 38 328 81 33 80 128 256), losses := [] }

theorem u4010 : Upper (D 6) (R 6) [10,132,34,320,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4010 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4011 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 11 134 38 328 81 33 96 148 276), lower := (rows 11 134 38 328 81 33 96 128 256), losses := [] }

theorem u4011 : Upper (D 6) (R 6) [10,132,34,320,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4012 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 328 84 33 65 176 304), lower := (rows 11 134 38 328 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 97 97 148 276), good := (rows 105 412 508 360 508 97 97 128 256) }] }

theorem u4012 : Upper (D 6) (R 6) [10,132,34,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4013 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 38 328 84 33 80 161 289), lower := (rows 11 134 38 328 84 33 80 128 256), losses := [] }

theorem u4013 : Upper (D 6) (R 6) [10,132,34,320,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4013 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4014 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 38 328 84 33 96 145 273), lower := (rows 11 134 38 328 84 33 96 128 256), losses := [] }

theorem u4014 : Upper (D 6) (R 6) [10,132,34,320,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4015 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 328 112 33 65 148 276), lower := (rows 11 134 38 328 112 33 65 128 256), losses := [] }

theorem u4015 : Upper (D 6) (R 6) [10,132,34,320,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4016 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,0),(4,1)], upper := (rows 11 134 38 328 112 33 68 145 273), lower := (rows 11 134 38 328 112 33 68 128 256), losses := [] }

theorem u4016 : Upper (D 6) (R 6) [10,132,34,320,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4017 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 328 112 33 80 133 261), lower := (rows 11 134 38 328 112 33 80 128 256), losses := [] }

theorem u4017 : Upper (D 6) (R 6) [10,132,34,320,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4017 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4018 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 52 41 82 288 65 196 324), lower := (rows 11 134 52 41 82 288 65 128 256), losses := [] }

theorem u4018 : Upper (D 6) (R 6) [10,132,48,33,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4018 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4019 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 11 134 52 41 82 288 68 193 321), lower := (rows 11 134 52 41 82 288 68 128 256), losses := [] }

theorem u4019 : Upper (D 6) (R 6) [10,132,48,33,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4019 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4019
end Delivery.IrregularNine14.P06
