import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0015
import IrregularNine14P09C0016

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3960 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 13 168 336 160 340 404 276), lower := (rows 35 67 13 168 336 160 64 128 256), losses := [] }

theorem u3960 : Upper (D 9) (R 9) [34,65,9,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3960 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3961 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 168 336 288 212 148 404), lower := (rows 35 67 13 168 336 288 64 128 256), losses := [] }

theorem u3961 : Upper (D 9) (R 9) [34,65,9,160,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3961 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3962 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 168 400 36 336 464 336), lower := (rows 35 67 13 168 400 36 64 128 256), losses := [] }

theorem u3962 : Upper (D 9) (R 9) [34,65,9,160,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3962 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3963 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 67 13 168 400 48 324 452 324), lower := (rows 35 67 13 168 400 48 64 128 256), losses := [] }

theorem u3963 : Upper (D 9) (R 9) [34,65,9,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3963 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3964 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 168 400 96 340 404 276), lower := (rows 35 67 13 168 400 96 64 128 256), losses := [] }

theorem u3964 : Upper (D 9) (R 9) [34,65,9,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3964 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3965 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 64 }], pairs := [(1,5),(3,0),(3,6),(4,0),(4,5)], upper := (rows 35 67 13 168 400 288 84 212 340), lower := (rows 35 67 13 168 400 288 64 128 256), losses := [] }

theorem u3965 : Upper (D 9) (R 9) [34,65,9,160,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3965 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3966 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 55, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 200 52 48 448 384 384), lower := (rows 35 67 13 200 52 48 64 128 256), losses := [] }

theorem u3966 : Upper (D 9) (R 9) [34,65,9,192,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3966 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3967 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 67 13 200 52 160 336 400 272), lower := (rows 35 67 13 200 52 160 64 128 256), losses := [] }

theorem u3967 : Upper (D 9) (R 9) [34,65,9,192,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3967 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3968 : Route 9 := (fun mask => (mask,id))

def c3968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u3968 : Upper (D 9) (R 9) [34,65,9,192,36,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,36,256] 13 (by decide) (choices 1) [16,128,256] r3968 c3968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u949
  · exact u950
  · exact u951

def b3969 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 13 200 176 36 336 400 272), lower := (rows 35 67 13 200 176 36 64 128 256), losses := [] }

theorem u3969 : Upper (D 9) (R 9) [34,65,9,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3969 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3970 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 13 200 176 48 324 388 260), lower := (rows 35 67 13 200 176 48 64 128 256), losses := [] }

theorem u3970 : Upper (D 9) (R 9) [34,65,9,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3970 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3971 : Route 9 := (fun mask => (mask,id))

def c3971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3971 : Upper (D 9) (R 9) [34,65,9,192,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,160,256] 13 (by decide) (choices 1) [4,16,256] r3971 c3971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u952
  · exact u953
  · exact u954

def r3972 : Route 9 := (fun mask => (mask,id))

def c3972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3972 : Upper (D 9) (R 9) [34,65,9,192,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,260,16] 13 (by decide) (choices 1) [32,128,256] r3972 c3972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u955
  · exact u956
  · exact u957

def b3973 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,0)], upper := (rows 35 67 13 200 276 160 368 432 304), lower := (rows 35 67 13 200 276 160 64 128 256), losses := [] }

theorem u3973 : Upper (D 9) (R 9) [34,65,9,192,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3973 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3974 : Route 9 := (fun mask => (mask,id))

def c3974 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3974 : Upper (D 9) (R 9) [34,65,9,192,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,260,256] 13 (by decide) (choices 1) [16,32,128] r3974 c3974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u958
  · exact u959
  · exact u960

def b3975 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 200 304 36 464 400 400), lower := (rows 35 67 13 200 304 36 64 128 256), losses := [] }

theorem u3975 : Upper (D 9) (R 9) [34,65,9,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3975 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3976 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 13 200 304 48 452 388 388), lower := (rows 35 67 13 200 304 48 64 128 256), losses := [] }

theorem u3976 : Upper (D 9) (R 9) [34,65,9,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3976 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3977 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,0)], upper := (rows 35 67 13 200 304 160 340 404 276), lower := (rows 35 67 13 200 304 160 64 128 256), losses := [] }

theorem u3977 : Upper (D 9) (R 9) [34,65,9,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3977 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3978 : PairBound 9 := { available := 148, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 13 200 304 288 212 148 404), lower := (rows 35 67 13 200 304 288 64 128 256), losses := [] }

theorem u3978 : Upper (D 9) (R 9) [34,65,9,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3978 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3979 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 200 400 36 368 432 304), lower := (rows 35 67 13 200 400 36 64 128 256), losses := [] }

theorem u3979 : Upper (D 9) (R 9) [34,65,9,192,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3979 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3980 : Route 9 := (fun mask => (mask,id))

def c3980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3980 : Upper (D 9) (R 9) [34,65,9,192,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,384,16] 13 (by decide) (choices 1) [4,32,256] r3980 c3980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u961
  · exact u962
  · exact u963

def r3981 : Route 9 := (fun mask => (mask,id))

def c3981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3981 : Upper (D 9) (R 9) [34,65,9,192,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,384,256] 13 (by decide) (choices 1) [4,16,32] r3981 c3981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u964
  · exact u965
  · exact u966

def b3982 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 67 13 392 52 48 448 448 448), lower := (rows 35 67 13 392 52 48 64 128 256), losses := [] }

theorem u3982 : Upper (D 9) (R 9) [34,65,9,384,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3982 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3983 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 392 52 96 464 400 400), lower := (rows 35 67 13 392 52 96 64 128 256), losses := [] }

theorem u3983 : Upper (D 9) (R 9) [34,65,9,384,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3983 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3984 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 323, targets := 128 },{ cop := 4, region := 456, targets := 32 }], pairs := [(0,7),(1,7),(3,0),(3,5),(4,0)], upper := (rows 35 67 13 392 52 160 336 464 336), lower := (rows 35 67 13 392 52 160 64 128 256), losses := [] }

theorem u3984 : Upper (D 9) (R 9) [34,65,9,384,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3984 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3985 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 392 84 48 480 416 416), lower := (rows 35 67 13 392 84 48 64 128 256), losses := [] }

theorem u3985 : Upper (D 9) (R 9) [34,65,9,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3985 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3986 : Route 9 := (fun mask => (mask,id))

def c3986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3986 : Upper (D 9) (R 9) [34,65,9,384,68,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,68,128] 13 (by decide) (choices 1) [16,32,256] r3986 c3986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u967
  · exact u968
  · exact u969

def b3987 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 392 148 48 352 480 352), lower := (rows 35 67 13 392 148 48 64 128 256), losses := [] }

theorem u3987 : Upper (D 9) (R 9) [34,65,9,384,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3987 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3988 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 392 148 96 368 432 304), lower := (rows 35 67 13 392 148 96 64 128 256), losses := [] }

theorem u3988 : Upper (D 9) (R 9) [34,65,9,384,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3988 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3989 : Route 9 := (fun mask => (mask,id))

def c3989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3989 : Upper (D 9) (R 9) [34,65,9,384,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,132,256] 13 (by decide) (choices 1) [16,32] r3989 c3989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u970
  · exact u971

def b3990 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 392 176 36 336 464 336), lower := (rows 35 67 13 392 176 36 64 128 256), losses := [] }

theorem u3990 : Upper (D 9) (R 9) [34,65,9,384,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3990 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3991 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 13 392 176 48 324 452 324), lower := (rows 35 67 13 392 176 48 64 128 256), losses := [] }

theorem u3991 : Upper (D 9) (R 9) [34,65,9,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3991 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3992 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 13 392 176 96 340 404 276), lower := (rows 35 67 13 392 176 96 64 128 256), losses := [] }

theorem u3992 : Upper (D 9) (R 9) [34,65,9,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3992 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3993 : Route 9 := (fun mask => (mask,id))

def c3993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3993 : Upper (D 9) (R 9) [34,65,9,384,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,160,256] 13 (by decide) (choices 1) [4,16] r3993 c3993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u972
  · exact u973

def r3994 : Route 9 := (fun mask => (mask,id))

def c3994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3994 : Upper (D 9) (R 9) [34,65,9,384,192,4] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,192,4] 13 (by decide) (choices 1) [16,32,256] r3994 c3994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u974
  · exact u975
  · exact u976

def b3995 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 392 208 48 356 420 292), lower := (rows 35 67 13 392 208 48 64 128 256), losses := [] }

theorem u3995 : Upper (D 9) (R 9) [34,65,9,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3995 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3996 : Route 9 := (fun mask => (mask,id))

def c3996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3996 : Upper (D 9) (R 9) [34,65,9,384,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,192,256] 13 (by decide) (choices 1) [4,16,32] r3996 c3996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u977
  · exact u978
  · exact u979

def b3997 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 28 44 145 96 448 384 384), lower := (rows 35 67 28 44 145 96 64 128 256), losses := [] }

theorem u3997 : Upper (D 9) (R 9) [34,65,24,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3997 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3998 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 44, targets := 320 },{ cop := 0, region := 322, targets := 32 }], pairs := [(1,5),(2,6),(2,8),(3,6),(3,8)], upper := (rows 35 67 28 44 145 160 320 448 320), lower := (rows 35 67 28 44 145 160 64 128 256), losses := [] }

theorem u3998 : Upper (D 9) (R 9) [34,65,24,36,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3998 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3999 : Route 9 := (fun mask => (mask,id))

def c3999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3999 : Upper (D 9) (R 9) [34,65,24,36,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,129,256] 13 (by decide) (choices 1) [128,256] r3999 c3999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u980
  · exact u981

def b4000 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 28 44 208 33 448 384 384), lower := (rows 35 67 28 44 208 33 64 128 256), losses := [] }

theorem u4000 : Upper (D 9) (R 9) [34,65,24,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4000 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4001 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 44, targets := 65 },{ cop := 4, region := 35, targets := 256 }], pairs := [(0,8),(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 28 44 208 160 321 385 257), lower := (rows 35 67 28 44 208 160 64 128 256), losses := [] }

theorem u4001 : Upper (D 9) (R 9) [34,65,24,36,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4001 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4002 : Route 9 := (fun mask => (mask,id))

def c4002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4002 : Upper (D 9) (R 9) [34,65,24,36,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,192,256] 13 (by decide) (choices 1) [1,128,256] r4002 c4002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u982
  · exact u983
  · exact u984

def b4003 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 468, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 28 44 400 33 448 448 448), lower := (rows 35 67 28 44 400 33 64 128 256), losses := [] }

theorem u4003 : Upper (D 9) (R 9) [34,65,24,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4003 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4004 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 28 44 400 96 449 385 385), lower := (rows 35 67 28 44 400 96 64 128 256), losses := [] }

theorem u4004 : Upper (D 9) (R 9) [34,65,24,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4004 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4005 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 44, targets := 321 }], pairs := [(2,0),(2,6),(2,8),(3,0),(3,6)], upper := (rows 35 67 28 44 400 160 321 449 321), lower := (rows 35 67 28 44 400 160 64 128 256), losses := [] }

theorem u4005 : Upper (D 9) (R 9) [34,65,24,36,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4005 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4006 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 364, targets := 1 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(2,0),(3,0),(4,6)], upper := (rows 35 67 28 76 145 160 352 416 288), lower := (rows 35 67 28 76 145 160 64 128 256), losses := [] }

theorem u4006 : Upper (D 9) (R 9) [34,65,24,68,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4006 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4007 : Route 9 := (fun mask => (mask,id))

def c4007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u4007 : Upper (D 9) (R 9) [34,65,24,68,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,68,129,256] 13 (by decide) (choices 1) [32,128,256] r4007 c4007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u985
  · exact u986
  · exact u987

def b4008 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 35, targets := 384 },{ cop := 4, region := 332, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 28 76 176 33 448 384 384), lower := (rows 35 67 28 76 176 33 64 128 256), losses := [] }

theorem u4008 : Upper (D 9) (R 9) [34,65,24,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4008 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4009 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 67 28 76 176 160 321 385 257), lower := (rows 35 67 28 76 176 160 64 128 256), losses := [] }

theorem u4009 : Upper (D 9) (R 9) [34,65,24,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4009 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4010 : Route 9 := (fun mask => (mask,id))

def c4010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4010 : Upper (D 9) (R 9) [34,65,24,68,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,68,160,256] 13 (by decide) (choices 1) [1,128,256] r4010 c4010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u988
  · exact u989
  · exact u990

def b4011 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 28 76 400 33 480 416 416), lower := (rows 35 67 28 76 400 33 64 128 256), losses := [] }

theorem u4011 : Upper (D 9) (R 9) [34,65,24,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4011 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4012 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,6)], upper := (rows 35 67 28 76 400 160 353 417 289), lower := (rows 35 67 28 76 400 160 64 128 256), losses := [{ target := 8, region := (rows 5 10 4 8 16 176 64 128 0), good := (rows 35 67 63 79 176 160 64 160 0) }] }

theorem u4012 : Upper (D 9) (R 9) [34,65,24,68,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4012 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4013 : PairBound 9 := { available := 388, camps := [{ cop := 6, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 67 28 104 400 33 452 388 388), lower := (rows 35 67 28 104 400 33 64 128 256), losses := [] }

theorem u4013 : Upper (D 9) (R 9) [34,65,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4013 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4014 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 3, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 28 104 400 36 449 385 385), lower := (rows 35 67 28 104 400 36 64 128 256), losses := [] }

theorem u4014 : Upper (D 9) (R 9) [34,65,24,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4014 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4015 : Route 9 := (fun mask => (mask,id))

def c4015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4015 : Upper (D 9) (R 9) [34,65,24,96,384,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,384,128] 13 (by decide) (choices 1) [1,4,256] r4015 c4015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u991
  · exact u992
  · exact u993

def b4016 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 52, targets := 320 }], pairs := [(2,6),(2,8),(4,6),(4,8)], upper := (rows 35 67 28 137 176 36 320 448 320), lower := (rows 35 67 28 137 176 36 64 128 256), losses := [] }

theorem u4016 : Upper (D 9) (R 9) [34,65,24,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4016 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4017 : PairBound 9 := { available := 260, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 28 137 176 96 324 388 260), lower := (rows 35 67 28 137 176 96 64 128 256), losses := [] }

theorem u4017 : Upper (D 9) (R 9) [34,65,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4017 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4018 : Route 9 := (fun mask => (mask,id))

def c4018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4018 : Upper (D 9) (R 9) [34,65,24,129,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,160,256] 13 (by decide) (choices 1) [4,256] r4018 c4018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u994
  · exact u995

def b4019 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 28 137 208 36 352 416 288), lower := (rows 35 67 28 137 208 36 64 128 256), losses := [] }

theorem u4019 : Upper (D 9) (R 9) [34,65,24,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4019 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4019
end Delivery.IrregularNine14.P09
