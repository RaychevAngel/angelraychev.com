import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0000

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b960 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 168 112 33 240 176 432), lower := (rows 7 11 324 168 112 33 64 128 256), losses := [] }

theorem u960 : Upper (D 8) (R 8) [6,9,320,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 324 168 112 48 225 161 417), lower := (rows 7 11 324 168 112 48 64 128 256), losses := [] }

theorem u961 : Upper (D 8) (R 8) [6,9,320,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b961 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b962 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 324 168 112 160 113 177 305), lower := (rows 7 11 324 168 112 160 64 128 256), losses := [] }

theorem u962 : Upper (D 8) (R 8) [6,9,320,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b963 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 168 208 33 112 176 304), lower := (rows 7 11 324 168 208 33 64 128 256), losses := [] }

theorem u963 : Upper (D 8) (R 8) [6,9,320,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b964 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 11 324 168 208 48 97 161 289), lower := (rows 7 11 324 168 208 48 64 128 256), losses := [] }

theorem u964 : Upper (D 8) (R 8) [6,9,320,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b964 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 176 33 448 448 448), lower := (rows 7 26 37 104 176 33 64 128 256), losses := [] }

theorem u965 : Upper (D 8) (R 8) [6,24,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 176 96 449 385 385), lower := (rows 7 26 37 104 176 96 64 128 256), losses := [] }

theorem u966 : Upper (D 8) (R 8) [6,24,33,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 26 37 104 176 288 193 193 449), lower := (rows 7 26 37 104 176 288 64 128 256), losses := [] }

theorem u967 : Upper (D 8) (R 8) [6,24,33,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b967 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 304 33 192 192 448), lower := (rows 7 26 37 104 304 33 64 128 256), losses := [] }

theorem u968 : Upper (D 8) (R 8) [6,24,33,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b969 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 304 96 193 129 385), lower := (rows 7 26 37 104 304 96 64 128 256), losses := [] }

theorem u969 : Upper (D 8) (R 8) [6,24,33,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r970 : Route 9 := (fun mask => (mask,id))

def c970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u970 : Upper (D 8) (R 8) [6,24,33,96,288,128] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,288,128] 13 (by decide) (choices 1) [1,128] r970 c970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u35
  · exact u36

def b971 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 400 33 224 224 480), lower := (rows 7 26 37 104 400 33 64 128 256), losses := [] }

theorem u971 : Upper (D 8) (R 8) [6,24,33,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 400 96 225 161 417), lower := (rows 7 26 37 104 400 96 64 128 256), losses := [] }

theorem u972 : Upper (D 8) (R 8) [6,24,33,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 7 26 37 104 400 160 97 225 353), lower := (rows 7 26 37 104 400 160 64 128 256), losses := [] }

theorem u973 : Upper (D 8) (R 8) [6,24,33,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 200 304 33 224 224 480), lower := (rows 7 26 37 200 304 33 64 128 256), losses := [] }

theorem u974 : Upper (D 8) (R 8) [6,24,33,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 37 200 304 96 225 161 417), lower := (rows 7 26 37 200 304 96 64 128 256), losses := [] }

theorem u975 : Upper (D 8) (R 8) [6,24,33,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 168 304 33 224 224 480), lower := (rows 7 26 69 168 304 33 64 128 256), losses := [] }

theorem u976 : Upper (D 8) (R 8) [6,24,65,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r977 : Route 9 := (fun mask => (mask,id))

def c977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u977 : Upper (D 8) (R 8) [6,24,65,160,288,64] 13 := by
  apply FastRouting.sound _ _ [6,24,65,160,288,64] 13 (by decide) (choices 1) [1,32,128] r977 c977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37
  · exact u38
  · exact u39

def b978 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 69 168 304 160 97 225 353), lower := (rows 7 26 69 168 304 160 64 128 256), losses := [] }

theorem u978 : Upper (D 8) (R 8) [6,24,65,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b979 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 100 41 176 33 448 448 448), lower := (rows 7 26 100 41 176 33 64 128 256), losses := [] }

theorem u979 : Upper (D 8) (R 8) [6,24,96,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b980 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 41 176 96 449 385 385), lower := (rows 7 26 100 41 176 96 64 128 256), losses := [] }

theorem u980 : Upper (D 8) (R 8) [6,24,96,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 41 176 160 321 449 321), lower := (rows 7 26 100 41 176 160 64 128 256), losses := [] }

theorem u981 : Upper (D 8) (R 8) [6,24,96,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b982 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 26 100 41 176 288 193 193 449), lower := (rows 7 26 100 41 176 288 64 128 256), losses := [] }

theorem u982 : Upper (D 8) (R 8) [6,24,96,33,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b982 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b983 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 100 41 304 33 192 192 448), lower := (rows 7 26 100 41 304 33 64 128 256), losses := [] }

theorem u983 : Upper (D 8) (R 8) [6,24,96,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 41 304 96 193 129 385), lower := (rows 7 26 100 41 304 96 64 128 256), losses := [] }

theorem u984 : Upper (D 8) (R 8) [6,24,96,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r985 : Route 9 := (fun mask => (mask,id))

def c985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u985 : Upper (D 8) (R 8) [6,24,96,33,288,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,288,128] 13 (by decide) (choices 1) [1,128] r985 c985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u40
  · exact u41

def b986 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 100 41 400 33 224 224 480), lower := (rows 7 26 100 41 400 33 64 128 256), losses := [] }

theorem u986 : Upper (D 8) (R 8) [6,24,96,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 41 400 96 225 161 417), lower := (rows 7 26 100 41 400 96 64 128 256), losses := [] }

theorem u987 : Upper (D 8) (R 8) [6,24,96,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b988 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 7 26 100 41 400 160 97 225 353), lower := (rows 7 26 100 41 400 160 64 128 256), losses := [] }

theorem u988 : Upper (D 8) (R 8) [6,24,96,33,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b989 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 137 304 33 224 224 480), lower := (rows 7 26 100 137 304 33 64 128 256), losses := [] }

theorem u989 : Upper (D 8) (R 8) [6,24,96,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b990 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 137 304 96 225 161 417), lower := (rows 7 26 100 137 304 96 64 128 256), losses := [] }

theorem u990 : Upper (D 8) (R 8) [6,24,96,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r991 : Route 9 := (fun mask => (mask,id))

def c991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u991 : Upper (D 8) (R 8) [6,24,96,129,288,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,128] 13 (by decide) (choices 1) [1,32] r991 c991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u42
  · exact u43

def b992 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 168 273 33 224 224 480), lower := (rows 7 26 100 168 273 33 64 128 256), losses := [] }

theorem u992 : Upper (D 8) (R 8) [6,24,96,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 168 273 96 225 161 417), lower := (rows 7 26 100 168 273 96 64 128 256), losses := [] }

theorem u993 : Upper (D 8) (R 8) [6,24,96,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 168 273 160 97 225 353), lower := (rows 7 26 100 168 273 160 64 128 256), losses := [] }

theorem u994 : Upper (D 8) (R 8) [6,24,96,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r995 : Route 9 := (fun mask => (mask,id))

def c995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u995 : Upper (D 8) (R 8) [6,24,96,160,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,288,1] 13 (by decide) (choices 1) [1,128] r995 c995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u44
  · exact u45

def b996 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 168 304 96 193 129 385), lower := (rows 7 26 100 168 304 96 64 128 256), losses := [] }

theorem u996 : Upper (D 8) (R 8) [6,24,96,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b997 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 168 304 160 65 193 321), lower := (rows 7 26 100 168 304 160 64 128 256), losses := [] }

theorem u997 : Upper (D 8) (R 8) [6,24,96,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b998 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 196 41 304 33 224 224 480), lower := (rows 7 26 196 41 304 33 64 128 256), losses := [] }

theorem u998 : Upper (D 8) (R 8) [6,24,192,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 402, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 196 41 304 96 225 161 417), lower := (rows 7 26 196 41 304 96 64 128 256), losses := [] }

theorem u999 : Upper (D 8) (R 8) [6,24,192,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1000 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 104 176 33 224 224 480), lower := (rows 7 26 261 104 176 33 64 128 256), losses := [] }

theorem u1000 : Upper (D 8) (R 8) [6,24,257,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1001 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 261 104 176 96 225 161 417), lower := (rows 7 26 261 104 176 96 64 128 256), losses := [] }

theorem u1001 : Upper (D 8) (R 8) [6,24,257,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 292 41 112 33 192 192 448), lower := (rows 7 26 292 41 112 33 64 128 256), losses := [] }

theorem u1002 : Upper (D 8) (R 8) [6,24,288,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 41 112 96 193 129 385), lower := (rows 7 26 292 41 112 96 64 128 256), losses := [] }

theorem u1003 : Upper (D 8) (R 8) [6,24,288,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1004 : Route 9 := (fun mask => (mask,id))

def c1004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1004 : Upper (D 8) (R 8) [6,24,288,33,96,128] 13 := by
  apply FastRouting.sound _ _ [6,24,288,33,96,128] 13 (by decide) (choices 1) [1,128] r1004 c1004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u46
  · exact u47

def b1005 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 292 41 208 33 224 224 480), lower := (rows 7 26 292 41 208 33 64 128 256), losses := [] }

theorem u1005 : Upper (D 8) (R 8) [6,24,288,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1006 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 26 292 41 208 96 225 161 417), lower := (rows 7 26 292 41 208 96 64 128 256), losses := [] }

theorem u1006 : Upper (D 8) (R 8) [6,24,288,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1007 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 292 73 176 33 224 224 480), lower := (rows 7 26 292 73 176 33 64 128 256), losses := [] }

theorem u1007 : Upper (D 8) (R 8) [6,24,288,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1008 : Route 9 := (fun mask => (mask,id))

def c1008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1008 : Upper (D 8) (R 8) [6,24,288,65,160,64] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,160,64] 13 (by decide) (choices 1) [1,32,128] r1008 c1008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u48
  · exact u49
  · exact u50

def b1009 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 292 73 176 160 97 225 353), lower := (rows 7 26 292 73 176 160 64 128 256), losses := [] }

theorem u1009 : Upper (D 8) (R 8) [6,24,288,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1010 : Route 9 := (fun mask => (mask,id))

def c1010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1010 : Upper (D 8) (R 8) [6,24,288,96,160,1] 13 := by
  apply FastRouting.sound _ _ [6,24,288,96,160,1] 13 (by decide) (choices 1) [1,128] r1010 c1010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u51
  · exact u52

def b1011 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 104 176 96 193 129 385), lower := (rows 7 26 292 104 176 96 64 128 256), losses := [] }

theorem u1011 : Upper (D 8) (R 8) [6,24,288,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1012 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 324 41 176 33 224 224 480), lower := (rows 7 26 324 41 176 33 64 128 256), losses := [] }

theorem u1012 : Upper (D 8) (R 8) [6,24,320,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1013 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 146, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 324 41 176 96 225 161 417), lower := (rows 7 26 324 41 176 96 64 128 256), losses := [] }

theorem u1013 : Upper (D 8) (R 8) [6,24,320,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 324 41 176 160 97 225 353), lower := (rows 7 26 324 41 176 160 64 128 256), losses := [] }

theorem u1014 : Upper (D 8) (R 8) [6,24,320,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 56 400 33 224 224 480), lower := (rows 7 35 76 56 400 33 64 128 256), losses := [] }

theorem u1015 : Upper (D 8) (R 8) [6,33,72,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1016 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 56 400 96 225 161 417), lower := (rows 7 35 76 56 400 96 64 128 256), losses := [] }

theorem u1016 : Upper (D 8) (R 8) [6,33,72,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1017 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 56 400 160 97 225 353), lower := (rows 7 35 76 56 400 160 64 128 256), losses := [] }

theorem u1017 : Upper (D 8) (R 8) [6,33,72,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1018 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 304 33 224 224 480), lower := (rows 7 35 76 152 304 33 64 128 256), losses := [] }

theorem u1018 : Upper (D 8) (R 8) [6,33,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 152 304 96 225 161 417), lower := (rows 7 35 76 152 304 96 64 128 256), losses := [] }

theorem u1019 : Upper (D 8) (R 8) [6,33,72,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P08
