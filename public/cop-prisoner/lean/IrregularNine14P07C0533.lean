import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0248
import IrregularNine14P07C0249
import IrregularNine14P07C0250

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31980 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 266 52 104 19 225 193 193 449), lower := (rows 7 266 52 104 19 32 64 128 256), losses := [] }

theorem u31980 : Upper (D 7) (R 7) [6,264,48,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31981 : Route 9 := (fun mask => (mask,id))

def c31981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31981 : Upper (D 7) (R 7) [6,264,48,96,65] 13 := by
  apply FastRouting.sound _ _ [6,264,48,96,65] 13 (by decide) (choices 1) [1,2,128] r31981 c31981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14925
  · exact u14926
  · exact u14927

def b31982 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(2,6),(3,1),(4,5)], upper := (rows 7 266 52 104 82 161 193 129 385), lower := (rows 7 266 52 104 82 32 64 128 256), losses := [] }

theorem u31982 : Upper (D 7) (R 7) [6,264,48,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31983 : Route 9 := (fun mask => (mask,id))

def c31983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31983 : Upper (D 7) (R 7) [6,264,48,96,129] 13 := by
  apply FastRouting.sound _ _ [6,264,48,96,129] 13 (by decide) (choices 1) [1,2,64,128] r31983 c31983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14928
  · exact u14929
  · exact u14930
  · exact u14931

def r31984 : Route 9 := (fun mask => (mask,id))

def c31984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31984 : Upper (D 7) (R 7) [6,264,48,96,130] 13 := by
  apply FastRouting.sound _ _ [6,264,48,96,130] 13 (by decide) (choices 1) [1,64,128] r31984 c31984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14932
  · exact u14933
  · exact u14934

def r31985 : Route 9 := (fun mask => (mask,id))

def c31985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31985 : Upper (D 7) (R 7) [6,264,48,96,192] 13 := by
  apply FastRouting.sound _ _ [6,264,48,96,192] 13 (by decide) (choices 1) [1,2,128] r31985 c31985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14935
  · exact u14936
  · exact u14937

def b31986 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 266 52 200 19 225 225 225 481), lower := (rows 7 266 52 200 19 32 64 128 256), losses := [] }

theorem u31986 : Upper (D 7) (R 7) [6,264,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31987 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 200 49 227 195 195 451), lower := (rows 7 266 52 200 49 32 64 128 256), losses := [] }

theorem u31987 : Upper (D 7) (R 7) [6,264,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31988 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 52 200 50 225 193 193 449), lower := (rows 7 266 52 200 50 32 64 128 256), losses := [] }

theorem u31988 : Upper (D 7) (R 7) [6,264,48,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31989 : Route 9 := (fun mask => (mask,id))

def c31989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31989 : Upper (D 7) (R 7) [6,264,48,192,65] 13 := by
  apply FastRouting.sound _ _ [6,264,48,192,65] 13 (by decide) (choices 1) [1,2,128] r31989 c31989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14938
  · exact u14939
  · exact u14940

def r31990 : Route 9 := (fun mask => (mask,id))

def c31990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31990 : Upper (D 7) (R 7) [6,264,48,192,66] 13 := by
  apply FastRouting.sound _ _ [6,264,48,192,66] 13 (by decide) (choices 1) [1,128] r31990 c31990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14941
  · exact u14942

def b31991 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 200 112 163 195 131 387), lower := (rows 7 266 52 200 112 32 64 128 256), losses := [] }

theorem u31991 : Upper (D 7) (R 7) [6,264,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31992 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 266 52 200 208 35 99 163 291), lower := (rows 7 266 52 200 208 32 64 128 256), losses := [] }

theorem u31992 : Upper (D 7) (R 7) [6,264,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31993 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 266 100 25 19 224 224 224 480), lower := (rows 7 266 100 25 19 32 64 128 256), losses := [] }

theorem u31993 : Upper (D 7) (R 7) [6,264,96,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31994 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 266 100 25 49 226 194 194 450), lower := (rows 7 266 100 25 49 32 64 128 256), losses := [] }

theorem u31994 : Upper (D 7) (R 7) [6,264,96,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31995 : Route 9 := (fun mask => (mask,id))

def c31995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31995 : Upper (D 7) (R 7) [6,264,96,17,34] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,34] 13 (by decide) (choices 1) [1,64,128] r31995 c31995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14943
  · exact u14944
  · exact u14945

def b31996 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 266 100 25 112 163 195 131 387), lower := (rows 7 266 100 25 112 32 64 128 256), losses := [] }

theorem u31996 : Upper (D 7) (R 7) [6,264,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31997 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 266 100 25 145 226 226 226 482), lower := (rows 7 266 100 25 145 32 64 128 256), losses := [] }

theorem u31997 : Upper (D 7) (R 7) [6,264,96,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31998 : Route 9 := (fun mask => (mask,id))

def c31998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31998 : Upper (D 7) (R 7) [6,264,96,17,130] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,130] 13 (by decide) (choices 1) [1,64,128] r31998 c31998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14946
  · exact u14947
  · exact u14948

def r31999 : Route 9 := (fun mask => (mask,id))

def c31999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31999 : Upper (D 7) (R 7) [6,264,96,17,160] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,160] 13 (by decide) (choices 1) [1,2,64,128] r31999 c31999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14949
  · exact u14950
  · exact u14951
  · exact u14952

def b32000 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 266 100 26 49 225 193 193 449), lower := (rows 7 266 100 26 49 32 64 128 256), losses := [] }

theorem u32000 : Upper (D 7) (R 7) [6,264,96,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32001 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 266 100 26 112 161 193 129 385), lower := (rows 7 266 100 26 112 32 64 128 256), losses := [] }

theorem u32001 : Upper (D 7) (R 7) [6,264,96,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32002 : Route 9 := (fun mask => (mask,id))

def c32002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32002 : Upper (D 7) (R 7) [6,264,96,18,129] 13 := by
  apply FastRouting.sound _ _ [6,264,96,18,129] 13 (by decide) (choices 1) [1,64,128] r32002 c32002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14953
  · exact u14954
  · exact u14955

def r32003 : Route 9 := (fun mask => (mask,id))

def c32003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32003 : Upper (D 7) (R 7) [6,264,96,18,160] 13 := by
  apply FastRouting.sound _ _ [6,264,96,18,160] 13 (by decide) (choices 1) [1,64,128] r32003 c32003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14956
  · exact u14957
  · exact u14958

def b32004 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 7 266 100 41 19 240 208 208 464), lower := (rows 7 266 100 41 19 32 64 128 256), losses := [] }

theorem u32004 : Upper (D 7) (R 7) [6,264,96,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32005 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 7 266 100 41 81 178 210 146 402), lower := (rows 7 266 100 41 81 32 64 128 256), losses := [] }

theorem u32005 : Upper (D 7) (R 7) [6,264,96,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32006 : Route 9 := (fun mask => (mask,id))

def c32006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32006 : Upper (D 7) (R 7) [6,264,96,33,66] 13 := by
  apply FastRouting.sound _ _ [6,264,96,33,66] 13 (by decide) (choices 1) [1,16,128] r32006 c32006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14959
  · exact u14960
  · exact u14961

def r32007 : Route 9 := (fun mask => (mask,id))

def c32007 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32007 : Upper (D 7) (R 7) [6,264,96,33,129] 13 := by
  apply FastRouting.sound _ _ [6,264,96,33,129] 13 (by decide) (choices 1) [2,16,64,128] r32007 c32007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14962
  · exact u14963
  · exact u14964
  · exact u14965

def r32008 : Route 9 := (fun mask => (mask,id))

def c32008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32008 : Upper (D 7) (R 7) [6,264,96,33,130] 13 := by
  apply FastRouting.sound _ _ [6,264,96,33,130] 13 (by decide) (choices 1) [1,16,64,128] r32008 c32008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14966
  · exact u14967
  · exact u14968
  · exact u14969

def r32009 : Route 9 := (fun mask => (mask,id))

def c32009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32009 : Upper (D 7) (R 7) [6,264,96,33,192] 13 := by
  apply FastRouting.sound _ _ [6,264,96,33,192] 13 (by decide) (choices 1) [1,2,16,128] r32009 c32009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14970
  · exact u14971
  · exact u14972
  · exact u14973

def b32010 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 266 100 42 81 177 209 145 401), lower := (rows 7 266 100 42 81 32 64 128 256), losses := [] }

theorem u32010 : Upper (D 7) (R 7) [6,264,96,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32011 : Route 9 := (fun mask => (mask,id))

def c32011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32011 : Upper (D 7) (R 7) [6,264,96,34,129] 13 := by
  apply FastRouting.sound _ _ [6,264,96,34,129] 13 (by decide) (choices 1) [1,16,64,128] r32011 c32011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14974
  · exact u14975
  · exact u14976
  · exact u14977

def r32012 : Route 9 := (fun mask => (mask,id))

def c32012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32012 : Upper (D 7) (R 7) [6,264,96,34,192] 13 := by
  apply FastRouting.sound _ _ [6,264,96,34,192] 13 (by decide) (choices 1) [1,16,128] r32012 c32012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14978
  · exact u14979
  · exact u14980

def b32013 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 266 100 56 19 225 193 193 449), lower := (rows 7 266 100 56 19 32 64 128 256), losses := [] }

theorem u32013 : Upper (D 7) (R 7) [6,264,96,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32014 : Route 9 := (fun mask => (mask,id))

def c32014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32014 : Upper (D 7) (R 7) [6,264,96,48,65] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,65] 13 (by decide) (choices 1) [1,2,128] r32014 c32014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14981
  · exact u14982
  · exact u14983

def r32015 : Route 9 := (fun mask => (mask,id))

def c32015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32015 : Upper (D 7) (R 7) [6,264,96,48,66] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,66] 13 (by decide) (choices 1) [1,128] r32015 c32015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14984
  · exact u14985

def r32016 : Route 9 := (fun mask => (mask,id))

def c32016 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32016 : Upper (D 7) (R 7) [6,264,96,48,129] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,129] 13 (by decide) (choices 1) [1,2,64,128] r32016 c32016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14986
  · exact u14987
  · exact u14988
  · exact u14989

def r32017 : Route 9 := (fun mask => (mask,id))

def c32017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32017 : Upper (D 7) (R 7) [6,264,96,48,130] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,130] 13 (by decide) (choices 1) [1,64,128] r32017 c32017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14990
  · exact u14991
  · exact u14992

def r32018 : Route 9 := (fun mask => (mask,id))

def c32018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32018 : Upper (D 7) (R 7) [6,264,96,48,192] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,192] 13 (by decide) (choices 1) [1,2,128] r32018 c32018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14993
  · exact u14994
  · exact u14995

def b32019 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 266 100 137 19 240 240 240 496), lower := (rows 7 266 100 137 19 32 64 128 256), losses := [] }

theorem u32019 : Upper (D 7) (R 7) [6,264,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32020 : Route 9 := (fun mask => (mask,id))

def c32020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32020 : Upper (D 7) (R 7) [6,264,96,129,33] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129,33] 13 (by decide) (choices 1) [2,16,64,128] r32020 c32020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14996
  · exact u14997
  · exact u14998
  · exact u14999

def r32021 : Route 9 := (fun mask => (mask,id))

def c32021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32021 : Upper (D 7) (R 7) [6,264,96,129,34] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129,34] 13 (by decide) (choices 1) [1,16,64,128] r32021 c32021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15000
  · exact u15001
  · exact u15002
  · exact u15003

def b32022 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 266 100 137 112 179 211 147 403), lower := (rows 7 266 100 137 112 32 64 128 256), losses := [] }

theorem u32022 : Upper (D 7) (R 7) [6,264,96,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32023 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 266 100 137 145 114 114 242 370), lower := (rows 7 266 100 137 145 32 64 128 256), losses := [] }

theorem u32023 : Upper (D 7) (R 7) [6,264,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32024 : Route 9 := (fun mask => (mask,id))

def c32024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32024 : Upper (D 7) (R 7) [6,264,96,129,130] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129,130] 13 (by decide) (choices 1) [1,16,64] r32024 c32024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15004
  · exact u15005
  · exact u15006

def r32025 : Route 9 := (fun mask => (mask,id))

def c32025 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32025 : Upper (D 7) (R 7) [6,264,96,129,160] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129,160] 13 (by decide) (choices 1) [1,2,16,64] r32025 c32025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15007
  · exact u15008
  · exact u15009
  · exact u15010

def b32026 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 266 100 138 49 241 209 209 465), lower := (rows 7 266 100 138 49 32 64 128 256), losses := [] }

theorem u32026 : Upper (D 7) (R 7) [6,264,96,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32027 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 266 100 138 112 177 209 145 401), lower := (rows 7 266 100 138 112 32 64 128 256), losses := [] }

theorem u32027 : Upper (D 7) (R 7) [6,264,96,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32028 : Route 9 := (fun mask => (mask,id))

def c32028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32028 : Upper (D 7) (R 7) [6,264,96,130,129] 13 := by
  apply FastRouting.sound _ _ [6,264,96,130,129] 13 (by decide) (choices 1) [1,16,64] r32028 c32028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15011
  · exact u15012
  · exact u15013

def r32029 : Route 9 := (fun mask => (mask,id))

def c32029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32029 : Upper (D 7) (R 7) [6,264,96,130,160] 13 := by
  apply FastRouting.sound _ _ [6,264,96,130,160] 13 (by decide) (choices 1) [1,16,64] r32029 c32029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15014
  · exact u15015
  · exact u15016

def b32030 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 266 100 152 19 225 225 225 481), lower := (rows 7 266 100 152 19 32 64 128 256), losses := [] }

theorem u32030 : Upper (D 7) (R 7) [6,264,96,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32031 : Route 9 := (fun mask => (mask,id))

def c32031 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32031 : Upper (D 7) (R 7) [6,264,96,144,33] 13 := by
  apply FastRouting.sound _ _ [6,264,96,144,33] 13 (by decide) (choices 1) [1,2,64,128] r32031 c32031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15017
  · exact u15018
  · exact u15019
  · exact u15020

def r32032 : Route 9 := (fun mask => (mask,id))

def c32032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32032 : Upper (D 7) (R 7) [6,264,96,144,34] 13 := by
  apply FastRouting.sound _ _ [6,264,96,144,34] 13 (by decide) (choices 1) [1,64,128] r32032 c32032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15021
  · exact u15022
  · exact u15023

def b32033 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 266 100 152 112 163 195 131 387), lower := (rows 7 266 100 152 112 32 64 128 256), losses := [] }

theorem u32033 : Upper (D 7) (R 7) [6,264,96,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32034 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 266 100 152 145 99 99 227 355), lower := (rows 7 266 100 152 145 32 64 128 256), losses := [] }

theorem u32034 : Upper (D 7) (R 7) [6,264,96,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32035 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 266 100 152 146 97 97 225 353), lower := (rows 7 266 100 152 146 32 64 128 256), losses := [] }

theorem u32035 : Upper (D 7) (R 7) [6,264,96,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32036 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 266 100 152 176 99 67 195 323), lower := (rows 7 266 100 152 176 32 64 128 256), losses := [] }

theorem u32036 : Upper (D 7) (R 7) [6,264,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32037 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 266 100 168 19 241 209 209 465), lower := (rows 7 266 100 168 19 32 64 128 256), losses := [] }

theorem u32037 : Upper (D 7) (R 7) [6,264,96,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32038 : Route 9 := (fun mask => (mask,id))

def c32038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32038 : Upper (D 7) (R 7) [6,264,96,160,65] 13 := by
  apply FastRouting.sound _ _ [6,264,96,160,65] 13 (by decide) (choices 1) [1,2,16,128] r32038 c32038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15024
  · exact u15025
  · exact u15026
  · exact u15027

def r32039 : Route 9 := (fun mask => (mask,id))

def c32039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32039 : Upper (D 7) (R 7) [6,264,96,160,66] 13 := by
  apply FastRouting.sound _ _ [6,264,96,160,66] 13 (by decide) (choices 1) [1,16,128] r32039 c32039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15028
  · exact u15029
  · exact u15030

#print axioms u32039
end Delivery.IrregularNine14.P07
