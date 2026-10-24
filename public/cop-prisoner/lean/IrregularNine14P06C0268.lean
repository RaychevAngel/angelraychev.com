import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0065

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16080 : Route 9 := (fun mask => (mask,id))

def c16080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16080 : Upper (D 6) (R 6) [10,132,34,48,68,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,68,256] 13 (by decide) (choices 1) [1] r16080 c16080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u3925

def b16081 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 134 38 56 273 33 68 196 324), lower := (rows 11 134 38 56 273 33 64 128 256), losses := [] }

theorem u16081 : Upper (D 6) (R 6) [10,132,34,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16082 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 56 273 36 65 193 321), lower := (rows 11 134 38 56 273 36 64 128 256), losses := [] }

theorem u16082 : Upper (D 6) (R 6) [10,132,34,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16083 : Route 9 := (fun mask => (mask,id))

def c16083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16083 : Upper (D 6) (R 6) [10,132,34,48,257,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,257,64] 13 (by decide) (choices 1) [1,4] r16083 c16083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3926
  · exact u3927

def b16084 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 56 276 33 65 193 321), lower := (rows 11 134 38 56 276 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 33 97 161 289), good := (rows 489 156 508 504 284 481 64 128 256) }] }

theorem u16084 : Upper (D 6) (R 6) [10,132,34,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16085 : Route 9 := (fun mask => (mask,id))

def c16085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16085 : Upper (D 6) (R 6) [10,132,34,48,260,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,260,64] 13 (by decide) (choices 1) [1] r16085 c16085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u3928

def r16086 : Route 9 := (fun mask => (mask,id))

def c16086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16086 : Upper (D 6) (R 6) [10,132,34,48,320,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,320,1] 13 (by decide) (choices 1) [1,4] r16086 c16086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3929
  · exact u3930

def b16087 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 56 336 36 65 193 321), lower := (rows 11 134 38 56 336 36 64 128 256), losses := [] }

theorem u16087 : Upper (D 6) (R 6) [10,132,34,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16088 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 56 336 96 69 133 261), lower := (rows 11 134 38 56 336 96 64 128 256), losses := [] }

theorem u16088 : Upper (D 6) (R 6) [10,132,34,48,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16089 : PairBound 9 := { available := 336, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 73 49 36 336 464 336), lower := (rows 11 134 38 73 49 36 64 128 256), losses := [] }

theorem u16089 : Upper (D 6) (R 6) [10,132,34,65,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16090 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 73 49 48 324 452 324), lower := (rows 11 134 38 73 49 48 64 128 256), losses := [] }

theorem u16090 : Upper (D 6) (R 6) [10,132,34,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16090 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16091 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 48, targets := 6 },{ cop := 4, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 73 49 96 340 404 276), lower := (rows 11 134 38 73 49 96 64 128 256), losses := [] }

theorem u16091 : Upper (D 6) (R 6) [10,132,34,65,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16092 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 38 73 49 288 84 212 340), lower := (rows 11 134 38 73 49 288 64 128 256), losses := [] }

theorem u16092 : Upper (D 6) (R 6) [10,132,34,65,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16092 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16093 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 73 84 33 368 432 304), lower := (rows 11 134 38 73 84 33 64 128 256), losses := [] }

theorem u16093 : Upper (D 6) (R 6) [10,132,34,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16094 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 73 84 48 353 417 289), lower := (rows 11 134 38 73 84 48 64 128 256), losses := [] }

theorem u16094 : Upper (D 6) (R 6) [10,132,34,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16094 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16095 : Route 9 := (fun mask => (mask,id))

def c16095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16095 : Upper (D 6) (R 6) [10,132,34,65,68,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,68,256] 13 (by decide) (choices 1) [1,16,32] r16095 c16095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3931
  · exact u3932
  · exact u3933

def b16096 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 73 112 33 340 404 276), lower := (rows 11 134 38 73 112 33 64 128 256), losses := [] }

theorem u16096 : Upper (D 6) (R 6) [10,132,34,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16097 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 73 112 36 337 401 273), lower := (rows 11 134 38 73 112 36 64 128 256), losses := [] }

theorem u16097 : Upper (D 6) (R 6) [10,132,34,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16098 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 73 112 48 325 389 261), lower := (rows 11 134 38 73 112 48 64 128 256), losses := [] }

theorem u16098 : Upper (D 6) (R 6) [10,132,34,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16098 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16099 : Route 9 := (fun mask => (mask,id))

def c16099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16099 : Upper (D 6) (R 6) [10,132,34,65,96,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,96,256] 13 (by decide) (choices 1) [1,4,16] r16099 c16099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3934
  · exact u3935
  · exact u3936

def b16100 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 73 273 36 112 240 368), lower := (rows 11 134 38 73 273 36 64 128 256), losses := [] }

theorem u16100 : Upper (D 6) (R 6) [10,132,34,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16101 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 38 73 273 48 100 228 356), lower := (rows 11 134 38 73 273 48 64 128 256), losses := [] }

theorem u16101 : Upper (D 6) (R 6) [10,132,34,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16101 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16102 : Route 9 := (fun mask => (mask,id))

def c16102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16102 : Upper (D 6) (R 6) [10,132,34,65,257,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,257,64] 13 (by decide) (choices 1) [4,16,32] r16102 c16102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3937
  · exact u3938
  · exact u3939

def b16103 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 73 276 33 112 240 368), lower := (rows 11 134 38 73 276 33 64 128 256), losses := [] }

theorem u16103 : Upper (D 6) (R 6) [10,132,34,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16104 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 73 276 48 97 225 353), lower := (rows 11 134 38 73 276 48 64 128 256), losses := [] }

theorem u16104 : Upper (D 6) (R 6) [10,132,34,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16104 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16105 : Route 9 := (fun mask => (mask,id))

def c16105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16105 : Upper (D 6) (R 6) [10,132,34,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,260,64] 13 (by decide) (choices 1) [1,16,32] r16105 c16105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3940
  · exact u3941
  · exact u3942

def b16106 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 73 304 33 84 212 340), lower := (rows 11 134 38 73 304 33 64 128 256), losses := [] }

theorem u16106 : Upper (D 6) (R 6) [10,132,34,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16107 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 73 304 36 81 209 337), lower := (rows 11 134 38 73 304 36 64 128 256), losses := [] }

theorem u16107 : Upper (D 6) (R 6) [10,132,34,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16108 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 38 73 304 48 69 197 325), lower := (rows 11 134 38 73 304 48 64 128 256), losses := [] }

theorem u16108 : Upper (D 6) (R 6) [10,132,34,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16108 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16109 : Route 9 := (fun mask => (mask,id))

def c16109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16109 : Upper (D 6) (R 6) [10,132,34,65,288,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,288,64] 13 (by decide) (choices 1) [1,4,16] r16109 c16109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3943
  · exact u3944
  · exact u3945

def b16110 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 73 336 33 116 180 308), lower := (rows 11 134 38 73 336 33 64 128 256), losses := [] }

theorem u16110 : Upper (D 6) (R 6) [10,132,34,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16111 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 73 336 36 113 177 305), lower := (rows 11 134 38 73 336 36 64 128 256), losses := [] }

theorem u16111 : Upper (D 6) (R 6) [10,132,34,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16112 : Route 9 := (fun mask => (mask,id))

def c16112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16112 : Upper (D 6) (R 6) [10,132,34,65,320,16] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,320,16] 13 (by decide) (choices 1) [1,4,32] r16112 c16112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3946
  · exact u3947
  · exact u3948

def b16113 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 76 49 33 336 464 336), lower := (rows 11 134 38 76 49 33 64 128 256), losses := [] }

theorem u16113 : Upper (D 6) (R 6) [10,132,34,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16114 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 76 49 48 321 449 321), lower := (rows 11 134 38 76 49 48 64 128 256), losses := [] }

theorem u16114 : Upper (D 6) (R 6) [10,132,34,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16114 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16115 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 11 134 38 76 49 96 337 401 273), lower := (rows 11 134 38 76 49 96 64 128 256), losses := [] }

theorem u16115 : Upper (D 6) (R 6) [10,132,34,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16116 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 76 49 288 81 209 337), lower := (rows 11 134 38 76 49 288 64 128 256), losses := [] }

theorem u16116 : Upper (D 6) (R 6) [10,132,34,68,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16116 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16117 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 134 38 76 112 33 337 401 273), lower := (rows 11 134 38 76 112 33 64 128 256), losses := [] }

theorem u16117 : Upper (D 6) (R 6) [10,132,34,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16118 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 76 112 48 321 385 257), lower := (rows 11 134 38 76 112 48 64 128 256), losses := [] }

theorem u16118 : Upper (D 6) (R 6) [10,132,34,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16118 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16119 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 76 112 288 81 145 273), lower := (rows 11 134 38 76 112 288 64 128 256), losses := [] }

theorem u16119 : Upper (D 6) (R 6) [10,132,34,68,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16119 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16120 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 134 38 76 273 33 112 240 368), lower := (rows 11 134 38 76 273 33 64 128 256), losses := [] }

theorem u16120 : Upper (D 6) (R 6) [10,132,34,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16121 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 76 273 48 97 225 353), lower := (rows 11 134 38 76 273 48 64 128 256), losses := [] }

theorem u16121 : Upper (D 6) (R 6) [10,132,34,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16121 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16122 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 11 134 38 76 273 96 113 177 305), lower := (rows 11 134 38 76 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 134 38 108 276 96 96 128 256) }] }

theorem u16122 : Upper (D 6) (R 6) [10,132,34,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16123 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 134 38 76 304 33 81 209 337), lower := (rows 11 134 38 76 304 33 64 128 256), losses := [] }

theorem u16123 : Upper (D 6) (R 6) [10,132,34,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16124 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 38 76 304 48 65 193 321), lower := (rows 11 134 38 76 304 48 64 128 256), losses := [] }

theorem u16124 : Upper (D 6) (R 6) [10,132,34,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16124 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16125 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 11 134 38 76 304 96 81 145 273), lower := (rows 11 134 38 76 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 134 38 108 304 96 96 128 256) }] }

theorem u16125 : Upper (D 6) (R 6) [10,132,34,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16126 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 134 38 76 336 33 113 177 305), lower := (rows 11 134 38 76 336 33 64 128 256), losses := [] }

theorem u16126 : Upper (D 6) (R 6) [10,132,34,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16127 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 76 336 48 97 161 289), lower := (rows 11 134 38 76 336 48 64 128 256), losses := [] }

theorem u16127 : Upper (D 6) (R 6) [10,132,34,68,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16127 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16128 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 11 134 38 88 21 33 352 480 352), lower := (rows 11 134 38 88 21 33 64 128 256), losses := [] }

theorem u16128 : Upper (D 6) (R 6) [10,132,34,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16129 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 360, targets := 6 }], pairs := [(2,0),(3,1),(3,2)], upper := (rows 11 134 38 88 21 96 353 417 289), lower := (rows 11 134 38 88 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 134 38 120 20 96 96 128 256) }] }

theorem u16129 : Upper (D 6) (R 6) [10,132,34,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16130 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 360, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 134 38 88 21 288 97 225 353), lower := (rows 11 134 38 88 21 288 64 128 256), losses := [] }

theorem u16130 : Upper (D 6) (R 6) [10,132,34,80,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16130 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16131 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 88 49 33 324 452 324), lower := (rows 11 134 38 88 49 33 64 128 256), losses := [] }

theorem u16131 : Upper (D 6) (R 6) [10,132,34,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16132 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 88 49 36 321 449 321), lower := (rows 11 134 38 88 49 36 64 128 256), losses := [] }

theorem u16132 : Upper (D 6) (R 6) [10,132,34,80,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16133 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 134 38 88 49 96 325 389 261), lower := (rows 11 134 38 88 49 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 134 38 120 52 96 96 128 256) }] }

theorem u16133 : Upper (D 6) (R 6) [10,132,34,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16134 : Route 9 := (fun mask => (mask,id))

def c16134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16134 : Upper (D 6) (R 6) [10,132,34,80,33,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,33,256] 13 (by decide) (choices 1) [1,4] r16134 c16134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3949
  · exact u3950

def b16135 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 134 38 88 273 33 100 228 356), lower := (rows 11 134 38 88 273 33 64 128 256), losses := [] }

theorem u16135 : Upper (D 6) (R 6) [10,132,34,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16136 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 88 273 36 97 225 353), lower := (rows 11 134 38 88 273 36 64 128 256), losses := [] }

theorem u16136 : Upper (D 6) (R 6) [10,132,34,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16137 : Route 9 := (fun mask => (mask,id))

def c16137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16137 : Upper (D 6) (R 6) [10,132,34,80,257,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,257,64] 13 (by decide) (choices 1) [1,4,32] r16137 c16137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3951
  · exact u3952
  · exact u3953

def b16138 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 88 276 33 97 225 353), lower := (rows 11 134 38 88 276 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 33 97 161 289), good := (rows 489 156 508 88 284 481 64 128 256) }] }

theorem u16138 : Upper (D 6) (R 6) [10,132,34,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16139 : Route 9 := (fun mask => (mask,id))

def c16139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16139 : Upper (D 6) (R 6) [10,132,34,80,260,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,260,64] 13 (by decide) (choices 1) [1,32] r16139 c16139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3954
  · exact u3955

#print axioms u16139
end Delivery.IrregularNine14.P06
