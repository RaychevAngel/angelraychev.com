import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0129
import IrregularNine14P06C0130

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r25080 : Route 9 := (fun mask => (mask,id))

def c25080 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25080 : Upper (D 6) (R 6) [34,192,264,80,36,1] 13 := by
  apply FastRouting.sound _ _ [34,192,264,80,36,1] 13 (by decide) (choices 1) [1,2,4] r25080 c25080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7791
  · exact u7792
  · exact u7793

def b25081 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 88 52 34 69 133 261), lower := (rows 35 194 268 88 52 34 64 128 256), losses := [] }

theorem u25081 : Upper (D 6) (R 6) [34,192,264,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25082 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 268 88 52 36 67 131 259), lower := (rows 35 194 268 88 52 36 64 128 256), losses := [] }

theorem u25082 : Upper (D 6) (R 6) [34,192,264,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25083 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 35 194 268 104 21 33 86 150 278), lower := (rows 35 194 268 104 21 33 64 128 256), losses := [] }

theorem u25083 : Upper (D 6) (R 6) [34,192,264,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25084 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 104 21 34 85 149 277), lower := (rows 35 194 268 104 21 34 64 128 256), losses := [] }

theorem u25084 : Upper (D 6) (R 6) [34,192,264,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25085 : Route 9 := (fun mask => (mask,id))

def c25085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25085 : Upper (D 6) (R 6) [34,192,264,96,5,4] 13 := by
  apply FastRouting.sound _ _ [34,192,264,96,5,4] 13 (by decide) (choices 1) [1,2,16] r25085 c25085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7794
  · exact u7795
  · exact u7796

def r25086 : Route 9 := (fun mask => (mask,id))

def c25086 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25086 : Upper (D 6) (R 6) [34,192,264,96,5,16] 13 := by
  apply FastRouting.sound _ _ [34,192,264,96,5,16] 13 (by decide) (choices 1) [1,2,4] r25086 c25086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7797
  · exact u7798
  · exact u7799

def b25087 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 268 104 22 33 85 149 277), lower := (rows 35 194 268 104 22 33 64 128 256), losses := [] }

theorem u25087 : Upper (D 6) (R 6) [34,192,264,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25088 : Route 9 := (fun mask => (mask,id))

def c25088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25088 : Upper (D 6) (R 6) [34,192,264,96,6,4] 13 := by
  apply FastRouting.sound _ _ [34,192,264,96,6,4] 13 (by decide) (choices 1) [1,16] r25088 c25088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7800
  · exact u7801

def b25089 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 268 104 22 48 69 133 261), lower := (rows 35 194 268 104 22 48 64 128 256), losses := [] }

theorem u25089 : Upper (D 6) (R 6) [34,192,264,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25089 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25090 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 292 13 22 33 88 216 344), lower := (rows 35 194 292 13 22 33 64 128 256), losses := [] }

theorem u25090 : Upper (D 6) (R 6) [34,192,288,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25091 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 292 13 22 40 81 209 337), lower := (rows 35 194 292 13 22 40 64 128 256), losses := [] }

theorem u25091 : Upper (D 6) (R 6) [34,192,288,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25091 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25092 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 292 13 22 48 73 201 329), lower := (rows 35 194 292 13 22 48 64 128 256), losses := [] }

theorem u25092 : Upper (D 6) (R 6) [34,192,288,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25092 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25093 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 292 13 22 96 89 153 281), lower := (rows 35 194 292 13 22 96 64 128 256), losses := [] }

theorem u25093 : Upper (D 6) (R 6) [34,192,288,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25094 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 292 13 26 33 84 212 340), lower := (rows 35 194 292 13 26 33 64 128 256), losses := [] }

theorem u25094 : Upper (D 6) (R 6) [34,192,288,5,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25095 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 292 13 26 36 81 209 337), lower := (rows 35 194 292 13 26 36 64 128 256), losses := [] }

theorem u25095 : Upper (D 6) (R 6) [34,192,288,5,10,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25096 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 292 13 26 48 69 197 325), lower := (rows 35 194 292 13 26 48 64 128 256), losses := [] }

theorem u25096 : Upper (D 6) (R 6) [34,192,288,5,10,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25096 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25097 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 292 13 26 96 85 149 277), lower := (rows 35 194 292 13 26 96 64 128 256), losses := [] }

theorem u25097 : Upper (D 6) (R 6) [34,192,288,5,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25098 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 292 13 81 34 92 156 284), lower := (rows 35 194 292 13 81 34 64 128 256), losses := [] }

theorem u25098 : Upper (D 6) (R 6) [34,192,288,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25099 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 292 13 81 36 90 154 282), lower := (rows 35 194 292 13 81 36 64 128 256), losses := [] }

theorem u25099 : Upper (D 6) (R 6) [34,192,288,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25100 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 292 13 81 40 86 150 278), lower := (rows 35 194 292 13 81 40 64 128 256), losses := [] }

theorem u25100 : Upper (D 6) (R 6) [34,192,288,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25100 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25101 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 292 13 81 48 78 142 270), lower := (rows 35 194 292 13 81 48 64 128 256), losses := [] }

theorem u25101 : Upper (D 6) (R 6) [34,192,288,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25101 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25102 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 292 13 84 33 90 154 282), lower := (rows 35 194 292 13 84 33 64 128 256), losses := [] }

theorem u25102 : Upper (D 6) (R 6) [34,192,288,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25103 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 292 13 84 34 89 153 281), lower := (rows 35 194 292 13 84 34 64 128 256), losses := [] }

theorem u25103 : Upper (D 6) (R 6) [34,192,288,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25104 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 292 13 84 40 83 147 275), lower := (rows 35 194 292 13 84 40 64 128 256), losses := [] }

theorem u25104 : Upper (D 6) (R 6) [34,192,288,5,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25104 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25105 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 292 13 84 48 75 139 267), lower := (rows 35 194 292 13 84 48 64 128 256), losses := [] }

theorem u25105 : Upper (D 6) (R 6) [34,192,288,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25105 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25106 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 292 13 88 33 86 150 278), lower := (rows 35 194 292 13 88 33 64 128 256), losses := [] }

theorem u25106 : Upper (D 6) (R 6) [34,192,288,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25107 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 292 13 88 34 85 149 277), lower := (rows 35 194 292 13 88 34 64 128 256), losses := [] }

theorem u25107 : Upper (D 6) (R 6) [34,192,288,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25108 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 292 13 88 36 83 147 275), lower := (rows 35 194 292 13 88 36 64 128 256), losses := [] }

theorem u25108 : Upper (D 6) (R 6) [34,192,288,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25109 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 292 13 88 48 71 135 263), lower := (rows 35 194 292 13 88 48 64 128 256), losses := [] }

theorem u25109 : Upper (D 6) (R 6) [34,192,288,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25109 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25110 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 292 14 25 33 84 212 340), lower := (rows 35 194 292 14 25 33 64 128 256), losses := [] }

theorem u25110 : Upper (D 6) (R 6) [34,192,288,6,9,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25111 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 14 25 36 81 209 337), lower := (rows 35 194 292 14 25 36 64 128 256), losses := [] }

theorem u25111 : Upper (D 6) (R 6) [34,192,288,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25112 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 292 14 25 48 69 197 325), lower := (rows 35 194 292 14 25 48 64 128 256), losses := [] }

theorem u25112 : Upper (D 6) (R 6) [34,192,288,6,9,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25112 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25113 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 292 14 25 96 85 149 277), lower := (rows 35 194 292 14 25 96 64 128 256), losses := [] }

theorem u25113 : Upper (D 6) (R 6) [34,192,288,6,9,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25114 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 292 14 81 33 92 156 284), lower := (rows 35 194 292 14 81 33 64 128 256), losses := [] }

theorem u25114 : Upper (D 6) (R 6) [34,192,288,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25115 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 14 81 36 89 153 281), lower := (rows 35 194 292 14 81 36 64 128 256), losses := [] }

theorem u25115 : Upper (D 6) (R 6) [34,192,288,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25116 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 292 14 81 40 85 149 277), lower := (rows 35 194 292 14 81 40 64 128 256), losses := [] }

theorem u25116 : Upper (D 6) (R 6) [34,192,288,6,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25116 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25117 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 292 14 81 48 77 141 269), lower := (rows 35 194 292 14 81 48 64 128 256), losses := [] }

theorem u25117 : Upper (D 6) (R 6) [34,192,288,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25117 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25118 : Route 9 := (fun mask => (mask,id))

def c25118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25118 : Upper (D 6) (R 6) [34,192,288,6,68,1] 13 := by
  apply FastRouting.sound _ _ [34,192,288,6,68,1] 13 (by decide) (choices 1) [1,8,16] r25118 c25118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7802
  · exact u7803
  · exact u7804

def b25119 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 292 14 84 40 81 145 273), lower := (rows 35 194 292 14 84 40 64 128 256), losses := [] }

theorem u25119 : Upper (D 6) (R 6) [34,192,288,6,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25119 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25120 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 292 14 84 48 73 137 265), lower := (rows 35 194 292 14 84 48 64 128 256), losses := [] }

theorem u25120 : Upper (D 6) (R 6) [34,192,288,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25120 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25121 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 292 14 88 33 85 149 277), lower := (rows 35 194 292 14 88 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 20 8 16 59 0 144 272), good := (rows 35 163 292 47 445 33 0 128 256) }] }

theorem u25121 : Upper (D 6) (R 6) [34,192,288,6,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25122 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 14 88 36 81 145 273), lower := (rows 35 194 292 14 88 36 64 128 256), losses := [] }

theorem u25122 : Upper (D 6) (R 6) [34,192,288,6,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25123 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 292 14 88 48 69 133 261), lower := (rows 35 194 292 14 88 48 64 128 256), losses := [] }

theorem u25123 : Upper (D 6) (R 6) [34,192,288,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25123 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25124 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 194 292 25 28 33 70 198 326), lower := (rows 35 194 292 25 28 33 64 128 256), losses := [] }

theorem u25124 : Upper (D 6) (R 6) [34,192,288,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25125 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 292 25 28 34 69 197 325), lower := (rows 35 194 292 25 28 34 64 128 256), losses := [] }

theorem u25125 : Upper (D 6) (R 6) [34,192,288,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25126 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 25 28 36 67 195 323), lower := (rows 35 194 292 25 28 36 64 128 256), losses := [] }

theorem u25126 : Upper (D 6) (R 6) [34,192,288,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25127 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 292 25 28 96 71 135 263), lower := (rows 35 194 292 25 28 96 64 128 256), losses := [] }

theorem u25127 : Upper (D 6) (R 6) [34,192,288,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25128 : Route 9 := (fun mask => (mask,id))

def c25128 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25128 : Upper (D 6) (R 6) [34,192,288,17,68,1] 13 := by
  apply FastRouting.sound _ _ [34,192,288,17,68,1] 13 (by decide) (choices 1) [2,4,8] r25128 c25128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7805
  · exact u7806
  · exact u7807

def b25129 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 292 25 84 34 77 141 269), lower := (rows 35 194 292 25 84 34 64 128 256), losses := [] }

theorem u25129 : Upper (D 6) (R 6) [34,192,288,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25130 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 25 84 36 75 139 267), lower := (rows 35 194 292 25 84 36 64 128 256), losses := [] }

theorem u25130 : Upper (D 6) (R 6) [34,192,288,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25131 : Route 9 := (fun mask => (mask,id))

def c25131 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25131 : Upper (D 6) (R 6) [34,192,288,17,68,8] 13 := by
  apply FastRouting.sound _ _ [34,192,288,17,68,8] 13 (by decide) (choices 1) [1,2,4] r25131 c25131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7808
  · exact u7809
  · exact u7810

def b25132 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 194 292 25 88 33 70 134 262), lower := (rows 35 194 292 25 88 33 64 128 256), losses := [] }

theorem u25132 : Upper (D 6) (R 6) [34,192,288,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25133 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 292 25 88 34 69 133 261), lower := (rows 35 194 292 25 88 34 64 128 256), losses := [] }

theorem u25133 : Upper (D 6) (R 6) [34,192,288,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25134 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 25 88 36 71 135 263), lower := (rows 35 194 292 25 88 36 64 128 256), losses := [] }

theorem u25134 : Upper (D 6) (R 6) [34,192,288,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25135 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 292 26 28 33 69 197 325), lower := (rows 35 194 292 26 28 33 64 128 256), losses := [] }

theorem u25135 : Upper (D 6) (R 6) [34,192,288,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25136 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 26 28 36 65 193 321), lower := (rows 35 194 292 26 28 36 64 128 256), losses := [] }

theorem u25136 : Upper (D 6) (R 6) [34,192,288,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25137 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 292 26 28 96 69 133 261), lower := (rows 35 194 292 26 28 96 64 128 256), losses := [] }

theorem u25137 : Upper (D 6) (R 6) [34,192,288,18,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25138 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 194 292 26 81 33 76 140 268), lower := (rows 35 194 292 26 81 33 64 128 256), losses := [] }

theorem u25138 : Upper (D 6) (R 6) [34,192,288,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25139 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 26 81 36 77 141 269), lower := (rows 35 194 292 26 81 36 64 128 256), losses := [] }

theorem u25139 : Upper (D 6) (R 6) [34,192,288,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25139
end Delivery.IrregularNine14.P06
