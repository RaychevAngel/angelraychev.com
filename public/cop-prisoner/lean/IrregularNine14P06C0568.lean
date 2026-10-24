import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0292
import IrregularNine14P06C0293

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34080 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 84 73 19 292 356 420 292), lower := (rows 11 162 84 73 19 32 64 128 256), losses := [] }

theorem u34080 : Upper (D 6) (R 6) [10,160,80,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34081 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 20, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 84 73 21 294 358 422 294), lower := (rows 11 162 84 73 21 32 64 128 256), losses := [] }

theorem u34081 : Upper (D 6) (R 6) [10,160,80,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34082 : PairBound 9 := { available := 293, camps := [], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 162 84 73 22 293 357 421 293), lower := (rows 11 162 84 73 22 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 32 64 128 256), good := (rows 30 162 84 92 22 32 64 128 256) },{ target := 2, region := (rows 17 2 0 12 16 32 64 128 256), good := (rows 11 162 89 73 27 32 64 128 256) }] }

theorem u34082 : Upper (D 6) (R 6) [10,160,80,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34083 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 454, targets := 1 },{ cop := 2, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 84 73 49 294 326 390 262), lower := (rows 11 162 84 73 49 32 64 128 256), losses := [] }

theorem u34083 : Upper (D 6) (R 6) [10,160,80,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34084 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 84 73 50 293 325 389 261), lower := (rows 11 162 84 73 50 32 64 128 256), losses := [] }

theorem u34084 : Upper (D 6) (R 6) [10,160,80,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34085 : Route 9 := (fun mask => (mask,id))

def c34085 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34085 : Upper (D 6) (R 6) [10,160,80,65,36] 13 := by
  apply FastRouting.sound _ _ [10,160,80,65,36] 13 (by decide) (choices 1) [1,2,4,256] r34085 c34085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17521
  · exact u17522
  · exact u17523
  · exact u17524

def b34086 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 2, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 84 73 273 38 102 166 294), lower := (rows 11 162 84 73 273 32 64 128 256), losses := [] }

theorem u34086 : Upper (D 6) (R 6) [10,160,80,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34087 : Route 9 := (fun mask => (mask,id))

def c34087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34087 : Upper (D 6) (R 6) [10,160,80,65,258] 13 := by
  apply FastRouting.sound _ _ [10,160,80,65,258] 13 (by decide) (choices 1) [1,4] r34087 c34087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17525
  · exact u17526

def r34088 : Route 9 := (fun mask => (mask,id))

def c34088 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34088 : Upper (D 6) (R 6) [10,160,80,65,260] 13 := by
  apply FastRouting.sound _ _ [10,160,80,65,260] 13 (by decide) (choices 1) [1,2,4] r34088 c34088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17527
  · exact u17528
  · exact u17529

def r34089 : Route 9 := (fun mask => (mask,id))

def c34089 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34089 : Upper (D 6) (R 6) [10,160,80,65,288] 13 := by
  apply FastRouting.sound _ _ [10,160,80,65,288] 13 (by decide) (choices 1) [1,2,4] r34089 c34089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17530
  · exact u17531
  · exact u17532

def b34090 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 84 104 19 293 325 389 261), lower := (rows 11 162 84 104 19 32 64 128 256), losses := [] }

theorem u34090 : Upper (D 6) (R 6) [10,160,80,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34091 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 162 84 104 21 295 327 391 263), lower := (rows 11 162 84 104 21 32 64 128 256), losses := [] }

theorem u34091 : Upper (D 6) (R 6) [10,160,80,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34092 : Route 9 := (fun mask => (mask,id))

def c34092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34092 : Upper (D 6) (R 6) [10,160,80,96,6] 13 := by
  apply FastRouting.sound _ _ [10,160,80,96,6] 13 (by decide) (choices 1) [1,4,256] r34092 c34092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17533
  · exact u17534
  · exact u17535

def r34093 : Route 9 := (fun mask => (mask,id))

def c34093 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34093 : Upper (D 6) (R 6) [10,160,80,96,257] 13 := by
  apply FastRouting.sound _ _ [10,160,80,96,257] 13 (by decide) (choices 1) [1,2,4] r34093 c34093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17536
  · exact u17537
  · exact u17538

def r34094 : Route 9 := (fun mask => (mask,id))

def c34094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34094 : Upper (D 6) (R 6) [10,160,80,96,258] 13 := by
  apply FastRouting.sound _ _ [10,160,80,96,258] 13 (by decide) (choices 1) [1,4] r34094 c34094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17539
  · exact u17540

def r34095 : Route 9 := (fun mask => (mask,id))

def c34095 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34095 : Upper (D 6) (R 6) [10,160,80,96,260] 13 := by
  apply FastRouting.sound _ _ [10,160,80,96,260] 13 (by decide) (choices 1) [1,2,4] r34095 c34095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17541
  · exact u17542
  · exact u17543

def b34096 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 84 265 19 100 100 228 356), lower := (rows 11 162 84 265 19 32 64 128 256), losses := [] }

theorem u34096 : Upper (D 6) (R 6) [10,160,80,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34097 : Route 9 := (fun mask => (mask,id))

def c34097 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34097 : Upper (D 6) (R 6) [10,160,80,257,5] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257,5] 13 (by decide) (choices 1) [2,4,64] r34097 c34097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17544
  · exact u17545
  · exact u17546

def r34098 : Route 9 := (fun mask => (mask,id))

def c34098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34098 : Upper (D 6) (R 6) [10,160,80,257,6] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257,6] 13 (by decide) (choices 1) [1,4,64] r34098 c34098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17547
  · exact u17548
  · exact u17549

def r34099 : Route 9 := (fun mask => (mask,id))

def c34099 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34099 : Upper (D 6) (R 6) [10,160,80,257,33] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257,33] 13 (by decide) (choices 1) [2,4,64] r34099 c34099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17550
  · exact u17551
  · exact u17552

def b34100 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 84 265 50 101 69 197 325), lower := (rows 11 162 84 265 50 32 64 128 256), losses := [] }

theorem u34100 : Upper (D 6) (R 6) [10,160,80,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34101 : Route 9 := (fun mask => (mask,id))

def c34101 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34101 : Upper (D 6) (R 6) [10,160,80,257,36] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257,36] 13 (by decide) (choices 1) [1,2,4,64] r34101 c34101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17553
  · exact u17554
  · exact u17555
  · exact u17556

def b34102 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 265 81 38 102 166 294), lower := (rows 11 162 84 265 81 32 64 128 256), losses := [] }

theorem u34102 : Upper (D 6) (R 6) [10,160,80,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34103 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 265 82 37 101 165 293), lower := (rows 11 162 84 265 82 32 64 128 256), losses := [] }

theorem u34103 : Upper (D 6) (R 6) [10,160,80,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34104 : PairBound 9 := { available := 39, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 84 265 84 39 103 167 295), lower := (rows 11 162 84 265 84 32 64 128 256), losses := [] }

theorem u34104 : Upper (D 6) (R 6) [10,160,80,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34105 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 265 112 39 71 135 263), lower := (rows 11 162 84 265 112 32 64 128 256), losses := [] }

theorem u34105 : Upper (D 6) (R 6) [10,160,80,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34106 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 84 268 19 101 101 229 357), lower := (rows 11 162 84 268 19 32 64 128 256), losses := [] }

theorem u34106 : Upper (D 6) (R 6) [10,160,80,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34107 : Route 9 := (fun mask => (mask,id))

def c34107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34107 : Upper (D 6) (R 6) [10,160,80,260,5] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,5] 13 (by decide) (choices 1) [1,2,64] r34107 c34107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17557
  · exact u17558
  · exact u17559

def r34108 : Route 9 := (fun mask => (mask,id))

def c34108 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34108 : Upper (D 6) (R 6) [10,160,80,260,6] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,6] 13 (by decide) (choices 1) [1,64] r34108 c34108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17560
  · exact u17561

def r34109 : Route 9 := (fun mask => (mask,id))

def c34109 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34109 : Upper (D 6) (R 6) [10,160,80,260,33] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,33] 13 (by decide) (choices 1) [1,2,4,64] r34109 c34109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17562
  · exact u17563
  · exact u17564
  · exact u17565

def b34110 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 84 268 50 101 69 197 325), lower := (rows 11 162 84 268 50 32 64 128 256), losses := [] }

theorem u34110 : Upper (D 6) (R 6) [10,160,80,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34111 : Route 9 := (fun mask => (mask,id))

def c34111 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34111 : Upper (D 6) (R 6) [10,160,80,260,36] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,36] 13 (by decide) (choices 1) [1,2,64] r34111 c34111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17566
  · exact u17567
  · exact u17568

def b34112 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 268 81 39 103 167 295), lower := (rows 11 162 84 268 81 32 64 128 256), losses := [] }

theorem u34112 : Upper (D 6) (R 6) [10,160,80,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34113 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 268 82 37 101 165 293), lower := (rows 11 162 84 268 82 32 64 128 256), losses := [] }

theorem u34113 : Upper (D 6) (R 6) [10,160,80,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34114 : PairBound 9 := { available := 35, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 84 268 84 35 99 163 291), lower := (rows 11 162 84 268 84 32 64 128 256), losses := [] }

theorem u34114 : Upper (D 6) (R 6) [10,160,80,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34115 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 268 112 39 71 135 263), lower := (rows 11 162 84 268 112 32 64 128 256), losses := [] }

theorem u34115 : Upper (D 6) (R 6) [10,160,80,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34116 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 84 296 19 101 69 197 325), lower := (rows 11 162 84 296 19 32 64 128 256), losses := [] }

theorem u34116 : Upper (D 6) (R 6) [10,160,80,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34117 : Route 9 := (fun mask => (mask,id))

def c34117 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34117 : Upper (D 6) (R 6) [10,160,80,288,5] 13 := by
  apply FastRouting.sound _ _ [10,160,80,288,5] 13 (by decide) (choices 1) [1,2,4,64] r34117 c34117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17569
  · exact u17570
  · exact u17571
  · exact u17572

def r34118 : Route 9 := (fun mask => (mask,id))

def c34118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34118 : Upper (D 6) (R 6) [10,160,80,288,6] 13 := by
  apply FastRouting.sound _ _ [10,160,80,288,6] 13 (by decide) (choices 1) [1,4,64] r34118 c34118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17573
  · exact u17574
  · exact u17575

def b34119 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 296 81 39 71 135 263), lower := (rows 11 162 84 296 81 32 64 128 256), losses := [] }

theorem u34119 : Upper (D 6) (R 6) [10,160,80,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34120 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 296 82 37 69 133 261), lower := (rows 11 162 84 296 82 32 64 128 256), losses := [] }

theorem u34120 : Upper (D 6) (R 6) [10,160,80,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34121 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 84 296 84 39 71 135 263), lower := (rows 11 162 84 296 84 32 64 128 256), losses := [] }

theorem u34121 : Upper (D 6) (R 6) [10,160,80,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34122 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 84 328 19 37 101 165 293), lower := (rows 11 162 84 328 19 32 64 128 256), losses := [] }

theorem u34122 : Upper (D 6) (R 6) [10,160,80,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34123 : Route 9 := (fun mask => (mask,id))

def c34123 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34123 : Upper (D 6) (R 6) [10,160,80,320,5] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,5] 13 (by decide) (choices 1) [1,2,4] r34123 c34123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17576
  · exact u17577
  · exact u17578

def r34124 : Route 9 := (fun mask => (mask,id))

def c34124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34124 : Upper (D 6) (R 6) [10,160,80,320,6] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,6] 13 (by decide) (choices 1) [1,4] r34124 c34124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17579
  · exact u17580

def r34125 : Route 9 := (fun mask => (mask,id))

def c34125 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34125 : Upper (D 6) (R 6) [10,160,80,320,33] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,33] 13 (by decide) (choices 1) [1,2,4] r34125 c34125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17581
  · exact u17582
  · exact u17583

def b34126 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 84 328 50 37 69 133 261), lower := (rows 11 162 84 328 50 32 64 128 256), losses := [] }

theorem u34126 : Upper (D 6) (R 6) [10,160,80,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34127 : Route 9 := (fun mask => (mask,id))

def c34127 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34127 : Upper (D 6) (R 6) [10,160,80,320,36] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,36] 13 (by decide) (choices 1) [1,2,4] r34127 c34127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17584
  · exact u17585
  · exact u17586

def b34128 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 100 13 19 372 340 468 340), lower := (rows 11 162 100 13 19 32 64 128 256), losses := [] }

theorem u34128 : Upper (D 6) (R 6) [10,160,96,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34129 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 100 13 21 370 338 466 338), lower := (rows 11 162 100 13 21 32 64 128 256), losses := [] }

theorem u34129 : Upper (D 6) (R 6) [10,160,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34130 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 9, targets := 32 },{ cop := 4, region := 9, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 100 13 22 369 337 465 337), lower := (rows 11 162 100 13 22 32 64 128 256), losses := [] }

theorem u34130 : Upper (D 6) (R 6) [10,160,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34131 : Route 9 := (fun mask => (mask,id))

def c34131 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34131 : Upper (D 6) (R 6) [10,160,96,5,65] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,65] 13 (by decide) (choices 1) [2,4,16,256] r34131 c34131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17587
  · exact u17588
  · exact u17589
  · exact u17590

def r34132 : Route 9 := (fun mask => (mask,id))

def c34132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34132 : Upper (D 6) (R 6) [10,160,96,5,66] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,66] 13 (by decide) (choices 1) [1,4,16,256] r34132 c34132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17591
  · exact u17592
  · exact u17593
  · exact u17594

def b34133 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 100 13 84 307 339 403 275), lower := (rows 11 162 100 13 84 32 64 128 256), losses := [] }

theorem u34133 : Upper (D 6) (R 6) [10,160,96,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34134 : Route 9 := (fun mask => (mask,id))

def c34134 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34134 : Upper (D 6) (R 6) [10,160,96,5,257] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,257] 13 (by decide) (choices 1) [2,4,16,64] r34134 c34134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17595
  · exact u17596
  · exact u17597
  · exact u17598

def r34135 : Route 9 := (fun mask => (mask,id))

def c34135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34135 : Upper (D 6) (R 6) [10,160,96,5,258] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,258] 13 (by decide) (choices 1) [1,4,16,64] r34135 c34135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17599
  · exact u17600
  · exact u17601
  · exact u17602

def r34136 : Route 9 := (fun mask => (mask,id))

def c34136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34136 : Upper (D 6) (R 6) [10,160,96,5,260] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,260] 13 (by decide) (choices 1) [1,2,16,64] r34136 c34136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17603
  · exact u17604
  · exact u17605
  · exact u17606

def r34137 : Route 9 := (fun mask => (mask,id))

def c34137 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34137 : Upper (D 6) (R 6) [10,160,96,5,320] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,320] 13 (by decide) (choices 1) [1,2,4,16] r34137 c34137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17607
  · exact u17608
  · exact u17609
  · exact u17610

def b34138 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 25 19 356 324 452 324), lower := (rows 11 162 100 25 19 32 64 128 256), losses := [] }

theorem u34138 : Upper (D 6) (R 6) [10,160,96,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34139 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 100 25 21 358 326 454 326), lower := (rows 11 162 100 25 21 32 64 128 256), losses := [] }

theorem u34139 : Upper (D 6) (R 6) [10,160,96,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34139
end Delivery.IrregularNine14.P06
