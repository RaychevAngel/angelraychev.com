import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0475
import IrregularNine14P07C0476
import IrregularNine14P07C0477

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40080 : Route 9 := (fun mask => (mask,id))

def c40080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40080 : Upper (D 7) (R 7) [96,257,10,48,130] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,130] 13 (by decide) (choices 1) [1,4,64,128] r40080 c40080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28514
  · exact u28515
  · exact u28516
  · exact u28517

def r40081 : Route 9 := (fun mask => (mask,id))

def c40081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40081 : Upper (D 7) (R 7) [96,257,10,48,132] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,132] 13 (by decide) (choices 1) [1,2,64,128] r40081 c40081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28518
  · exact u28519
  · exact u28520
  · exact u28521

def r40082 : Route 9 := (fun mask => (mask,id))

def c40082 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40082 : Upper (D 7) (R 7) [96,257,10,48,192] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,192] 13 (by decide) (choices 1) [1,2,4,128] r40082 c40082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28522
  · exact u28523
  · exact u28524
  · exact u28525

def b40083 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 14 104 145 182 214 150 406), lower := (rows 97 259 14 104 145 32 64 128 256), losses := [] }

theorem u40083 : Upper (D 7) (R 7) [96,257,10,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40084 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 14 104 146 181 213 149 405), lower := (rows 97 259 14 104 146 32 64 128 256), losses := [] }

theorem u40084 : Upper (D 7) (R 7) [96,257,10,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40085 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 14 104 148 179 211 147 403), lower := (rows 97 259 14 104 148 32 64 128 256), losses := [] }

theorem u40085 : Upper (D 7) (R 7) [96,257,10,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40086 : Route 9 := (fun mask => (mask,id))

def c40086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40086 : Upper (D 7) (R 7) [96,257,10,129,34] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,34] 13 (by decide) (choices 1) [4,16,64,128] r40086 c40086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28526
  · exact u28527
  · exact u28528
  · exact u28529

def r40087 : Route 9 := (fun mask => (mask,id))

def c40087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40087 : Upper (D 7) (R 7) [96,257,10,129,36] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,36] 13 (by decide) (choices 1) [2,16,64,128] r40087 c40087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28530
  · exact u28531
  · exact u28532
  · exact u28533

def b40088 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 259 14 137 112 182 214 150 406), lower := (rows 97 259 14 137 112 32 64 128 256), losses := [] }

theorem u40088 : Upper (D 7) (R 7) [96,257,10,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40089 : Route 9 := (fun mask => (mask,id))

def c40089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40089 : Upper (D 7) (R 7) [96,257,10,129,130] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,130] 13 (by decide) (choices 1) [4,16,64] r40089 c40089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28534
  · exact u28535
  · exact u28536

def r40090 : Route 9 := (fun mask => (mask,id))

def c40090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40090 : Upper (D 7) (R 7) [96,257,10,129,132] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,132] 13 (by decide) (choices 1) [2,16,64] r40090 c40090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28537
  · exact u28538
  · exact u28539

def r40091 : Route 9 := (fun mask => (mask,id))

def c40091 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40091 : Upper (D 7) (R 7) [96,257,10,129,160] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,160] 13 (by decide) (choices 1) [2,4,16,64] r40091 c40091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28540
  · exact u28541
  · exact u28542
  · exact u28543

def b40092 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 138 52 241 209 209 465), lower := (rows 97 259 14 138 52 32 64 128 256), losses := [] }

theorem u40092 : Upper (D 7) (R 7) [96,257,10,130,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40093 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 138 145 116 116 244 372), lower := (rows 97 259 14 138 145 32 64 128 256), losses := [] }

theorem u40093 : Upper (D 7) (R 7) [96,257,10,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40094 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 259 14 138 148 113 113 241 369), lower := (rows 97 259 14 138 148 32 64 128 256), losses := [] }

theorem u40094 : Upper (D 7) (R 7) [96,257,10,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40095 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 138 176 117 85 213 341), lower := (rows 97 259 14 138 176 32 64 128 256), losses := [] }

theorem u40095 : Upper (D 7) (R 7) [96,257,10,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40096 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 259 14 140 49 242 210 210 466), lower := (rows 97 259 14 140 49 32 64 128 256), losses := [] }

theorem u40096 : Upper (D 7) (R 7) [96,257,10,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40097 : Route 9 := (fun mask => (mask,id))

def c40097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40097 : Upper (D 7) (R 7) [96,257,10,132,34] 13 := by
  apply FastRouting.sound _ _ [96,257,10,132,34] 13 (by decide) (choices 1) [1,16,64,128] r40097 c40097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28544
  · exact u28545
  · exact u28546
  · exact u28547

def b40098 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 259 14 140 112 179 211 147 403), lower := (rows 97 259 14 140 112 32 64 128 256), losses := [] }

theorem u40098 : Upper (D 7) (R 7) [96,257,10,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40099 : Route 9 := (fun mask => (mask,id))

def c40099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40099 : Upper (D 7) (R 7) [96,257,10,132,129] 13 := by
  apply FastRouting.sound _ _ [96,257,10,132,129] 13 (by decide) (choices 1) [2,16,64] r40099 c40099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28548
  · exact u28549
  · exact u28550

def b40100 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 259 14 140 146 113 113 241 369), lower := (rows 97 259 14 140 146 32 64 128 256), losses := [] }

theorem u40100 : Upper (D 7) (R 7) [96,257,10,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40101 : Route 9 := (fun mask => (mask,id))

def c40101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40101 : Upper (D 7) (R 7) [96,257,10,132,160] 13 := by
  apply FastRouting.sound _ _ [96,257,10,132,160] 13 (by decide) (choices 1) [1,2,16,64] r40101 c40101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28551
  · exact u28552
  · exact u28553
  · exact u28554

def b40102 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 259 14 152 49 230 198 198 454), lower := (rows 97 259 14 152 49 32 64 128 256), losses := [] }

theorem u40102 : Upper (D 7) (R 7) [96,257,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40103 : Route 9 := (fun mask => (mask,id))

def c40103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40103 : Upper (D 7) (R 7) [96,257,10,144,34] 13 := by
  apply FastRouting.sound _ _ [96,257,10,144,34] 13 (by decide) (choices 1) [1,4,64,128] r40103 c40103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28555
  · exact u28556
  · exact u28557
  · exact u28558

def r40104 : Route 9 := (fun mask => (mask,id))

def c40104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40104 : Upper (D 7) (R 7) [96,257,10,144,36] 13 := by
  apply FastRouting.sound _ _ [96,257,10,144,36] 13 (by decide) (choices 1) [1,2,64,128] r40104 c40104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28559
  · exact u28560
  · exact u28561
  · exact u28562

def b40105 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 259 14 152 112 167 199 135 391), lower := (rows 97 259 14 152 112 32 64 128 256), losses := [] }

theorem u40105 : Upper (D 7) (R 7) [96,257,10,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40106 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 14 152 145 102 102 230 358), lower := (rows 97 259 14 152 145 32 64 128 256), losses := [] }

theorem u40106 : Upper (D 7) (R 7) [96,257,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40107 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 259 14 152 146 101 101 229 357), lower := (rows 97 259 14 152 146 32 64 128 256), losses := [] }

theorem u40107 : Upper (D 7) (R 7) [96,257,10,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40108 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 14 152 148 99 99 227 355), lower := (rows 97 259 14 152 148 32 64 128 256), losses := [] }

theorem u40108 : Upper (D 7) (R 7) [96,257,10,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40109 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 14 152 176 103 71 199 327), lower := (rows 97 259 14 152 176 32 64 128 256), losses := [] }

theorem u40109 : Upper (D 7) (R 7) [96,257,10,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40110 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 259 14 168 81 182 214 150 406), lower := (rows 97 259 14 168 81 32 64 128 256), losses := [] }

theorem u40110 : Upper (D 7) (R 7) [96,257,10,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40111 : Route 9 := (fun mask => (mask,id))

def c40111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40111 : Upper (D 7) (R 7) [96,257,10,160,66] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,66] 13 (by decide) (choices 1) [1,4,16,128] r40111 c40111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28563
  · exact u28564
  · exact u28565
  · exact u28566

def r40112 : Route 9 := (fun mask => (mask,id))

def c40112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40112 : Upper (D 7) (R 7) [96,257,10,160,68] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,68] 13 (by decide) (choices 1) [1,2,16,128] r40112 c40112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28567
  · exact u28568
  · exact u28569
  · exact u28570

def r40113 : Route 9 := (fun mask => (mask,id))

def c40113 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40113 : Upper (D 7) (R 7) [96,257,10,160,129] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,129] 13 (by decide) (choices 1) [2,4,16,64] r40113 c40113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28571
  · exact u28572
  · exact u28573
  · exact u28574

def r40114 : Route 9 := (fun mask => (mask,id))

def c40114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40114 : Upper (D 7) (R 7) [96,257,10,160,130] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,130] 13 (by decide) (choices 1) [1,4,16,64] r40114 c40114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28575
  · exact u28576
  · exact u28577
  · exact u28578

def r40115 : Route 9 := (fun mask => (mask,id))

def c40115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40115 : Upper (D 7) (R 7) [96,257,10,160,132] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,132] 13 (by decide) (choices 1) [1,2,16,64] r40115 c40115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28579
  · exact u28580
  · exact u28581
  · exact u28582

def r40116 : Route 9 := (fun mask => (mask,id))

def c40116 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40116 : Upper (D 7) (R 7) [96,257,10,160,192] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,192] 13 (by decide) (choices 1) [1,2,4,16] r40116 c40116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28583
  · exact u28584
  · exact u28585
  · exact u28586

def b40117 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 28 41 82 166 198 134 390), lower := (rows 97 259 28 41 82 32 64 128 256), losses := [] }

theorem u40117 : Upper (D 7) (R 7) [96,257,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40118 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 28 41 84 162 194 130 386), lower := (rows 97 259 28 41 84 32 64 128 256), losses := [] }

theorem u40118 : Upper (D 7) (R 7) [96,257,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40119 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 28 41 146 230 198 198 454), lower := (rows 97 259 28 41 146 32 64 128 256), losses := [] }

theorem u40119 : Upper (D 7) (R 7) [96,257,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40120 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 28 41 148 226 194 194 450), lower := (rows 97 259 28 41 148 32 64 128 256), losses := [] }

theorem u40120 : Upper (D 7) (R 7) [96,257,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40121 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 28 41 208 166 198 134 390), lower := (rows 97 259 28 41 208 32 64 128 256), losses := [] }

theorem u40121 : Upper (D 7) (R 7) [96,257,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40122 : Route 9 := (fun mask => (mask,id))

def c40122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40122 : Upper (D 7) (R 7) [96,257,24,34,66] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,66] 13 (by decide) (choices 1) [1,4,128] r40122 c40122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28587
  · exact u28588
  · exact u28589

def b40123 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(1,6),(2,5),(3,6)], upper := (rows 97 259 28 42 84 163 195 131 387), lower := (rows 97 259 28 42 84 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 12 8 24 0 67 131 259), good := (rows 451 451 28 478 84 0 64 128 256) }] }

theorem u40123 : Upper (D 7) (R 7) [96,257,24,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40124 : Route 9 := (fun mask => (mask,id))

def c40124 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40124 : Upper (D 7) (R 7) [96,257,24,34,129] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,129] 13 (by decide) (choices 1) [2,4,64,128] r40124 c40124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28590
  · exact u28591
  · exact u28592
  · exact u28593

def r40125 : Route 9 := (fun mask => (mask,id))

def c40125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40125 : Upper (D 7) (R 7) [96,257,24,34,130] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,130] 13 (by decide) (choices 1) [1,4,64,128] r40125 c40125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28594
  · exact u28595
  · exact u28596
  · exact u28597

def r40126 : Route 9 := (fun mask => (mask,id))

def c40126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40126 : Upper (D 7) (R 7) [96,257,24,34,132] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,132] 13 (by decide) (choices 1) [1,2,64,128] r40126 c40126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28598
  · exact u28599
  · exact u28600
  · exact u28601

def r40127 : Route 9 := (fun mask => (mask,id))

def c40127 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40127 : Upper (D 7) (R 7) [96,257,24,34,192] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,192] 13 (by decide) (choices 1) [1,2,4,128] r40127 c40127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28602
  · exact u28603
  · exact u28604
  · exact u28605

def r40128 : Route 9 := (fun mask => (mask,id))

def c40128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40128 : Upper (D 7) (R 7) [96,257,24,36,129] 13 := by
  apply FastRouting.sound _ _ [96,257,24,36,129] 13 (by decide) (choices 1) [2,64,128] r40128 c40128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28606
  · exact u28607
  · exact u28608

def r40129 : Route 9 := (fun mask => (mask,id))

def c40129 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40129 : Upper (D 7) (R 7) [96,257,24,36,130] 13 := by
  apply FastRouting.sound _ _ [96,257,24,36,130] 13 (by decide) (choices 1) [1,2,64,128] r40129 c40129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28609
  · exact u28610
  · exact u28611
  · exact u28612

def r40130 : Route 9 := (fun mask => (mask,id))

def c40130 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40130 : Upper (D 7) (R 7) [96,257,24,36,192] 13 := by
  apply FastRouting.sound _ _ [96,257,24,36,192] 13 (by decide) (choices 1) [1,2,128] r40130 c40130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28613
  · exact u28614
  · exact u28615

def b40131 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 28 104 145 166 198 134 390), lower := (rows 97 259 28 104 145 32 64 128 256), losses := [] }

theorem u40131 : Upper (D 7) (R 7) [96,257,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40132 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 28 104 146 167 199 135 391), lower := (rows 97 259 28 104 146 32 64 128 256), losses := [] }

theorem u40132 : Upper (D 7) (R 7) [96,257,24,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40133 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 28 104 148 163 195 131 387), lower := (rows 97 259 28 104 148 32 64 128 256), losses := [] }

theorem u40133 : Upper (D 7) (R 7) [96,257,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40134 : Route 9 := (fun mask => (mask,id))

def c40134 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40134 : Upper (D 7) (R 7) [96,257,24,129,130] 13 := by
  apply FastRouting.sound _ _ [96,257,24,129,130] 13 (by decide) (choices 1) [2,4,64] r40134 c40134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28616
  · exact u28617
  · exact u28618

def b40135 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 20, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 259 28 137 148 98 98 226 354), lower := (rows 97 259 28 137 148 32 64 128 256), losses := [] }

theorem u40135 : Upper (D 7) (R 7) [96,257,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40136 : Route 9 := (fun mask => (mask,id))

def c40136 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40136 : Upper (D 7) (R 7) [96,257,24,129,160] 13 := by
  apply FastRouting.sound _ _ [96,257,24,129,160] 13 (by decide) (choices 1) [2,4,64] r40136 c40136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28619
  · exact u28620
  · exact u28621

def b40137 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 259 28 138 146 101 101 229 357), lower := (rows 97 259 28 138 146 32 64 128 256), losses := [] }

theorem u40137 : Upper (D 7) (R 7) [96,257,24,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40138 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 20, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 259 28 138 148 99 99 227 355), lower := (rows 97 259 28 138 148 32 64 128 256), losses := [] }

theorem u40138 : Upper (D 7) (R 7) [96,257,24,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40139 : Route 9 := (fun mask => (mask,id))

def c40139 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40139 : Upper (D 7) (R 7) [96,257,24,130,160] 13 := by
  apply FastRouting.sound _ _ [96,257,24,130,160] 13 (by decide) (choices 1) [1,2,4,64] r40139 c40139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28622
  · exact u28623
  · exact u28624
  · exact u28625

#print axioms u40139
end Delivery.IrregularNine14.P07
