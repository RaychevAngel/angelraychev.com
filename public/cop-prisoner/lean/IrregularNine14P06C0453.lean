import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0142

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27180 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 261 26 56 96 70 134 262), lower := (rows 97 131 261 26 56 96 64 128 256), losses := [] }

theorem u27180 : Upper (D 6) (R 6) [96,129,257,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27181 : Route 9 := (fun mask => (mask,id))

def c27181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27181 : Upper (D 6) (R 6) [96,129,257,34,66,4] 13 := by
  apply FastRouting.sound _ _ [96,129,257,34,66,4] 13 (by decide) (choices 1) [4,8,16] r27181 c27181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8561
  · exact u8562
  · exact u8563

def b27182 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 261 42 82 40 84 148 276), lower := (rows 97 131 261 42 82 40 64 128 256), losses := [] }

theorem u27182 : Upper (D 6) (R 6) [96,129,257,34,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27182 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27183 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 261 42 82 48 76 140 268), lower := (rows 97 131 261 42 82 48 64 128 256), losses := [] }

theorem u27183 : Upper (D 6) (R 6) [96,129,257,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27183 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27184 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 131 261 42 84 34 92 156 284), lower := (rows 97 131 261 42 84 34 64 128 256), losses := [] }

theorem u27184 : Upper (D 6) (R 6) [96,129,257,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27185 : Route 9 := (fun mask => (mask,id))

def c27185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27185 : Upper (D 6) (R 6) [96,129,257,34,68,4] 13 := by
  apply FastRouting.sound _ _ [96,129,257,34,68,4] 13 (by decide) (choices 1) [2,8,16] r27185 c27185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8564
  · exact u8565
  · exact u8566

def b27186 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 261 42 84 40 86 150 278), lower := (rows 97 131 261 42 84 40 64 128 256), losses := [] }

theorem u27186 : Upper (D 6) (R 6) [96,129,257,34,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27186 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27187 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 261 42 84 48 78 142 270), lower := (rows 97 131 261 42 84 48 64 128 256), losses := [] }

theorem u27187 : Upper (D 6) (R 6) [96,129,257,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27187 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27188 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 131 261 42 88 34 84 148 276), lower := (rows 97 131 261 42 88 34 64 128 256), losses := [] }

theorem u27188 : Upper (D 6) (R 6) [96,129,257,34,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27189 : Route 9 := (fun mask => (mask,id))

def c27189 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27189 : Upper (D 6) (R 6) [96,129,257,34,72,4] 13 := by
  apply FastRouting.sound _ _ [96,129,257,34,72,4] 13 (by decide) (choices 1) [2,4,16] r27189 c27189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8567
  · exact u8568
  · exact u8569

def b27190 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 261 42 88 48 70 134 262), lower := (rows 97 131 261 42 88 48 64 128 256), losses := [] }

theorem u27190 : Upper (D 6) (R 6) [96,129,257,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27190 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27191 : Route 9 := (fun mask => (mask,id))

def c27191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27191 : Upper (D 6) (R 6) [96,129,258,5,10,4] 13 := by
  apply FastRouting.sound _ _ [96,129,258,5,10,4] 13 (by decide) (choices 1) [16,32] r27191 c27191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8570
  · exact u8571

theorem m27192_4 : Upper (D 6) (R 6) [96,129,258,5,10,16,4] 13 :=
  permutation_upper _ _ _ [96,129,258,5,10,4,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8570

def r27192 : Route 9 := (fun mask => (mask,id))

def c27192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27192 : Upper (D 6) (R 6) [96,129,258,5,10,16] 13 := by
  apply FastRouting.sound _ _ [96,129,258,5,10,16] 13 (by decide) (choices 1) [4,32] r27192 c27192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m27192_4
  · exact u8572

def b27193 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 13 26 96 116 180 308), lower := (rows 97 131 262 13 26 96 64 128 256), losses := [] }

theorem u27193 : Upper (D 6) (R 6) [96,129,258,5,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27194 : Route 9 := (fun mask => (mask,id))

def c27194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27194 : Upper (D 6) (R 6) [96,129,258,5,34,4] 13 := by
  apply FastRouting.sound _ _ [96,129,258,5,34,4] 13 (by decide) (choices 1) [8,16] r27194 c27194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8573
  · exact u8574

def b27195 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 324, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 97 131 262 13 50 40 84 212 340), lower := (rows 97 131 262 13 50 40 64 128 256), losses := [] }

theorem u27195 : Upper (D 6) (R 6) [96,129,258,5,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27195 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27196 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 262 13 50 48 76 204 332), lower := (rows 97 131 262 13 50 48 64 128 256), losses := [] }

theorem u27196 : Upper (D 6) (R 6) [96,129,258,5,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27196 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27197 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 13 50 96 92 156 284), lower := (rows 97 131 262 13 50 96 64 128 256), losses := [] }

theorem u27197 : Upper (D 6) (R 6) [96,129,258,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27198 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 4, region := 73, targets := 2 }], pairs := [(0,1),(4,0),(4,6)], upper := (rows 97 131 262 13 52 34 88 216 344), lower := (rows 97 131 262 13 52 34 64 128 256), losses := [] }

theorem u27198 : Upper (D 6) (R 6) [96,129,258,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27199 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 97 131 262 13 52 40 82 210 338), lower := (rows 97 131 262 13 52 40 64 128 256), losses := [] }

theorem u27199 : Upper (D 6) (R 6) [96,129,258,5,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27199 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27200 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 262 13 52 48 74 202 330), lower := (rows 97 131 262 13 52 48 64 128 256), losses := [] }

theorem u27200 : Upper (D 6) (R 6) [96,129,258,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27200 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27201 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 13 52 96 90 154 282), lower := (rows 97 131 262 13 52 96 64 128 256), losses := [] }

theorem u27201 : Upper (D 6) (R 6) [96,129,258,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27202 : PairBound 9 := { available := 84, camps := [], pairs := [(4,0),(4,2),(4,6)], upper := (rows 97 131 262 13 56 34 84 212 340), lower := (rows 97 131 262 13 56 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 38 72 136 264), good := (rows 96 162 294 508 504 34 64 128 256) },{ target := 2, region := (rows 1 2 0 8 24 38 64 128 256), good := (rows 97 163 290 57 56 34 64 128 256) },{ target := 6, region := (rows 1 2 4 8 24 38 0 128 256), good := (rows 33 163 294 61 56 34 0 128 256) }] }

theorem u27202 : Upper (D 6) (R 6) [96,129,258,5,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27203 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 97 131 262 13 56 36 82 210 338), lower := (rows 97 131 262 13 56 36 64 128 256), losses := [] }

theorem u27203 : Upper (D 6) (R 6) [96,129,258,5,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27204 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 97 131 262 13 56 48 70 198 326), lower := (rows 97 131 262 13 56 48 64 128 256), losses := [] }

theorem u27204 : Upper (D 6) (R 6) [96,129,258,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27204 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27205 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 13 56 96 86 150 278), lower := (rows 97 131 262 13 56 96 64 128 256), losses := [] }

theorem u27205 : Upper (D 6) (R 6) [96,129,258,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27206 : Route 9 := (fun mask => (mask,id))

def c27206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27206 : Upper (D 6) (R 6) [96,129,258,17,12,2] 13 := by
  apply FastRouting.sound _ _ [96,129,258,17,12,2] 13 (by decide) (choices 1) [4,32] r27206 c27206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8575
  · exact u8576

def b27207 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 1, region := 356, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 97 131 262 25 28 36 98 226 354), lower := (rows 97 131 262 25 28 36 64 128 256), losses := [] }

theorem u27207 : Upper (D 6) (R 6) [96,129,258,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27208 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 25 28 96 102 166 294), lower := (rows 97 131 262 25 28 96 64 128 256), losses := [] }

theorem u27208 : Upper (D 6) (R 6) [96,129,258,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27209 : PairBound 9 := { available := 76, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,6)], upper := (rows 97 131 262 25 50 36 76 204 332), lower := (rows 97 131 262 25 50 36 64 128 256), losses := [] }

theorem u27209 : Upper (D 6) (R 6) [96,129,258,17,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27210 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 56, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 97 131 262 25 50 40 68 196 324), lower := (rows 97 131 262 25 50 40 64 128 256), losses := [] }

theorem u27210 : Upper (D 6) (R 6) [96,129,258,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27210 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27211 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 25 50 96 76 140 268), lower := (rows 97 131 262 25 50 96 64 128 256), losses := [] }

theorem u27211 : Upper (D 6) (R 6) [96,129,258,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27212 : PairBound 9 := { available := 76, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,6)], upper := (rows 97 131 262 25 52 34 76 204 332), lower := (rows 97 131 262 25 52 34 64 128 256), losses := [] }

theorem u27212 : Upper (D 6) (R 6) [96,129,258,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27213 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 97 131 262 25 52 36 74 202 330), lower := (rows 97 131 262 25 52 36 64 128 256), losses := [] }

theorem u27213 : Upper (D 6) (R 6) [96,129,258,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27214 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 262 25 52 40 70 198 326), lower := (rows 97 131 262 25 52 40 64 128 256), losses := [] }

theorem u27214 : Upper (D 6) (R 6) [96,129,258,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27214 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27215 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 25 52 96 78 142 270), lower := (rows 97 131 262 25 52 96 64 128 256), losses := [] }

theorem u27215 : Upper (D 6) (R 6) [96,129,258,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27216 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 324, targets := 33 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(2,0),(2,5)], upper := (rows 97 131 262 26 52 33 76 204 332), lower := (rows 97 131 262 26 52 33 64 128 256), losses := [] }

theorem u27216 : Upper (D 6) (R 6) [96,129,258,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27217 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 131 262 26 52 36 73 201 329), lower := (rows 97 131 262 26 52 36 64 128 256), losses := [] }

theorem u27217 : Upper (D 6) (R 6) [96,129,258,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27218 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6)], upper := (rows 97 131 262 26 52 40 69 197 325), lower := (rows 97 131 262 26 52 40 64 128 256), losses := [] }

theorem u27218 : Upper (D 6) (R 6) [96,129,258,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27218 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27219 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 26 52 96 77 141 269), lower := (rows 97 131 262 26 52 96 64 128 256), losses := [] }

theorem u27219 : Upper (D 6) (R 6) [96,129,258,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27220 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 131 262 28 50 33 76 204 332), lower := (rows 97 131 262 28 50 33 64 128 256), losses := [] }

theorem u27220 : Upper (D 6) (R 6) [96,129,258,20,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27221 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 131 262 28 50 36 73 201 329), lower := (rows 97 131 262 28 50 36 64 128 256), losses := [] }

theorem u27221 : Upper (D 6) (R 6) [96,129,258,20,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27222 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6)], upper := (rows 97 131 262 28 50 40 69 197 325), lower := (rows 97 131 262 28 50 40 64 128 256), losses := [] }

theorem u27222 : Upper (D 6) (R 6) [96,129,258,20,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27222 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27223 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 28 50 96 77 141 269), lower := (rows 97 131 262 28 50 96 64 128 256), losses := [] }

theorem u27223 : Upper (D 6) (R 6) [96,129,258,20,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27224 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 131 262 28 56 33 70 198 326), lower := (rows 97 131 262 28 56 33 64 128 256), losses := [] }

theorem u27224 : Upper (D 6) (R 6) [96,129,258,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27225 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 131 262 28 56 34 69 197 325), lower := (rows 97 131 262 28 56 34 64 128 256), losses := [] }

theorem u27225 : Upper (D 6) (R 6) [96,129,258,20,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27226 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 56, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 131 262 28 56 36 67 195 323), lower := (rows 97 131 262 28 56 36 64 128 256), losses := [] }

theorem u27226 : Upper (D 6) (R 6) [96,129,258,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27227 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 262 28 56 96 71 135 263), lower := (rows 97 131 262 28 56 96 64 128 256), losses := [] }

theorem u27227 : Upper (D 6) (R 6) [96,129,258,20,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27228 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 131 262 42 84 33 92 156 284), lower := (rows 97 131 262 42 84 33 64 128 256), losses := [] }

theorem u27228 : Upper (D 6) (R 6) [96,129,258,34,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27229 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 40, targets := 65 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(3,0),(3,6)], upper := (rows 97 131 262 42 84 36 89 153 281), lower := (rows 97 131 262 42 84 36 64 128 256), losses := [] }

theorem u27229 : Upper (D 6) (R 6) [96,129,258,34,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27230 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 262 42 84 40 85 149 277), lower := (rows 97 131 262 42 84 40 64 128 256), losses := [] }

theorem u27230 : Upper (D 6) (R 6) [96,129,258,34,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27230 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27231 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 262 42 84 48 77 141 269), lower := (rows 97 131 262 42 84 48 64 128 256), losses := [] }

theorem u27231 : Upper (D 6) (R 6) [96,129,258,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27231 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27232 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 131 262 42 88 33 84 148 276), lower := (rows 97 131 262 42 88 33 64 128 256), losses := [] }

theorem u27232 : Upper (D 6) (R 6) [96,129,258,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27233 : Route 9 := (fun mask => (mask,id))

def c27233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27233 : Upper (D 6) (R 6) [96,129,258,34,72,4] 13 := by
  apply FastRouting.sound _ _ [96,129,258,34,72,4] 13 (by decide) (choices 1) [1,4,16] r27233 c27233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8577
  · exact u8578
  · exact u8579

def b27234 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 262 42 88 48 69 133 261), lower := (rows 97 131 262 42 88 48 64 128 256), losses := [] }

theorem u27234 : Upper (D 6) (R 6) [96,129,258,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27234 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27235 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 41, targets := 2 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 131 262 44 84 33 90 154 282), lower := (rows 97 131 262 44 84 33 64 128 256), losses := [] }

theorem u27235 : Upper (D 6) (R 6) [96,129,258,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27236 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 40, targets := 65 },{ cop := 3, region := 81, targets := 2 }], pairs := [(0,1),(3,0),(3,6)], upper := (rows 97 131 262 44 84 34 89 153 281), lower := (rows 97 131 262 44 84 34 64 128 256), losses := [] }

theorem u27236 : Upper (D 6) (R 6) [96,129,258,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27237 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 262 44 84 40 83 147 275), lower := (rows 97 131 262 44 84 40 64 128 256), losses := [] }

theorem u27237 : Upper (D 6) (R 6) [96,129,258,36,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27237 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27238 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 262 44 84 48 75 139 267), lower := (rows 97 131 262 44 84 48 64 128 256), losses := [] }

theorem u27238 : Upper (D 6) (R 6) [96,129,258,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27238 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27239 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 131 262 44 88 33 86 150 278), lower := (rows 97 131 262 44 88 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 4 12 16 115 64 128 256), good := (rows 97 161 300 44 121 33 97 128 256) }] }

theorem u27239 : Upper (D 6) (R 6) [96,129,258,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27239
end Delivery.IrregularNine14.P06
