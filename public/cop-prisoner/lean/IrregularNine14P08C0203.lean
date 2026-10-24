import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0065
import IrregularNine14P08C0066

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12180 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 137 112 180 244 180 436), lower := (rows 67 290 13 137 112 32 64 128 256), losses := [] }

theorem u12180 : Upper (D 8) (R 8) [66,288,9,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12181 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 137 148 112 112 240 368), lower := (rows 67 290 13 137 148 32 64 128 256), losses := [] }

theorem u12181 : Upper (D 8) (R 8) [66,288,9,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12182 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 137 176 116 116 244 372), lower := (rows 67 290 13 137 176 32 64 128 256), losses := [] }

theorem u12182 : Upper (D 8) (R 8) [66,288,9,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12183 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 137 208 52 116 180 308), lower := (rows 67 290 13 137 208 32 64 128 256), losses := [] }

theorem u12183 : Upper (D 8) (R 8) [66,288,9,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12184 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 140 49 240 240 240 496), lower := (rows 67 290 13 140 49 32 64 128 256), losses := [] }

theorem u12184 : Upper (D 8) (R 8) [66,288,9,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12185 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 140 81 176 240 176 432), lower := (rows 67 290 13 140 81 32 64 128 256), losses := [] }

theorem u12185 : Upper (D 8) (R 8) [66,288,9,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12186 : Route 9 := (fun mask => (mask,id))

def c12186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12186 : Upper (D 8) (R 8) [66,288,9,132,96] 13 := by
  apply FastRouting.sound _ _ [66,288,9,132,96] 13 (by decide) (choices 1) [1,16,128] r12186 c12186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3925
  · exact u3926
  · exact u3927

def b12187 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 140 145 112 112 240 368), lower := (rows 67 290 13 140 145 32 64 128 256), losses := [] }

theorem u12187 : Upper (D 8) (R 8) [66,288,9,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12188 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 140 176 113 113 241 369), lower := (rows 67 290 13 140 176 32 64 128 256), losses := [] }

theorem u12188 : Upper (D 8) (R 8) [66,288,9,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12189 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 140 208 49 113 177 305), lower := (rows 67 290 13 140 208 32 64 128 256), losses := [] }

theorem u12189 : Upper (D 8) (R 8) [66,288,9,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12190 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 152 49 228 228 228 484), lower := (rows 67 290 13 152 49 32 64 128 256), losses := [] }

theorem u12190 : Upper (D 8) (R 8) [66,288,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12191 : Route 9 := (fun mask => (mask,id))

def c12191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12191 : Upper (D 8) (R 8) [66,288,9,144,36] 13 := by
  apply FastRouting.sound _ _ [66,288,9,144,36] 13 (by decide) (choices 1) [1,64,128] r12191 c12191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3928
  · exact u3929
  · exact u3930

def b12192 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 152 81 164 228 164 420), lower := (rows 67 290 13 152 81 32 64 128 256), losses := [] }

theorem u12192 : Upper (D 8) (R 8) [66,288,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12193 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 152 84 161 225 161 417), lower := (rows 67 290 13 152 84 32 64 128 256), losses := [] }

theorem u12193 : Upper (D 8) (R 8) [66,288,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12194 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 152 112 165 229 165 421), lower := (rows 67 290 13 152 112 32 64 128 256), losses := [] }

theorem u12194 : Upper (D 8) (R 8) [66,288,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12195 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 152 145 100 100 228 356), lower := (rows 67 290 13 152 145 32 64 128 256), losses := [] }

theorem u12195 : Upper (D 8) (R 8) [66,288,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12196 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 152 148 97 97 225 353), lower := (rows 67 290 13 152 148 32 64 128 256), losses := [] }

theorem u12196 : Upper (D 8) (R 8) [66,288,9,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12197 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 152 176 101 101 229 357), lower := (rows 67 290 13 152 176 32 64 128 256), losses := [] }

theorem u12197 : Upper (D 8) (R 8) [66,288,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12198 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 152 208 37 101 165 293), lower := (rows 67 290 13 152 208 32 64 128 256), losses := [] }

theorem u12198 : Upper (D 8) (R 8) [66,288,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12199 : Route 9 := (fun mask => (mask,id))

def c12199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12199 : Upper (D 8) (R 8) [66,288,9,160,33] 13 := by
  apply FastRouting.sound _ _ [66,288,9,160,33] 13 (by decide) (choices 1) [4,16,64,128] r12199 c12199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3931
  · exact u3932
  · exact u3933
  · exact u3934

def r12200 : Route 9 := (fun mask => (mask,id))

def c12200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12200 : Upper (D 8) (R 8) [66,288,9,160,36] 13 := by
  apply FastRouting.sound _ _ [66,288,9,160,36] 13 (by decide) (choices 1) [1,16,64,128] r12200 c12200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3935
  · exact u3936
  · exact u3937
  · exact u3938

def b12201 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 168 81 180 244 180 436), lower := (rows 67 290 13 168 81 32 64 128 256), losses := [] }

theorem u12201 : Upper (D 8) (R 8) [66,288,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12202 : Route 9 := (fun mask => (mask,id))

def c12202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12202 : Upper (D 8) (R 8) [66,288,9,160,68] 13 := by
  apply FastRouting.sound _ _ [66,288,9,160,68] 13 (by decide) (choices 1) [1,16,128] r12202 c12202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3939
  · exact u3940
  · exact u3941

def r12203 : Route 9 := (fun mask => (mask,id))

def c12203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12203 : Upper (D 8) (R 8) [66,288,9,160,96] 13 := by
  apply FastRouting.sound _ _ [66,288,9,160,96] 13 (by decide) (choices 1) [1,4,16,128] r12203 c12203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3942
  · exact u3943
  · exact u3944
  · exact u3945

def r12204 : Route 9 := (fun mask => (mask,id))

def c12204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12204 : Upper (D 8) (R 8) [66,288,9,160,129] 13 := by
  apply FastRouting.sound _ _ [66,288,9,160,129] 13 (by decide) (choices 1) [4,16,64] r12204 c12204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3946
  · exact u3947
  · exact u3948

def b12205 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 168 148 113 113 241 369), lower := (rows 67 290 13 168 148 32 64 128 256), losses := [] }

theorem u12205 : Upper (D 8) (R 8) [66,288,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12206 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 290 13 168 176 117 85 213 341), lower := (rows 67 290 13 168 176 32 64 128 256), losses := [] }

theorem u12206 : Upper (D 8) (R 8) [66,288,9,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12207 : Route 9 := (fun mask => (mask,id))

def c12207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12207 : Upper (D 8) (R 8) [66,288,9,160,192] 13 := by
  apply FastRouting.sound _ _ [66,288,9,160,192] 13 (by decide) (choices 1) [1,4,16] r12207 c12207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3949
  · exact u3950
  · exact u3951

def b12208 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 200 49 180 244 180 436), lower := (rows 67 290 13 200 49 32 64 128 256), losses := [] }

theorem u12208 : Upper (D 8) (R 8) [66,288,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12209 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 200 52 177 241 177 433), lower := (rows 67 290 13 200 52 32 64 128 256), losses := [] }

theorem u12209 : Upper (D 8) (R 8) [66,288,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12210 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 200 145 52 116 180 308), lower := (rows 67 290 13 200 145 32 64 128 256), losses := [] }

theorem u12210 : Upper (D 8) (R 8) [66,288,9,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12211 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 200 148 49 113 177 305), lower := (rows 67 290 13 200 148 32 64 128 256), losses := [] }

theorem u12211 : Upper (D 8) (R 8) [66,288,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12212 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 200 176 53 117 181 309), lower := (rows 67 290 13 200 176 32 64 128 256), losses := [] }

theorem u12212 : Upper (D 8) (R 8) [66,288,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12213 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 28 41 49 228 196 196 452), lower := (rows 67 290 28 41 49 32 64 128 256), losses := [] }

theorem u12213 : Upper (D 8) (R 8) [66,288,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12214 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 28 41 52 225 193 193 449), lower := (rows 67 290 28 41 52 32 64 128 256), losses := [] }

theorem u12214 : Upper (D 8) (R 8) [66,288,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12215 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 41 81 164 228 164 420), lower := (rows 67 290 28 41 81 32 64 128 256), losses := [] }

theorem u12215 : Upper (D 8) (R 8) [66,288,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12216 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 41 84 161 225 161 417), lower := (rows 67 290 28 41 84 32 64 128 256), losses := [] }

theorem u12216 : Upper (D 8) (R 8) [66,288,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12217 : Route 9 := (fun mask => (mask,id))

def c12217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12217 : Upper (D 8) (R 8) [66,288,24,33,96] 13 := by
  apply FastRouting.sound _ _ [66,288,24,33,96] 13 (by decide) (choices 1) [1,4,128] r12217 c12217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3952
  · exact u3953
  · exact u3954

def b12218 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 28 41 145 228 228 228 484), lower := (rows 67 290 28 41 145 32 64 128 256), losses := [] }

theorem u12218 : Upper (D 8) (R 8) [66,288,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12219 : Route 9 := (fun mask => (mask,id))

def c12219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12219 : Upper (D 8) (R 8) [66,288,24,33,132] 13 := by
  apply FastRouting.sound _ _ [66,288,24,33,132] 13 (by decide) (choices 1) [1,64,128] r12219 c12219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3955
  · exact u3956
  · exact u3957

def r12220 : Route 9 := (fun mask => (mask,id))

def c12220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12220 : Upper (D 8) (R 8) [66,288,24,33,160] 13 := by
  apply FastRouting.sound _ _ [66,288,24,33,160] 13 (by decide) (choices 1) [1,4,64,128] r12220 c12220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3958
  · exact u3959
  · exact u3960
  · exact u3961

def r12221 : Route 9 := (fun mask => (mask,id))

def c12221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12221 : Upper (D 8) (R 8) [66,288,24,33,192] 13 := by
  apply FastRouting.sound _ _ [66,288,24,33,192] 13 (by decide) (choices 1) [1,4,128] r12221 c12221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3962
  · exact u3963
  · exact u3964

def b12222 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 44 81 161 225 161 417), lower := (rows 67 290 28 44 81 32 64 128 256), losses := [] }

theorem u12222 : Upper (D 8) (R 8) [66,288,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12223 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 28 44 112 161 193 129 385), lower := (rows 67 290 28 44 112 32 64 128 256), losses := [] }

theorem u12223 : Upper (D 8) (R 8) [66,288,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12224 : Route 9 := (fun mask => (mask,id))

def c12224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12224 : Upper (D 8) (R 8) [66,288,24,36,129] 13 := by
  apply FastRouting.sound _ _ [66,288,24,36,129] 13 (by decide) (choices 1) [1,64,128] r12224 c12224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3965
  · exact u3966
  · exact u3967

def b12225 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 28 44 176 225 193 193 449), lower := (rows 67 290 28 44 176 32 64 128 256), losses := [] }

theorem u12225 : Upper (D 8) (R 8) [66,288,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12226 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 44 208 161 225 161 417), lower := (rows 67 290 28 44 208 32 64 128 256), losses := [] }

theorem u12226 : Upper (D 8) (R 8) [66,288,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12227 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 73 145 164 228 164 420), lower := (rows 67 290 28 73 145 32 64 128 256), losses := [] }

theorem u12227 : Upper (D 8) (R 8) [66,288,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12228 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 73 148 161 225 161 417), lower := (rows 67 290 28 73 148 32 64 128 256), losses := [] }

theorem u12228 : Upper (D 8) (R 8) [66,288,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12229 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 73 176 165 229 165 421), lower := (rows 67 290 28 73 176 32 64 128 256), losses := [] }

theorem u12229 : Upper (D 8) (R 8) [66,288,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12230 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 76 145 161 225 161 417), lower := (rows 67 290 28 76 145 32 64 128 256), losses := [] }

theorem u12230 : Upper (D 8) (R 8) [66,288,24,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12231 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 76 176 161 225 161 417), lower := (rows 67 290 28 76 176 32 64 128 256), losses := [] }

theorem u12231 : Upper (D 8) (R 8) [66,288,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12232 : Route 9 := (fun mask => (mask,id))

def c12232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12232 : Upper (D 8) (R 8) [66,288,24,96,129] 13 := by
  apply FastRouting.sound _ _ [66,288,24,96,129] 13 (by decide) (choices 1) [1,4,128] r12232 c12232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3968
  · exact u3969
  · exact u3970

def b12233 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 104 148 161 225 161 417), lower := (rows 67 290 28 104 148 32 64 128 256), losses := [] }

theorem u12233 : Upper (D 8) (R 8) [66,288,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12234 : Route 9 := (fun mask => (mask,id))

def c12234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12234 : Upper (D 8) (R 8) [66,288,24,96,160] 13 := by
  apply FastRouting.sound _ _ [66,288,24,96,160] 13 (by decide) (choices 1) [1,4,128] r12234 c12234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3971
  · exact u3972
  · exact u3973

def b12235 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 28 137 145 100 100 228 356), lower := (rows 67 290 28 137 145 32 64 128 256), losses := [] }

theorem u12235 : Upper (D 8) (R 8) [66,288,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12236 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 28 137 148 97 97 225 353), lower := (rows 67 290 28 137 148 32 64 128 256), losses := [] }

theorem u12236 : Upper (D 8) (R 8) [66,288,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12237 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 137 176 101 101 229 357), lower := (rows 67 290 28 137 176 32 64 128 256), losses := [] }

theorem u12237 : Upper (D 8) (R 8) [66,288,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12238 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 137 208 37 101 165 293), lower := (rows 67 290 28 137 208 32 64 128 256), losses := [] }

theorem u12238 : Upper (D 8) (R 8) [66,288,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12239 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 28 140 176 97 97 225 353), lower := (rows 67 290 28 140 176 32 64 128 256), losses := [] }

theorem u12239 : Upper (D 8) (R 8) [66,288,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12239
end Delivery.IrregularNine14.P08
