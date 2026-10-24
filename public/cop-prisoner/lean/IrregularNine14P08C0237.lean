import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0080

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14220 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 164 266 49 241 209 209 465), lower := (rows 97 14 164 266 49 32 64 128 256), losses := [] }

theorem u14220 : Upper (D 8) (R 8) [96,12,160,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14221 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 266 81 177 241 177 433), lower := (rows 97 14 164 266 81 32 64 128 256), losses := [] }

theorem u14221 : Upper (D 8) (R 8) [96,12,160,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14222 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 164 266 112 177 209 145 401), lower := (rows 97 14 164 266 112 32 64 128 256), losses := [] }

theorem u14222 : Upper (D 8) (R 8) [96,12,160,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14223 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 266 145 113 113 241 369), lower := (rows 97 14 164 266 145 32 64 128 256), losses := [] }

theorem u14223 : Upper (D 8) (R 8) [96,12,160,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14224 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 164 266 176 113 81 209 337), lower := (rows 97 14 164 266 176 32 64 128 256), losses := [] }

theorem u14224 : Upper (D 8) (R 8) [96,12,160,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14225 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 266 208 49 113 177 305), lower := (rows 97 14 164 266 208 32 64 128 256), losses := [] }

theorem u14225 : Upper (D 8) (R 8) [96,12,160,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14226 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 164 280 49 227 195 195 451), lower := (rows 97 14 164 280 49 32 64 128 256), losses := [] }

theorem u14226 : Upper (D 8) (R 8) [96,12,160,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14227 : Route 9 := (fun mask => (mask,id))

def c14227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14227 : Upper (D 8) (R 8) [96,12,160,272,34] 13 := by
  apply FastRouting.sound _ _ [96,12,160,272,34] 13 (by decide) (choices 1) [1,64,128] r14227 c14227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4814
  · exact u4815
  · exact u4816

def b14228 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 280 81 163 227 163 419), lower := (rows 97 14 164 280 81 32 64 128 256), losses := [] }

theorem u14228 : Upper (D 8) (R 8) [96,12,160,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14229 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 164 280 82 161 225 161 417), lower := (rows 97 14 164 280 82 32 64 128 256), losses := [] }

theorem u14229 : Upper (D 8) (R 8) [96,12,160,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14230 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 164 280 112 163 195 131 387), lower := (rows 97 14 164 280 112 32 64 128 256), losses := [] }

theorem u14230 : Upper (D 8) (R 8) [96,12,160,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14231 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 280 145 99 99 227 355), lower := (rows 97 14 164 280 145 32 64 128 256), losses := [] }

theorem u14231 : Upper (D 8) (R 8) [96,12,160,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14232 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 280 146 97 97 225 353), lower := (rows 97 14 164 280 146 32 64 128 256), losses := [] }

theorem u14232 : Upper (D 8) (R 8) [96,12,160,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14233 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 164 280 176 99 67 195 323), lower := (rows 97 14 164 280 176 32 64 128 256), losses := [] }

theorem u14233 : Upper (D 8) (R 8) [96,12,160,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14234 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 280 208 35 99 163 291), lower := (rows 97 14 164 280 208 32 64 128 256), losses := [] }

theorem u14234 : Upper (D 8) (R 8) [96,12,160,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14235 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 296 81 179 211 147 403), lower := (rows 97 14 164 296 81 32 64 128 256), losses := [] }

theorem u14235 : Upper (D 8) (R 8) [96,12,160,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14236 : Route 9 := (fun mask => (mask,id))

def c14236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14236 : Upper (D 8) (R 8) [96,12,160,288,66] 13 := by
  apply FastRouting.sound _ _ [96,12,160,288,66] 13 (by decide) (choices 1) [1,16,128] r14236 c14236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4817
  · exact u4818
  · exact u4819

def r14237 : Route 9 := (fun mask => (mask,id))

def c14237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14237 : Upper (D 8) (R 8) [96,12,160,288,129] 13 := by
  apply FastRouting.sound _ _ [96,12,160,288,129] 13 (by decide) (choices 1) [1,2,16,64] r14237 c14237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4820
  · exact u4821
  · exact u4822
  · exact u4823

def b14238 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 296 146 113 81 209 337), lower := (rows 97 14 164 296 146 32 64 128 256), losses := [] }

theorem u14238 : Upper (D 8) (R 8) [96,12,160,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14239 : Route 9 := (fun mask => (mask,id))

def c14239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14239 : Upper (D 8) (R 8) [96,12,160,288,192] 13 := by
  apply FastRouting.sound _ _ [96,12,160,288,192] 13 (by decide) (choices 1) [1,2,16] r14239 c14239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4824
  · exact u4825
  · exact u4826

def b14240 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 164 328 49 179 211 147 403), lower := (rows 97 14 164 328 49 32 64 128 256), losses := [] }

theorem u14240 : Upper (D 8) (R 8) [96,12,160,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14241 : Route 9 := (fun mask => (mask,id))

def c14241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14241 : Upper (D 8) (R 8) [96,12,160,320,34] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,34] 13 (by decide) (choices 1) [1,16,128] r14241 c14241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4827
  · exact u4828
  · exact u4829

def r14242 : Route 9 := (fun mask => (mask,id))

def c14242 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14242 : Upper (D 8) (R 8) [96,12,160,320,129] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,129] 13 (by decide) (choices 1) [1,2,16] r14242 c14242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4830
  · exact u4831
  · exact u4832

def b14243 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 328 146 49 113 177 305), lower := (rows 97 14 164 328 146 32 64 128 256), losses := [] }

theorem u14243 : Upper (D 8) (R 8) [96,12,160,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14244 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 164 328 176 51 83 147 275), lower := (rows 97 14 164 328 176 32 64 128 256), losses := [] }

theorem u14244 : Upper (D 8) (R 8) [96,12,160,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14245 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 392 50 113 81 209 337), lower := (rows 97 14 164 392 50 32 64 128 256), losses := [] }

theorem u14245 : Upper (D 8) (R 8) [96,12,160,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14246 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 392 82 49 113 177 305), lower := (rows 97 14 164 392 82 32 64 128 256), losses := [] }

theorem u14246 : Upper (D 8) (R 8) [96,12,160,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14247 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 196 265 49 178 242 178 434), lower := (rows 97 14 196 265 49 32 64 128 256), losses := [] }

theorem u14247 : Upper (D 8) (R 8) [96,12,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14248 : Route 9 := (fun mask => (mask,id))

def c14248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14248 : Upper (D 8) (R 8) [96,12,192,257,34] 13 := by
  apply FastRouting.sound _ _ [96,12,192,257,34] 13 (by decide) (choices 1) [1,16,128] r14248 c14248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4833
  · exact u4834
  · exact u4835

def r14249 : Route 9 := (fun mask => (mask,id))

def c14249 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14249 : Upper (D 8) (R 8) [96,12,192,257,129] 13 := by
  apply FastRouting.sound _ _ [96,12,192,257,129] 13 (by decide) (choices 1) [2,16] r14249 c14249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4836
  · exact u4837

def b14250 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 265 146 49 113 177 305), lower := (rows 97 14 196 265 146 32 64 128 256), losses := [] }

theorem u14250 : Upper (D 8) (R 8) [96,12,192,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14251 : Route 9 := (fun mask => (mask,id))

def c14251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14251 : Upper (D 8) (R 8) [96,12,192,257,160] 13 := by
  apply FastRouting.sound _ _ [96,12,192,257,160] 13 (by decide) (choices 1) [1,2,16] r14251 c14251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4838
  · exact u4839
  · exact u4840

def b14252 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 196 266 145 49 113 177 305), lower := (rows 97 14 196 266 145 32 64 128 256), losses := [] }

theorem u14252 : Upper (D 8) (R 8) [96,12,192,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14253 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 196 266 176 49 113 177 305), lower := (rows 97 14 196 266 176 32 64 128 256), losses := [] }

theorem u14253 : Upper (D 8) (R 8) [96,12,192,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14254 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 196 280 49 163 227 163 419), lower := (rows 97 14 196 280 49 32 64 128 256), losses := [] }

theorem u14254 : Upper (D 8) (R 8) [96,12,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14255 : Route 9 := (fun mask => (mask,id))

def c14255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14255 : Upper (D 8) (R 8) [96,12,192,272,34] 13 := by
  apply FastRouting.sound _ _ [96,12,192,272,34] 13 (by decide) (choices 1) [1,128] r14255 c14255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4841
  · exact u4842

def b14256 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 280 145 35 99 163 291), lower := (rows 97 14 196 280 145 32 64 128 256), losses := [] }

theorem u14256 : Upper (D 8) (R 8) [96,12,192,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14257 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 280 146 33 97 161 289), lower := (rows 97 14 196 280 146 32 64 128 256), losses := [] }

theorem u14257 : Upper (D 8) (R 8) [96,12,192,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14258 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 280 176 35 99 163 291), lower := (rows 97 14 196 280 176 32 64 128 256), losses := [] }

theorem u14258 : Upper (D 8) (R 8) [96,12,192,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14259 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 196 296 49 179 211 147 403), lower := (rows 97 14 196 296 49 32 64 128 256), losses := [] }

theorem u14259 : Upper (D 8) (R 8) [96,12,192,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14260 : Route 9 := (fun mask => (mask,id))

def c14260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14260 : Upper (D 8) (R 8) [96,12,192,288,34] 13 := by
  apply FastRouting.sound _ _ [96,12,192,288,34] 13 (by decide) (choices 1) [1,16,128] r14260 c14260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4843
  · exact u4844
  · exact u4845

def r14261 : Route 9 := (fun mask => (mask,id))

def c14261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14261 : Upper (D 8) (R 8) [96,12,192,288,129] 13 := by
  apply FastRouting.sound _ _ [96,12,192,288,129] 13 (by decide) (choices 1) [1,2,16] r14261 c14261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4846
  · exact u4847
  · exact u4848

def b14262 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 296 146 49 113 177 305), lower := (rows 97 14 196 296 146 32 64 128 256), losses := [] }

theorem u14262 : Upper (D 8) (R 8) [96,12,192,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14263 : Route 9 := (fun mask => (mask,id))

def c14263 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14263 : Upper (D 8) (R 8) [96,12,192,288,160] 13 := by
  apply FastRouting.sound _ _ [96,12,192,288,160] 13 (by decide) (choices 1) [1,2,16] r14263 c14263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4849
  · exact u4850
  · exact u4851

def b14264 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 392 50 49 113 177 305), lower := (rows 97 14 196 392 50 32 64 128 256), losses := [] }

theorem u14264 : Upper (D 8) (R 8) [96,12,192,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14265 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 38 76 145 440 472 408 408), lower := (rows 97 35 38 76 145 32 64 128 256), losses := [] }

theorem u14265 : Upper (D 8) (R 8) [96,33,34,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14266 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 38 76 152 433 465 401 401), lower := (rows 97 35 38 76 152 32 64 128 256), losses := [] }

theorem u14266 : Upper (D 8) (R 8) [96,33,34,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14267 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 38 76 273 184 216 152 408), lower := (rows 97 35 38 76 273 32 64 128 256), losses := [] }

theorem u14267 : Upper (D 8) (R 8) [96,33,34,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14268 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 38 76 280 177 209 145 401), lower := (rows 97 35 38 76 280 32 64 128 256), losses := [] }

theorem u14268 : Upper (D 8) (R 8) [96,33,34,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14269 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 38 76 400 185 217 153 409), lower := (rows 97 35 38 76 400 32 64 128 256), losses := [] }

theorem u14269 : Upper (D 8) (R 8) [96,33,34,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14270 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 88 145 428 460 396 396), lower := (rows 97 35 38 88 145 32 64 128 256), losses := [] }

theorem u14270 : Upper (D 8) (R 8) [96,33,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14271 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 88 148 425 457 393 393), lower := (rows 97 35 38 88 148 32 64 128 256), losses := [] }

theorem u14271 : Upper (D 8) (R 8) [96,33,34,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14272 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 88 273 172 204 140 396), lower := (rows 97 35 38 88 273 32 64 128 256), losses := [] }

theorem u14272 : Upper (D 8) (R 8) [96,33,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14273 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 88 276 169 201 137 393), lower := (rows 97 35 38 88 276 32 64 128 256), losses := [] }

theorem u14273 : Upper (D 8) (R 8) [96,33,34,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14274 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 88 400 173 205 141 397), lower := (rows 97 35 38 88 400 32 64 128 256), losses := [] }

theorem u14274 : Upper (D 8) (R 8) [96,33,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14275 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 137 148 376 344 472 344), lower := (rows 97 35 38 137 148 32 64 128 256), losses := [] }

theorem u14275 : Upper (D 8) (R 8) [96,33,34,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14276 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 137 208 316 348 412 284), lower := (rows 97 35 38 137 208 32 64 128 256), losses := [] }

theorem u14276 : Upper (D 8) (R 8) [96,33,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14277 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 137 276 248 216 216 472), lower := (rows 97 35 38 137 276 32 64 128 256), losses := [] }

theorem u14277 : Upper (D 8) (R 8) [96,33,34,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14278 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 137 280 244 212 212 468), lower := (rows 97 35 38 137 280 32 64 128 256), losses := [] }

theorem u14278 : Upper (D 8) (R 8) [96,33,34,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14279 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 137 336 188 220 156 412), lower := (rows 97 35 38 137 336 32 64 128 256), losses := [] }

theorem u14279 : Upper (D 8) (R 8) [96,33,34,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14279
end Delivery.IrregularNine14.P08
