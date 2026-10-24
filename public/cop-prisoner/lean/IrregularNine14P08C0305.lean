import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0112
import IrregularNine14P08C0113

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18300 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 137 82 176 240 176 432), lower := (rows 321 14 37 137 82 32 64 128 256), losses := [] }

theorem u18300 : Upper (D 8) (R 8) [320,12,33,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18301 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 137 112 178 242 178 434), lower := (rows 321 14 37 137 112 32 64 128 256), losses := [] }

theorem u18301 : Upper (D 8) (R 8) [320,12,33,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18302 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 137 146 112 112 240 368), lower := (rows 321 14 37 137 146 32 64 128 256), losses := [] }

theorem u18302 : Upper (D 8) (R 8) [320,12,33,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18303 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 137 176 114 114 242 370), lower := (rows 321 14 37 137 176 32 64 128 256), losses := [] }

theorem u18303 : Upper (D 8) (R 8) [320,12,33,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18304 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 137 208 50 114 178 306), lower := (rows 321 14 37 137 208 32 64 128 256), losses := [] }

theorem u18304 : Upper (D 8) (R 8) [320,12,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18305 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 37 138 49 240 240 240 496), lower := (rows 321 14 37 138 49 32 64 128 256), losses := [] }

theorem u18305 : Upper (D 8) (R 8) [320,12,33,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18306 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 138 81 176 240 176 432), lower := (rows 321 14 37 138 81 32 64 128 256), losses := [] }

theorem u18306 : Upper (D 8) (R 8) [320,12,33,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18307 : Route 9 := (fun mask => (mask,id))

def c18307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18307 : Upper (D 8) (R 8) [320,12,33,130,96] 13 := by
  apply FastRouting.sound _ _ [320,12,33,130,96] 13 (by decide) (choices 1) [1,16,128] r18307 c18307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6758
  · exact u6759
  · exact u6760

def b18308 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 138 145 112 112 240 368), lower := (rows 321 14 37 138 145 32 64 128 256), losses := [] }

theorem u18308 : Upper (D 8) (R 8) [320,12,33,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18309 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 138 176 113 113 241 369), lower := (rows 321 14 37 138 176 32 64 128 256), losses := [] }

theorem u18309 : Upper (D 8) (R 8) [320,12,33,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18310 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 138 208 49 113 177 305), lower := (rows 321 14 37 138 208 32 64 128 256), losses := [] }

theorem u18310 : Upper (D 8) (R 8) [320,12,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18311 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 37 152 49 226 226 226 482), lower := (rows 321 14 37 152 49 32 64 128 256), losses := [] }

theorem u18311 : Upper (D 8) (R 8) [320,12,33,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18312 : Route 9 := (fun mask => (mask,id))

def c18312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18312 : Upper (D 8) (R 8) [320,12,33,144,34] 13 := by
  apply FastRouting.sound _ _ [320,12,33,144,34] 13 (by decide) (choices 1) [1,64,128] r18312 c18312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6761
  · exact u6762
  · exact u6763

def b18313 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 152 81 162 226 162 418), lower := (rows 321 14 37 152 81 32 64 128 256), losses := [] }

theorem u18313 : Upper (D 8) (R 8) [320,12,33,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18314 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 152 82 161 225 161 417), lower := (rows 321 14 37 152 82 32 64 128 256), losses := [] }

theorem u18314 : Upper (D 8) (R 8) [320,12,33,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18315 : Route 9 := (fun mask => (mask,id))

def c18315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18315 : Upper (D 8) (R 8) [320,12,33,144,96] 13 := by
  apply FastRouting.sound _ _ [320,12,33,144,96] 13 (by decide) (choices 1) [1,2,128] r18315 c18315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6764
  · exact u6765
  · exact u6766

def b18316 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 152 145 98 98 226 354), lower := (rows 321 14 37 152 145 32 64 128 256), losses := [] }

theorem u18316 : Upper (D 8) (R 8) [320,12,33,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18317 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 152 146 97 97 225 353), lower := (rows 321 14 37 152 146 32 64 128 256), losses := [] }

theorem u18317 : Upper (D 8) (R 8) [320,12,33,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18318 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 152 176 99 99 227 355), lower := (rows 321 14 37 152 176 32 64 128 256), losses := [] }

theorem u18318 : Upper (D 8) (R 8) [320,12,33,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18319 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 152 208 35 99 163 291), lower := (rows 321 14 37 152 208 32 64 128 256), losses := [] }

theorem u18319 : Upper (D 8) (R 8) [320,12,33,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18320 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 37 168 49 242 210 210 466), lower := (rows 321 14 37 168 49 32 64 128 256), losses := [] }

theorem u18320 : Upper (D 8) (R 8) [320,12,33,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18321 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 321 14 37 168 50 241 209 209 465), lower := (rows 321 14 37 168 50 32 64 128 256), losses := [] }

theorem u18321 : Upper (D 8) (R 8) [320,12,33,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18322 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 168 81 178 242 178 434), lower := (rows 321 14 37 168 81 32 64 128 256), losses := [] }

theorem u18322 : Upper (D 8) (R 8) [320,12,33,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18323 : Route 9 := (fun mask => (mask,id))

def c18323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18323 : Upper (D 8) (R 8) [320,12,33,160,66] 13 := by
  apply FastRouting.sound _ _ [320,12,33,160,66] 13 (by decide) (choices 1) [1,16,128] r18323 c18323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6767
  · exact u6768
  · exact u6769

def r18324 : Route 9 := (fun mask => (mask,id))

def c18324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18324 : Upper (D 8) (R 8) [320,12,33,160,96] 13 := by
  apply FastRouting.sound _ _ [320,12,33,160,96] 13 (by decide) (choices 1) [1,2,16,128] r18324 c18324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6770
  · exact u6771
  · exact u6772
  · exact u6773

def r18325 : Route 9 := (fun mask => (mask,id))

def c18325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18325 : Upper (D 8) (R 8) [320,12,33,160,129] 13 := by
  apply FastRouting.sound _ _ [320,12,33,160,129] 13 (by decide) (choices 1) [2,16,64] r18325 c18325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6774
  · exact u6775
  · exact u6776

def b18326 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 168 146 113 113 241 369), lower := (rows 321 14 37 168 146 32 64 128 256), losses := [] }

theorem u18326 : Upper (D 8) (R 8) [320,12,33,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18327 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 168 176 115 83 211 339), lower := (rows 321 14 37 168 176 32 64 128 256), losses := [] }

theorem u18327 : Upper (D 8) (R 8) [320,12,33,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18328 : Route 9 := (fun mask => (mask,id))

def c18328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18328 : Upper (D 8) (R 8) [320,12,33,160,192] 13 := by
  apply FastRouting.sound _ _ [320,12,33,160,192] 13 (by decide) (choices 1) [1,2,16] r18328 c18328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6777
  · exact u6778
  · exact u6779

def b18329 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 37 200 49 178 242 178 434), lower := (rows 321 14 37 200 49 32 64 128 256), losses := [] }

theorem u18329 : Upper (D 8) (R 8) [320,12,33,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18330 : Route 9 := (fun mask => (mask,id))

def c18330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18330 : Upper (D 8) (R 8) [320,12,33,192,34] 13 := by
  apply FastRouting.sound _ _ [320,12,33,192,34] 13 (by decide) (choices 1) [1,16,128] r18330 c18330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6780
  · exact u6781
  · exact u6782

def r18331 : Route 9 := (fun mask => (mask,id))

def c18331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18331 : Upper (D 8) (R 8) [320,12,33,192,129] 13 := by
  apply FastRouting.sound _ _ [320,12,33,192,129] 13 (by decide) (choices 1) [2,16] r18331 c18331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6783
  · exact u6784

def b18332 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 200 146 49 113 177 305), lower := (rows 321 14 37 200 146 32 64 128 256), losses := [] }

theorem u18332 : Upper (D 8) (R 8) [320,12,33,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18333 : Route 9 := (fun mask => (mask,id))

def c18333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18333 : Upper (D 8) (R 8) [320,12,33,192,160] 13 := by
  apply FastRouting.sound _ _ [320,12,33,192,160] 13 (by decide) (choices 1) [1,2,16] r18333 c18333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6785
  · exact u6786
  · exact u6787

def b18334 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 56 49 225 193 193 449), lower := (rows 321 14 38 56 49 32 64 128 256), losses := [] }

theorem u18334 : Upper (D 8) (R 8) [320,12,34,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18335 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 56 112 161 193 129 385), lower := (rows 321 14 38 56 112 32 64 128 256), losses := [] }

theorem u18335 : Upper (D 8) (R 8) [320,12,34,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18336 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 56 145 225 225 225 481), lower := (rows 321 14 38 56 145 32 64 128 256), losses := [] }

theorem u18336 : Upper (D 8) (R 8) [320,12,34,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18337 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 56 176 225 193 193 449), lower := (rows 321 14 38 56 176 32 64 128 256), losses := [] }

theorem u18337 : Upper (D 8) (R 8) [320,12,34,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18338 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 56 208 161 225 161 417), lower := (rows 321 14 38 56 208 32 64 128 256), losses := [] }

theorem u18338 : Upper (D 8) (R 8) [320,12,34,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18339 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 73 49 176 240 176 432), lower := (rows 321 14 38 73 49 32 64 128 256), losses := [] }

theorem u18339 : Upper (D 8) (R 8) [320,12,34,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18340 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 73 145 176 240 176 432), lower := (rows 321 14 38 73 145 32 64 128 256), losses := [] }

theorem u18340 : Upper (D 8) (R 8) [320,12,34,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18341 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 73 176 177 241 177 433), lower := (rows 321 14 38 73 176 32 64 128 256), losses := [] }

theorem u18341 : Upper (D 8) (R 8) [320,12,34,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18342 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 38 88 49 161 225 161 417), lower := (rows 321 14 38 88 49 32 64 128 256), losses := [] }

theorem u18342 : Upper (D 8) (R 8) [320,12,34,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18343 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 38 88 145 161 225 161 417), lower := (rows 321 14 38 88 145 32 64 128 256), losses := [] }

theorem u18343 : Upper (D 8) (R 8) [320,12,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18344 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 38 88 176 161 225 161 417), lower := (rows 321 14 38 88 176 32 64 128 256), losses := [] }

theorem u18344 : Upper (D 8) (R 8) [320,12,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18345 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 104 49 177 209 145 401), lower := (rows 321 14 38 104 49 32 64 128 256), losses := [] }

theorem u18345 : Upper (D 8) (R 8) [320,12,34,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18346 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 104 145 177 241 177 433), lower := (rows 321 14 38 104 145 32 64 128 256), losses := [] }

theorem u18346 : Upper (D 8) (R 8) [320,12,34,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18347 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 104 176 177 209 145 401), lower := (rows 321 14 38 104 176 32 64 128 256), losses := [] }

theorem u18347 : Upper (D 8) (R 8) [320,12,34,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18348 : Route 9 := (fun mask => (mask,id))

def c18348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u18348 : Upper (D 8) (R 8) [320,12,34,129,33] 13 := by
  apply FastRouting.sound _ _ [320,12,34,129,33] 13 (by decide) (choices 1) [16,64,128] r18348 c18348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6788
  · exact u6789
  · exact u6790

def b18349 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 137 81 176 240 176 432), lower := (rows 321 14 38 137 81 32 64 128 256), losses := [] }

theorem u18349 : Upper (D 8) (R 8) [320,12,34,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18350 : Route 9 := (fun mask => (mask,id))

def c18350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18350 : Upper (D 8) (R 8) [320,12,34,129,96] 13 := by
  apply FastRouting.sound _ _ [320,12,34,129,96] 13 (by decide) (choices 1) [1,16,128] r18350 c18350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6791
  · exact u6792
  · exact u6793

def b18351 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 14 38 137 145 112 112 240 368), lower := (rows 321 14 38 137 145 32 64 128 256), losses := [] }

theorem u18351 : Upper (D 8) (R 8) [320,12,34,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18352 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 38 137 176 113 113 241 369), lower := (rows 321 14 38 137 176 32 64 128 256), losses := [] }

theorem u18352 : Upper (D 8) (R 8) [320,12,34,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18353 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 38 137 208 49 113 177 305), lower := (rows 321 14 38 137 208 32 64 128 256), losses := [] }

theorem u18353 : Upper (D 8) (R 8) [320,12,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18354 : Route 9 := (fun mask => (mask,id))

def c18354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18354 : Upper (D 8) (R 8) [320,12,34,144,33] 13 := by
  apply FastRouting.sound _ _ [320,12,34,144,33] 13 (by decide) (choices 1) [1,64,128] r18354 c18354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6794
  · exact u6795
  · exact u6796

def b18355 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 152 81 161 225 161 417), lower := (rows 321 14 38 152 81 32 64 128 256), losses := [] }

theorem u18355 : Upper (D 8) (R 8) [320,12,34,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18356 : Route 9 := (fun mask => (mask,id))

def c18356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18356 : Upper (D 8) (R 8) [320,12,34,144,96] 13 := by
  apply FastRouting.sound _ _ [320,12,34,144,96] 13 (by decide) (choices 1) [1,128] r18356 c18356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6797
  · exact u6798

def b18357 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 38 152 145 97 97 225 353), lower := (rows 321 14 38 152 145 32 64 128 256), losses := [] }

theorem u18357 : Upper (D 8) (R 8) [320,12,34,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18358 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 152 176 97 97 225 353), lower := (rows 321 14 38 152 176 32 64 128 256), losses := [] }

theorem u18358 : Upper (D 8) (R 8) [320,12,34,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18359 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 38 152 208 33 97 161 289), lower := (rows 321 14 38 152 208 32 64 128 256), losses := [] }

theorem u18359 : Upper (D 8) (R 8) [320,12,34,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18359
end Delivery.IrregularNine14.P08
