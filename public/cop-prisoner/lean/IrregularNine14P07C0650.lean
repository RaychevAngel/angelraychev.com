import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0444
import IrregularNine14P07C0445
import IrregularNine14P07C0446

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39000 : Route 9 := (fun mask => (mask,id))

def c39000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39000 : Upper (D 7) (R 7) [36,264,80,192,3] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192,3] 13 (by decide) (choices 1) [1,2,128] r39000 c39000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26650
  · exact u26651
  · exact u26652

def b39001 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 84 200 49 163 195 131 387), lower := (rows 37 266 84 200 49 32 64 128 256), losses := [] }

theorem u39001 : Upper (D 7) (R 7) [36,264,80,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39002 : Route 9 := (fun mask => (mask,id))

def c39002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39002 : Upper (D 7) (R 7) [36,264,80,192,34] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192,34] 13 (by decide) (choices 1) [1,2,128] r39002 c39002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26653
  · exact u26654
  · exact u26655

def r39003 : Route 9 := (fun mask => (mask,id))

def c39003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39003 : Upper (D 7) (R 7) [36,264,80,192,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192,129] 13 (by decide) (choices 1) [1,2] r39003 c39003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26656
  · exact u26657

def r39004 : Route 9 := (fun mask => (mask,id))

def c39004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39004 : Upper (D 7) (R 7) [36,264,80,192,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192,130] 13 (by decide) (choices 1) [1,2] r39004 c39004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26658
  · exact u26659

def r39005 : Route 9 := (fun mask => (mask,id))

def c39005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39005 : Upper (D 7) (R 7) [36,264,80,192,160] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192,160] 13 (by decide) (choices 1) [1,2] r39005 c39005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26660
  · exact u26661

def b39006 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 37 266 196 11 19 240 240 240 496), lower := (rows 37 266 196 11 19 32 64 128 256), losses := [] }

theorem u39006 : Upper (D 7) (R 7) [36,264,192,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39007 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 196 11 49 242 210 210 466), lower := (rows 37 266 196 11 49 32 64 128 256), losses := [] }

theorem u39007 : Upper (D 7) (R 7) [36,264,192,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39008 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39008 : Upper (D 7) (R 7) [36,264,192,3,34] 13 := by
  apply FastRouting.sound _ _ [36,264,192,3,34] 13 (by decide) (choices 1) [1,16,64] r39008 c39008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26662
  · exact u26663
  · exact u26664

def r39009 : Route 9 := (fun mask => (mask,id))

def c39009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39009 : Upper (D 7) (R 7) [36,264,192,3,65] 13 := by
  apply FastRouting.sound _ _ [36,264,192,3,65] 13 (by decide) (choices 1) [2,16,128] r39009 c39009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26665
  · exact u26666
  · exact u26667

def r39010 : Route 9 := (fun mask => (mask,id))

def c39010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39010 : Upper (D 7) (R 7) [36,264,192,3,66] 13 := by
  apply FastRouting.sound _ _ [36,264,192,3,66] 13 (by decide) (choices 1) [1,16,128] r39010 c39010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26668
  · exact u26669
  · exact u26670

def r39011 : Route 9 := (fun mask => (mask,id))

def c39011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39011 : Upper (D 7) (R 7) [36,264,192,3,96] 13 := by
  apply FastRouting.sound _ _ [36,264,192,3,96] 13 (by decide) (choices 1) [1,2,16,128] r39011 c39011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26671
  · exact u26672
  · exact u26673
  · exact u26674

def b39012 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 266 196 11 208 51 115 179 307), lower := (rows 37 266 196 11 208 32 64 128 256), losses := [] }

theorem u39012 : Upper (D 7) (R 7) [36,264,192,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39013 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 266 196 25 19 226 226 226 482), lower := (rows 37 266 196 25 19 32 64 128 256), losses := [] }

theorem u39013 : Upper (D 7) (R 7) [36,264,192,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39014 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 266 196 25 49 226 194 194 450), lower := (rows 37 266 196 25 49 32 64 128 256), losses := [] }

theorem u39014 : Upper (D 7) (R 7) [36,264,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39015 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39015 : Upper (D 7) (R 7) [36,264,192,17,34] 13 := by
  apply FastRouting.sound _ _ [36,264,192,17,34] 13 (by decide) (choices 1) [1,2,64] r39015 c39015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26675
  · exact u26676
  · exact u26677

def b39016 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 196 25 81 162 226 162 418), lower := (rows 37 266 196 25 81 32 64 128 256), losses := [] }

theorem u39016 : Upper (D 7) (R 7) [36,264,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39017 : Route 9 := (fun mask => (mask,id))

def c39017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39017 : Upper (D 7) (R 7) [36,264,192,17,66] 13 := by
  apply FastRouting.sound _ _ [36,264,192,17,66] 13 (by decide) (choices 1) [1,2,128] r39017 c39017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26678
  · exact u26679
  · exact u26680

def r39018 : Route 9 := (fun mask => (mask,id))

def c39018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39018 : Upper (D 7) (R 7) [36,264,192,17,96] 13 := by
  apply FastRouting.sound _ _ [36,264,192,17,96] 13 (by decide) (choices 1) [1,2,128] r39018 c39018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26681
  · exact u26682
  · exact u26683

def b39019 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 266 196 25 208 35 99 163 291), lower := (rows 37 266 196 25 208 32 64 128 256), losses := [] }

theorem u39019 : Upper (D 7) (R 7) [36,264,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39020 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 266 196 26 19 225 225 225 481), lower := (rows 37 266 196 26 19 32 64 128 256), losses := [] }

theorem u39020 : Upper (D 7) (R 7) [36,264,192,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39021 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 196 26 49 227 195 195 451), lower := (rows 37 266 196 26 49 32 64 128 256), losses := [] }

theorem u39021 : Upper (D 7) (R 7) [36,264,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39022 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 266 196 26 50 225 193 193 449), lower := (rows 37 266 196 26 50 32 64 128 256), losses := [] }

theorem u39022 : Upper (D 7) (R 7) [36,264,192,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39023 : Route 9 := (fun mask => (mask,id))

def c39023 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39023 : Upper (D 7) (R 7) [36,264,192,18,65] 13 := by
  apply FastRouting.sound _ _ [36,264,192,18,65] 13 (by decide) (choices 1) [1,2,128] r39023 c39023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26684
  · exact u26685
  · exact u26686

def b39024 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 266 196 26 82 161 225 161 417), lower := (rows 37 266 196 26 82 32 64 128 256), losses := [] }

theorem u39024 : Upper (D 7) (R 7) [36,264,192,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39025 : Route 9 := (fun mask => (mask,id))

def c39025 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39025 : Upper (D 7) (R 7) [36,264,192,18,96] 13 := by
  apply FastRouting.sound _ _ [36,264,192,18,96] 13 (by decide) (choices 1) [1,2,128] r39025 c39025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26687
  · exact u26688
  · exact u26689

def b39026 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 266 196 26 208 35 99 163 291), lower := (rows 37 266 196 26 208 32 64 128 256), losses := [] }

theorem u39026 : Upper (D 7) (R 7) [36,264,192,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39027 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39027 : Upper (D 7) (R 7) [36,264,192,34,3] 13 := by
  apply FastRouting.sound _ _ [36,264,192,34,3] 13 (by decide) (choices 1) [1,16,64] r39027 c39027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26690
  · exact u26691
  · exact u26692

def r39028 : Route 9 := (fun mask => (mask,id))

def c39028 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39028 : Upper (D 7) (R 7) [36,264,192,34,65] 13 := by
  apply FastRouting.sound _ _ [36,264,192,34,65] 13 (by decide) (choices 1) [1,2,16,128] r39028 c39028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26693
  · exact u26694
  · exact u26695
  · exact u26696

def r39029 : Route 9 := (fun mask => (mask,id))

def c39029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39029 : Upper (D 7) (R 7) [36,264,192,34,66] 13 := by
  apply FastRouting.sound _ _ [36,264,192,34,66] 13 (by decide) (choices 1) [1,16,128] r39029 c39029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26697
  · exact u26698
  · exact u26699

def b39030 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 266 196 42 208 51 83 147 275), lower := (rows 37 266 196 42 208 32 64 128 256), losses := [] }

theorem u39030 : Upper (D 7) (R 7) [36,264,192,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39031 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39031 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39031 : Upper (D 7) (R 7) [36,264,192,48,3] 13 := by
  apply FastRouting.sound _ _ [36,264,192,48,3] 13 (by decide) (choices 1) [1,2,64] r39031 c39031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26700
  · exact u26701
  · exact u26702

def r39032 : Route 9 := (fun mask => (mask,id))

def c39032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39032 : Upper (D 7) (R 7) [36,264,192,48,65] 13 := by
  apply FastRouting.sound _ _ [36,264,192,48,65] 13 (by decide) (choices 1) [1,2,128] r39032 c39032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26703
  · exact u26704
  · exact u26705

def r39033 : Route 9 := (fun mask => (mask,id))

def c39033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39033 : Upper (D 7) (R 7) [36,264,192,48,66] 13 := by
  apply FastRouting.sound _ _ [36,264,192,48,66] 13 (by decide) (choices 1) [1,2,128] r39033 c39033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26706
  · exact u26707
  · exact u26708

def b39034 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 266 196 56 208 35 67 131 259), lower := (rows 37 266 196 56 208 32 64 128 256), losses := [] }

theorem u39034 : Upper (D 7) (R 7) [36,264,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39035 : Route 9 := (fun mask => (mask,id))

def c39035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39035 : Upper (D 7) (R 7) [36,264,192,65,3] 13 := by
  apply FastRouting.sound _ _ [36,264,192,65,3] 13 (by decide) (choices 1) [2,16,128] r39035 c39035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26709
  · exact u26710
  · exact u26711

def b39036 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 196 73 49 178 210 146 402), lower := (rows 37 266 196 73 49 32 64 128 256), losses := [] }

theorem u39036 : Upper (D 7) (R 7) [36,264,192,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39037 : Route 9 := (fun mask => (mask,id))

def c39037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39037 : Upper (D 7) (R 7) [36,264,192,65,34] 13 := by
  apply FastRouting.sound _ _ [36,264,192,65,34] 13 (by decide) (choices 1) [1,2,16,128] r39037 c39037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26712
  · exact u26713
  · exact u26714
  · exact u26715

def b39038 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 37 266 196 73 145 50 114 178 306), lower := (rows 37 266 196 73 145 32 64 128 256), losses := [] }

theorem u39038 : Upper (D 7) (R 7) [36,264,192,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39039 : Route 9 := (fun mask => (mask,id))

def c39039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39039 : Upper (D 7) (R 7) [36,264,192,65,130] 13 := by
  apply FastRouting.sound _ _ [36,264,192,65,130] 13 (by decide) (choices 1) [1,2,16] r39039 c39039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26716
  · exact u26717
  · exact u26718

def r39040 : Route 9 := (fun mask => (mask,id))

def c39040 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39040 : Upper (D 7) (R 7) [36,264,192,65,160] 13 := by
  apply FastRouting.sound _ _ [36,264,192,65,160] 13 (by decide) (choices 1) [1,2,16] r39040 c39040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26719
  · exact u26720
  · exact u26721

def r39041 : Route 9 := (fun mask => (mask,id))

def c39041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39041 : Upper (D 7) (R 7) [36,264,192,66,3] 13 := by
  apply FastRouting.sound _ _ [36,264,192,66,3] 13 (by decide) (choices 1) [1,16,128] r39041 c39041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26722
  · exact u26723
  · exact u26724

def b39042 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 196 74 49 179 211 147 403), lower := (rows 37 266 196 74 49 32 64 128 256), losses := [] }

theorem u39042 : Upper (D 7) (R 7) [36,264,192,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39043 : Route 9 := (fun mask => (mask,id))

def c39043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39043 : Upper (D 7) (R 7) [36,264,192,66,34] 13 := by
  apply FastRouting.sound _ _ [36,264,192,66,34] 13 (by decide) (choices 1) [1,16,128] r39043 c39043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26725
  · exact u26726
  · exact u26727

def r39044 : Route 9 := (fun mask => (mask,id))

def c39044 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39044 : Upper (D 7) (R 7) [36,264,192,66,129] 13 := by
  apply FastRouting.sound _ _ [36,264,192,66,129] 13 (by decide) (choices 1) [1,2,16] r39044 c39044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26728
  · exact u26729
  · exact u26730

def r39045 : Route 9 := (fun mask => (mask,id))

def c39045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39045 : Upper (D 7) (R 7) [36,264,192,66,130] 13 := by
  apply FastRouting.sound _ _ [36,264,192,66,130] 13 (by decide) (choices 1) [1,16] r39045 c39045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26731
  · exact u26732

def r39046 : Route 9 := (fun mask => (mask,id))

def c39046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39046 : Upper (D 7) (R 7) [36,264,192,66,160] 13 := by
  apply FastRouting.sound _ _ [36,264,192,66,160] 13 (by decide) (choices 1) [1,2,16] r39046 c39046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26733
  · exact u26734
  · exact u26735

def r39047 : Route 9 := (fun mask => (mask,id))

def c39047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39047 : Upper (D 7) (R 7) [36,264,192,80,3] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,3] 13 (by decide) (choices 1) [1,2,128] r39047 c39047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26736
  · exact u26737
  · exact u26738

def b39048 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 196 88 49 163 195 131 387), lower := (rows 37 266 196 88 49 32 64 128 256), losses := [] }

theorem u39048 : Upper (D 7) (R 7) [36,264,192,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39049 : Route 9 := (fun mask => (mask,id))

def c39049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39049 : Upper (D 7) (R 7) [36,264,192,80,34] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,34] 13 (by decide) (choices 1) [1,2,128] r39049 c39049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26739
  · exact u26740
  · exact u26741

def r39050 : Route 9 := (fun mask => (mask,id))

def c39050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39050 : Upper (D 7) (R 7) [36,264,192,80,129] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,129] 13 (by decide) (choices 1) [1,2] r39050 c39050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26742
  · exact u26743

def r39051 : Route 9 := (fun mask => (mask,id))

def c39051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39051 : Upper (D 7) (R 7) [36,264,192,80,130] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,130] 13 (by decide) (choices 1) [1,2] r39051 c39051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26744
  · exact u26745

def r39052 : Route 9 := (fun mask => (mask,id))

def c39052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39052 : Upper (D 7) (R 7) [36,264,192,80,160] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,160] 13 (by decide) (choices 1) [1,2] r39052 c39052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26746
  · exact u26747

def r39053 : Route 9 := (fun mask => (mask,id))

def c39053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39053 : Upper (D 7) (R 7) [36,264,192,96,3] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,3] 13 (by decide) (choices 1) [1,2,16,128] r39053 c39053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26748
  · exact u26749
  · exact u26750
  · exact u26751

def r39054 : Route 9 := (fun mask => (mask,id))

def c39054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39054 : Upper (D 7) (R 7) [36,264,192,96,129] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,129] 13 (by decide) (choices 1) [1,2,16] r39054 c39054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26752
  · exact u26753
  · exact u26754

def r39055 : Route 9 := (fun mask => (mask,id))

def c39055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39055 : Upper (D 7) (R 7) [36,264,192,96,130] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,130] 13 (by decide) (choices 1) [1,2,16] r39055 c39055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26755
  · exact u26756
  · exact u26757

def b39056 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 13 26 19 224 192 192 448), lower := (rows 37 290 13 26 19 32 64 128 256), losses := [] }

theorem u39056 : Upper (D 7) (R 7) [36,288,9,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39057 : Route 9 := (fun mask => (mask,id))

def c39057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39057 : Upper (D 7) (R 7) [36,288,9,18,65] 13 := by
  apply FastRouting.sound _ _ [36,288,9,18,65] 13 (by decide) (choices 1) [2,64,128] r39057 c39057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26758
  · exact u26759
  · exact u26760

def b39058 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 290 13 26 82 225 193 193 449), lower := (rows 37 290 13 26 82 32 64 128 256), losses := [] }

theorem u39058 : Upper (D 7) (R 7) [36,288,9,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39059 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39059 : Upper (D 7) (R 7) [36,288,9,18,192] 13 := by
  apply FastRouting.sound _ _ [36,288,9,18,192] 13 (by decide) (choices 1) [1,2,64] r39059 c39059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26761
  · exact u26762
  · exact u26763

#print axioms u39059
end Delivery.IrregularNine14.P07
