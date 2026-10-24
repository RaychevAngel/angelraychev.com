import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0438
import IrregularNine14P07C0439
import IrregularNine14P07C0440

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38820 : Route 9 := (fun mask => (mask,id))

def c38820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38820 : Upper (D 7) (R 7) [36,264,65,80,160] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,160] 13 (by decide) (choices 1) [1,2,128] r38820 c38820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26336
  · exact u26337
  · exact u26338

def r38821 : Route 9 := (fun mask => (mask,id))

def c38821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38821 : Upper (D 7) (R 7) [36,264,65,129,34] 13 := by
  apply FastRouting.sound _ _ [36,264,65,129,34] 13 (by decide) (choices 1) [2,16,64,128] r38821 c38821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26339
  · exact u26340
  · exact u26341
  · exact u26342

def r38822 : Route 9 := (fun mask => (mask,id))

def c38822 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38822 : Upper (D 7) (R 7) [36,264,65,129,66] 13 := by
  apply FastRouting.sound _ _ [36,264,65,129,66] 13 (by decide) (choices 1) [2,16,128] r38822 c38822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26343
  · exact u26344
  · exact u26345

def b38823 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 137 112 178 210 146 402), lower := (rows 37 266 69 137 112 32 64 128 256), losses := [] }

theorem u38823 : Upper (D 7) (R 7) [36,264,65,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38824 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 266 69 137 146 114 114 242 370), lower := (rows 37 266 69 137 146 32 64 128 256), losses := [] }

theorem u38824 : Upper (D 7) (R 7) [36,264,65,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38825 : Route 9 := (fun mask => (mask,id))

def c38825 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38825 : Upper (D 7) (R 7) [36,264,65,129,160] 13 := by
  apply FastRouting.sound _ _ [36,264,65,129,160] 13 (by decide) (choices 1) [2,16,64] r38825 c38825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26346
  · exact u26347
  · exact u26348

def r38826 : Route 9 := (fun mask => (mask,id))

def c38826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38826 : Upper (D 7) (R 7) [36,264,65,129,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,129,192] 13 (by decide) (choices 1) [2,16] r38826 c38826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26349
  · exact u26350

def b38827 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 266 69 138 19 240 240 240 496), lower := (rows 37 266 69 138 19 32 64 128 256), losses := [] }

theorem u38827 : Upper (D 7) (R 7) [36,264,65,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38828 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 69 138 49 242 210 210 466), lower := (rows 37 266 69 138 49 32 64 128 256), losses := [] }

theorem u38828 : Upper (D 7) (R 7) [36,264,65,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38829 : Route 9 := (fun mask => (mask,id))

def c38829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38829 : Upper (D 7) (R 7) [36,264,65,130,34] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130,34] 13 (by decide) (choices 1) [1,16,64,128] r38829 c38829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26351
  · exact u26352
  · exact u26353
  · exact u26354

def b38830 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 266 69 138 81 178 242 178 434), lower := (rows 37 266 69 138 81 32 64 128 256), losses := [] }

theorem u38830 : Upper (D 7) (R 7) [36,264,65,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38831 : Route 9 := (fun mask => (mask,id))

def c38831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38831 : Upper (D 7) (R 7) [36,264,65,130,66] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130,66] 13 (by decide) (choices 1) [1,16,128] r38831 c38831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26355
  · exact u26356
  · exact u26357

def b38832 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 138 112 179 211 147 403), lower := (rows 37 266 69 138 112 32 64 128 256), losses := [] }

theorem u38832 : Upper (D 7) (R 7) [36,264,65,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38833 : Route 9 := (fun mask => (mask,id))

def c38833 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38833 : Upper (D 7) (R 7) [36,264,65,130,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130,129] 13 (by decide) (choices 1) [2,16,64] r38833 c38833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26358
  · exact u26359
  · exact u26360

def b38834 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 266 69 138 146 113 113 241 369), lower := (rows 37 266 69 138 146 32 64 128 256), losses := [] }

theorem u38834 : Upper (D 7) (R 7) [36,264,65,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38835 : Route 9 := (fun mask => (mask,id))

def c38835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38835 : Upper (D 7) (R 7) [36,264,65,130,160] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130,160] 13 (by decide) (choices 1) [1,2,16,64] r38835 c38835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26361
  · exact u26362
  · exact u26363
  · exact u26364

def r38836 : Route 9 := (fun mask => (mask,id))

def c38836 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38836 : Upper (D 7) (R 7) [36,264,65,130,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130,192] 13 (by decide) (choices 1) [1,2,16] r38836 c38836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26365
  · exact u26366
  · exact u26367

def r38837 : Route 9 := (fun mask => (mask,id))

def c38837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38837 : Upper (D 7) (R 7) [36,264,65,144,3] 13 := by
  apply FastRouting.sound _ _ [36,264,65,144,3] 13 (by decide) (choices 1) [2,64,128] r38837 c38837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26368
  · exact u26369
  · exact u26370

def b38838 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 69 152 49 226 194 194 450), lower := (rows 37 266 69 152 49 32 64 128 256), losses := [] }

theorem u38838 : Upper (D 7) (R 7) [36,264,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38839 : Route 9 := (fun mask => (mask,id))

def c38839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38839 : Upper (D 7) (R 7) [36,264,65,144,34] 13 := by
  apply FastRouting.sound _ _ [36,264,65,144,34] 13 (by decide) (choices 1) [1,2,64,128] r38839 c38839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26371
  · exact u26372
  · exact u26373
  · exact u26374

def b38840 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 266 69 152 81 162 226 162 418), lower := (rows 37 266 69 152 81 32 64 128 256), losses := [] }

theorem u38840 : Upper (D 7) (R 7) [36,264,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38841 : Route 9 := (fun mask => (mask,id))

def c38841 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38841 : Upper (D 7) (R 7) [36,264,65,144,66] 13 := by
  apply FastRouting.sound _ _ [36,264,65,144,66] 13 (by decide) (choices 1) [1,2,128] r38841 c38841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26375
  · exact u26376
  · exact u26377

def b38842 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 152 112 163 195 131 387), lower := (rows 37 266 69 152 112 32 64 128 256), losses := [] }

theorem u38842 : Upper (D 7) (R 7) [36,264,65,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38843 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 37 266 69 152 145 98 98 226 354), lower := (rows 37 266 69 152 145 32 64 128 256), losses := [] }

theorem u38843 : Upper (D 7) (R 7) [36,264,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38844 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 266 69 152 146 99 99 227 355), lower := (rows 37 266 69 152 146 32 64 128 256), losses := [] }

theorem u38844 : Upper (D 7) (R 7) [36,264,65,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38845 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 266 69 152 176 99 67 195 323), lower := (rows 37 266 69 152 176 32 64 128 256), losses := [] }

theorem u38845 : Upper (D 7) (R 7) [36,264,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38846 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 266 69 152 208 35 99 163 291), lower := (rows 37 266 69 152 208 32 64 128 256), losses := [] }

theorem u38846 : Upper (D 7) (R 7) [36,264,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38847 : Route 9 := (fun mask => (mask,id))

def c38847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38847 : Upper (D 7) (R 7) [36,264,65,160,3] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160,3] 13 (by decide) (choices 1) [2,16,64,128] r38847 c38847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26378
  · exact u26379
  · exact u26380
  · exact u26381

def b38848 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 266 69 168 81 178 210 146 402), lower := (rows 37 266 69 168 81 32 64 128 256), losses := [] }

theorem u38848 : Upper (D 7) (R 7) [36,264,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38849 : Route 9 := (fun mask => (mask,id))

def c38849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38849 : Upper (D 7) (R 7) [36,264,65,160,66] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160,66] 13 (by decide) (choices 1) [1,2,16,128] r38849 c38849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26382
  · exact u26383
  · exact u26384
  · exact u26385

def r38850 : Route 9 := (fun mask => (mask,id))

def c38850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38850 : Upper (D 7) (R 7) [36,264,65,160,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160,129] 13 (by decide) (choices 1) [2,16,64] r38850 c38850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26386
  · exact u26387
  · exact u26388

def r38851 : Route 9 := (fun mask => (mask,id))

def c38851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38851 : Upper (D 7) (R 7) [36,264,65,160,130] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160,130] 13 (by decide) (choices 1) [1,2,16,64] r38851 c38851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26389
  · exact u26390
  · exact u26391
  · exact u26392

def r38852 : Route 9 := (fun mask => (mask,id))

def c38852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38852 : Upper (D 7) (R 7) [36,264,65,160,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160,192] 13 (by decide) (choices 1) [1,2,16] r38852 c38852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26393
  · exact u26394
  · exact u26395

def r38853 : Route 9 := (fun mask => (mask,id))

def c38853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38853 : Upper (D 7) (R 7) [36,264,65,192,3] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,3] 13 (by decide) (choices 1) [2,16,128] r38853 c38853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26396
  · exact u26397
  · exact u26398

def b38854 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 69 200 49 178 210 146 402), lower := (rows 37 266 69 200 49 32 64 128 256), losses := [] }

theorem u38854 : Upper (D 7) (R 7) [36,264,65,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38855 : Route 9 := (fun mask => (mask,id))

def c38855 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38855 : Upper (D 7) (R 7) [36,264,65,192,34] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,34] 13 (by decide) (choices 1) [1,2,16,128] r38855 c38855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26399
  · exact u26400
  · exact u26401
  · exact u26402

def r38856 : Route 9 := (fun mask => (mask,id))

def c38856 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38856 : Upper (D 7) (R 7) [36,264,65,192,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,129] 13 (by decide) (choices 1) [2,16] r38856 c38856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26403
  · exact u26404

def r38857 : Route 9 := (fun mask => (mask,id))

def c38857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38857 : Upper (D 7) (R 7) [36,264,65,192,130] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,130] 13 (by decide) (choices 1) [1,2,16] r38857 c38857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26405
  · exact u26406
  · exact u26407

def r38858 : Route 9 := (fun mask => (mask,id))

def c38858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38858 : Upper (D 7) (R 7) [36,264,65,192,160] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,160] 13 (by decide) (choices 1) [1,2,16] r38858 c38858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26408
  · exact u26409
  · exact u26410

def b38859 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 266 70 11 49 240 208 208 464), lower := (rows 37 266 70 11 49 32 64 128 256), losses := [] }

theorem u38859 : Upper (D 7) (R 7) [36,264,66,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38860 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 266 70 11 81 176 240 176 432), lower := (rows 37 266 70 11 81 32 64 128 256), losses := [] }

theorem u38860 : Upper (D 7) (R 7) [36,264,66,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38861 : Route 9 := (fun mask => (mask,id))

def c38861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38861 : Upper (D 7) (R 7) [36,264,66,3,96] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3,96] 13 (by decide) (choices 1) [1,16,128] r38861 c38861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26411
  · exact u26412
  · exact u26413

def r38862 : Route 9 := (fun mask => (mask,id))

def c38862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38862 : Upper (D 7) (R 7) [36,264,66,3,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3,129] 13 (by decide) (choices 1) [16,64,128] r38862 c38862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26414
  · exact u26415
  · exact u26416

def r38863 : Route 9 := (fun mask => (mask,id))

def c38863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38863 : Upper (D 7) (R 7) [36,264,66,3,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3,160] 13 (by decide) (choices 1) [1,16,64,128] r38863 c38863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26417
  · exact u26418
  · exact u26419
  · exact u26420

def r38864 : Route 9 := (fun mask => (mask,id))

def c38864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38864 : Upper (D 7) (R 7) [36,264,66,3,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3,192] 13 (by decide) (choices 1) [1,16,128] r38864 c38864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26421
  · exact u26422
  · exact u26423

def b38865 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 37 266 70 25 19 224 224 224 480), lower := (rows 37 266 70 25 19 32 64 128 256), losses := [] }

theorem u38865 : Upper (D 7) (R 7) [36,264,66,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38866 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 266 70 25 49 226 194 194 450), lower := (rows 37 266 70 25 49 32 64 128 256), losses := [] }

theorem u38866 : Upper (D 7) (R 7) [36,264,66,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38867 : Route 9 := (fun mask => (mask,id))

def c38867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38867 : Upper (D 7) (R 7) [36,264,66,17,34] 13 := by
  apply FastRouting.sound _ _ [36,264,66,17,34] 13 (by decide) (choices 1) [1,64,128] r38867 c38867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26424
  · exact u26425
  · exact u26426

def b38868 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 70 25 81 162 226 162 418), lower := (rows 37 266 70 25 81 32 64 128 256), losses := [] }

theorem u38868 : Upper (D 7) (R 7) [36,264,66,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38869 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 266 70 25 82 161 225 161 417), lower := (rows 37 266 70 25 82 32 64 128 256), losses := [] }

theorem u38869 : Upper (D 7) (R 7) [36,264,66,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38870 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 2, region := 161, targets := 64 },{ cop := 3, region := 386, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(2,5)], upper := (rows 37 266 70 25 112 163 195 131 387), lower := (rows 37 266 70 25 112 32 64 128 256), losses := [] }

theorem u38870 : Upper (D 7) (R 7) [36,264,66,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38871 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 266 70 25 145 226 226 226 482), lower := (rows 37 266 70 25 145 32 64 128 256), losses := [] }

theorem u38871 : Upper (D 7) (R 7) [36,264,66,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38872 : Route 9 := (fun mask => (mask,id))

def c38872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38872 : Upper (D 7) (R 7) [36,264,66,17,130] 13 := by
  apply FastRouting.sound _ _ [36,264,66,17,130] 13 (by decide) (choices 1) [1,64,128] r38872 c38872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26427
  · exact u26428
  · exact u26429

def r38873 : Route 9 := (fun mask => (mask,id))

def c38873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38873 : Upper (D 7) (R 7) [36,264,66,17,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,17,160] 13 (by decide) (choices 1) [1,2,64,128] r38873 c38873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26430
  · exact u26431
  · exact u26432
  · exact u26433

def r38874 : Route 9 := (fun mask => (mask,id))

def c38874 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38874 : Upper (D 7) (R 7) [36,264,66,17,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,17,192] 13 (by decide) (choices 1) [1,2,128] r38874 c38874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26434
  · exact u26435
  · exact u26436

def b38875 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 266 70 26 49 225 193 193 449), lower := (rows 37 266 70 26 49 32 64 128 256), losses := [] }

theorem u38875 : Upper (D 7) (R 7) [36,264,66,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38876 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 266 70 26 81 161 225 161 417), lower := (rows 37 266 70 26 81 32 64 128 256), losses := [] }

theorem u38876 : Upper (D 7) (R 7) [36,264,66,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38877 : Route 9 := (fun mask => (mask,id))

def c38877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38877 : Upper (D 7) (R 7) [36,264,66,18,96] 13 := by
  apply FastRouting.sound _ _ [36,264,66,18,96] 13 (by decide) (choices 1) [1,128] r38877 c38877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26437
  · exact u26438

def r38878 : Route 9 := (fun mask => (mask,id))

def c38878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38878 : Upper (D 7) (R 7) [36,264,66,18,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,18,129] 13 (by decide) (choices 1) [1,64,128] r38878 c38878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26439
  · exact u26440
  · exact u26441

def r38879 : Route 9 := (fun mask => (mask,id))

def c38879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38879 : Upper (D 7) (R 7) [36,264,66,18,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,18,160] 13 (by decide) (choices 1) [1,64,128] r38879 c38879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26442
  · exact u26443
  · exact u26444

#print axioms u38879
end Delivery.IrregularNine14.P07
