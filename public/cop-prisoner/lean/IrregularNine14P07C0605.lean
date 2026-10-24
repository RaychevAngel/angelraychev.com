import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0363
import IrregularNine14P07C0364
import IrregularNine14P07C0365

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36300 : Route 9 := (fun mask => (mask,id))

def c36300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36300 : Upper (D 7) (R 7) [34,320,10,80,132] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,132] 13 (by decide) (choices 1) [1,128] r36300 c36300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21803
  · exact u21804

def r36301 : Route 9 := (fun mask => (mask,id))

def c36301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36301 : Upper (D 7) (R 7) [34,320,10,80,160] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,160] 13 (by decide) (choices 1) [1,4,128] r36301 c36301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21805
  · exact u21806
  · exact u21807

def r36302 : Route 9 := (fun mask => (mask,id))

def c36302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36302 : Upper (D 7) (R 7) [34,320,10,96,129] 13 := by
  apply FastRouting.sound _ _ [34,320,10,96,129] 13 (by decide) (choices 1) [1,4,16,128] r36302 c36302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21808
  · exact u21809
  · exact u21810
  · exact u21811

def r36303 : Route 9 := (fun mask => (mask,id))

def c36303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36303 : Upper (D 7) (R 7) [34,320,10,96,132] 13 := by
  apply FastRouting.sound _ _ [34,320,10,96,132] 13 (by decide) (choices 1) [1,16,128] r36303 c36303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21812
  · exact u21813
  · exact u21814

def b36304 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 14 137 49 244 212 212 468), lower := (rows 35 322 14 137 49 32 64 128 256), losses := [] }

theorem u36304 : Upper (D 7) (R 7) [34,320,10,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36305 : Route 9 := (fun mask => (mask,id))

def c36305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36305 : Upper (D 7) (R 7) [34,320,10,129,36] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,36] 13 (by decide) (choices 1) [1,16,64,128] r36305 c36305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21815
  · exact u21816
  · exact u21817
  · exact u21818

def r36306 : Route 9 := (fun mask => (mask,id))

def c36306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36306 : Upper (D 7) (R 7) [34,320,10,129,65] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,65] 13 (by decide) (choices 1) [4,16,128] r36306 c36306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21819
  · exact u21820
  · exact u21821

def r36307 : Route 9 := (fun mask => (mask,id))

def c36307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36307 : Upper (D 7) (R 7) [34,320,10,129,68] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,68] 13 (by decide) (choices 1) [1,16,128] r36307 c36307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21822
  · exact u21823
  · exact u21824

def r36308 : Route 9 := (fun mask => (mask,id))

def c36308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36308 : Upper (D 7) (R 7) [34,320,10,129,96] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,96] 13 (by decide) (choices 1) [1,4,16,128] r36308 c36308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21825
  · exact u21826
  · exact u21827
  · exact u21828

def b36309 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 322 14 137 145 116 116 244 372), lower := (rows 35 322 14 137 145 32 64 128 256), losses := [] }

theorem u36309 : Upper (D 7) (R 7) [34,320,10,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36310 : Route 9 := (fun mask => (mask,id))

def c36310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36310 : Upper (D 7) (R 7) [34,320,10,129,132] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,132] 13 (by decide) (choices 1) [1,16,64] r36310 c36310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21829
  · exact u21830
  · exact u21831

def r36311 : Route 9 := (fun mask => (mask,id))

def c36311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36311 : Upper (D 7) (R 7) [34,320,10,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,160] 13 (by decide) (choices 1) [1,4,16,64] r36311 c36311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21832
  · exact u21833
  · exact u21834
  · exact u21835

def r36312 : Route 9 := (fun mask => (mask,id))

def c36312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36312 : Upper (D 7) (R 7) [34,320,10,129,192] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,192] 13 (by decide) (choices 1) [1,4,16] r36312 c36312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21836
  · exact u21837
  · exact u21838

def b36313 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 322 14 140 49 241 209 209 465), lower := (rows 35 322 14 140 49 32 64 128 256), losses := [] }

theorem u36313 : Upper (D 7) (R 7) [34,320,10,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36314 : Route 9 := (fun mask => (mask,id))

def c36314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36314 : Upper (D 7) (R 7) [34,320,10,132,65] 13 := by
  apply FastRouting.sound _ _ [34,320,10,132,65] 13 (by decide) (choices 1) [1,16,128] r36314 c36314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21839
  · exact u21840
  · exact u21841

def r36315 : Route 9 := (fun mask => (mask,id))

def c36315 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36315 : Upper (D 7) (R 7) [34,320,10,132,96] 13 := by
  apply FastRouting.sound _ _ [34,320,10,132,96] 13 (by decide) (choices 1) [1,16,128] r36315 c36315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21842
  · exact u21843
  · exact u21844

def r36316 : Route 9 := (fun mask => (mask,id))

def c36316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36316 : Upper (D 7) (R 7) [34,320,10,132,129] 13 := by
  apply FastRouting.sound _ _ [34,320,10,132,129] 13 (by decide) (choices 1) [1,16,64] r36316 c36316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21845
  · exact u21846
  · exact u21847

def r36317 : Route 9 := (fun mask => (mask,id))

def c36317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36317 : Upper (D 7) (R 7) [34,320,10,132,160] 13 := by
  apply FastRouting.sound _ _ [34,320,10,132,160] 13 (by decide) (choices 1) [1,16,64] r36317 c36317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21848
  · exact u21849
  · exact u21850

def r36318 : Route 9 := (fun mask => (mask,id))

def c36318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36318 : Upper (D 7) (R 7) [34,320,10,132,192] 13 := by
  apply FastRouting.sound _ _ [34,320,10,132,192] 13 (by decide) (choices 1) [1,16] r36318 c36318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21851
  · exact u21852

def b36319 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 14 152 49 229 197 197 453), lower := (rows 35 322 14 152 49 32 64 128 256), losses := [] }

theorem u36319 : Upper (D 7) (R 7) [34,320,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36320 : Route 9 := (fun mask => (mask,id))

def c36320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36320 : Upper (D 7) (R 7) [34,320,10,144,36] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,36] 13 (by decide) (choices 1) [1,64,128] r36320 c36320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21853
  · exact u21854
  · exact u21855

def r36321 : Route 9 := (fun mask => (mask,id))

def c36321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36321 : Upper (D 7) (R 7) [34,320,10,144,65] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,65] 13 (by decide) (choices 1) [1,4,128] r36321 c36321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21856
  · exact u21857
  · exact u21858

def r36322 : Route 9 := (fun mask => (mask,id))

def c36322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36322 : Upper (D 7) (R 7) [34,320,10,144,68] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,68] 13 (by decide) (choices 1) [1,128] r36322 c36322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21859
  · exact u21860

def r36323 : Route 9 := (fun mask => (mask,id))

def c36323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36323 : Upper (D 7) (R 7) [34,320,10,144,96] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,96] 13 (by decide) (choices 1) [1,4,128] r36323 c36323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21861
  · exact u21862
  · exact u21863

def b36324 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 14 152 145 101 101 229 357), lower := (rows 35 322 14 152 145 32 64 128 256), losses := [] }

theorem u36324 : Upper (D 7) (R 7) [34,320,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36325 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 14 152 148 97 97 225 353), lower := (rows 35 322 14 152 148 32 64 128 256), losses := [] }

theorem u36325 : Upper (D 7) (R 7) [34,320,10,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36326 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 14 152 176 101 69 197 325), lower := (rows 35 322 14 152 176 32 64 128 256), losses := [] }

theorem u36326 : Upper (D 7) (R 7) [34,320,10,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36327 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 14 152 208 37 101 165 293), lower := (rows 35 322 14 152 208 32 64 128 256), losses := [] }

theorem u36327 : Upper (D 7) (R 7) [34,320,10,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36328 : Route 9 := (fun mask => (mask,id))

def c36328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36328 : Upper (D 7) (R 7) [34,320,10,160,65] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,65] 13 (by decide) (choices 1) [1,4,16,128] r36328 c36328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21864
  · exact u21865
  · exact u21866
  · exact u21867

def r36329 : Route 9 := (fun mask => (mask,id))

def c36329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36329 : Upper (D 7) (R 7) [34,320,10,160,68] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,68] 13 (by decide) (choices 1) [1,16,128] r36329 c36329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21868
  · exact u21869
  · exact u21870

def r36330 : Route 9 := (fun mask => (mask,id))

def c36330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36330 : Upper (D 7) (R 7) [34,320,10,160,129] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,129] 13 (by decide) (choices 1) [1,4,16,64] r36330 c36330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21871
  · exact u21872
  · exact u21873
  · exact u21874

def r36331 : Route 9 := (fun mask => (mask,id))

def c36331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36331 : Upper (D 7) (R 7) [34,320,10,160,132] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,132] 13 (by decide) (choices 1) [1,16,64] r36331 c36331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21875
  · exact u21876
  · exact u21877

def r36332 : Route 9 := (fun mask => (mask,id))

def c36332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36332 : Upper (D 7) (R 7) [34,320,10,160,192] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,192] 13 (by decide) (choices 1) [1,4,16] r36332 c36332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21878
  · exact u21879
  · exact u21880

def b36333 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 322 14 200 49 181 213 149 405), lower := (rows 35 322 14 200 49 32 64 128 256), losses := [] }

theorem u36333 : Upper (D 7) (R 7) [34,320,10,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36334 : Route 9 := (fun mask => (mask,id))

def c36334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36334 : Upper (D 7) (R 7) [34,320,10,192,36] 13 := by
  apply FastRouting.sound _ _ [34,320,10,192,36] 13 (by decide) (choices 1) [1,16,128] r36334 c36334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21881
  · exact u21882
  · exact u21883

def r36335 : Route 9 := (fun mask => (mask,id))

def c36335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36335 : Upper (D 7) (R 7) [34,320,10,192,129] 13 := by
  apply FastRouting.sound _ _ [34,320,10,192,129] 13 (by decide) (choices 1) [1,4,16] r36335 c36335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21884
  · exact u21885
  · exact u21886

def b36336 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 14 200 148 49 113 177 305), lower := (rows 35 322 14 200 148 32 64 128 256), losses := [] }

theorem u36336 : Upper (D 7) (R 7) [34,320,10,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36337 : Route 9 := (fun mask => (mask,id))

def c36337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36337 : Upper (D 7) (R 7) [34,320,10,192,160] 13 := by
  apply FastRouting.sound _ _ [34,320,10,192,160] 13 (by decide) (choices 1) [1,4,16] r36337 c36337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21887
  · exact u21888
  · exact u21889

def b36338 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 322 28 41 81 166 198 134 390), lower := (rows 35 322 28 41 81 32 64 128 256), losses := [] }

theorem u36338 : Upper (D 7) (R 7) [34,320,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36339 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 322 28 41 84 163 195 131 387), lower := (rows 35 322 28 41 84 32 64 128 256), losses := [] }

theorem u36339 : Upper (D 7) (R 7) [34,320,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36340 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 322 28 41 145 230 198 198 454), lower := (rows 35 322 28 41 145 32 64 128 256), losses := [] }

theorem u36340 : Upper (D 7) (R 7) [34,320,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36341 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 322 28 41 146 229 197 197 453), lower := (rows 35 322 28 41 146 32 64 128 256), losses := [] }

theorem u36341 : Upper (D 7) (R 7) [34,320,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36342 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 322 28 41 148 227 195 195 451), lower := (rows 35 322 28 41 148 32 64 128 256), losses := [] }

theorem u36342 : Upper (D 7) (R 7) [34,320,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36343 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 322 28 41 208 167 199 135 391), lower := (rows 35 322 28 41 208 32 64 128 256), losses := [] }

theorem u36343 : Upper (D 7) (R 7) [34,320,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36344 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 322 28 42 81 165 197 133 389), lower := (rows 35 322 28 42 81 32 64 128 256), losses := [] }

theorem u36344 : Upper (D 7) (R 7) [34,320,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36345 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(3,0),(3,6)], upper := (rows 35 322 28 42 84 161 193 129 385), lower := (rows 35 322 28 42 84 32 64 128 256), losses := [] }

theorem u36345 : Upper (D 7) (R 7) [34,320,24,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36346 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 322 28 42 145 229 197 197 453), lower := (rows 35 322 28 42 145 32 64 128 256), losses := [] }

theorem u36346 : Upper (D 7) (R 7) [34,320,24,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36347 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 322 28 42 148 225 193 193 449), lower := (rows 35 322 28 42 148 32 64 128 256), losses := [] }

theorem u36347 : Upper (D 7) (R 7) [34,320,24,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36348 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 322 28 42 208 165 197 133 389), lower := (rows 35 322 28 42 208 32 64 128 256), losses := [] }

theorem u36348 : Upper (D 7) (R 7) [34,320,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36349 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(2,6),(4,5)], upper := (rows 35 322 28 44 81 163 195 131 387), lower := (rows 35 322 28 44 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 35 0 131 259), good := (rows 419 419 28 44 445 32 0 128 256) }] }

theorem u36349 : Upper (D 7) (R 7) [34,320,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36350 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 28 44 82 161 193 129 385), lower := (rows 35 322 28 44 82 32 64 128 256), losses := [] }

theorem u36350 : Upper (D 7) (R 7) [34,320,24,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36351 : Route 9 := (fun mask => (mask,id))

def c36351 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36351 : Upper (D 7) (R 7) [34,320,24,36,129] 13 := by
  apply FastRouting.sound _ _ [34,320,24,36,129] 13 (by decide) (choices 1) [1,2,64,128] r36351 c36351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21890
  · exact u21891
  · exact u21892
  · exact u21893

def r36352 : Route 9 := (fun mask => (mask,id))

def c36352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36352 : Upper (D 7) (R 7) [34,320,24,36,130] 13 := by
  apply FastRouting.sound _ _ [34,320,24,36,130] 13 (by decide) (choices 1) [1,64,128] r36352 c36352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21894
  · exact u21895
  · exact u21896

def r36353 : Route 9 := (fun mask => (mask,id))

def c36353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36353 : Upper (D 7) (R 7) [34,320,24,36,192] 13 := by
  apply FastRouting.sound _ _ [34,320,24,36,192] 13 (by decide) (choices 1) [1,2,128] r36353 c36353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21897
  · exact u21898
  · exact u21899

def r36354 : Route 9 := (fun mask => (mask,id))

def c36354 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36354 : Upper (D 7) (R 7) [34,320,24,65,129] 13 := by
  apply FastRouting.sound _ _ [34,320,24,65,129] 13 (by decide) (choices 1) [2,4,128] r36354 c36354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21900
  · exact u21901
  · exact u21902

def r36355 : Route 9 := (fun mask => (mask,id))

def c36355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36355 : Upper (D 7) (R 7) [34,320,24,65,130] 13 := by
  apply FastRouting.sound _ _ [34,320,24,65,130] 13 (by decide) (choices 1) [1,4,128] r36355 c36355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21903
  · exact u21904
  · exact u21905

def r36356 : Route 9 := (fun mask => (mask,id))

def c36356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36356 : Upper (D 7) (R 7) [34,320,24,65,132] 13 := by
  apply FastRouting.sound _ _ [34,320,24,65,132] 13 (by decide) (choices 1) [1,2,128] r36356 c36356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21906
  · exact u21907
  · exact u21908

def r36357 : Route 9 := (fun mask => (mask,id))

def c36357 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36357 : Upper (D 7) (R 7) [34,320,24,65,160] 13 := by
  apply FastRouting.sound _ _ [34,320,24,65,160] 13 (by decide) (choices 1) [1,2,4,128] r36357 c36357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21909
  · exact u21910
  · exact u21911
  · exact u21912

def b36358 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 28 74 145 165 229 165 421), lower := (rows 35 322 28 74 145 32 64 128 256), losses := [] }

theorem u36358 : Upper (D 7) (R 7) [34,320,24,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36359 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 28 74 148 161 225 161 417), lower := (rows 35 322 28 74 148 32 64 128 256), losses := [] }

theorem u36359 : Upper (D 7) (R 7) [34,320,24,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36359
end Delivery.IrregularNine14.P07
