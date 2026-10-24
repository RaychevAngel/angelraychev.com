import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0663
import IrregularNine14P06C0664
import IrregularNine14P06C0665
import IrregularNine14P06C0666
import IrregularNine14P06C0667

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b43440 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 262 104 87 119 87 215 343), lower := (rows 41 131 262 104 16 32 64 128 256), losses := [] }

theorem u43440 : Upper (D 6) (R 6) [40,129,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43441 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 41 131 276 11 118 102 102 230 358), lower := (rows 41 131 276 11 16 32 64 128 256), losses := [] }

theorem u43441 : Upper (D 6) (R 6) [40,129,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43442 : Route 9 := (fun mask => (mask,id))

def c43442 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43442 : Upper (D 6) (R 6) [40,129,272,5] 13 := by
  apply FastRouting.sound _ _ [40,129,272,5] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43442 c43442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39797
  · exact u39798
  · exact u39799
  · exact u39800
  · exact u39801
  · exact u39802

def r43443 : Route 9 := (fun mask => (mask,id))

def c43443 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43443 : Upper (D 6) (R 6) [40,129,272,6] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43443 c43443
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39803
  · exact u39804
  · exact u39805
  · exact u39806
  · exact u39807
  · exact u39808
  · exact u39809
  · exact u39810
  · exact u39811
  · exact u39812

def b43444 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 41 86 102 70 198 326), lower := (rows 41 131 276 41 16 32 64 128 256), losses := [] }

theorem u43444 : Upper (D 6) (R 6) [40,129,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43445 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 276 42 87 103 71 199 327), lower := (rows 41 131 276 42 16 32 64 128 256), losses := [] }

theorem u43445 : Upper (D 6) (R 6) [40,129,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43446 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 276 44 87 103 71 199 327), lower := (rows 41 131 276 44 16 32 64 128 256), losses := [] }

theorem u43446 : Upper (D 6) (R 6) [40,129,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43447 : Route 9 := (fun mask => (mask,id))

def c43447 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43447 : Upper (D 6) (R 6) [40,129,272,65] 13 := by
  apply FastRouting.sound _ _ [40,129,272,65] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43447 c43447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39813
  · exact u39814
  · exact u39815
  · exact u39816
  · exact u39817
  · exact u39818

def r43448 : Route 9 := (fun mask => (mask,id))

def c43448 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43448 : Upper (D 6) (R 6) [40,129,272,66] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43448 c43448
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39819
  · exact u39820
  · exact u39821
  · exact u39822
  · exact u39823
  · exact u39824
  · exact u39825
  · exact u39826
  · exact u39827
  · exact u39828

def r43449 : Route 9 := (fun mask => (mask,id))

def c43449 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43449 : Upper (D 6) (R 6) [40,129,272,68] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43449 c43449
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39829
  · exact u39830
  · exact u39831
  · exact u39832
  · exact u39833
  · exact u39834
  · exact u39835
  · exact u39836
  · exact u39837
  · exact u39838

def b43450 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 276 104 87 103 71 199 327), lower := (rows 41 131 276 104 16 32 64 128 256), losses := [] }

theorem u43450 : Upper (D 6) (R 6) [40,129,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43451 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 41 131 292 11 86 118 86 214 342), lower := (rows 41 131 292 11 16 32 64 128 256), losses := [] }

theorem u43451 : Upper (D 6) (R 6) [40,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43452 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 292 13 86 118 86 214 342), lower := (rows 41 131 292 13 16 32 64 128 256), losses := [] }

theorem u43452 : Upper (D 6) (R 6) [40,129,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43453 : Route 9 := (fun mask => (mask,id))

def c43453 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43453 : Upper (D 6) (R 6) [40,129,288,6] 13 := by
  apply FastRouting.sound _ _ [40,129,288,6] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43453 c43453
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39839
  · exact u39840
  · exact u39841
  · exact u39842
  · exact u39843
  · exact u39844

def r43454 : Route 9 := (fun mask => (mask,id))

def c43454 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43454 : Upper (D 6) (R 6) [40,129,288,17] 13 := by
  apply FastRouting.sound _ _ [40,129,288,17] 13 (by decide) (choices 2) [6,66,68] r43454 c43454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39845
  · exact u39846
  · exact u39847

def r43455 : Route 9 := (fun mask => (mask,id))

def c43455 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43455 : Upper (D 6) (R 6) [40,129,288,18] 13 := by
  apply FastRouting.sound _ _ [40,129,288,18] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43455 c43455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39848
  · exact u39849
  · exact u39850
  · exact u39851
  · exact u39852
  · exact u39853

def r43456 : Route 9 := (fun mask => (mask,id))

def c43456 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43456 : Upper (D 6) (R 6) [40,129,288,20] 13 := by
  apply FastRouting.sound _ _ [40,129,288,20] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43456 c43456
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39854
  · exact u39855
  · exact u39856
  · exact u39857
  · exact u39858
  · exact u39859

def r43457 : Route 9 := (fun mask => (mask,id))

def c43457 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43457 : Upper (D 6) (R 6) [40,129,288,65] 13 := by
  apply FastRouting.sound _ _ [40,129,288,65] 13 (by decide) (choices 2) [6,66,68] r43457 c43457
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39860
  · exact u39861
  · exact u39862

def r43458 : Route 9 := (fun mask => (mask,id))

def c43458 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43458 : Upper (D 6) (R 6) [40,129,288,66] 13 := by
  apply FastRouting.sound _ _ [40,129,288,66] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43458 c43458
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39863
  · exact u39864
  · exact u39865
  · exact u39866
  · exact u39867
  · exact u39868

def r43459 : Route 9 := (fun mask => (mask,id))

def c43459 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43459 : Upper (D 6) (R 6) [40,129,288,68] 13 := by
  apply FastRouting.sound _ _ [40,129,288,68] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43459 c43459
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39869
  · exact u39870
  · exact u39871
  · exact u39872
  · exact u39873
  · exact u39874

def r43460 : Route 9 := (fun mask => (mask,id))

def c43460 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43460 : Upper (D 6) (R 6) [40,129,288,80] 13 := by
  apply FastRouting.sound _ _ [40,129,288,80] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43460 c43460
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39875
  · exact u39876
  · exact u39877
  · exact u39878
  · exact u39879
  · exact u39880

def b43461 : PairBound 9 := { available := 118, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 41 131 324 11 118 118 118 246 374), lower := (rows 41 131 324 11 16 32 64 128 256), losses := [] }

theorem u43461 : Upper (D 6) (R 6) [40,129,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43462 : Route 9 := (fun mask => (mask,id))

def c43462 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43462 : Upper (D 6) (R 6) [40,129,320,5] 13 := by
  apply FastRouting.sound _ _ [40,129,320,5] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43462 c43462
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39881
  · exact u39882
  · exact u39883
  · exact u39884
  · exact u39885
  · exact u39886

def r43463 : Route 9 := (fun mask => (mask,id))

def c43463 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43463 : Upper (D 6) (R 6) [40,129,320,6] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43463 c43463
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39887
  · exact u39888
  · exact u39889
  · exact u39890
  · exact u39891
  · exact u39892
  · exact u39893
  · exact u39894
  · exact u39895
  · exact u39896

def r43464 : Route 9 := (fun mask => (mask,id))

def c43464 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43464 : Upper (D 6) (R 6) [40,129,320,17] 13 := by
  apply FastRouting.sound _ _ [40,129,320,17] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43464 c43464
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39897
  · exact u39898
  · exact u39899
  · exact u39900
  · exact u39901
  · exact u39902

def r43465 : Route 9 := (fun mask => (mask,id))

def c43465 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43465 : Upper (D 6) (R 6) [40,129,320,18] 13 := by
  apply FastRouting.sound _ _ [40,129,320,18] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43465 c43465
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39903
  · exact u39904
  · exact u39905
  · exact u39906
  · exact u39907
  · exact u39908
  · exact u39909
  · exact u39910
  · exact u39911
  · exact u39912

def r43466 : Route 9 := (fun mask => (mask,id))

def c43466 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43466 : Upper (D 6) (R 6) [40,129,320,20] 13 := by
  apply FastRouting.sound _ _ [40,129,320,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43466 c43466
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39913
  · exact u39914
  · exact u39915
  · exact u39916
  · exact u39917
  · exact u39918
  · exact u39919
  · exact u39920
  · exact u39921
  · exact u39922

def b43467 : PairBound 9 := { available := 86, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 41 86 118 86 214 342), lower := (rows 41 131 324 41 16 32 64 128 256), losses := [] }

theorem u43467 : Upper (D 6) (R 6) [40,129,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43468 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 324 42 87 119 87 215 343), lower := (rows 41 131 324 42 16 32 64 128 256), losses := [] }

theorem u43468 : Upper (D 6) (R 6) [40,129,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43469 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 324 44 87 119 87 215 343), lower := (rows 41 131 324 44 16 32 64 128 256), losses := [] }

theorem u43469 : Upper (D 6) (R 6) [40,129,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43470 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 324 56 87 103 71 199 327), lower := (rows 41 131 324 56 16 32 64 128 256), losses := [] }

theorem u43470 : Upper (D 6) (R 6) [40,129,320,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43471 : Route 9 := (fun mask => (mask,id))

def c43471 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43471 : Upper (D 6) (R 6) [40,129,320,65] 13 := by
  apply FastRouting.sound _ _ [40,129,320,65] 13 (by decide) (choices 2) [6,34,36] r43471 c43471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39923
  · exact u39924
  · exact u39925

def r43472 : Route 9 := (fun mask => (mask,id))

def c43472 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43472 : Upper (D 6) (R 6) [40,129,320,66] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43472 c43472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39926
  · exact u39927
  · exact u39928
  · exact u39929
  · exact u39930
  · exact u39931

def b43473 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 324 76 55 55 119 183 311), lower := (rows 41 131 324 76 16 32 64 128 256), losses := [] }

theorem u43473 : Upper (D 6) (R 6) [40,129,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43474 : Route 9 := (fun mask => (mask,id))

def c43474 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43474 : Upper (D 6) (R 6) [40,129,320,80] 13 := by
  apply FastRouting.sound _ _ [40,129,320,80] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43474 c43474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39932
  · exact u39933
  · exact u39934
  · exact u39935
  · exact u39936
  · exact u39937

def b43475 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 131 324 104 23 55 87 151 279), lower := (rows 41 131 324 104 16 32 64 128 256), losses := [] }

theorem u43475 : Upper (D 6) (R 6) [40,129,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43476 : Route 9 := (fun mask => (mask,id))

def c43476 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43476 : Upper (D 6) (R 6) [40,132,258,3] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43476 c43476
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39938
  · exact u39939
  · exact u39940
  · exact u39941
  · exact u39942
  · exact u39943

def b43477 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 134 262 14 113 113 113 241 369), lower := (rows 41 134 262 14 16 32 64 128 256), losses := [] }

theorem u43477 : Upper (D 6) (R 6) [40,132,258,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43478_5 : Upper (D 6) (R 6) [40,132,258,17,5] 13 :=
  permutation_upper _ _ _ [40,132,258,17,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39944

theorem m43478_36 : Upper (D 6) (R 6) [40,132,258,17,36] 13 :=
  permutation_upper _ _ _ [40,132,258,17,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39947

theorem m43478_68 : Upper (D 6) (R 6) [40,132,258,17,68] 13 :=
  permutation_upper _ _ _ [40,132,258,17,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39949

def r43478 : Route 9 := (fun mask => (mask,id))

def c43478 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43478 : Upper (D 6) (R 6) [40,132,258,17] 13 := by
  apply FastRouting.sound _ _ [40,132,258,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43478 c43478
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39944
  · exact m43478_5
  · exact u39945
  · exact u39946
  · exact u39947
  · exact m43478_36
  · exact u39948
  · exact u39949
  · exact m43478_68
  · exact u39950

def r43479 : Route 9 := (fun mask => (mask,id))

def c43479 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43479 : Upper (D 6) (R 6) [40,132,258,18] 13 := by
  apply FastRouting.sound _ _ [40,132,258,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43479 c43479
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39951
  · exact u39952
  · exact u39953
  · exact u39954
  · exact u39955
  · exact u39956

def b43480 : PairBound 9 := { available := 87, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 41 87 119 87 215 343), lower := (rows 41 134 262 41 16 32 64 128 256), losses := [] }

theorem u43480 : Upper (D 6) (R 6) [40,132,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43481 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 262 42 85 117 85 213 341), lower := (rows 41 134 262 42 16 32 64 128 256), losses := [] }

theorem u43481 : Upper (D 6) (R 6) [40,132,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43482 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 262 56 87 103 71 199 327), lower := (rows 41 134 262 56 16 32 64 128 256), losses := [] }

theorem u43482 : Upper (D 6) (R 6) [40,132,258,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43483_5 : Upper (D 6) (R 6) [40,132,258,65,5] 13 :=
  permutation_upper _ _ _ [40,132,258,65,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39957

theorem m43483_36 : Upper (D 6) (R 6) [40,132,258,65,36] 13 :=
  permutation_upper _ _ _ [40,132,258,65,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39960

theorem m43483_68 : Upper (D 6) (R 6) [40,132,258,65,68] 13 :=
  permutation_upper _ _ _ [40,132,258,65,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39962

def r43483 : Route 9 := (fun mask => (mask,id))

def c43483 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43483 : Upper (D 6) (R 6) [40,132,258,65] 13 := by
  apply FastRouting.sound _ _ [40,132,258,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43483 c43483
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39957
  · exact m43483_5
  · exact u39958
  · exact u39959
  · exact u39960
  · exact m43483_36
  · exact u39961
  · exact u39962
  · exact m43483_68
  · exact u39963

def r43484 : Route 9 := (fun mask => (mask,id))

def c43484 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43484 : Upper (D 6) (R 6) [40,132,258,66] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43484 c43484
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39964
  · exact u39965
  · exact u39966
  · exact u39967
  · exact u39968
  · exact u39969

theorem m43485_5 : Upper (D 6) (R 6) [40,132,258,80,5] 13 :=
  permutation_upper _ _ _ [40,132,258,80,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39970

theorem m43485_36 : Upper (D 6) (R 6) [40,132,258,80,36] 13 :=
  permutation_upper _ _ _ [40,132,258,80,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39973

theorem m43485_68 : Upper (D 6) (R 6) [40,132,258,80,68] 13 :=
  permutation_upper _ _ _ [40,132,258,80,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39975

def r43485 : Route 9 := (fun mask => (mask,id))

def c43485 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43485 : Upper (D 6) (R 6) [40,132,258,80] 13 := by
  apply FastRouting.sound _ _ [40,132,258,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43485 c43485
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39970
  · exact m43485_5
  · exact u39971
  · exact u39972
  · exact u39973
  · exact m43485_36
  · exact u39974
  · exact u39975
  · exact m43485_68
  · exact u39976

def b43486 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 262 104 87 119 87 215 343), lower := (rows 41 134 262 104 16 32 64 128 256), losses := [] }

theorem u43486 : Upper (D 6) (R 6) [40,132,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43487 : Route 9 := (fun mask => (mask,id))

def c43487 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43487 : Upper (D 6) (R 6) [40,132,272,3] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43487 c43487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39977
  · exact u39978
  · exact u39979
  · exact u39980
  · exact u39981
  · exact u39982
  · exact u39983
  · exact u39984
  · exact u39985
  · exact u39986

def r43488 : Route 9 := (fun mask => (mask,id))

def c43488 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43488 : Upper (D 6) (R 6) [40,132,272,5] 13 := by
  apply FastRouting.sound _ _ [40,132,272,5] 13 (by decide) (choices 2) [3,33,34,65,66,96] r43488 c43488
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39987
  · exact u39988
  · exact u39989
  · exact u39990
  · exact u39991
  · exact u39992

def b43489 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 134 276 14 115 99 99 227 355), lower := (rows 41 134 276 14 16 32 64 128 256), losses := [] }

theorem u43489 : Upper (D 6) (R 6) [40,132,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43490 : PairBound 9 := { available := 71, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 276 41 87 103 71 199 327), lower := (rows 41 134 276 41 16 32 64 128 256), losses := [] }

theorem u43490 : Upper (D 6) (R 6) [40,132,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43491 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 276 42 87 103 71 199 327), lower := (rows 41 134 276 42 16 32 64 128 256), losses := [] }

theorem u43491 : Upper (D 6) (R 6) [40,132,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43492 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 276 44 83 99 67 195 323), lower := (rows 41 134 276 44 16 32 64 128 256), losses := [] }

theorem u43492 : Upper (D 6) (R 6) [40,132,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43493 : Route 9 := (fun mask => (mask,id))

def c43493 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43493 : Upper (D 6) (R 6) [40,132,272,65] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43493 c43493
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39993
  · exact u39994
  · exact u39995
  · exact u39996
  · exact u39997
  · exact u39998
  · exact u39999
  · exact u40000
  · exact u40001
  · exact u40002

def r43494 : Route 9 := (fun mask => (mask,id))

def c43494 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43494 : Upper (D 6) (R 6) [40,132,272,66] 13 := by
  apply FastRouting.sound _ _ [40,132,272,66] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43494 c43494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40003
  · exact u40004
  · exact u40005
  · exact u40006
  · exact u40007
  · exact u40008
  · exact u40009
  · exact u40010
  · exact u40011
  · exact u40012

def r43495 : Route 9 := (fun mask => (mask,id))

def c43495 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43495 : Upper (D 6) (R 6) [40,132,272,68] 13 := by
  apply FastRouting.sound _ _ [40,132,272,68] 13 (by decide) (choices 2) [3,33,34,65,66,96] r43495 c43495
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40013
  · exact u40014
  · exact u40015
  · exact u40016
  · exact u40017
  · exact u40018

def b43496 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 276 104 87 103 71 199 327), lower := (rows 41 134 276 104 16 32 64 128 256), losses := [] }

theorem u43496 : Upper (D 6) (R 6) [40,132,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43497 : Route 9 := (fun mask => (mask,id))

def c43497 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43497 : Upper (D 6) (R 6) [40,132,288,3] 13 := by
  apply FastRouting.sound _ _ [40,132,288,3] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43497 c43497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40019
  · exact u40020
  · exact u40021
  · exact u40022
  · exact u40023
  · exact u40024

def b43498 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 292 13 83 115 83 211 339), lower := (rows 41 134 292 13 16 32 64 128 256), losses := [] }

theorem u43498 : Upper (D 6) (R 6) [40,132,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43499 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 134 292 14 83 115 83 211 339), lower := (rows 41 134 292 14 16 32 64 128 256), losses := [] }

theorem u43499 : Upper (D 6) (R 6) [40,132,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u43499
end Delivery.IrregularNine14.P06
