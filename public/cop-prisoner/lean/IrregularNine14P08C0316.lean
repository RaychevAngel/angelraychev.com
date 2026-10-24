import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0125
import IrregularNine14P08C0126
import IrregularNine14P08C0127
import IrregularNine14P08C0128

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18960 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 73 433 433 497 433 433), lower := (rows 7 42 196 73 16 32 64 128 256), losses := [] }

theorem u18960 : Upper (D 8) (R 8) [6,40,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18961 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 88 433 417 481 417 417), lower := (rows 7 42 196 88 16 32 64 128 256), losses := [] }

theorem u18961 : Upper (D 8) (R 8) [6,40,192,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18962 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 196 104 433 433 497 433 433), lower := (rows 7 42 196 104 16 32 64 128 256), losses := [] }

theorem u18962 : Upper (D 8) (R 8) [6,40,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18963 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 42 196 200 305 305 369 433 305), lower := (rows 7 42 196 200 16 32 64 128 256), losses := [] }

theorem u18963 : Upper (D 8) (R 8) [6,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18964 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18964 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18964 : Upper (D 8) (R 8) [6,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257] 13 (by decide) (choices 2) [33,65,96,192] r18964 c18964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7539
  · exact u7540
  · exact u7541
  · exact u7542

def r18965 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18965 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18965 : Upper (D 8) (R 8) [6,40,192,272] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272] 13 (by decide) (choices 2) [33,65,96,192] r18965 c18965
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7543
  · exact u7544
  · exact u7545
  · exact u7546

def b18966 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 196 296 241 241 241 241 497), lower := (rows 7 42 196 296 16 32 64 128 256), losses := [] }

theorem u18966 : Upper (D 8) (R 8) [6,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18967 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 328 177 177 241 177 433), lower := (rows 7 42 196 328 16 32 64 128 256), losses := [] }

theorem u18967 : Upper (D 8) (R 8) [6,40,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18968 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 25 240 224 224 224 480), lower := (rows 7 42 261 25 16 32 64 128 256), losses := [] }

theorem u18968 : Upper (D 8) (R 8) [6,40,257,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18969 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 41 240 240 240 240 496), lower := (rows 7 42 261 41 16 32 64 128 256), losses := [] }

theorem u18969 : Upper (D 8) (R 8) [6,40,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18970 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 56 241 225 225 225 481), lower := (rows 7 42 261 56 16 32 64 128 256), losses := [] }

theorem u18970 : Upper (D 8) (R 8) [6,40,257,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18971 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 73 240 240 240 240 496), lower := (rows 7 42 261 73 16 32 64 128 256), losses := [] }

theorem u18971 : Upper (D 8) (R 8) [6,40,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18972 : Route 9 := (fun mask => (mask,id))

def c18972 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18972 : Upper (D 8) (R 8) [6,40,257,80] 13 := by
  apply FastRouting.sound _ _ [6,40,257,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18972 c18972
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7547
  · exact u7548
  · exact u7549
  · exact u7550
  · exact u7551
  · exact u7552

def b18973 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 104 241 241 241 241 497), lower := (rows 7 42 261 104 16 32 64 128 256), losses := [] }

theorem u18973 : Upper (D 8) (R 8) [6,40,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18974 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18974 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18974 : Upper (D 8) (R 8) [6,40,257,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192] 13 (by decide) (choices 2) [33,65,96,192] r18974 c18974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7553
  · exact u7554
  · exact u7555
  · exact u7556

def b18975 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 276 41 241 225 225 225 481), lower := (rows 7 42 276 41 16 32 64 128 256), losses := [] }

theorem u18975 : Upper (D 8) (R 8) [6,40,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18976 : Route 9 := (fun mask => (mask,id))

def c18976 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18976 : Upper (D 8) (R 8) [6,40,272,65] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18976 c18976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7557
  · exact u7558
  · exact u7559
  · exact u7560
  · exact u7561
  · exact u7562

def b18977 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 276 104 241 225 225 225 481), lower := (rows 7 42 276 104 16 32 64 128 256), losses := [] }

theorem u18977 : Upper (D 8) (R 8) [6,40,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18978 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18978 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18978 : Upper (D 8) (R 8) [6,40,272,192] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192] 13 (by decide) (choices 2) [33,65,96,192] r18978 c18978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7563
  · exact u7564
  · exact u7565
  · exact u7566

def r18979 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18979 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18979 : Upper (D 8) (R 8) [6,40,288,17] 13 := by
  apply FastRouting.sound _ _ [6,40,288,17] 13 (by decide) (choices 2) [33,65,96,192] r18979 c18979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7567
  · exact u7568
  · exact u7569
  · exact u7570

def b18980 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 41 209 241 209 209 465), lower := (rows 7 42 292 41 16 32 64 128 256), losses := [] }

theorem u18980 : Upper (D 8) (R 8) [6,40,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18981 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 292 56 209 225 193 193 449), lower := (rows 7 42 292 56 16 32 64 128 256), losses := [] }

theorem u18981 : Upper (D 8) (R 8) [6,40,288,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18982 : Route 9 := (fun mask => (mask,id))

def c18982 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18982 : Upper (D 8) (R 8) [6,40,288,65] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18982 c18982
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7571
  · exact u7572
  · exact u7573
  · exact u7574
  · exact u7575
  · exact u7576

def r18983 : Route 9 := (fun mask => (mask,id))

def c18983 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18983 : Upper (D 8) (R 8) [6,40,288,80] 13 := by
  apply FastRouting.sound _ _ [6,40,288,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18983 c18983
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7577
  · exact u7578
  · exact u7579
  · exact u7580
  · exact u7581
  · exact u7582

def b18984 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 292 104 209 241 209 209 465), lower := (rows 7 42 292 104 16 32 64 128 256), losses := [] }

theorem u18984 : Upper (D 8) (R 8) [6,40,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18985 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18985 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18985 : Upper (D 8) (R 8) [6,40,288,192] 13 := by
  apply FastRouting.sound _ _ [6,40,288,192] 13 (by decide) (choices 2) [33,65,96,192] r18985 c18985
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7583
  · exact u7584
  · exact u7585
  · exact u7586

def r18986 : Route 9 := (fun mask => (mask,id))

def c18986 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18986 : Upper (D 8) (R 8) [6,40,320,17] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18986 c18986
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7587
  · exact u7588
  · exact u7589
  · exact u7590
  · exact u7591
  · exact u7592

def b18987 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 41 241 241 241 241 497), lower := (rows 7 42 324 41 16 32 64 128 256), losses := [] }

theorem u18987 : Upper (D 8) (R 8) [6,40,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18988 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 56 241 225 225 225 481), lower := (rows 7 42 324 56 16 32 64 128 256), losses := [] }

theorem u18988 : Upper (D 8) (R 8) [6,40,320,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18989 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 73 177 177 241 177 433), lower := (rows 7 42 324 73 16 32 64 128 256), losses := [] }

theorem u18989 : Upper (D 8) (R 8) [6,40,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18990 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 324 88 177 161 225 161 417), lower := (rows 7 42 324 88 16 32 64 128 256), losses := [] }

theorem u18990 : Upper (D 8) (R 8) [6,40,320,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18991 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 104 177 177 241 177 433), lower := (rows 7 42 324 104 16 32 64 128 256), losses := [] }

theorem u18991 : Upper (D 8) (R 8) [6,40,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18992 : Route 9 := (fun mask => (mask,id))

def c18992 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18992 : Upper (D 8) (R 8) [6,40,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18992 c18992
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7593
  · exact u7594
  · exact u7595
  · exact u7596
  · exact u7597
  · exact u7598

def r18993 : Route 9 := (fun mask => (mask,id))

def c18993 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18993 : Upper (D 8) (R 8) [6,40,320,144] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18993 c18993
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7599
  · exact u7600
  · exact u7601
  · exact u7602
  · exact u7603
  · exact u7604

def b18994 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 168 241 241 241 241 497), lower := (rows 7 42 324 168 16 32 64 128 256), losses := [] }

theorem u18994 : Upper (D 8) (R 8) [6,40,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18995 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 324 200 177 177 241 177 433), lower := (rows 7 42 324 200 16 32 64 128 256), losses := [] }

theorem u18995 : Upper (D 8) (R 8) [6,40,320,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18996 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 25 496 480 480 480 480), lower := (rows 7 67 140 25 16 32 64 128 256), losses := [] }

theorem u18996 : Upper (D 8) (R 8) [6,65,136,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18997 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 41 496 496 496 496 496), lower := (rows 7 67 140 41 16 32 64 128 256), losses := [] }

theorem u18997 : Upper (D 8) (R 8) [6,65,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18998 : Route 9 := (fun mask => (mask,id))

def c18998 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18998 : Upper (D 8) (R 8) [6,65,136,48] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18998 c18998
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7605
  · exact u7606
  · exact u7607
  · exact u7608
  · exact u7609
  · exact u7610
  · exact u7611
  · exact u7612
  · exact u7613
  · exact u7614

def b18999 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 140 73 432 432 496 432 432), lower := (rows 7 67 140 73 16 32 64 128 256), losses := [] }

theorem u18999 : Upper (D 8) (R 8) [6,65,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19000 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 67 140 88 433 417 481 417 417), lower := (rows 7 67 140 88 16 32 64 128 256), losses := [] }

theorem u19000 : Upper (D 8) (R 8) [6,65,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19001 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 67 140 104 433 433 497 433 433), lower := (rows 7 67 140 104 16 32 64 128 256), losses := [] }

theorem u19001 : Upper (D 8) (R 8) [6,65,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19002 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 137 368 368 368 496 368), lower := (rows 7 67 140 137 16 32 64 128 256), losses := [] }

theorem u19002 : Upper (D 8) (R 8) [6,65,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19003 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 152 369 353 353 481 353), lower := (rows 7 67 140 152 16 32 64 128 256), losses := [] }

theorem u19003 : Upper (D 8) (R 8) [6,65,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19004 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 168 369 369 369 497 369), lower := (rows 7 67 140 168 16 32 64 128 256), losses := [] }

theorem u19004 : Upper (D 8) (R 8) [6,65,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19005 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 200 305 305 369 433 305), lower := (rows 7 67 140 200 16 32 64 128 256), losses := [] }

theorem u19005 : Upper (D 8) (R 8) [6,65,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19006 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 265 240 240 240 240 496), lower := (rows 7 67 140 265 16 32 64 128 256), losses := [] }

theorem u19006 : Upper (D 8) (R 8) [6,65,136,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19007 : Route 9 := (fun mask => (mask,id))

def c19007 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19007 : Upper (D 8) (R 8) [6,65,136,272] 13 := by
  apply FastRouting.sound _ _ [6,65,136,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19007 c19007
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7615
  · exact u7616
  · exact u7617
  · exact u7618
  · exact u7619
  · exact u7620

def r19008 : Route 9 := (fun mask => (mask,id))

def c19008 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19008 : Upper (D 8) (R 8) [6,65,136,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19008 c19008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7621
  · exact u7622
  · exact u7623
  · exact u7624
  · exact u7625
  · exact u7626

def b19009 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 67 140 328 177 177 241 177 433), lower := (rows 7 67 140 328 16 32 64 128 256), losses := [] }

theorem u19009 : Upper (D 8) (R 8) [6,65,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19010 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 392 113 113 113 241 369), lower := (rows 7 67 140 392 16 32 64 128 256), losses := [] }

theorem u19010 : Upper (D 8) (R 8) [6,65,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19011 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 25 504 488 488 488 488), lower := (rows 7 67 164 25 16 32 64 128 256), losses := [] }

theorem u19011 : Upper (D 8) (R 8) [6,65,160,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19012 : PairBound 9 := { available := 504, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 504 504 504 504 504), lower := (rows 7 67 164 41 16 32 64 128 256), losses := [] }

theorem u19012 : Upper (D 8) (R 8) [6,65,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19013_9 : Upper (D 8) (R 8) [6,65,160,48,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7627

theorem m19013_33 : Upper (D 8) (R 8) [6,65,160,48,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7636

def r19013 : Route 9 := (fun mask => (mask,id))

def c19013 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u19013 : Upper (D 8) (R 8) [6,65,160,48] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r19013 c19013
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19013_9
  · exact m19013_33
  · exact u7645
  · exact u7646
  · exact u7647
  · exact u7648
  · exact u7649
  · exact u7650
  · exact u7651
  · exact u7652
  · exact u7653
  · exact u7654
  · exact u7655
  · exact u7656
  · exact u7657

def b19014 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 73 440 440 504 440 440), lower := (rows 7 67 164 73 16 32 64 128 256), losses := [] }

theorem u19014 : Upper (D 8) (R 8) [6,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19015_9 : Upper (D 8) (R 8) [6,65,160,80,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7628

theorem m19015_33 : Upper (D 8) (R 8) [6,65,160,80,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7637

theorem m19015_40 : Upper (D 8) (R 8) [6,65,160,80,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7647

def r19015 : Route 9 := (fun mask => (mask,id))

def c19015 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19015 : Upper (D 8) (R 8) [6,65,160,80] 13 := by
  apply FastRouting.sound _ _ [6,65,160,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19015 c19015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19015_9
  · exact m19015_33
  · exact m19015_40
  · exact u7662
  · exact u7663
  · exact u7664
  · exact u7665
  · exact u7666
  · exact u7667
  · exact u7668

theorem m19016_9 : Upper (D 8) (R 8) [6,65,160,96,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7629

theorem m19016_33 : Upper (D 8) (R 8) [6,65,160,96,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7638

theorem m19016_40 : Upper (D 8) (R 8) [6,65,160,96,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7648

def r19016 : Route 9 := (fun mask => (mask,id))

def c19016 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19016 : Upper (D 8) (R 8) [6,65,160,96] 13 := by
  apply FastRouting.sound _ _ [6,65,160,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19016 c19016
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19016_9
  · exact m19016_33
  · exact m19016_40
  · exact u7669
  · exact u7670
  · exact u7671
  · exact u7672
  · exact u7673
  · exact u7674
  · exact u7675

def b19017 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 137 376 376 376 504 376), lower := (rows 7 67 164 137 16 32 64 128 256), losses := [] }

theorem u19017 : Upper (D 8) (R 8) [6,65,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19018_9 : Upper (D 8) (R 8) [6,65,160,144,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7630

theorem m19018_33 : Upper (D 8) (R 8) [6,65,160,144,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7639

theorem m19018_40 : Upper (D 8) (R 8) [6,65,160,144,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7650

theorem m19018_65 : Upper (D 8) (R 8) [6,65,160,144,65] 13 :=
  permutation_upper _ _ _ [6,65,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7658

theorem m19018_72 : Upper (D 8) (R 8) [6,65,160,144,72] 13 :=
  permutation_upper _ _ _ [6,65,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7663

theorem m19018_96 : Upper (D 8) (R 8) [6,65,160,144,96] 13 :=
  permutation_upper _ _ _ [6,65,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7670

def r19018 : Route 9 := (fun mask => (mask,id))

def c19018 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u19018 : Upper (D 8) (R 8) [6,65,160,144] 13 := by
  apply FastRouting.sound _ _ [6,65,160,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r19018 c19018
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19018_9
  · exact m19018_33
  · exact m19018_40
  · exact m19018_65
  · exact m19018_72
  · exact m19018_96
  · exact u7679
  · exact u7680
  · exact u7681
  · exact u7682

def b19019 : PairBound 9 := { available := 377, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 168 377 377 377 505 377), lower := (rows 7 67 164 168 16 32 64 128 256), losses := [] }

theorem u19019 : Upper (D 8) (R 8) [6,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u19019
end Delivery.IrregularNine14.P08
