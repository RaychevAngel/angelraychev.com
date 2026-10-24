import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0143
import IrregularNine14P06C0144

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27300 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 40, targets := 65 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(3,0),(3,6)], upper := (rows 97 131 268 44 22 34 81 209 337), lower := (rows 97 131 268 44 22 34 64 128 256), losses := [] }

theorem u27300 : Upper (D 6) (R 6) [96,129,264,36,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27301 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 97 131 268 44 22 48 67 195 323), lower := (rows 97 131 268 44 22 48 64 128 256), losses := [] }

theorem u27301 : Upper (D 6) (R 6) [96,129,264,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27301 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27302 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 44 22 96 83 147 275), lower := (rows 97 131 268 44 22 96 64 128 256), losses := [] }

theorem u27302 : Upper (D 6) (R 6) [96,129,264,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27303 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(2,6)], upper := (rows 97 131 268 44 82 33 86 150 278), lower := (rows 97 131 268 44 82 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 144 272), good := (rows 33 163 268 44 446 33 0 128 256) }] }

theorem u27303 : Upper (D 6) (R 6) [96,129,264,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27304 : Route 9 := (fun mask => (mask,id))

def c27304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27304 : Upper (D 6) (R 6) [96,129,264,36,66,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,36,66,2] 13 (by decide) (choices 1) [1,4,16] r27304 c27304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8602
  · exact u8603
  · exact u8604

def b27305 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 268 44 82 36 83 147 275), lower := (rows 97 131 268 44 82 36 64 128 256), losses := [] }

theorem u27305 : Upper (D 6) (R 6) [96,129,264,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27306 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 268 44 82 48 71 135 263), lower := (rows 97 131 268 44 82 48 64 128 256), losses := [] }

theorem u27306 : Upper (D 6) (R 6) [96,129,264,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27306 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27307 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 41, targets := 2 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 131 268 44 84 33 82 146 274), lower := (rows 97 131 268 44 84 33 64 128 256), losses := [] }

theorem u27307 : Upper (D 6) (R 6) [96,129,264,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27308 : Route 9 := (fun mask => (mask,id))

def c27308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27308 : Upper (D 6) (R 6) [96,129,264,36,68,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,36,68,2] 13 (by decide) (choices 1) [1,2,16] r27308 c27308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8605
  · exact u8606
  · exact u8607

def b27309 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 268 44 84 48 67 131 259), lower := (rows 97 131 268 44 84 48 64 128 256), losses := [] }

theorem u27309 : Upper (D 6) (R 6) [96,129,264,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27309 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27310 : Route 9 := (fun mask => (mask,id))

def c27310 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27310 : Upper (D 6) (R 6) [96,129,264,48,5,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,48,5,2] 13 (by decide) (choices 1) [2,4] r27310 c27310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8608
  · exact u8609

def b27311 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 131 268 56 21 36 66 194 322), lower := (rows 97 131 268 56 21 36 64 128 256), losses := [] }

theorem u27311 : Upper (D 6) (R 6) [96,129,264,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27312 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 56 21 96 70 134 262), lower := (rows 97 131 268 56 21 96 64 128 256), losses := [] }

theorem u27312 : Upper (D 6) (R 6) [96,129,264,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27313 : PairBound 9 := { available := 70, camps := [{ cop := 6, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(2,0)], upper := (rows 97 131 268 56 22 33 70 198 326), lower := (rows 97 131 268 56 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 80 144 272), good := (rows 96 130 268 508 470 32 64 128 256) }] }

theorem u27313 : Upper (D 6) (R 6) [96,129,264,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27314 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 131 268 56 22 34 69 197 325), lower := (rows 97 131 268 56 22 34 64 128 256), losses := [] }

theorem u27314 : Upper (D 6) (R 6) [96,129,264,48,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27315 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 131 268 56 22 36 67 195 323), lower := (rows 97 131 268 56 22 36 64 128 256), losses := [] }

theorem u27315 : Upper (D 6) (R 6) [96,129,264,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27316 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 56 22 96 71 135 263), lower := (rows 97 131 268 56 22 96 64 128 256), losses := [] }

theorem u27316 : Upper (D 6) (R 6) [96,129,264,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27317 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 131 268 56 82 33 70 134 262), lower := (rows 97 131 268 56 82 33 64 128 256), losses := [] }

theorem u27317 : Upper (D 6) (R 6) [96,129,264,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27318 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 325, targets := 2 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 97 131 268 56 82 34 69 133 261), lower := (rows 97 131 268 56 82 34 64 128 256), losses := [] }

theorem u27318 : Upper (D 6) (R 6) [96,129,264,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27319 : Route 9 := (fun mask => (mask,id))

def c27319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27319 : Upper (D 6) (R 6) [96,129,264,48,66,4] 13 := by
  apply FastRouting.sound _ _ [96,129,264,48,66,4] 13 (by decide) (choices 1) [1,2,4] r27319 c27319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8610
  · exact u8611
  · exact u8612

def b27320 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 131 268 56 84 33 70 134 262), lower := (rows 97 131 268 56 84 33 64 128 256), losses := [] }

theorem u27320 : Upper (D 6) (R 6) [96,129,264,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27321 : Route 9 := (fun mask => (mask,id))

def c27321 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27321 : Upper (D 6) (R 6) [96,129,264,48,68,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,48,68,2] 13 (by decide) (choices 1) [1,2,4] r27321 c27321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8613
  · exact u8614
  · exact u8615

def b27322 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 36 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,2),(1,5),(3,0)], upper := (rows 97 131 268 56 84 36 67 131 259), lower := (rows 97 131 268 56 84 36 64 128 256), losses := [] }

theorem u27322 : Upper (D 6) (R 6) [96,129,264,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27323 : Route 9 := (fun mask => (mask,id))

def c27323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27323 : Upper (D 6) (R 6) [96,129,288,5,6,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,5,6,2] 13 (by decide) (choices 1) [8,16] r27323 c27323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8616
  · exact u8617

def b27324 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 97 131 292 13 22 40 82 210 338), lower := (rows 97 131 292 13 22 40 64 128 256), losses := [] }

theorem u27324 : Upper (D 6) (R 6) [96,129,288,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27324 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27325 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 97 131 292 13 22 48 74 202 330), lower := (rows 97 131 292 13 22 48 64 128 256), losses := [] }

theorem u27325 : Upper (D 6) (R 6) [96,129,288,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27325 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27326 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 292 13 22 96 90 154 282), lower := (rows 97 131 292 13 22 96 64 128 256), losses := [] }

theorem u27326 : Upper (D 6) (R 6) [96,129,288,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27327 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 97 131 292 13 82 34 92 156 284), lower := (rows 97 131 292 13 82 34 64 128 256), losses := [] }

theorem u27327 : Upper (D 6) (R 6) [96,129,288,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27328 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 97 131 292 13 82 36 90 154 282), lower := (rows 97 131 292 13 82 36 64 128 256), losses := [] }

theorem u27328 : Upper (D 6) (R 6) [96,129,288,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27329 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 97 131 292 13 82 40 86 150 278), lower := (rows 97 131 292 13 82 40 64 128 256), losses := [] }

theorem u27329 : Upper (D 6) (R 6) [96,129,288,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27329 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27330 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 13 82 48 78 142 270), lower := (rows 97 131 292 13 82 48 64 128 256), losses := [] }

theorem u27330 : Upper (D 6) (R 6) [96,129,288,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27330 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27331 : Route 9 := (fun mask => (mask,id))

def c27331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27331 : Upper (D 6) (R 6) [96,129,288,5,68,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,5,68,2] 13 (by decide) (choices 1) [2,8,16] r27331 c27331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8618
  · exact u8619
  · exact u8620

def b27332 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 97 131 292 13 84 40 82 146 274), lower := (rows 97 131 292 13 84 40 64 128 256), losses := [] }

theorem u27332 : Upper (D 6) (R 6) [96,129,288,5,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27332 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27333 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 13 84 48 74 138 266), lower := (rows 97 131 292 13 84 48 64 128 256), losses := [] }

theorem u27333 : Upper (D 6) (R 6) [96,129,288,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27333 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27334 : Route 9 := (fun mask => (mask,id))

def c27334 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27334 : Upper (D 6) (R 6) [96,129,288,5,72,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,5,72,2] 13 (by decide) (choices 1) [2,4,16] r27334 c27334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8621
  · exact u8622
  · exact u8623

def b27335 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 97 131 292 13 88 36 82 146 274), lower := (rows 97 131 292 13 88 36 64 128 256), losses := [] }

theorem u27335 : Upper (D 6) (R 6) [96,129,288,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27336 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 13 88 48 70 134 262), lower := (rows 97 131 292 13 88 48 64 128 256), losses := [] }

theorem u27336 : Upper (D 6) (R 6) [96,129,288,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27336 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27337 : Route 9 := (fun mask => (mask,id))

def c27337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27337 : Upper (D 6) (R 6) [96,129,288,6,9,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,9,2] 13 (by decide) (choices 1) [4,16] r27337 c27337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8624
  · exact u8625

def b27338 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 14 25 36 82 210 338), lower := (rows 97 131 292 14 25 36 64 128 256), losses := [] }

theorem u27338 : Upper (D 6) (R 6) [96,129,288,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27339 : PairBound 9 := { available := 70, camps := [], pairs := [(1,5),(2,0)], upper := (rows 97 131 292 14 25 48 70 198 326), lower := (rows 97 131 292 14 25 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 48 72 136 264), good := (rows 96 130 292 462 508 52 64 128 256) },{ target := 5, region := (rows 1 18 4 8 16 0 72 136 264), good := (rows 65 131 260 462 475 18 64 128 256) }] }

theorem u27339 : Upper (D 6) (R 6) [96,129,288,6,9,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27339 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27340 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 292 14 25 96 86 150 278), lower := (rows 97 131 292 14 25 96 64 128 256), losses := [] }

theorem u27340 : Upper (D 6) (R 6) [96,129,288,6,9,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27341 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(4,0),(4,5)], upper := (rows 97 131 292 14 82 33 92 156 284), lower := (rows 97 131 292 14 82 33 64 128 256), losses := [] }

theorem u27341 : Upper (D 6) (R 6) [96,129,288,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27342 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 14 82 36 89 153 281), lower := (rows 97 131 292 14 82 36 64 128 256), losses := [] }

theorem u27342 : Upper (D 6) (R 6) [96,129,288,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27343 : Route 9 := (fun mask => (mask,id))

def c27343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27343 : Upper (D 6) (R 6) [96,129,288,6,66,8] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,66,8] 13 (by decide) (choices 1) [1,4,16] r27343 c27343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8626
  · exact u8627
  · exact u8628

def b27344 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 14 82 48 77 141 269), lower := (rows 97 131 292 14 82 48 64 128 256), losses := [] }

theorem u27344 : Upper (D 6) (R 6) [96,129,288,6,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27344 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27345 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(4,0),(4,5)], upper := (rows 97 131 292 14 84 33 90 154 282), lower := (rows 97 131 292 14 84 33 64 128 256), losses := [] }

theorem u27345 : Upper (D 6) (R 6) [96,129,288,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27346 : Route 9 := (fun mask => (mask,id))

def c27346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27346 : Upper (D 6) (R 6) [96,129,288,6,68,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,68,2] 13 (by decide) (choices 1) [1,8,16] r27346 c27346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8629
  · exact u8630
  · exact u8631

def r27347 : Route 9 := (fun mask => (mask,id))

def c27347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27347 : Upper (D 6) (R 6) [96,129,288,6,68,8] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,68,8] 13 (by decide) (choices 1) [1,2,16] r27347 c27347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8632
  · exact u8633
  · exact u8634

def b27348 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 14 84 48 75 139 267), lower := (rows 97 131 292 14 84 48 64 128 256), losses := [] }

theorem u27348 : Upper (D 6) (R 6) [96,129,288,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27348 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27349 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(4,0),(4,5)], upper := (rows 97 131 292 14 88 33 86 150 278), lower := (rows 97 131 292 14 88 33 64 128 256), losses := [] }

theorem u27349 : Upper (D 6) (R 6) [96,129,288,6,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27350 : Route 9 := (fun mask => (mask,id))

def c27350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27350 : Upper (D 6) (R 6) [96,129,288,6,72,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,72,2] 13 (by decide) (choices 1) [1,4,16] r27350 c27350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8635
  · exact u8636
  · exact u8637

def b27351 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 14 88 36 83 147 275), lower := (rows 97 131 292 14 88 36 64 128 256), losses := [] }

theorem u27351 : Upper (D 6) (R 6) [96,129,288,6,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27352 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 14 88 48 71 135 263), lower := (rows 97 131 292 14 88 48 64 128 256), losses := [] }

theorem u27352 : Upper (D 6) (R 6) [96,129,288,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27352 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27353 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 97 131 292 25 28 34 70 198 326), lower := (rows 97 131 292 25 28 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 39 8 24 34 98 162 290), good := (rows 484 486 484 28 28 486 64 128 256) },{ target := 5, region := (rows 1 10 4 8 16 0 80 144 272), good := (rows 65 131 260 475 478 2 64 128 256) }] }

theorem u27353 : Upper (D 6) (R 6) [96,129,288,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27354 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 25 28 36 66 194 322), lower := (rows 97 131 292 25 28 36 64 128 256), losses := [] }

theorem u27354 : Upper (D 6) (R 6) [96,129,288,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27355 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 292 25 28 96 70 134 262), lower := (rows 97 131 292 25 28 96 64 128 256), losses := [] }

theorem u27355 : Upper (D 6) (R 6) [96,129,288,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27356 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 422, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 97 131 292 25 82 34 76 140 268), lower := (rows 97 131 292 25 82 34 64 128 256), losses := [] }

theorem u27356 : Upper (D 6) (R 6) [96,129,288,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27357 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 131 292 25 82 36 78 142 270), lower := (rows 97 131 292 25 82 36 64 128 256), losses := [] }

theorem u27357 : Upper (D 6) (R 6) [96,129,288,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27358 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 131 292 25 82 40 70 134 262), lower := (rows 97 131 292 25 82 40 64 128 256), losses := [] }

theorem u27358 : Upper (D 6) (R 6) [96,129,288,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27358 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27359 : Route 9 := (fun mask => (mask,id))

def c27359 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27359 : Upper (D 6) (R 6) [96,129,288,17,68,2] 13 := by
  apply FastRouting.sound _ _ [96,129,288,17,68,2] 13 (by decide) (choices 1) [2,4,8] r27359 c27359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8638
  · exact u8639
  · exact u8640

#print axioms u27359
end Delivery.IrregularNine14.P06
