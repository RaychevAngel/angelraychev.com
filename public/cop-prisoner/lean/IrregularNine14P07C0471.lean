import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0175
import IrregularNine14P07C0176

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r28260 : Route 9 := (fun mask => (mask,id))

def c28260 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28260 : Upper (D 7) (R 7) [96,160,9,258,192,1] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,192,1] 13 (by decide) (choices 1) [2,4,16] r28260 c28260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10523
  · exact u10524
  · exact u10525

def b28261 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 266 208 34 85 149 277), lower := (rows 97 162 13 266 208 34 64 128 256), losses := [] }

theorem u28261 : Upper (D 7) (R 7) [96,160,9,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28262 : Route 9 := (fun mask => (mask,id))

def c28262 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28262 : Upper (D 7) (R 7) [96,160,9,258,192,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,192,4] 13 (by decide) (choices 1) [1,2,16] r28262 c28262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10526
  · exact u10527
  · exact u10528

def b28263 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 266 208 48 71 135 263), lower := (rows 97 162 13 266 208 48 64 128 256), losses := [] }

theorem u28263 : Upper (D 7) (R 7) [96,160,9,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28263 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28264 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 146, targets := 1 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 162 13 268 82 33 210 146 402), lower := (rows 97 162 13 268 82 33 64 128 256), losses := [] }

theorem u28264 : Upper (D 7) (R 7) [96,160,9,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28265 : Route 9 := (fun mask => (mask,id))

def c28265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28265 : Upper (D 7) (R 7) [96,160,9,260,66,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,260,66,2] 13 (by decide) (choices 1) [1,16,128] r28265 c28265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10529
  · exact u10530
  · exact u10531

def b28266 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 268 82 48 195 131 387), lower := (rows 97 162 13 268 82 48 64 128 256), losses := [] }

theorem u28266 : Upper (D 7) (R 7) [96,160,9,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28266 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28267 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 268 82 160 83 147 275), lower := (rows 97 162 13 268 82 160 64 128 256), losses := [] }

theorem u28267 : Upper (D 7) (R 7) [96,160,9,260,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28268 : Route 9 := (fun mask => (mask,id))

def c28268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28268 : Upper (D 7) (R 7) [96,160,9,260,129,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,260,129,2] 13 (by decide) (choices 1) [2,16] r28268 c28268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10532
  · exact u10533

def b28269 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 268 145 48 66 194 322), lower := (rows 97 162 13 268 145 48 64 128 256), losses := [] }

theorem u28269 : Upper (D 7) (R 7) [96,160,9,260,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28269 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28270 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 268 145 96 82 146 274), lower := (rows 97 162 13 268 145 96 64 128 256), losses := [] }

theorem u28270 : Upper (D 7) (R 7) [96,160,9,260,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28271 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 146, targets := 1 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 162 13 268 208 33 82 146 274), lower := (rows 97 162 13 268 208 33 64 128 256), losses := [] }

theorem u28271 : Upper (D 7) (R 7) [96,160,9,260,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28272 : Route 9 := (fun mask => (mask,id))

def c28272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28272 : Upper (D 7) (R 7) [96,160,9,260,192,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,260,192,2] 13 (by decide) (choices 1) [1,2,16] r28272 c28272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10534
  · exact u10535
  · exact u10536

def b28273 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 268 208 48 67 131 259), lower := (rows 97 162 13 268 208 48 64 128 256), losses := [] }

theorem u28273 : Upper (D 7) (R 7) [96,160,9,260,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28273 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28274 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 2, region := 162, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 97 162 13 280 82 33 198 134 390), lower := (rows 97 162 13 280 82 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 125 64 128 256), good := (rows 97 160 45 317 113 33 97 128 256) }] }

theorem u28274 : Upper (D 7) (R 7) [96,160,9,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28275 : PairBound 9 := { available := 133, camps := [{ cop := 7, region := 34, targets := 65 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 97 162 13 280 82 34 197 133 389), lower := (rows 97 162 13 280 82 34 64 128 256), losses := [{ target := 7, region := (rows 17 2 12 8 16 50 64 0 256), good := (rows 97 34 13 317 115 34 64 0 256) }] }

theorem u28275 : Upper (D 7) (R 7) [96,160,9,272,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28276 : Route 9 := (fun mask => (mask,id))

def c28276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28276 : Upper (D 7) (R 7) [96,160,9,272,66,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,66,4] 13 (by decide) (choices 1) [1,2,128] r28276 c28276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10537
  · exact u10538
  · exact u10539

def b28277 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 280 82 160 71 135 263), lower := (rows 97 162 13 280 82 160 64 128 256), losses := [] }

theorem u28277 : Upper (D 7) (R 7) [96,160,9,272,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28278 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 0, region := 130, targets := 1 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 13 280 84 33 194 130 386), lower := (rows 97 162 13 280 84 33 64 128 256), losses := [] }

theorem u28278 : Upper (D 7) (R 7) [96,160,9,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28279 : Route 9 := (fun mask => (mask,id))

def c28279 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28279 : Upper (D 7) (R 7) [96,160,9,272,68,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,68,2] 13 (by decide) (choices 1) [1,2,128] r28279 c28279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10540
  · exact u10541
  · exact u10542

def b28280 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 280 84 160 67 131 259), lower := (rows 97 162 13 280 84 160 64 128 256), losses := [] }

theorem u28280 : Upper (D 7) (R 7) [96,160,9,272,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28281 : Route 9 := (fun mask => (mask,id))

def c28281 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28281 : Upper (D 7) (R 7) [96,160,9,272,129,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,129,2] 13 (by decide) (choices 1) [2,4] r28281 c28281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10543
  · exact u10544

def b28282 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 130, targets := 1 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,0),(3,0)], upper := (rows 97 162 13 280 145 36 66 194 322), lower := (rows 97 162 13 280 145 36 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 24 16 36 119 183 311), good := (rows 482 482 494 472 474 486 64 128 256) }] }

theorem u28282 : Upper (D 7) (R 7) [96,160,9,272,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28282 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28283 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 280 145 96 70 134 262), lower := (rows 97 162 13 280 145 96 64 128 256), losses := [] }

theorem u28283 : Upper (D 7) (R 7) [96,160,9,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28284 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 130, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 97 162 13 280 148 33 66 194 322), lower := (rows 97 162 13 280 148 33 64 128 256), losses := [{ target := 0, region := (rows 0 35 4 28 20 32 103 167 295), good := (rows 482 482 478 280 476 482 64 128 256) }] }

theorem u28284 : Upper (D 7) (R 7) [96,160,9,272,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28285 : Route 9 := (fun mask => (mask,id))

def c28285 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28285 : Upper (D 7) (R 7) [96,160,9,272,132,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,132,2] 13 (by decide) (choices 1) [1,2] r28285 c28285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10545
  · exact u10546

def b28286 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 280 148 96 67 131 259), lower := (rows 97 162 13 280 148 96 64 128 256), losses := [] }

theorem u28286 : Upper (D 7) (R 7) [96,160,9,272,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28287 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 2, region := 162, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 97 162 13 280 208 33 70 134 262), lower := (rows 97 162 13 280 208 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 125 64 128 256), good := (rows 97 160 45 317 241 33 97 128 256) }] }

theorem u28287 : Upper (D 7) (R 7) [96,160,9,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28288 : Route 9 := (fun mask => (mask,id))

def c28288 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28288 : Upper (D 7) (R 7) [96,160,9,272,192,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,192,2] 13 (by decide) (choices 1) [1,2,4] r28288 c28288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10547
  · exact u10548
  · exact u10549

def r28289 : Route 9 := (fun mask => (mask,id))

def c28289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28289 : Upper (D 7) (R 7) [96,160,9,272,192,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,192,4] 13 (by decide) (choices 1) [1,2] r28289 c28289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10550
  · exact u10551

def r28290 : Route 9 := (fun mask => (mask,id))

def c28290 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28290 : Upper (D 7) (R 7) [96,160,9,320,129,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,320,129,2] 13 (by decide) (choices 1) [2,4,16] r28290 c28290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10552
  · exact u10553
  · exact u10554

def b28291 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 328 145 36 82 146 274), lower := (rows 97 162 13 328 145 36 64 128 256), losses := [] }

theorem u28291 : Upper (D 7) (R 7) [96,160,9,320,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28291 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28292 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 328 145 48 70 134 262), lower := (rows 97 162 13 328 145 48 64 128 256), losses := [] }

theorem u28292 : Upper (D 7) (R 7) [96,160,9,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28292 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28293 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 328 148 33 82 146 274), lower := (rows 97 162 13 328 148 33 64 128 256), losses := [] }

theorem u28293 : Upper (D 7) (R 7) [96,160,9,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28294 : Route 9 := (fun mask => (mask,id))

def c28294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28294 : Upper (D 7) (R 7) [96,160,9,320,132,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,320,132,2] 13 (by decide) (choices 1) [1,2,16] r28294 c28294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10555
  · exact u10556
  · exact u10557

def b28295 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 328 148 48 67 131 259), lower := (rows 97 162 13 328 148 48 64 128 256), losses := [] }

theorem u28295 : Upper (D 7) (R 7) [96,160,9,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28295 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28296 : Route 9 := (fun mask => (mask,id))

def c28296 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28296 : Upper (D 7) (R 7) [96,160,9,384,66,1] 13 := by
  apply FastRouting.sound _ _ [96,160,9,384,66,1] 13 (by decide) (choices 1) [2,4,16] r28296 c28296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10558
  · exact u10559
  · exact u10560

def r28297 : Route 9 := (fun mask => (mask,id))

def c28297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28297 : Upper (D 7) (R 7) [96,160,9,384,66,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,384,66,2] 13 (by decide) (choices 1) [1,4,16] r28297 c28297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10561
  · exact u10562
  · exact u10563

def r28298 : Route 9 := (fun mask => (mask,id))

def c28298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28298 : Upper (D 7) (R 7) [96,160,9,384,66,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,384,66,4] 13 (by decide) (choices 1) [1,2,16] r28298 c28298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10564
  · exact u10565
  · exact u10566

def b28299 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 392 82 48 71 135 263), lower := (rows 97 162 13 392 82 48 64 128 256), losses := [] }

theorem u28299 : Upper (D 7) (R 7) [96,160,9,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28299 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28300 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(3,6)], upper := (rows 97 162 13 392 84 33 82 146 274), lower := (rows 97 162 13 392 84 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 37 0 144 272), good := (rows 33 162 45 392 446 33 0 128 256) }] }

theorem u28300 : Upper (D 7) (R 7) [96,160,9,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28301 : Route 9 := (fun mask => (mask,id))

def c28301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28301 : Upper (D 7) (R 7) [96,160,9,384,68,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,384,68,2] 13 (by decide) (choices 1) [1,2,16] r28301 c28301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10567
  · exact u10568
  · exact u10569

def b28302 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 392 84 48 67 131 259), lower := (rows 97 162 13 392 84 48 64 128 256), losses := [] }

theorem u28302 : Upper (D 7) (R 7) [96,160,9,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28302 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28303 : Route 9 := (fun mask => (mask,id))

def c28303 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u28303 : Upper (D 7) (R 7) [96,160,24,66,129,1] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,129,1] 13 (by decide) (choices 1) [2,4,256] r28303 c28303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10570
  · exact u10571
  · exact u10572

def b28304 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,6),(4,6)], upper := (rows 97 162 28 74 145 36 323 387 259), lower := (rows 97 162 28 74 145 36 64 128 256), losses := [] }

theorem u28304 : Upper (D 7) (R 7) [96,160,24,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28304 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28305 : Route 9 := (fun mask => (mask,id))

def c28305 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28305 : Upper (D 7) (R 7) [96,160,24,66,129,256] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,129,256] 13 (by decide) (choices 1) [1,2,4] r28305 c28305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10573
  · exact u10574
  · exact u10575

def b28306 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 329, targets := 128 },{ cop := 0, region := 386, targets := 64 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,6),(3,7)], upper := (rows 97 162 28 74 148 33 323 387 259), lower := (rows 97 162 28 74 148 33 64 128 256), losses := [] }

theorem u28306 : Upper (D 7) (R 7) [96,160,24,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28307 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 329, targets := 128 },{ cop := 4, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7)], upper := (rows 97 162 28 74 148 34 321 385 257), lower := (rows 97 162 28 74 148 34 64 128 256), losses := [] }

theorem u28307 : Upper (D 7) (R 7) [96,160,24,66,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28308 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 73, targets := 128 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,7),(1,6),(3,7)], upper := (rows 97 162 28 74 148 288 67 131 259), lower := (rows 97 162 28 74 148 288 64 128 256), losses := [] }

theorem u28308 : Upper (D 7) (R 7) [96,160,24,66,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28308 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28309 : Route 9 := (fun mask => (mask,id))

def c28309 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28309 : Upper (D 7) (R 7) [96,160,24,66,257,1] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,257,1] 13 (by decide) (choices 1) [2,4,128] r28309 c28309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10576
  · exact u10577
  · exact u10578

def r28310 : Route 9 := (fun mask => (mask,id))

def c28310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28310 : Upper (D 7) (R 7) [96,160,24,66,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,257,2] 13 (by decide) (choices 1) [1,4,128] r28310 c28310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10579
  · exact u10580
  · exact u10581

def r28311 : Route 9 := (fun mask => (mask,id))

def c28311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28311 : Upper (D 7) (R 7) [96,160,24,66,257,4] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,257,4] 13 (by decide) (choices 1) [1,2,128] r28311 c28311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10582
  · exact u10583
  · exact u10584

def b28312 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 28 74 273 160 71 135 263), lower := (rows 97 162 28 74 273 160 64 128 256), losses := [] }

theorem u28312 : Upper (D 7) (R 7) [96,160,24,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28313 : Route 9 := (fun mask => (mask,id))

def c28313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28313 : Upper (D 7) (R 7) [96,160,24,66,258,1] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,258,1] 13 (by decide) (choices 1) [1,4,128] r28313 c28313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10585
  · exact u10586
  · exact u10587

def b28314 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 97 162 28 74 274 36 193 129 385), lower := (rows 97 162 28 74 274 36 64 128 256), losses := [] }

theorem u28314 : Upper (D 7) (R 7) [96,160,24,66,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28314 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28315 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 28 74 274 160 69 133 261), lower := (rows 97 162 28 74 274 160 64 128 256), losses := [] }

theorem u28315 : Upper (D 7) (R 7) [96,160,24,66,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28316 : Route 9 := (fun mask => (mask,id))

def c28316 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28316 : Upper (D 7) (R 7) [96,160,24,66,260,1] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,260,1] 13 (by decide) (choices 1) [1,2,128] r28316 c28316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10588
  · exact u10589
  · exact u10590

def b28317 : PairBound 9 := { available := 129, camps := [{ cop := 7, region := 34, targets := 65 },{ cop := 1, region := 65, targets := 2 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 28 74 276 34 193 129 385), lower := (rows 97 162 28 74 276 34 64 128 256), losses := [] }

theorem u28317 : Upper (D 7) (R 7) [96,160,24,66,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28318 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 28 74 276 160 67 131 259), lower := (rows 97 162 28 74 276 160 64 128 256), losses := [] }

theorem u28318 : Upper (D 7) (R 7) [96,160,24,66,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28319 : Route 9 := (fun mask => (mask,id))

def c28319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28319 : Upper (D 7) (R 7) [96,160,24,66,384,1] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,384,1] 13 (by decide) (choices 1) [1,2,4] r28319 c28319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10591
  · exact u10592
  · exact u10593

#print axioms u28319
end Delivery.IrregularNine14.P07
