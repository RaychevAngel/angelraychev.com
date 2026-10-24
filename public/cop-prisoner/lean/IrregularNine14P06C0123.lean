import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0009

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7380 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 72, targets := 36 },{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1),(3,2),(3,5)], upper := (rows 35 138 100 73 273 36 66 148 276), lower := (rows 35 138 100 73 273 36 66 128 256), losses := [] }

theorem u7380 : Upper (D 6) (R 6) [34,136,96,65,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7381 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 402, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 138 100 73 273 36 68 146 274), lower := (rows 35 138 100 73 273 36 68 128 256), losses := [] }

theorem u7381 : Upper (D 6) (R 6) [34,136,96,65,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7382 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 166, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 138 100 73 273 36 80 134 262), lower := (rows 35 138 100 73 273 36 80 128 256), losses := [] }

theorem u7382 : Upper (D 6) (R 6) [34,136,96,65,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7382 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7383 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 35 138 100 73 274 36 65 148 276), lower := (rows 35 138 100 73 274 36 65 128 256), losses := [] }

theorem u7383 : Upper (D 6) (R 6) [34,136,96,65,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7384 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 402, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 138 100 73 274 36 68 145 273), lower := (rows 35 138 100 73 274 36 68 128 256), losses := [] }

theorem u7384 : Upper (D 6) (R 6) [34,136,96,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7385 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 138 100 73 274 36 80 133 261), lower := (rows 35 138 100 73 274 36 80 128 256), losses := [] }

theorem u7385 : Upper (D 6) (R 6) [34,136,96,65,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7385 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7386 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 35 138 100 73 276 36 65 146 274), lower := (rows 35 138 100 73 276 36 65 128 256), losses := [] }

theorem u7386 : Upper (D 6) (R 6) [34,136,96,65,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7387 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 36 },{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1),(3,2),(3,5)], upper := (rows 35 138 100 73 276 36 66 145 273), lower := (rows 35 138 100 73 276 36 66 128 256), losses := [] }

theorem u7387 : Upper (D 6) (R 6) [34,136,96,65,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7388 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 138 100 73 276 36 80 131 259), lower := (rows 35 138 100 73 276 36 80 128 256), losses := [] }

theorem u7388 : Upper (D 6) (R 6) [34,136,96,65,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7388 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7389 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 138 100 73 276 48 65 134 262), lower := (rows 35 138 100 73 276 48 65 128 256), losses := [] }

theorem u7389 : Upper (D 6) (R 6) [34,136,96,65,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7389 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7390 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 138 100 73 276 48 66 133 261), lower := (rows 35 138 100 73 276 48 66 128 256), losses := [] }

theorem u7390 : Upper (D 6) (R 6) [34,136,96,65,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7390 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7391 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 138 100 73 276 48 68 131 259), lower := (rows 35 138 100 73 276 48 68 128 256), losses := [] }

theorem u7391 : Upper (D 6) (R 6) [34,136,96,65,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7391 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7392 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 166, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 138 100 88 273 36 65 134 262), lower := (rows 35 138 100 88 273 36 65 128 256), losses := [] }

theorem u7392 : Upper (D 6) (R 6) [34,136,96,80,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7393 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 138 100 88 273 36 66 133 261), lower := (rows 35 138 100 88 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 95 24 16 127 67 128 256), good := (rows 102 238 100 124 380 36 102 128 256) }] }

theorem u7393 : Upper (D 6) (R 6) [34,136,96,80,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7394 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 100 88 273 36 68 131 259), lower := (rows 35 138 100 88 273 36 68 128 256), losses := [] }

theorem u7394 : Upper (D 6) (R 6) [34,136,96,80,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7395 : Route 9 := (fun mask => (mask,id))

def c7395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7395 : Upper (D 6) (R 6) [34,136,96,80,258,4,1] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80,258,4,1] 13 (by decide) (choices 1) [1,4] r7395 c7395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u571
  · exact u572

def b7396 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 100 88 274 36 68 129 257), lower := (rows 35 138 100 88 274 36 68 128 256), losses := [] }

theorem u7396 : Upper (D 6) (R 6) [34,136,96,80,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7397 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 100 88 276 33 65 134 262), lower := (rows 35 138 100 88 276 33 65 128 256), losses := [] }

theorem u7397 : Upper (D 6) (R 6) [34,136,96,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7398 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 138 100 88 276 33 66 133 261), lower := (rows 35 138 100 88 276 33 66 128 256), losses := [] }

theorem u7398 : Upper (D 6) (R 6) [34,136,96,80,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7399 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 100 88 276 33 68 131 259), lower := (rows 35 138 100 88 276 33 68 128 256), losses := [] }

theorem u7399 : Upper (D 6) (R 6) [34,136,96,80,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7400 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 35 138 100 265 81 36 66 148 276), lower := (rows 35 138 100 265 81 36 66 128 256), losses := [] }

theorem u7400 : Upper (D 6) (R 6) [34,136,96,257,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7401 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 394, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 138 100 265 81 36 68 146 274), lower := (rows 35 138 100 265 81 36 68 128 256), losses := [] }

theorem u7401 : Upper (D 6) (R 6) [34,136,96,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7402 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 265 81 36 80 134 262), lower := (rows 35 138 100 265 81 36 80 128 256), losses := [] }

theorem u7402 : Upper (D 6) (R 6) [34,136,96,257,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7402 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7403 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 138 100 265 82 36 65 148 276), lower := (rows 35 138 100 265 82 36 65 128 256), losses := [] }

theorem u7403 : Upper (D 6) (R 6) [34,136,96,257,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7404 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 100 265 82 36 68 145 273), lower := (rows 35 138 100 265 82 36 68 128 256), losses := [] }

theorem u7404 : Upper (D 6) (R 6) [34,136,96,257,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7405 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 265 82 36 80 133 261), lower := (rows 35 138 100 265 82 36 80 128 256), losses := [] }

theorem u7405 : Upper (D 6) (R 6) [34,136,96,257,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7405 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7406 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 100 268 22 33 65 208 336), lower := (rows 35 138 100 268 22 33 65 128 256), losses := [] }

theorem u7406 : Upper (D 6) (R 6) [34,136,96,260,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7407 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 138 100 268 22 33 80 193 321), lower := (rows 35 138 100 268 22 33 80 128 256), losses := [] }

theorem u7407 : Upper (D 6) (R 6) [34,136,96,260,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7407 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7408 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 100 268 82 33 65 148 276), lower := (rows 35 138 100 268 82 33 65 128 256), losses := [] }

theorem u7408 : Upper (D 6) (R 6) [34,136,96,260,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7409 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 268 82 33 68 145 273), lower := (rows 35 138 100 268 82 33 68 128 256), losses := [] }

theorem u7409 : Upper (D 6) (R 6) [34,136,96,260,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7410 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 268 82 33 80 133 261), lower := (rows 35 138 100 268 82 33 80 128 256), losses := [] }

theorem u7410 : Upper (D 6) (R 6) [34,136,96,260,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7410 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7411 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 138 100 280 81 36 65 134 262), lower := (rows 35 138 100 280 81 36 65 128 256), losses := [] }

theorem u7411 : Upper (D 6) (R 6) [34,136,96,272,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7412 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 35 138 100 280 81 36 66 133 261), lower := (rows 35 138 100 280 81 36 66 128 256), losses := [] }

theorem u7412 : Upper (D 6) (R 6) [34,136,96,272,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7413 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 394, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 138 100 280 81 36 68 131 259), lower := (rows 35 138 100 280 81 36 68 128 256), losses := [] }

theorem u7413 : Upper (D 6) (R 6) [34,136,96,272,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7414 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 138 100 280 82 36 65 133 261), lower := (rows 35 138 100 280 82 36 65 128 256), losses := [] }

theorem u7414 : Upper (D 6) (R 6) [34,136,96,272,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7415 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 100 280 82 36 68 129 257), lower := (rows 35 138 100 280 82 36 68 128 256), losses := [] }

theorem u7415 : Upper (D 6) (R 6) [34,136,96,272,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7416 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 100 328 22 33 65 148 276), lower := (rows 35 138 100 328 22 33 65 128 256), losses := [] }

theorem u7416 : Upper (D 6) (R 6) [34,136,96,320,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7417 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 328 22 33 68 145 273), lower := (rows 35 138 100 328 22 33 68 128 256), losses := [] }

theorem u7417 : Upper (D 6) (R 6) [34,136,96,320,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7418 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 138 100 328 22 33 80 133 261), lower := (rows 35 138 100 328 22 33 80 128 256), losses := [] }

theorem u7418 : Upper (D 6) (R 6) [34,136,96,320,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7418 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7419 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 261 14 52 96 65 208 336), lower := (rows 35 138 261 14 52 96 65 128 256), losses := [] }

theorem u7419 : Upper (D 6) (R 6) [34,136,257,6,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7420 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 261 14 52 96 80 193 321), lower := (rows 35 138 261 14 52 96 80 128 256), losses := [] }

theorem u7420 : Upper (D 6) (R 6) [34,136,257,6,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7420 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7421 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 2, region := 80, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 35 138 261 14 81 96 68 176 304), lower := (rows 35 138 261 14 81 96 68 128 256), losses := [] }

theorem u7421 : Upper (D 6) (R 6) [34,136,257,6,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7422 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 261 14 81 96 80 164 292), lower := (rows 35 138 261 14 81 96 80 128 256), losses := [] }

theorem u7422 : Upper (D 6) (R 6) [34,136,257,6,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7422 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7423 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 138 261 14 81 96 96 148 276), lower := (rows 35 138 261 14 81 96 96 128 256), losses := [] }

theorem u7423 : Upper (D 6) (R 6) [34,136,257,6,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7424 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 35 138 261 14 84 96 65 176 304), lower := (rows 35 138 261 14 84 96 65 128 256), losses := [] }

theorem u7424 : Upper (D 6) (R 6) [34,136,257,6,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7425 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 261 14 84 96 80 161 289), lower := (rows 35 138 261 14 84 96 80 128 256), losses := [] }

theorem u7425 : Upper (D 6) (R 6) [34,136,257,6,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7425 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7426 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 261 14 84 96 96 145 273), lower := (rows 35 138 261 14 84 96 96 128 256), losses := [] }

theorem u7426 : Upper (D 6) (R 6) [34,136,257,6,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7427 : Route 9 := (fun mask => (mask,id))

def c7427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7427 : Upper (D 6) (R 6) [34,136,257,17,6,64,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,6,64,4] 13 (by decide) (choices 1) [32,64] r7427 c7427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u573
  · exact u574

def b7428 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 138 261 25 22 96 96 196 324), lower := (rows 35 138 261 25 22 96 96 128 256), losses := [] }

theorem u7428 : Upper (D 6) (R 6) [34,136,257,17,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7429 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 138 261 25 52 96 66 196 324), lower := (rows 35 138 261 25 52 96 66 128 256), losses := [] }

theorem u7429 : Upper (D 6) (R 6) [34,136,257,17,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7430 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 138 261 25 52 96 68 194 322), lower := (rows 35 138 261 25 52 96 68 128 256), losses := [] }

theorem u7430 : Upper (D 6) (R 6) [34,136,257,17,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7431 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 35 138 261 25 82 36 68 224 352), lower := (rows 35 138 261 25 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 100 100 245 373), good := (rows 498 138 500 410 498 484 484 128 256) }] }

theorem u7431 : Upper (D 6) (R 6) [34,136,257,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7432 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 138 261 25 82 36 96 196 324), lower := (rows 35 138 261 25 82 36 96 128 256), losses := [] }

theorem u7432 : Upper (D 6) (R 6) [34,136,257,17,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7433 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 35 138 261 25 84 96 66 164 292), lower := (rows 35 138 261 25 84 96 66 128 256), losses := [] }

theorem u7433 : Upper (D 6) (R 6) [34,136,257,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7434 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 261 25 84 96 68 162 290), lower := (rows 35 138 261 25 84 96 68 128 256), losses := [] }

theorem u7434 : Upper (D 6) (R 6) [34,136,257,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7435 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 138 261 25 84 96 96 134 262), lower := (rows 35 138 261 25 84 96 96 128 256), losses := [] }

theorem u7435 : Upper (D 6) (R 6) [34,136,257,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7436 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 138 261 25 112 36 66 196 324), lower := (rows 35 138 261 25 112 36 66 128 256), losses := [] }

theorem u7436 : Upper (D 6) (R 6) [34,136,257,17,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7437 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 261 25 112 36 68 194 322), lower := (rows 35 138 261 25 112 36 68 128 256), losses := [] }

theorem u7437 : Upper (D 6) (R 6) [34,136,257,17,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7438 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 2, region := 80, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 35 138 261 26 81 36 68 224 352), lower := (rows 35 138 261 26 81 36 68 128 256), losses := [] }

theorem u7438 : Upper (D 6) (R 6) [34,136,257,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7439 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 261 26 81 36 96 196 324), lower := (rows 35 138 261 26 81 36 96 128 256), losses := [] }

theorem u7439 : Upper (D 6) (R 6) [34,136,257,18,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7439
end Delivery.IrregularNine14.P06
