import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0005

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 280 208 160 97 161 289), lower := (rows 67 7 44 280 208 160 64 128 256), losses := [] }

theorem u2700 : Upper (D 8) (R 8) [66,5,40,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 392 112 33 240 176 432), lower := (rows 67 7 44 392 112 33 64 128 256), losses := [] }

theorem u2701 : Upper (D 8) (R 8) [66,5,40,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2702 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 44 392 112 48 225 161 417), lower := (rows 67 7 44 392 112 48 64 128 256), losses := [] }

theorem u2702 : Upper (D 8) (R 8) [66,5,40,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2702 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2703 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 83, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 392 112 160 113 177 305), lower := (rows 67 7 44 392 112 160 64 128 256), losses := [] }

theorem u2703 : Upper (D 8) (R 8) [66,5,40,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2704 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 392 176 33 112 240 368), lower := (rows 67 7 44 392 176 33 64 128 256), losses := [] }

theorem u2704 : Upper (D 8) (R 8) [66,5,40,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2705 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 7 44 392 176 48 97 225 353), lower := (rows 67 7 44 392 176 48 64 128 256), losses := [] }

theorem u2705 : Upper (D 8) (R 8) [66,5,40,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2705 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2706 : Route 9 := (fun mask => (mask,id))

def c2706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2706 : Upper (D 8) (R 8) [66,5,40,384,160,64] 13 := by
  apply FastRouting.sound _ _ [66,5,40,384,160,64] 13 (by decide) (choices 1) [1,16,32] r2706 c2706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u327
  · exact u328
  · exact u329

def b2707 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 392 208 33 112 176 304), lower := (rows 67 7 44 392 208 33 64 128 256), losses := [] }

theorem u2707 : Upper (D 8) (R 8) [66,5,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2708 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 44 392 208 48 97 161 289), lower := (rows 67 7 44 392 208 48 64 128 256), losses := [] }

theorem u2708 : Upper (D 8) (R 8) [66,5,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2708 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2709 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 56 336 33 224 160 416), lower := (rows 67 7 140 56 336 33 64 128 256), losses := [] }

theorem u2709 : Upper (D 8) (R 8) [66,5,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2710 : Route 9 := (fun mask => (mask,id))

def c2710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2710 : Upper (D 8) (R 8) [66,5,136,48,320,128] 13 := by
  apply FastRouting.sound _ _ [66,5,136,48,320,128] 13 (by decide) (choices 1) [1,32] r2710 c2710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u330
  · exact u331

def b2711 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 280 112 33 224 160 416), lower := (rows 67 7 140 280 112 33 64 128 256), losses := [] }

theorem u2711 : Upper (D 8) (R 8) [66,5,136,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2712 : Route 9 := (fun mask => (mask,id))

def c2712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2712 : Upper (D 8) (R 8) [66,5,136,272,96,128] 13 := by
  apply FastRouting.sound _ _ [66,5,136,272,96,128] 13 (by decide) (choices 1) [1,32] r2712 c2712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u332
  · exact u333

def b2713 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 296 112 33 240 176 432), lower := (rows 67 7 140 296 112 33 64 128 256), losses := [] }

theorem u2713 : Upper (D 8) (R 8) [66,5,136,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2714 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 140 296 112 48 225 161 417), lower := (rows 67 7 140 296 112 48 64 128 256), losses := [] }

theorem u2714 : Upper (D 8) (R 8) [66,5,136,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2714 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2715 : Route 9 := (fun mask => (mask,id))

def c2715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2715 : Upper (D 8) (R 8) [66,5,136,288,96,128] 13 := by
  apply FastRouting.sound _ _ [66,5,136,288,96,128] 13 (by decide) (choices 1) [1,16,32] r2715 c2715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u334
  · exact u335
  · exact u336

def b2716 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 296 176 33 112 240 368), lower := (rows 67 7 140 296 176 33 64 128 256), losses := [] }

theorem u2716 : Upper (D 8) (R 8) [66,5,136,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2717 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 7 140 296 176 48 97 225 353), lower := (rows 67 7 140 296 176 48 64 128 256), losses := [] }

theorem u2717 : Upper (D 8) (R 8) [66,5,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2717 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2718 : Route 9 := (fun mask => (mask,id))

def c2718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2718 : Upper (D 8) (R 8) [66,5,136,288,160,64] 13 := by
  apply FastRouting.sound _ _ [66,5,136,288,160,64] 13 (by decide) (choices 1) [1,16,32] r2718 c2718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u337
  · exact u338
  · exact u339

def b2719 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 296 208 33 112 176 304), lower := (rows 67 7 140 296 208 33 64 128 256), losses := [] }

theorem u2719 : Upper (D 8) (R 8) [66,5,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2720 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 140 296 208 48 97 161 289), lower := (rows 67 7 140 296 208 48 64 128 256), losses := [] }

theorem u2720 : Upper (D 8) (R 8) [66,5,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2720 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2721 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 56 208 33 360 424 296), lower := (rows 67 7 164 56 208 33 64 128 256), losses := [] }

theorem u2721 : Upper (D 8) (R 8) [66,5,160,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2722 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 7 164 56 208 40 353 417 289), lower := (rows 67 7 164 56 208 40 64 128 256), losses := [] }

theorem u2722 : Upper (D 8) (R 8) [66,5,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2722 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2723 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 7 164 56 208 288 105 169 297), lower := (rows 67 7 164 56 208 288 64 128 256), losses := [] }

theorem u2723 : Upper (D 8) (R 8) [66,5,160,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2723 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2724 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 56 280 33 224 224 480), lower := (rows 67 7 164 56 280 33 64 128 256), losses := [] }

theorem u2724 : Upper (D 8) (R 8) [66,5,160,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2725 : Route 9 := (fun mask => (mask,id))

def c2725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2725 : Upper (D 8) (R 8) [66,5,160,48,264,64] 13 := by
  apply FastRouting.sound _ _ [66,5,160,48,264,64] 13 (by decide) (choices 1) [1,32,128] r2725 c2725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u340
  · exact u341
  · exact u342

def b2726 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 56 280 160 97 225 353), lower := (rows 67 7 164 56 280 160 64 128 256), losses := [] }

theorem u2726 : Upper (D 8) (R 8) [66,5,160,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2727 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 56 336 33 232 168 424), lower := (rows 67 7 164 56 336 33 64 128 256), losses := [] }

theorem u2727 : Upper (D 8) (R 8) [66,5,160,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2728 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 164 56 336 40 225 161 417), lower := (rows 67 7 164 56 336 40 64 128 256), losses := [] }

theorem u2728 : Upper (D 8) (R 8) [66,5,160,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2728 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2729 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 56 336 160 105 169 297), lower := (rows 67 7 164 56 336 160 64 128 256), losses := [] }

theorem u2729 : Upper (D 8) (R 8) [66,5,160,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2730 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 56 400 33 104 232 360), lower := (rows 67 7 164 56 400 33 64 128 256), losses := [] }

theorem u2730 : Upper (D 8) (R 8) [66,5,160,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2731 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 7 164 56 400 40 97 225 353), lower := (rows 67 7 164 56 400 40 64 128 256), losses := [] }

theorem u2731 : Upper (D 8) (R 8) [66,5,160,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2731 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2732 : Route 9 := (fun mask => (mask,id))

def c2732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2732 : Upper (D 8) (R 8) [66,5,160,48,384,64] 13 := by
  apply FastRouting.sound _ _ [66,5,160,48,384,64] 13 (by decide) (choices 1) [1,8,32] r2732 c2732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u343
  · exact u344
  · exact u345

def b2733 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 88 304 33 232 168 424), lower := (rows 67 7 164 88 304 33 64 128 256), losses := [] }

theorem u2733 : Upper (D 8) (R 8) [66,5,160,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2734 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 164 88 304 40 225 161 417), lower := (rows 67 7 164 88 304 40 64 128 256), losses := [] }

theorem u2734 : Upper (D 8) (R 8) [66,5,160,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2734 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2735 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 88 304 160 105 169 297), lower := (rows 67 7 164 88 304 160 64 128 256), losses := [] }

theorem u2735 : Upper (D 8) (R 8) [66,5,160,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 88 400 33 104 168 296), lower := (rows 67 7 164 88 400 33 64 128 256), losses := [] }

theorem u2736 : Upper (D 8) (R 8) [66,5,160,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2737 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 164 88 400 40 97 161 289), lower := (rows 67 7 164 88 400 40 64 128 256), losses := [] }

theorem u2737 : Upper (D 8) (R 8) [66,5,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2737 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2738 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 104 152 33 368 432 304), lower := (rows 67 7 164 104 152 33 64 128 256), losses := [] }

theorem u2738 : Upper (D 8) (R 8) [66,5,160,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2739 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 7 164 104 152 48 353 417 289), lower := (rows 67 7 164 104 152 48 64 128 256), losses := [] }

theorem u2739 : Upper (D 8) (R 8) [66,5,160,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2739 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2740 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 7 164 104 152 288 113 177 305), lower := (rows 67 7 164 104 152 288 64 128 256), losses := [] }

theorem u2740 : Upper (D 8) (R 8) [66,5,160,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2740 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2741 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 104 280 33 240 176 432), lower := (rows 67 7 164 104 280 33 64 128 256), losses := [] }

theorem u2741 : Upper (D 8) (R 8) [66,5,160,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2742 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 164 104 280 48 225 161 417), lower := (rows 67 7 164 104 280 48 64 128 256), losses := [] }

theorem u2742 : Upper (D 8) (R 8) [66,5,160,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2742 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2743 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 104 280 160 113 177 305), lower := (rows 67 7 164 104 280 160 64 128 256), losses := [] }

theorem u2743 : Upper (D 8) (R 8) [66,5,160,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2744 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 104 304 33 216 152 408), lower := (rows 67 7 164 104 304 33 64 128 256), losses := [] }

theorem u2744 : Upper (D 8) (R 8) [66,5,160,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2745 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 7 164 104 304 40 209 145 401), lower := (rows 67 7 164 104 304 40 64 128 256), losses := [] }

theorem u2745 : Upper (D 8) (R 8) [66,5,160,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2745 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2746 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 7 164 104 304 48 201 137 393), lower := (rows 67 7 164 104 304 48 64 128 256), losses := [] }

theorem u2746 : Upper (D 8) (R 8) [66,5,160,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2746 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2747 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 104 304 160 89 153 281), lower := (rows 67 7 164 104 304 160 64 128 256), losses := [] }

theorem u2747 : Upper (D 8) (R 8) [66,5,160,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2748 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 104 400 33 120 184 312), lower := (rows 67 7 164 104 400 33 64 128 256), losses := [] }

theorem u2748 : Upper (D 8) (R 8) [66,5,160,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2749 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 7 164 104 400 40 113 177 305), lower := (rows 67 7 164 104 400 40 64 128 256), losses := [] }

theorem u2749 : Upper (D 8) (R 8) [66,5,160,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2749 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2750 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 7 164 104 400 48 105 169 297), lower := (rows 67 7 164 104 400 48 64 128 256), losses := [] }

theorem u2750 : Upper (D 8) (R 8) [66,5,160,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2750 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2751 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 152 304 33 104 232 360), lower := (rows 67 7 164 152 304 33 64 128 256), losses := [] }

theorem u2751 : Upper (D 8) (R 8) [66,5,160,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2752 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 7 164 152 304 40 97 225 353), lower := (rows 67 7 164 152 304 40 64 128 256), losses := [] }

theorem u2752 : Upper (D 8) (R 8) [66,5,160,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2752 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2753 : Route 9 := (fun mask => (mask,id))

def c2753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2753 : Upper (D 8) (R 8) [66,5,160,144,288,64] 13 := by
  apply FastRouting.sound _ _ [66,5,160,144,288,64] 13 (by decide) (choices 1) [1,8,32] r2753 c2753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u346
  · exact u347
  · exact u348

def b2754 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 152 336 33 104 168 296), lower := (rows 67 7 164 152 336 33 64 128 256), losses := [] }

theorem u2754 : Upper (D 8) (R 8) [66,5,160,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2755 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 164 152 336 40 97 161 289), lower := (rows 67 7 164 152 336 40 64 128 256), losses := [] }

theorem u2755 : Upper (D 8) (R 8) [66,5,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2755 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2756 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 200 280 33 112 176 304), lower := (rows 67 7 164 200 280 33 64 128 256), losses := [] }

theorem u2756 : Upper (D 8) (R 8) [66,5,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2757 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 164 200 280 48 97 161 289), lower := (rows 67 7 164 200 280 48 64 128 256), losses := [] }

theorem u2757 : Upper (D 8) (R 8) [66,5,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2757 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2758 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 200 304 33 120 184 312), lower := (rows 67 7 164 200 304 33 64 128 256), losses := [] }

theorem u2758 : Upper (D 8) (R 8) [66,5,160,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2759 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 7 164 200 304 40 113 177 305), lower := (rows 67 7 164 200 304 40 64 128 256), losses := [] }

theorem u2759 : Upper (D 8) (R 8) [66,5,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2759 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2759
end Delivery.IrregularNine14.P08
