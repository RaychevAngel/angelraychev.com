import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0298
import IrregularNine14P07C0299

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33720 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 7 28 56 480 448 448 448), lower := (rows 35 67 7 28 56 32 64 128 256), losses := [] }

theorem u33720 : Upper (D 7) (R 7) [34,65,3,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33721 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 28 112 424 456 392 392), lower := (rows 35 67 7 28 112 32 64 128 256), losses := [] }

theorem u33721 : Upper (D 7) (R 7) [34,65,3,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33722 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 28 152 480 480 480 480), lower := (rows 35 67 7 28 152 32 64 128 256), losses := [] }

theorem u33722 : Upper (D 7) (R 7) [34,65,3,20,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33723 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 28 176 488 456 456 456), lower := (rows 35 67 7 28 176 32 64 128 256), losses := [] }

theorem u33723 : Upper (D 7) (R 7) [34,65,3,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33724 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 28 280 224 224 224 480), lower := (rows 35 67 7 28 280 32 64 128 256), losses := [] }

theorem u33724 : Upper (D 7) (R 7) [34,65,3,20,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33725 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 28 304 232 200 200 456), lower := (rows 35 67 7 28 304 32 64 128 256), losses := [] }

theorem u33725 : Upper (D 7) (R 7) [34,65,3,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33726 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 28 400 232 232 232 488), lower := (rows 35 67 7 28 400 32 64 128 256), losses := [] }

theorem u33726 : Upper (D 7) (R 7) [34,65,3,20,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33727 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 7 44 88 432 464 400 400), lower := (rows 35 67 7 44 88 32 64 128 256), losses := [] }

theorem u33727 : Upper (D 7) (R 7) [34,65,3,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33728 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 7 44 152 496 464 464 464), lower := (rows 35 67 7 44 152 32 64 128 256), losses := [] }

theorem u33728 : Upper (D 7) (R 7) [34,65,3,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33729 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 7 44 208 440 472 408 408), lower := (rows 35 67 7 44 208 32 64 128 256), losses := [] }

theorem u33729 : Upper (D 7) (R 7) [34,65,3,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33730 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 7 44 280 240 208 208 464), lower := (rows 35 67 7 44 280 32 64 128 256), losses := [] }

theorem u33730 : Upper (D 7) (R 7) [34,65,3,36,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33731 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 7 44 336 184 216 152 408), lower := (rows 35 67 7 44 336 32 64 128 256), losses := [] }

theorem u33731 : Upper (D 7) (R 7) [34,65,3,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33732 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 7 44 400 248 216 216 472), lower := (rows 35 67 7 44 400 32 64 128 256), losses := [] }

theorem u33732 : Upper (D 7) (R 7) [34,65,3,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33733 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 56 148 488 456 456 456), lower := (rows 35 67 7 56 148 32 64 128 256), losses := [] }

theorem u33733 : Upper (D 7) (R 7) [34,65,3,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33734 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 56 152 484 452 452 452), lower := (rows 35 67 7 56 152 32 64 128 256), losses := [] }

theorem u33734 : Upper (D 7) (R 7) [34,65,3,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33735 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 56 208 428 460 396 396), lower := (rows 35 67 7 56 208 32 64 128 256), losses := [] }

theorem u33735 : Upper (D 7) (R 7) [34,65,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33736 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 56 276 232 200 200 456), lower := (rows 35 67 7 56 276 32 64 128 256), losses := [] }

theorem u33736 : Upper (D 7) (R 7) [34,65,3,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33737 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 56 280 228 196 196 452), lower := (rows 35 67 7 56 280 32 64 128 256), losses := [] }

theorem u33737 : Upper (D 7) (R 7) [34,65,3,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33738 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 56 336 172 204 140 396), lower := (rows 35 67 7 56 336 32 64 128 256), losses := [] }

theorem u33738 : Upper (D 7) (R 7) [34,65,3,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33739 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 56 400 236 204 204 460), lower := (rows 35 67 7 56 400 32 64 128 256), losses := [] }

theorem u33739 : Upper (D 7) (R 7) [34,65,3,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33740 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 104 148 440 472 408 408), lower := (rows 35 67 7 104 148 32 64 128 256), losses := [] }

theorem u33740 : Upper (D 7) (R 7) [34,65,3,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33741 : PairBound 9 := { available := 404, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 104 152 436 468 404 404), lower := (rows 35 67 7 104 152 32 64 128 256), losses := [] }

theorem u33741 : Upper (D 7) (R 7) [34,65,3,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33742 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 104 276 184 216 152 408), lower := (rows 35 67 7 104 276 32 64 128 256), losses := [] }

theorem u33742 : Upper (D 7) (R 7) [34,65,3,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33743 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 104 280 180 212 148 404), lower := (rows 35 67 7 104 280 32 64 128 256), losses := [] }

theorem u33743 : Upper (D 7) (R 7) [34,65,3,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33744 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 104 400 188 220 156 412), lower := (rows 35 67 7 104 400 32 64 128 256), losses := [] }

theorem u33744 : Upper (D 7) (R 7) [34,65,3,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33745 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 140 176 376 344 472 344), lower := (rows 35 67 7 140 176 32 64 128 256), losses := [] }

theorem u33745 : Upper (D 7) (R 7) [34,65,3,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33746 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 140 280 240 240 240 496), lower := (rows 35 67 7 140 280 32 64 128 256), losses := [] }

theorem u33746 : Upper (D 7) (R 7) [34,65,3,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33747 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 140 304 248 216 216 472), lower := (rows 35 67 7 140 304 32 64 128 256), losses := [] }

theorem u33747 : Upper (D 7) (R 7) [34,65,3,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33748 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 140 400 120 120 248 376), lower := (rows 35 67 7 140 400 32 64 128 256), losses := [] }

theorem u33748 : Upper (D 7) (R 7) [34,65,3,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33749 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 152 276 232 232 232 488), lower := (rows 35 67 7 152 276 32 64 128 256), losses := [] }

theorem u33749 : Upper (D 7) (R 7) [34,65,3,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33750 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 152 280 228 228 228 484), lower := (rows 35 67 7 152 280 32 64 128 256), losses := [] }

theorem u33750 : Upper (D 7) (R 7) [34,65,3,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33751 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 152 304 236 204 204 460), lower := (rows 35 67 7 152 304 32 64 128 256), losses := [] }

theorem u33751 : Upper (D 7) (R 7) [34,65,3,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33752 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 168 208 316 348 412 284), lower := (rows 35 67 7 168 208 32 64 128 256), losses := [] }

theorem u33752 : Upper (D 7) (R 7) [34,65,3,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33753 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 168 276 248 216 216 472), lower := (rows 35 67 7 168 276 32 64 128 256), losses := [] }

theorem u33753 : Upper (D 7) (R 7) [34,65,3,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33754 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 168 280 244 212 212 468), lower := (rows 35 67 7 168 280 32 64 128 256), losses := [] }

theorem u33754 : Upper (D 7) (R 7) [34,65,3,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33755 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 168 336 188 220 156 412), lower := (rows 35 67 7 168 336 32 64 128 256), losses := [] }

theorem u33755 : Upper (D 7) (R 7) [34,65,3,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33756 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 168 400 124 92 220 348), lower := (rows 35 67 7 168 400 32 64 128 256), losses := [] }

theorem u33756 : Upper (D 7) (R 7) [34,65,3,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33757 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 67 13 14 112 432 464 400 400), lower := (rows 35 67 13 14 112 32 64 128 256), losses := [] }

theorem u33757 : Upper (D 7) (R 7) [34,65,9,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33758 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 67 13 14 176 496 464 464 464), lower := (rows 35 67 13 14 176 32 64 128 256), losses := [] }

theorem u33758 : Upper (D 7) (R 7) [34,65,9,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33759 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 67 13 14 304 240 208 208 464), lower := (rows 35 67 13 14 304 32 64 128 256), losses := [] }

theorem u33759 : Upper (D 7) (R 7) [34,65,9,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33760 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 67 13 14 400 240 240 240 496), lower := (rows 35 67 13 14 400 32 64 128 256), losses := [] }

theorem u33760 : Upper (D 7) (R 7) [34,65,9,6,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33761 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 26 52 480 448 448 448), lower := (rows 35 67 13 26 52 32 64 128 256), losses := [] }

theorem u33761 : Upper (D 7) (R 7) [34,65,9,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33762 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 28, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 26 84 416 480 416 416), lower := (rows 35 67 13 26 84 32 64 128 256), losses := [] }

theorem u33762 : Upper (D 7) (R 7) [34,65,9,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33763 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 26 112 420 452 388 388), lower := (rows 35 67 13 26 112 32 64 128 256), losses := [] }

theorem u33763 : Upper (D 7) (R 7) [34,65,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33764 : Route 9 := (fun mask => (mask,id))

def c33764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33764 : Upper (D 7) (R 7) [34,65,9,18,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18,132] 13 (by decide) (choices 1) [64,128,256] r33764 c33764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17923
  · exact u17924
  · exact u17925

def r33765 : Route 9 := (fun mask => (mask,id))

def c33765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33765 : Upper (D 7) (R 7) [34,65,9,18,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18,160] 13 (by decide) (choices 1) [4,64,128,256] r33765 c33765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17926
  · exact u17927
  · exact u17928
  · exact u17929

def b33766 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 67 13 26 208 420 484 420 420), lower := (rows 35 67 13 26 208 32 64 128 256), losses := [] }

theorem u33766 : Upper (D 7) (R 7) [34,65,9,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33767 : Route 9 := (fun mask => (mask,id))

def c33767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33767 : Upper (D 7) (R 7) [34,65,9,18,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18,260] 13 (by decide) (choices 1) [64,128] r33767 c33767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17930
  · exact u17931

def r33768 : Route 9 := (fun mask => (mask,id))

def c33768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33768 : Upper (D 7) (R 7) [34,65,9,18,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18,288] 13 (by decide) (choices 1) [4,64,128] r33768 c33768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17932
  · exact u17933
  · exact u17934

def b33769 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 67 13 26 336 164 228 164 420), lower := (rows 35 67 13 26 336 32 64 128 256), losses := [] }

theorem u33769 : Upper (D 7) (R 7) [34,65,9,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33770 : Route 9 := (fun mask => (mask,id))

def c33770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33770 : Upper (D 7) (R 7) [34,65,9,18,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18,384] 13 (by decide) (choices 1) [4,64,128] r33770 c33770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17935
  · exact u17936
  · exact u17937

def b33771 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 28 50 480 448 448 448), lower := (rows 35 67 13 28 50 32 64 128 256), losses := [] }

theorem u33771 : Upper (D 7) (R 7) [34,65,9,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33772 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 28, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 28 82 416 480 416 416), lower := (rows 35 67 13 28 82 32 64 128 256), losses := [] }

theorem u33772 : Upper (D 7) (R 7) [34,65,9,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33773 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 28 112 418 450 386 386), lower := (rows 35 67 13 28 112 32 64 128 256), losses := [] }

theorem u33773 : Upper (D 7) (R 7) [34,65,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33774 : Route 9 := (fun mask => (mask,id))

def c33774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33774 : Upper (D 7) (R 7) [34,65,9,20,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,130] 13 (by decide) (choices 1) [64,128,256] r33774 c33774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17938
  · exact u17939
  · exact u17940

def r33775 : Route 9 := (fun mask => (mask,id))

def c33775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33775 : Upper (D 7) (R 7) [34,65,9,20,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,160] 13 (by decide) (choices 1) [2,64,128,256] r33775 c33775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17941
  · exact u17942
  · exact u17943
  · exact u17944

def r33776 : Route 9 := (fun mask => (mask,id))

def c33776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33776 : Upper (D 7) (R 7) [34,65,9,20,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,192] 13 (by decide) (choices 1) [2,128,256] r33776 c33776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17945
  · exact u17946
  · exact u17947

def r33777 : Route 9 := (fun mask => (mask,id))

def c33777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33777 : Upper (D 7) (R 7) [34,65,9,20,258] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,258] 13 (by decide) (choices 1) [64,128] r33777 c33777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17948
  · exact u17949

def r33778 : Route 9 := (fun mask => (mask,id))

def c33778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33778 : Upper (D 7) (R 7) [34,65,9,20,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,288] 13 (by decide) (choices 1) [2,64,128] r33778 c33778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17950
  · exact u17951
  · exact u17952

def r33779 : Route 9 := (fun mask => (mask,id))

def c33779 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33779 : Upper (D 7) (R 7) [34,65,9,20,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,320] 13 (by decide) (choices 1) [2,128] r33779 c33779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17953
  · exact u17954

#print axioms u33779
end Delivery.IrregularNine14.P07
