import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12720 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 400 232 232 232 488), lower := (rows 97 7 37 26 400 32 64 128 256), losses := [] }

theorem u12720 : Upper (D 8) (R 8) [96,5,33,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12721 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 42 88 432 464 400 400), lower := (rows 97 7 37 42 88 32 64 128 256), losses := [] }

theorem u12721 : Upper (D 8) (R 8) [96,5,33,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12722 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 42 152 496 464 464 464), lower := (rows 97 7 37 42 152 32 64 128 256), losses := [] }

theorem u12722 : Upper (D 8) (R 8) [96,5,33,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12723 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 42 208 440 472 408 408), lower := (rows 97 7 37 42 208 32 64 128 256), losses := [] }

theorem u12723 : Upper (D 8) (R 8) [96,5,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12724 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 42 280 240 208 208 464), lower := (rows 97 7 37 42 280 32 64 128 256), losses := [] }

theorem u12724 : Upper (D 8) (R 8) [96,5,33,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12725 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 42 336 184 216 152 408), lower := (rows 97 7 37 42 336 32 64 128 256), losses := [] }

theorem u12725 : Upper (D 8) (R 8) [96,5,33,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12726 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 42 400 248 216 216 472), lower := (rows 97 7 37 42 400 32 64 128 256), losses := [] }

theorem u12726 : Upper (D 8) (R 8) [96,5,33,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12727 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 56 82 424 456 392 392), lower := (rows 97 7 37 56 82 32 64 128 256), losses := [] }

theorem u12727 : Upper (D 8) (R 8) [96,5,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12728 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 56 146 488 456 456 456), lower := (rows 97 7 37 56 146 32 64 128 256), losses := [] }

theorem u12728 : Upper (D 8) (R 8) [96,5,33,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12729 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 56 152 482 450 450 450), lower := (rows 97 7 37 56 152 32 64 128 256), losses := [] }

theorem u12729 : Upper (D 8) (R 8) [96,5,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12730 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 56 208 426 458 394 394), lower := (rows 97 7 37 56 208 32 64 128 256), losses := [] }

theorem u12730 : Upper (D 8) (R 8) [96,5,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12731 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 56 274 232 200 200 456), lower := (rows 97 7 37 56 274 32 64 128 256), losses := [] }

theorem u12731 : Upper (D 8) (R 8) [96,5,33,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12732 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 56 280 226 194 194 450), lower := (rows 97 7 37 56 280 32 64 128 256), losses := [] }

theorem u12732 : Upper (D 8) (R 8) [96,5,33,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12733 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 56 336 170 202 138 394), lower := (rows 97 7 37 56 336 32 64 128 256), losses := [] }

theorem u12733 : Upper (D 8) (R 8) [96,5,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12734 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 56 400 234 202 202 458), lower := (rows 97 7 37 56 400 32 64 128 256), losses := [] }

theorem u12734 : Upper (D 8) (R 8) [96,5,33,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12735 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 152 432 496 432 432), lower := (rows 97 7 37 74 152 32 64 128 256), losses := [] }

theorem u12735 : Upper (D 8) (R 8) [96,5,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12736 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 176 440 472 408 408), lower := (rows 97 7 37 74 176 32 64 128 256), losses := [] }

theorem u12736 : Upper (D 8) (R 8) [96,5,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12737 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 280 176 240 176 432), lower := (rows 97 7 37 74 280 32 64 128 256), losses := [] }

theorem u12737 : Upper (D 8) (R 8) [96,5,33,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12738 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 304 184 216 152 408), lower := (rows 97 7 37 74 304 32 64 128 256), losses := [] }

theorem u12738 : Upper (D 8) (R 8) [96,5,33,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12739 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 400 184 248 184 440), lower := (rows 97 7 37 74 400 32 64 128 256), losses := [] }

theorem u12739 : Upper (D 8) (R 8) [96,5,33,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12740 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 146 424 488 424 424), lower := (rows 97 7 37 88 146 32 64 128 256), losses := [] }

theorem u12740 : Upper (D 8) (R 8) [96,5,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12741 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 176 426 458 394 394), lower := (rows 97 7 37 88 176 32 64 128 256), losses := [] }

theorem u12741 : Upper (D 8) (R 8) [96,5,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12742 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 274 168 232 168 424), lower := (rows 97 7 37 88 274 32 64 128 256), losses := [] }

theorem u12742 : Upper (D 8) (R 8) [96,5,33,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12743 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 304 170 202 138 394), lower := (rows 97 7 37 88 304 32 64 128 256), losses := [] }

theorem u12743 : Upper (D 8) (R 8) [96,5,33,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12744 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 400 170 234 170 426), lower := (rows 97 7 37 88 400 32 64 128 256), losses := [] }

theorem u12744 : Upper (D 8) (R 8) [96,5,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12745 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 176 376 344 472 344), lower := (rows 97 7 37 138 176 32 64 128 256), losses := [] }

theorem u12745 : Upper (D 8) (R 8) [96,5,33,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12746 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 208 312 376 440 312), lower := (rows 97 7 37 138 208 32 64 128 256), losses := [] }

theorem u12746 : Upper (D 8) (R 8) [96,5,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12747 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 280 240 240 240 496), lower := (rows 97 7 37 138 280 32 64 128 256), losses := [] }

theorem u12747 : Upper (D 8) (R 8) [96,5,33,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12748 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 304 248 216 216 472), lower := (rows 97 7 37 138 304 32 64 128 256), losses := [] }

theorem u12748 : Upper (D 8) (R 8) [96,5,33,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12749 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 336 184 248 184 440), lower := (rows 97 7 37 138 336 32 64 128 256), losses := [] }

theorem u12749 : Upper (D 8) (R 8) [96,5,33,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12750 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 400 120 120 248 376), lower := (rows 97 7 37 138 400 32 64 128 256), losses := [] }

theorem u12750 : Upper (D 8) (R 8) [96,5,33,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12751 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 152 274 232 232 232 488), lower := (rows 97 7 37 152 274 32 64 128 256), losses := [] }

theorem u12751 : Upper (D 8) (R 8) [96,5,33,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12752 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 152 280 226 226 226 482), lower := (rows 97 7 37 152 280 32 64 128 256), losses := [] }

theorem u12752 : Upper (D 8) (R 8) [96,5,33,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12753 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 152 304 234 202 202 458), lower := (rows 97 7 37 152 304 32 64 128 256), losses := [] }

theorem u12753 : Upper (D 8) (R 8) [96,5,33,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12754 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 152 336 170 234 170 426), lower := (rows 97 7 37 152 336 32 64 128 256), losses := [] }

theorem u12754 : Upper (D 8) (R 8) [96,5,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12755 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 168 208 314 346 410 282), lower := (rows 97 7 37 168 208 32 64 128 256), losses := [] }

theorem u12755 : Upper (D 8) (R 8) [96,5,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12756 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 168 274 248 216 216 472), lower := (rows 97 7 37 168 274 32 64 128 256), losses := [] }

theorem u12756 : Upper (D 8) (R 8) [96,5,33,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12757 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 168 280 242 210 210 466), lower := (rows 97 7 37 168 280 32 64 128 256), losses := [] }

theorem u12757 : Upper (D 8) (R 8) [96,5,33,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12758 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 168 336 186 218 154 410), lower := (rows 97 7 37 168 336 32 64 128 256), losses := [] }

theorem u12758 : Upper (D 8) (R 8) [96,5,33,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12759 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 168 400 122 90 218 346), lower := (rows 97 7 37 168 400 32 64 128 256), losses := [] }

theorem u12759 : Upper (D 8) (R 8) [96,5,33,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12760 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 274 184 248 184 440), lower := (rows 97 7 37 200 274 32 64 128 256), losses := [] }

theorem u12760 : Upper (D 8) (R 8) [96,5,33,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12761 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 280 178 242 178 434), lower := (rows 97 7 37 200 280 32 64 128 256), losses := [] }

theorem u12761 : Upper (D 8) (R 8) [96,5,33,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12762 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 304 186 218 154 410), lower := (rows 97 7 37 200 304 32 64 128 256), losses := [] }

theorem u12762 : Upper (D 8) (R 8) [96,5,33,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12763 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 400 58 122 186 314), lower := (rows 97 7 37 200 400 32 64 128 256), losses := [] }

theorem u12763 : Upper (D 8) (R 8) [96,5,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12764 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 25 152 480 480 480 480), lower := (rows 97 7 38 25 152 32 64 128 256), losses := [] }

theorem u12764 : Upper (D 8) (R 8) [96,5,34,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12765 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 25 176 488 456 456 456), lower := (rows 97 7 38 25 176 32 64 128 256), losses := [] }

theorem u12765 : Upper (D 8) (R 8) [96,5,34,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12766 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 25 280 224 224 224 480), lower := (rows 97 7 38 25 280 32 64 128 256), losses := [] }

theorem u12766 : Upper (D 8) (R 8) [96,5,34,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12766 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12767 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 25 304 232 200 200 456), lower := (rows 97 7 38 25 304 32 64 128 256), losses := [] }

theorem u12767 : Upper (D 8) (R 8) [96,5,34,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12768 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 25 400 232 232 232 488), lower := (rows 97 7 38 25 400 32 64 128 256), losses := [] }

theorem u12768 : Upper (D 8) (R 8) [96,5,34,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12769 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 56 145 488 456 456 456), lower := (rows 97 7 38 56 145 32 64 128 256), losses := [] }

theorem u12769 : Upper (D 8) (R 8) [96,5,34,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12770 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 56 152 481 449 449 449), lower := (rows 97 7 38 56 152 32 64 128 256), losses := [] }

theorem u12770 : Upper (D 8) (R 8) [96,5,34,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12771 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 56 208 425 457 393 393), lower := (rows 97 7 38 56 208 32 64 128 256), losses := [] }

theorem u12771 : Upper (D 8) (R 8) [96,5,34,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12772 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 56 273 232 200 200 456), lower := (rows 97 7 38 56 273 32 64 128 256), losses := [] }

theorem u12772 : Upper (D 8) (R 8) [96,5,34,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12773 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 56 280 225 193 193 449), lower := (rows 97 7 38 56 280 32 64 128 256), losses := [] }

theorem u12773 : Upper (D 8) (R 8) [96,5,34,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12774 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 56 336 169 201 137 393), lower := (rows 97 7 38 56 336 32 64 128 256), losses := [] }

theorem u12774 : Upper (D 8) (R 8) [96,5,34,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12775 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 56 400 233 201 201 457), lower := (rows 97 7 38 56 400 32 64 128 256), losses := [] }

theorem u12775 : Upper (D 8) (R 8) [96,5,34,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12776 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 88 145 424 488 424 424), lower := (rows 97 7 38 88 145 32 64 128 256), losses := [] }

theorem u12776 : Upper (D 8) (R 8) [96,5,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12777 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 88 176 425 457 393 393), lower := (rows 97 7 38 88 176 32 64 128 256), losses := [] }

theorem u12777 : Upper (D 8) (R 8) [96,5,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12778 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 88 273 168 232 168 424), lower := (rows 97 7 38 88 273 32 64 128 256), losses := [] }

theorem u12778 : Upper (D 8) (R 8) [96,5,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12779 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 88 304 169 201 137 393), lower := (rows 97 7 38 88 304 32 64 128 256), losses := [] }

theorem u12779 : Upper (D 8) (R 8) [96,5,34,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12779
end Delivery.IrregularNine14.P08
