import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0010

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2640 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 13 392 80 178 242 178 434), lower := (rows 51 70 13 392 80 32 64 128 256), losses := [] }

theorem u2640 : Upper (D 1) (R 1) [50,68,9,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2640
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2641 : PairBound 9 := { available := 114, camps := [], pairs := [(1,7)], upper := (rows 51 70 13 392 144 114 114 242 370), lower := (rows 51 70 13 392 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 33 65 0 257), good := (rows 371 70 367 264 16 32 64 0 256) }] }

theorem u2641 : Upper (D 1) (R 1) [50,68,9,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2641
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2642 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 133 88 18 424 488 424 424), lower := (rows 51 70 133 88 18 32 64 128 256), losses := [] }

theorem u2642 : Upper (D 1) (R 1) [50,68,129,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2642
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2643 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 51 70 133 88 24 418 482 418 418), lower := (rows 51 70 133 88 24 32 64 128 256), losses := [] }

theorem u2643 : Upper (D 1) (R 1) [50,68,129,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2644 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 88 48 426 458 394 394), lower := (rows 51 70 133 88 48 32 64 128 256), losses := [] }

theorem u2644 : Upper (D 1) (R 1) [50,68,129,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2644
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2645 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 133 88 144 298 362 426 298), lower := (rows 51 70 133 88 144 32 64 128 256), losses := [] }

theorem u2645 : Upper (D 1) (R 1) [50,68,129,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2645
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2646 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 70 133 88 272 170 234 170 426), lower := (rows 51 70 133 88 272 32 64 128 256), losses := [] }

theorem u2646 : Upper (D 1) (R 1) [50,68,129,80,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2646
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2647 : PairBound 9 := { available := 360, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 133 152 18 360 360 488 360), lower := (rows 51 70 133 152 18 32 64 128 256), losses := [] }

theorem u2647 : Upper (D 1) (R 1) [50,68,129,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2648 : PairBound 9 := { available := 354, camps := [], pairs := [], upper := (rows 51 70 133 152 24 354 354 482 354), lower := (rows 51 70 133 152 24 32 64 128 256), losses := [] }

theorem u2648 : Upper (D 1) (R 1) [50,68,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2648
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2649 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 152 48 362 330 458 330), lower := (rows 51 70 133 152 48 32 64 128 256), losses := [] }

theorem u2649 : Upper (D 1) (R 1) [50,68,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2649
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2650 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 152 80 298 362 426 298), lower := (rows 51 70 133 152 80 32 64 128 256), losses := [] }

theorem u2650 : Upper (D 1) (R 1) [50,68,129,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2650
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2651 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 51 70 133 152 272 106 106 234 362), lower := (rows 51 70 133 152 272 32 64 128 256), losses := [] }

theorem u2651 : Upper (D 1) (R 1) [50,68,129,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2651
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2652 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 133 200 18 312 376 440 312), lower := (rows 51 70 133 200 18 32 64 128 256), losses := [] }

theorem u2652 : Upper (D 1) (R 1) [50,68,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2652
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2653 : PairBound 9 := { available := 306, camps := [], pairs := [], upper := (rows 51 70 133 200 24 306 370 434 306), lower := (rows 51 70 133 200 24 32 64 128 256), losses := [] }

theorem u2653 : Upper (D 1) (R 1) [50,68,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2653
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2654 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 200 48 314 346 410 282), lower := (rows 51 70 133 200 48 32 64 128 256), losses := [] }

theorem u2654 : Upper (D 1) (R 1) [50,68,129,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2654
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2655 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 51 70 133 200 272 58 122 186 314), lower := (rows 51 70 133 200 272 32 64 128 256), losses := [] }

theorem u2655 : Upper (D 1) (R 1) [50,68,129,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2655
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2656 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 70 133 266 24 240 240 240 496), lower := (rows 51 70 133 266 24 32 64 128 256), losses := [] }

theorem u2656 : Upper (D 1) (R 1) [50,68,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2657 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 266 48 248 216 216 472), lower := (rows 51 70 133 266 48 32 64 128 256), losses := [] }

theorem u2657 : Upper (D 1) (R 1) [50,68,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2658 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 266 80 184 248 184 440), lower := (rows 51 70 133 266 80 32 64 128 256), losses := [] }

theorem u2658 : Upper (D 1) (R 1) [50,68,129,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2658
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2659 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 133 266 144 120 120 248 376), lower := (rows 51 70 133 266 144 32 64 128 256), losses := [] }

theorem u2659 : Upper (D 1) (R 1) [50,68,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2659
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2660 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 133 280 18 232 232 232 488), lower := (rows 51 70 133 280 18 32 64 128 256), losses := [] }

theorem u2660 : Upper (D 1) (R 1) [50,68,129,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2660
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2661 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 70 133 280 24 226 226 226 482), lower := (rows 51 70 133 280 24 32 64 128 256), losses := [] }

theorem u2661 : Upper (D 1) (R 1) [50,68,129,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2661
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2662 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 280 48 234 202 202 458), lower := (rows 51 70 133 280 48 32 64 128 256), losses := [] }

theorem u2662 : Upper (D 1) (R 1) [50,68,129,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2663 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 280 80 170 234 170 426), lower := (rows 51 70 133 280 80 32 64 128 256), losses := [] }

theorem u2663 : Upper (D 1) (R 1) [50,68,129,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2663
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 106, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 133 280 144 106 106 234 362), lower := (rows 51 70 133 280 144 32 64 128 256), losses := [] }

theorem u2664 : Upper (D 1) (R 1) [50,68,129,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2664
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 133 328 18 184 248 184 440), lower := (rows 51 70 133 328 18 32 64 128 256), losses := [] }

theorem u2665 : Upper (D 1) (R 1) [50,68,129,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2665
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 70 133 328 24 178 242 178 434), lower := (rows 51 70 133 328 24 32 64 128 256), losses := [] }

theorem u2666 : Upper (D 1) (R 1) [50,68,129,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2667 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 328 48 186 218 154 410), lower := (rows 51 70 133 328 48 32 64 128 256), losses := [] }

theorem u2667 : Upper (D 1) (R 1) [50,68,129,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2667
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2668 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 133 328 144 58 122 186 314), lower := (rows 51 70 133 328 144 32 64 128 256), losses := [] }

theorem u2668 : Upper (D 1) (R 1) [50,68,129,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2668
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2669 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 133 392 18 120 120 248 376), lower := (rows 51 70 133 392 18 32 64 128 256), losses := [] }

theorem u2669 : Upper (D 1) (R 1) [50,68,129,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2669
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2670 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 51 70 133 392 24 114 114 242 370), lower := (rows 51 70 133 392 24 32 64 128 256), losses := [] }

theorem u2670 : Upper (D 1) (R 1) [50,68,129,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2670
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2671 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 392 48 122 90 218 346), lower := (rows 51 70 133 392 48 32 64 128 256), losses := [] }

theorem u2671 : Upper (D 1) (R 1) [50,68,129,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2671
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2672 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 392 80 58 122 186 314), lower := (rows 51 70 133 392 80 32 64 128 256), losses := [] }

theorem u2672 : Upper (D 1) (R 1) [50,68,129,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2672
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 140 265 18 240 240 240 496), lower := (rows 51 70 140 265 18 32 64 128 256), losses := [] }

theorem u2673 : Upper (D 1) (R 1) [50,68,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2673
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2674 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 140 265 48 242 210 210 466), lower := (rows 51 70 140 265 48 32 64 128 256), losses := [] }

theorem u2674 : Upper (D 1) (R 1) [50,68,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2674
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2675 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 140 265 80 178 242 178 434), lower := (rows 51 70 140 265 80 32 64 128 256), losses := [] }

theorem u2675 : Upper (D 1) (R 1) [50,68,136,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2675
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2676 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 140 265 144 114 114 242 370), lower := (rows 51 70 140 265 144 32 64 128 256), losses := [] }

theorem u2676 : Upper (D 1) (R 1) [50,68,136,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2676
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2677 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 70 140 266 17 240 240 240 496), lower := (rows 51 70 140 266 17 32 64 128 256), losses := [] }

theorem u2677 : Upper (D 1) (R 1) [50,68,136,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2677
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2678 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 140 266 48 241 209 209 465), lower := (rows 51 70 140 266 48 32 64 128 256), losses := [] }

theorem u2678 : Upper (D 1) (R 1) [50,68,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2678
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2679 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 140 266 80 177 241 177 433), lower := (rows 51 70 140 266 80 32 64 128 256), losses := [] }

theorem u2679 : Upper (D 1) (R 1) [50,68,136,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2679
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2680 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 140 266 144 113 113 241 369), lower := (rows 51 70 140 266 144 32 64 128 256), losses := [] }

theorem u2680 : Upper (D 1) (R 1) [50,68,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2681 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 70 140 280 17 226 226 226 482), lower := (rows 51 70 140 280 17 32 64 128 256), losses := [] }

theorem u2681 : Upper (D 1) (R 1) [50,68,136,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2682 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 140 280 18 225 225 225 481), lower := (rows 51 70 140 280 18 32 64 128 256), losses := [] }

theorem u2682 : Upper (D 1) (R 1) [50,68,136,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2683 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 140 280 48 227 195 195 451), lower := (rows 51 70 140 280 48 32 64 128 256), losses := [] }

theorem u2683 : Upper (D 1) (R 1) [50,68,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2683
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2684 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 140 280 80 163 227 163 419), lower := (rows 51 70 140 280 80 32 64 128 256), losses := [] }

theorem u2684 : Upper (D 1) (R 1) [50,68,136,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2684
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2685 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 140 280 144 99 99 227 355), lower := (rows 51 70 140 280 144 32 64 128 256), losses := [] }

theorem u2685 : Upper (D 1) (R 1) [50,68,136,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2685
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2686 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 261 88 18 168 232 168 424), lower := (rows 51 70 261 88 18 32 64 128 256), losses := [] }

theorem u2686 : Upper (D 1) (R 1) [50,68,257,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2686
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2687 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 70 261 88 24 162 226 162 418), lower := (rows 51 70 261 88 24 32 64 128 256), losses := [] }

theorem u2687 : Upper (D 1) (R 1) [50,68,257,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2687
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2688 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 88 48 170 202 138 394), lower := (rows 51 70 261 88 48 32 64 128 256), losses := [] }

theorem u2688 : Upper (D 1) (R 1) [50,68,257,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2688
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2689 : Route 9 := (fun mask => (mask,id))

def c2689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2689 : Upper (D 1) (R 1) [50,68,257,80,128] 13 := by
  apply FastRouting.sound _ _ [50,68,257,80,128] 13 (by decide) (choices 1) [2,8,128] r2689 c2689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u603
  · exact u604
  · exact u605

def b2690 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 70 261 138 24 240 240 240 496), lower := (rows 51 70 261 138 24 32 64 128 256), losses := [] }

theorem u2690 : Upper (D 1) (R 1) [50,68,257,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2690
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2691 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 138 48 248 216 216 472), lower := (rows 51 70 261 138 48 32 64 128 256), losses := [] }

theorem u2691 : Upper (D 1) (R 1) [50,68,257,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2691
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2692 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 261 138 80 184 248 184 440), lower := (rows 51 70 261 138 80 32 64 128 256), losses := [] }

theorem u2692 : Upper (D 1) (R 1) [50,68,257,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2692
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2693_8 : Upper (D 1) (R 1) [50,68,257,130,128,8] 13 :=
  permutation_upper _ _ _ [50,68,257,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u606

theorem m2693_16 : Upper (D 1) (R 1) [50,68,257,130,128,16] 13 :=
  permutation_upper _ _ _ [50,68,257,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u607

theorem m2693_64 : Upper (D 1) (R 1) [50,68,257,130,128,64] 13 :=
  permutation_upper _ _ _ [50,68,257,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u608

def r2693 : Route 9 := (fun mask => (mask,id))

def c2693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2693 : Upper (D 1) (R 1) [50,68,257,130,128] 13 := by
  apply FastRouting.sound _ _ [50,68,257,130,128] 13 (by decide) (choices 1) [8,16,64] r2693 c2693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2693_8
  · exact m2693_16
  · exact m2693_64

def b2694 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 261 152 18 232 232 232 488), lower := (rows 51 70 261 152 18 32 64 128 256), losses := [] }

theorem u2694 : Upper (D 1) (R 1) [50,68,257,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2694
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2695 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 70 261 152 24 226 226 226 482), lower := (rows 51 70 261 152 24 32 64 128 256), losses := [] }

theorem u2695 : Upper (D 1) (R 1) [50,68,257,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2695
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2696 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 152 48 234 202 202 458), lower := (rows 51 70 261 152 48 32 64 128 256), losses := [] }

theorem u2696 : Upper (D 1) (R 1) [50,68,257,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2696
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2697 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 261 152 80 170 234 170 426), lower := (rows 51 70 261 152 80 32 64 128 256), losses := [] }

theorem u2697 : Upper (D 1) (R 1) [50,68,257,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2697
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2698 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 70 261 152 144 106 106 234 362), lower := (rows 51 70 261 152 144 32 64 128 256), losses := [] }

theorem u2698 : Upper (D 1) (R 1) [50,68,257,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2698
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2699 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 261 200 18 184 248 184 440), lower := (rows 51 70 261 200 18 32 64 128 256), losses := [] }

theorem u2699 : Upper (D 1) (R 1) [50,68,257,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2699
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2699
end Delivery.IrregularNine14.P01
