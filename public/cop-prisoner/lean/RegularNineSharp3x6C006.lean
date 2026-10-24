import RegularNineSharp3x6Base
import RegularNineSharp3x6C000
import RegularNineSharp3x6C002
import RegularNineSharp3x6C003
import RegularNineSharp3x6C005
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
theorem node384 : UpperPrefix a [2,3] 30 :=
  branch_upper a [2,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut6 [2,3,1] [2,0,3] 30 (by decide +kernel) node6)
  (invalid_upper a [2,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,3] 30 (by decide +kernel))
  node40
  node128
  node231
  node338
  node383)

theorem node385 : UpperPrefix a [2] 30 :=
  branch_upper a [2] 30 (by decide) (fin9_cases _
  node7
  (invalid_upper a [2,1] 30 (by decide +kernel))
  (invalid_upper a [2,2] 30 (by decide +kernel))
  node384
  (PrefixConjugacy.upper aut5 [2,4] [2,3] 30 (by decide +kernel) node384)
  (PrefixConjugacy.upper aut4 [2,5] [2,3] 30 (by decide +kernel) node384)
  (PrefixConjugacy.upper aut3 [2,6] [2,3] 30 (by decide +kernel) node384)
  (PrefixConjugacy.upper aut2 [2,7] [2,3] 30 (by decide +kernel) node384)
  (PrefixConjugacy.upper aut1 [2,8] [2,3] 30 (by decide +kernel) node384))

theorem node386 : UpperPrefix a [3,0] 30 :=
  branch_upper a [3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut12 [3,0,1] [2,0,3] 30 (by decide +kernel) node6)
  (invalid_upper a [3,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut17 [3,0,4] [2,3,8] 30 (by decide +kernel) node383)
  (PrefixConjugacy.upper aut16 [3,0,5] [2,3,7] 30 (by decide +kernel) node338)
  (PrefixConjugacy.upper aut15 [3,0,6] [2,3,6] 30 (by decide +kernel) node231)
  (PrefixConjugacy.upper aut14 [3,0,7] [2,3,5] 30 (by decide +kernel) node128)
  (PrefixConjugacy.upper aut13 [3,0,8] [2,3,4] 30 (by decide +kernel) node40))

def cert387 : Leaf := ⟨⟨20,41,8,6,13,397,269,77,197⟩,[],[(4,1,0),(5,2,1),(1,4,3)],⟨11,22,37,25,50,484,452,452,460⟩,⟨11,22,37,25,50,96,192,384,264⟩,[⟨6,1210106412364828240805183,⟨11,31,63,31,63,63,128,385,267⟩⟩,⟨7,1208926973665615436348735,⟨11,31,63,31,63,127,64,257,267⟩⟩,⟨8,1181745671703672945983,⟨11,31,63,31,63,127,192,129,11⟩⟩]⟩
theorem node387 : UpperPrefix a [3,4,5,0,1] 30 :=
  Boolean.leaf_sound a [3,4,5,0,1] 30 cert387 (by decide +kernel)

def cert388 : Local := ⟨⟨464,0,458,450,0,395,267,75,195⟩,[(1,4),(4,2)],[(4,1,0),(5,2,1),(5,2,4),(2,4,1)]⟩
theorem node388 : UpperPrefix a [3,4,5,0,2] 30 :=
  local_sound a [3,4,5,0,2] 30 cert388 (by decide +kernel)

def cert389 : Leaf := ⟨⟨20,41,10,6,0,399,271,15,135⟩,[(4,5)],[(4,1,0),(5,2,1),(6,4,4)],⟨11,22,37,25,112,486,454,390,398⟩,⟨11,22,37,25,112,96,192,384,264⟩,[⟨7,1208926973665340558441791,⟨11,31,63,31,127,127,64,257,267⟩⟩,⟨8,1181745671428795039039,⟨11,31,63,31,127,127,192,129,11⟩⟩]⟩
theorem node389 : UpperPrefix a [3,4,5,0,6] 30 :=
  Boolean.leaf_sound a [3,4,5,0,6] 30 cert389 (by decide +kernel)

def cert390 : Leaf := ⟨⟨20,41,10,4,77,141,269,77,69⟩,[],[(4,1,0),(5,2,1),(1,5,2)],⟨11,22,37,25,176,98,452,452,332⟩,⟨11,22,37,25,176,98,192,384,264⟩,[⟨8,1181747925435701851519,⟨11,31,47,31,191,127,255,129,11⟩⟩,⟨7,1360042701114965350167867,⟨11,31,293,31,319,367,64,257,267⟩⟩,⟨6,1210106412362349507786043,⟨11,31,37,31,191,47,128,385,267⟩⟩]⟩
theorem node390 : UpperPrefix a [3,4,5,0,7,1] 30 :=
  Boolean.leaf_sound a [3,4,5,0,7,1] 30 cert390 (by decide +kernel)

def cert391 : Leaf := ⟨⟨208,232,202,194,74,138,266,74,194⟩,[],[(4,1,0),(5,2,1)],⟨11,22,37,25,176,100,450,450,330⟩,⟨11,22,37,25,176,100,192,384,264⟩,[⟨0,1214876138912684444765184,⟨506,246,502,472,178,246,192,384,264⟩⟩,⟨2,1224302388892042396697603,⟨459,475,505,473,176,120,192,384,264⟩⟩,⟨8,1181747925435701851519,⟨11,31,47,31,191,127,255,129,11⟩⟩]⟩
theorem node391 : UpperPrefix a [3,4,5,0,7,2] 30 :=
  Boolean.leaf_sound a [3,4,5,0,7,2] 30 cert391 (by decide +kernel)

def cert392 : Leaf := ⟨⟨16,41,10,2,335,15,13,79,71⟩,[],[(4,1,0),(5,2,1),(8,5,4)],⟨11,22,37,25,176,352,194,452,332⟩,⟨11,22,37,25,176,352,194,384,264⟩,[⟨7,1511158430818593827468635,⟨11,31,37,31,63,357,367,257,267⟩⟩,⟨6,1210106412362349507786075,⟨11,31,37,31,191,293,139,385,267⟩⟩,⟨2,1210107565283851953505347,⟨11,27,33,25,176,353,203,384,264⟩⟩]⟩
theorem node392 : UpperPrefix a [3,4,5,0,7,8,1] 30 :=
  Boolean.leaf_sound a [3,4,5,0,7,8,1] 30 cert392 (by decide +kernel)

def cert393 : Leaf := ⟨⟨148,160,138,134,326,142,2,70,198⟩,[],[(4,1,0),(5,2,1),(8,5,4)],⟨11,22,37,25,176,352,196,450,330⟩,⟨11,22,37,25,176,352,196,384,264⟩,[⟨0,1215171304802025737325568,⟨506,246,502,440,176,498,246,384,280⟩⟩,⟨3,1210402785249097904327681,⟨3,86,247,17,176,498,214,384,256⟩⟩,⟨6,1210106412362349507786011,⟨11,31,37,31,191,293,132,385,267⟩⟩]⟩
theorem node393 : UpperPrefix a [3,4,5,0,7,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,0,7,8,2] 30 cert393 (by decide +kernel)

theorem node394 : UpperPrefix a [3,4,5,0,7,8] 30 :=
  branch_upper a [3,4,5,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,5,0,7,8,0] 30 (by decide +kernel))
  node392
  node393
  (invalid_upper a [3,4,5,0,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,8,8] 30 (by decide +kernel)))

theorem node395 : UpperPrefix a [3,4,5,0,7] 30 :=
  branch_upper a [3,4,5,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,5,0,7,0] 30 (by decide +kernel))
  node390
  node391
  (invalid_upper a [3,4,5,0,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,7,7] 30 (by decide +kernel))
  node394)

def cert396 : Leaf := ⟨⟨276,289,258,260,197,389,261,69,197⟩,[],[(4,1,0),(5,2,1),(1,5,2)],⟨11,22,37,25,304,98,196,452,460⟩,⟨11,22,37,25,304,98,192,384,264⟩,[⟨3,1212473374311440979203073,⟨7,54,37,55,498,98,240,498,502⟩⟩,⟨6,1210106412362349507786043,⟨11,31,37,31,319,47,128,385,267⟩⟩,⟨7,1208926973663136703329595,⟨11,31,37,31,319,111,64,257,267⟩⟩]⟩
theorem node396 : UpperPrefix a [3,4,5,0,8,1] 30 :=
  Boolean.leaf_sound a [3,4,5,0,8,1] 30 cert396 (by decide +kernel)

def cert397 : Leaf := ⟨⟨464,480,450,450,194,386,258,66,194⟩,[],[(4,1,0),(5,2,1)],⟨11,22,37,25,304,100,194,450,458⟩,⟨11,22,37,25,304,100,192,384,264⟩,[⟨0,1215024613582863133068288,⟨506,246,502,472,498,246,192,384,264⟩⟩,⟨2,1224302388892042396697603,⟨459,475,505,473,304,120,192,384,264⟩⟩,⟨3,1212623717801879628289025,⟨103,246,37,247,498,100,208,498,502⟩⟩]⟩
theorem node397 : UpperPrefix a [3,4,5,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,0,8,2] 30 cert397 (by decide +kernel)

def cert398 : Leaf := ⟨⟨276,289,258,262,71,0,263,71,71⟩,[(5,6)],[(4,1,0),(5,2,1),(7,5,5)],⟨11,22,37,25,304,224,198,454,334⟩,⟨11,22,37,25,304,224,192,384,264⟩,[⟨3,1212473376563240792888321,⟨7,54,37,55,498,240,240,498,502⟩⟩,⟨6,1210106412362349499397403,⟨11,31,37,31,319,160,128,385,267⟩⟩]⟩
theorem node398 : UpperPrefix a [3,4,5,0,8,7] 30 :=
  Boolean.leaf_sound a [3,4,5,0,8,7] 30 cert398 (by decide +kernel)

theorem node399 : UpperPrefix a [3,4,5,0,8] 30 :=
  branch_upper a [3,4,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,5,0,8,0] 30 (by decide +kernel))
  node396
  node397
  (invalid_upper a [3,4,5,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,8,6] 30 (by decide +kernel))
  node398
  (invalid_upper a [3,4,5,0,8,8] 30 (by decide +kernel)))

theorem node400 : UpperPrefix a [3,4,5,0] 30 :=
  branch_upper a [3,4,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,5,0,0] 30 (by decide +kernel))
  node387
  node388
  (invalid_upper a [3,4,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,0,5] 30 (by decide +kernel))
  node389
  node395
  node399)

def cert401 : Leaf := ⟨⟨0,297,264,0,461,397,269,77,197⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(5,2,1),(1,3,0)],⟨11,22,37,26,501,485,453,453,461⟩,⟨11,22,37,26,48,96,192,384,264⟩,[⟨6,1210106412362349499397403,⟨11,31,37,31,63,32,128,385,267⟩⟩,⟨7,1208926973663136694940955,⟨11,31,37,31,63,96,64,257,267⟩⟩]⟩
theorem node401 : UpperPrefix a [3,4,5,1] 30 :=
  Boolean.leaf_sound a [3,4,5,1] 30 cert401 (by decide +kernel)

def cert402 : Leaf := ⟨⟨276,0,266,0,459,395,267,75,195⟩,[(1,3),(3,1)],[(4,1,0),(5,2,1),(5,2,3),(2,3,0)],⟨11,22,37,28,499,483,451,451,459⟩,⟨11,22,37,28,48,96,192,384,264⟩,[⟨6,1210106412362349499397403,⟨11,31,37,31,63,32,128,385,267⟩⟩,⟨7,1208926973663136694940955,⟨11,31,37,31,63,96,64,257,267⟩⟩]⟩
theorem node402 : UpperPrefix a [3,4,5,2] 30 :=
  Boolean.leaf_sound a [3,4,5,2] 30 cert402 (by decide +kernel)

def cert403 : Leaf := ⟨⟨404,425,0,390,0,398,270,14,134⟩,[(2,4),(4,2)],[(4,1,0),(5,2,1),(0,4,1)],⟨11,22,37,88,49,486,454,390,398⟩,⟨11,22,37,88,49,96,192,384,264⟩,[⟨6,1247959131201873961303305,⟨395,22,55,415,55,32,128,385,395⟩⟩]⟩
theorem node403 : UpperPrefix a [3,4,5,6,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,0] 30 cert403 (by decide +kernel)

def cert404 : Leaf := ⟨⟨84,104,72,5,76,397,269,77,197⟩,[],[(4,1,0),(5,2,1)],⟨11,22,37,88,50,485,453,389,397⟩,⟨11,22,37,88,50,96,192,384,264⟩,[⟨1,1214876138874820281761793,⟨493,252,485,88,56,96,192,384,264⟩⟩,⟨7,1208926973665612483558717,⟨11,23,63,95,63,127,64,257,267⟩⟩,⟨8,1181745671700720155965,⟨11,23,63,95,63,127,192,129,11⟩⟩,⟨0,1210107565284126564027392,⟨10,22,54,88,50,96,192,384,264⟩⟩]⟩
theorem node404 : UpperPrefix a [3,4,5,6,1] 30 :=
  Boolean.leaf_sound a [3,4,5,6,1] 30 cert404 (by decide +kernel)

def cert405 : Local := ⟨⟨464,0,458,387,0,395,267,75,195⟩,[(1,4),(4,2)],[(4,1,0),(5,2,1),(5,2,4),(2,4,1)]⟩
theorem node405 : UpperPrefix a [3,4,5,6,2] 30 :=
  local_sound a [3,4,5,6,2] 30 cert405 (by decide +kernel)

def cert406 : Leaf := ⟨⟨84,104,0,134,78,14,270,78,70⟩,[(2,5)],[(4,1,0),(5,2,1),(7,4,3),(0,5,2)],⟨11,22,37,88,176,97,454,390,270⟩,⟨11,22,37,88,176,97,192,384,264⟩,[⟨8,1181748206908332111229,⟨47,23,47,127,191,127,255,133,47⟩⟩]⟩
theorem node406 : UpperPrefix a [3,4,5,6,7,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,0] 30 cert406 (by decide +kernel)

def cert407 : Leaf := ⟨⟨84,105,74,133,77,13,12,77,69⟩,[],[(4,1,0),(5,2,1),(7,4,3),(1,5,2)],⟨11,22,37,88,176,98,193,388,268⟩,⟨11,22,37,88,176,98,193,384,264⟩,[⟨8,1184347426027745441279,⟨47,127,47,127,255,127,255,255,47⟩⟩]⟩
theorem node407 : UpperPrefix a [3,4,5,6,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,1,0] 30 cert407 (by decide +kernel)

def cert408 : Leaf := ⟨⟨80,105,74,129,73,13,9,73,65⟩,[],[(4,1,0),(5,2,1),(7,4,3),(1,5,2),(2,6,5)],⟨11,22,37,88,176,98,196,385,265⟩,⟨11,22,37,88,176,98,196,384,264⟩,[⟨8,1184347426027745441279,⟨47,127,47,127,255,127,255,255,47⟩⟩]⟩
theorem node408 : UpperPrefix a [3,4,5,6,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,1,2] 30 cert408 (by decide +kernel)

def cert409 : Local := ⟨⟨84,105,74,133,77,13,0,77,69⟩,[(6,7)],[(4,1,0),(5,2,1),(7,4,3),(1,5,2),(8,6,6)]⟩
theorem node409 : UpperPrefix a [3,4,5,6,7,1,8] 30 :=
  local_sound a [3,4,5,6,7,1,8] 30 cert409 (by decide +kernel)

theorem node410 : UpperPrefix a [3,4,5,6,7,1] 30 :=
  branch_upper a [3,4,5,6,7,1] 30 (by decide) (fin9_cases _
  node407
  (invalid_upper a [3,4,5,6,7,1,1] 30 (by decide +kernel))
  node408
  (invalid_upper a [3,4,5,6,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,1,7] 30 (by decide +kernel))
  node409)

def cert411 : Leaf := ⟨⟨80,105,74,131,75,11,267,75,67⟩,[],[(4,1,0),(5,2,1),(7,4,3)],⟨11,22,37,88,176,100,451,387,267⟩,⟨11,22,37,88,176,100,192,384,264⟩,[⟨2,1224302388892046691664899,⟨459,475,505,88,184,120,192,384,264⟩⟩,⟨8,1181748206908332111229,⟨47,23,47,127,191,127,255,133,47⟩⟩]⟩
theorem node411 : UpperPrefix a [3,4,5,6,7,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,2] 30 cert411 (by decide +kernel)

def cert412 : Local := ⟨⟨84,105,72,133,333,13,14,77,69⟩,[],[(4,1,0),(5,2,1),(7,4,3),(8,5,4),(1,7,6)]⟩
theorem node412 : UpperPrefix a [3,4,5,6,7,8,0,1] 30 :=
  local_sound a [3,4,5,6,7,8,0,1] 30 cert412 (by decide +kernel)

def cert413 : Leaf := ⟨⟨84,104,74,134,334,14,14,74,70⟩,[],[(4,1,0),(5,2,1),(7,4,3),(8,5,4)],⟨11,22,37,88,176,352,193,388,266⟩,⟨11,22,37,88,176,352,193,388,264⟩,[⟨0,1611564059098021977197568,⟨442,406,446,376,442,376,506,406,296⟩⟩]⟩
theorem node413 : UpperPrefix a [3,4,5,6,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,8,0,2] 30 cert413 (by decide +kernel)

theorem node414 : UpperPrefix a [3,4,5,6,7,8,0] 30 :=
  branch_upper a [3,4,5,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,5,6,7,8,0,0] 30 (by decide +kernel))
  node412
  node413
  (invalid_upper a [3,4,5,6,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,0,8] 30 (by decide +kernel)))

def cert415 : Local := ⟨⟨84,97,66,135,327,7,5,78,71⟩,[],[(3,0,7),(4,1,0),(5,2,1),(7,4,3),(8,5,4)]⟩
theorem node415 : UpperPrefix a [3,4,5,6,7,8,1,0] 30 :=
  local_sound a [3,4,5,6,7,8,1,0] 30 cert415 (by decide +kernel)

def cert416 : Local := ⟨⟨80,105,74,131,331,11,13,75,67⟩,[],[(4,1,0),(5,2,1),(7,4,3),(8,5,4),(2,7,6)]⟩
theorem node416 : UpperPrefix a [3,4,5,6,7,8,1,2] 30 :=
  local_sound a [3,4,5,6,7,8,1,2] 30 cert416 (by decide +kernel)

theorem node417 : UpperPrefix a [3,4,5,6,7,8,1] 30 :=
  branch_upper a [3,4,5,6,7,8,1] 30 (by decide) (fin9_cases _
  node415
  (invalid_upper a [3,4,5,6,7,8,1,1] 30 (by decide +kernel))
  node416
  (invalid_upper a [3,4,5,6,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,1,8] 30 (by decide +kernel)))

def cert418 : Leaf := ⟨⟨20,41,74,131,267,15,11,11,3⟩,[],[(4,1,0),(5,2,1),(7,4,3),(8,5,4)],⟨11,22,37,88,176,352,196,387,267⟩,⟨11,22,37,88,176,352,196,384,264⟩,[⟨6,1252727614544927876221961,⟨395,150,439,411,176,290,150,384,393⟩⟩,⟨2,1214839155139041652900865,⟨395,18,433,88,176,360,216,384,264⟩⟩]⟩
theorem node418 : UpperPrefix a [3,4,5,6,7,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,8,2] 30 cert418 (by decide +kernel)

theorem node419 : UpperPrefix a [3,4,5,6,7,8] 30 :=
  branch_upper a [3,4,5,6,7,8] 30 (by decide) (fin9_cases _
  node414
  node417
  node418
  (invalid_upper a [3,4,5,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,8] 30 (by decide +kernel)))

theorem node420 : UpperPrefix a [3,4,5,6,7] 30 :=
  branch_upper a [3,4,5,6,7] 30 (by decide) (fin9_cases _
  node406
  node410
  node411
  (invalid_upper a [3,4,5,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,7] 30 (by decide +kernel))
  node419)

def cert421 : Leaf := ⟨⟨404,416,0,390,206,390,262,6,134⟩,[(2,5)],[(4,1,0),(5,2,1),(0,5,2)],⟨11,22,37,88,304,97,198,390,398⟩,⟨11,22,37,88,304,97,192,384,264⟩,[⟨3,1210255463530797840212993,⟨103,214,37,210,502,101,192,384,256⟩⟩,⟨6,1248106705154188768195849,⟨395,150,37,415,439,37,128,385,395⟩⟩]⟩
theorem node421 : UpperPrefix a [3,4,5,6,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,0] 30 cert421 (by decide +kernel)

def cert422 : Leaf := ⟨⟨20,41,10,389,77,13,13,13,133⟩,[],[(4,1,0),(5,2,1),(1,5,2)],⟨11,22,37,88,304,98,197,389,397⟩,⟨11,22,37,88,304,98,192,384,264⟩,[⟨6,1248106705154188759807241,⟨395,150,37,415,439,34,128,385,395⟩⟩,⟨7,1208926976214001325126921,⟨47,22,37,127,311,98,98,279,319⟩⟩,⟨8,1184051793706775491849,⟨47,22,37,127,55,98,192,197,47⟩⟩]⟩
theorem node422 : UpperPrefix a [3,4,5,6,8,1] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,1] 30 cert422 (by decide +kernel)

def cert423 : Leaf := ⟨⟨272,297,266,387,11,267,267,11,131⟩,[],[(4,1,0),(5,2,1)],⟨11,22,37,88,304,100,195,387,395⟩,⟨11,22,37,88,304,100,192,384,264⟩,[⟨2,1224302388892046691664899,⟨459,475,505,88,312,120,192,384,264⟩⟩,⟨6,1255236371738952379432201,⟨395,150,439,415,439,182,128,385,395⟩⟩,⟨7,1208926973962201511441673,⟨47,22,37,127,311,100,66,279,319⟩⟩]⟩
theorem node423 : UpperPrefix a [3,4,5,6,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,2] 30 cert423 (by decide +kernel)

def cert424 : Leaf := ⟨⟨20,41,10,263,79,0,271,15,7⟩,[(5,6)],[(4,1,0),(5,2,1),(7,5,5)],⟨11,22,37,88,304,224,199,391,271⟩,⟨11,22,37,88,304,224,192,384,264⟩,[⟨6,1248106705154188759807241,⟨395,150,37,415,439,160,128,385,395⟩⟩,⟨8,1181747921022331401481,⟨15,22,37,127,55,224,224,129,15⟩⟩]⟩
theorem node424 : UpperPrefix a [3,4,5,6,8,7] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,7] 30 cert424 (by decide +kernel)

theorem node425 : UpperPrefix a [3,4,5,6,8] 30 :=
  branch_upper a [3,4,5,6,8] 30 (by decide) (fin9_cases _
  node421
  node422
  node423
  (invalid_upper a [3,4,5,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,6] 30 (by decide +kernel))
  node424
  (invalid_upper a [3,4,5,6,8,8] 30 (by decide +kernel)))

theorem node426 : UpperPrefix a [3,4,5,6] 30 :=
  branch_upper a [3,4,5,6] 30 (by decide) (fin9_cases _
  node403
  node404
  node405
  (invalid_upper a [3,4,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,6] 30 (by decide +kernel))
  node420
  node425)

def cert427 : Leaf := ⟨⟨404,425,0,326,0,398,270,78,198⟩,[(2,4),(4,2)],[(4,1,0),(5,2,1),(0,4,1)],⟨11,22,37,152,49,358,454,454,334⟩,⟨11,22,37,152,49,96,192,384,264⟩,[⟨6,1210106412362621961387273,⟨11,22,55,159,55,32,128,385,267⟩⟩]⟩
theorem node427 : UpperPrefix a [3,4,5,7,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,0] 30 cert427 (by decide +kernel)

def cert428 : Leaf := ⟨⟨212,232,0,68,204,140,268,76,196⟩,[(2,5)],[(4,1,0),(5,2,1),(0,5,2)],⟨11,22,37,152,50,97,452,452,332⟩,⟨11,22,37,152,50,97,192,384,264⟩,[⟨1,1300340804888244264370177,⟨493,508,485,472,508,485,192,384,264⟩⟩,⟨8,1181747927902892129641,⟨11,22,55,159,55,127,255,129,11⟩⟩]⟩
theorem node428 : UpperPrefix a [3,4,5,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,0] 30 cert428 (by decide +kernel)

def cert429 : Leaf := ⟨⟨208,233,200,65,205,137,265,73,193⟩,[],[(4,1,0),(5,2,1),(2,5,4)],⟨11,22,37,152,50,100,449,449,329⟩,⟨11,22,37,152,50,100,192,384,264⟩,[⟨1,1214876138945189025939457,⟨493,252,485,152,56,228,192,384,264⟩⟩,⟨8,1181747927902892129641,⟨11,22,55,159,55,127,255,129,11⟩⟩]⟩
theorem node429 : UpperPrefix a [3,4,5,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,2] 30 cert429 (by decide +kernel)

def cert430 : Leaf := ⟨⟨468,32,456,325,4,141,268,77,197⟩,[],[(4,1,0),(5,2,1)],⟨11,22,37,152,50,352,193,452,332⟩,⟨11,22,37,152,50,352,193,384,264⟩,[⟨1,1225224764622342062342145,⟨493,508,485,152,440,484,485,384,264⟩⟩,⟨0,1210107565284126564027392,⟨10,22,54,152,50,352,192,384,264⟩⟩,⟨3,1210107565284125490285569,⟨3,22,55,144,50,352,193,384,256⟩⟩,⟨6,1210106412362621957180417,⟨11,22,55,152,50,288,129,384,264⟩⟩,⟨7,1208926973663409152723969,⟨11,22,55,24,50,352,65,256,264⟩⟩,⟨8,1181745669497389321217,⟨11,22,55,152,50,96,193,128,8⟩⟩]⟩
theorem node430 : UpperPrefix a [3,4,5,7,1,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,8,0] 30 cert430 (by decide +kernel)

def cert431 : Leaf := ⟨⟨148,169,136,5,141,141,9,77,197⟩,[],[(4,1,0),(5,2,1)],⟨11,22,37,152,50,352,196,449,329⟩,⟨11,22,37,152,50,352,196,384,264⟩,[⟨1,1214876174903617300725761,⟨493,252,485,152,120,352,228,384,264⟩⟩,⟨8,1181889786893091011945,⟨75,22,55,223,55,127,223,129,75⟩⟩,⟨6,1210106412364829583015273,⟨11,22,55,159,55,319,159,385,267⟩⟩]⟩
theorem node431 : UpperPrefix a [3,4,5,7,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,8,2] 30 cert431 (by decide +kernel)

theorem node432 : UpperPrefix a [3,4,5,7,1,8] 30 :=
  branch_upper a [3,4,5,7,1,8] 30 (by decide) (fin9_cases _
  node430
  (invalid_upper a [3,4,5,7,1,8,1] 30 (by decide +kernel))
  node431
  (invalid_upper a [3,4,5,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,8] 30 (by decide +kernel)))

theorem node433 : UpperPrefix a [3,4,5,7,1] 30 :=
  branch_upper a [3,4,5,7,1] 30 (by decide) (fin9_cases _
  node428
  (invalid_upper a [3,4,5,7,1,1] 30 (by decide +kernel))
  node429
  (invalid_upper a [3,4,5,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,7] 30 (by decide +kernel))
  node432)

def cert434 : Local := ⟨⟨464,0,458,323,0,395,267,75,195⟩,[(1,4),(4,2)],[(4,1,0),(5,2,1),(5,2,4),(2,4,1)]⟩
theorem node434 : UpperPrefix a [3,4,5,7,2] 30 :=
  local_sound a [3,4,5,7,2] 30 cert434 (by decide +kernel)

def cert435 : Local := ⟨⟨404,424,0,262,0,398,270,14,134⟩,[(2,5),(4,5)],[(4,1,0),(5,2,1),(6,4,4),(0,5,2)]⟩
theorem node435 : UpperPrefix a [3,4,5,7,6,0] 30 :=
  local_sound a [3,4,5,7,6,0] 30 cert435 (by decide +kernel)

def cert436 : Leaf := ⟨⟨148,169,138,5,0,141,269,13,133⟩,[(4,5)],[(4,1,0),(5,2,1),(6,4,4),(1,5,2)],⟨11,22,37,152,112,98,453,389,269⟩,⟨11,22,37,152,112,98,192,384,264⟩,[⟨8,1181748490577970265465,⟨15,55,55,191,127,127,255,129,15⟩⟩]⟩
theorem node436 : UpperPrefix a [3,4,5,7,6,1] 30 :=
  Boolean.leaf_sound a [3,4,5,7,6,1] 30 cert436 (by decide +kernel)

def cert437 : Leaf := ⟨⟨400,425,394,259,0,395,267,11,131⟩,[(4,5)],[(4,1,0),(5,2,1),(6,4,4)],⟨11,22,37,152,112,100,451,387,267⟩,⟨11,22,37,152,112,100,192,384,264⟩,[⟨2,1224302388894241419953155,⟨459,475,505,152,112,120,192,384,264⟩⟩]⟩
theorem node437 : UpperPrefix a [3,4,5,7,6,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,6,2] 30 cert437 (by decide +kernel)

def cert438 : Leaf := ⟨⟨404,424,394,262,0,143,270,14,134⟩,[(4,5)],[(4,1,0),(5,2,1),(6,4,4)],⟨11,22,37,152,112,352,193,390,270⟩,⟨11,22,37,152,112,352,193,384,264⟩,[⟨0,1238497104415490514619392,⟨394,414,446,152,112,368,192,384,264⟩⟩]⟩
theorem node438 : UpperPrefix a [3,4,5,7,6,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,6,8,0] 30 cert438 (by decide +kernel)

def cert439 : Leaf := ⟨⟨404,424,394,261,0,143,269,13,133⟩,[(4,5)],[(4,1,0),(5,2,1),(6,4,4)],⟨11,22,37,152,112,352,194,389,269⟩,⟨11,22,37,152,112,352,194,384,264⟩,[⟨1,1229033924705677514637313,⟨9,412,445,152,112,368,200,384,264⟩⟩,⟨0,1210107565286050709376000,⟨10,22,54,152,112,368,194,384,264⟩⟩]⟩
theorem node439 : UpperPrefix a [3,4,5,7,6,8,1] 30 :=
  Boolean.leaf_sound a [3,4,5,7,6,8,1] 30 cert439 (by decide +kernel)

def cert440 : Leaf := ⟨⟨400,425,394,259,0,143,267,11,131⟩,[(4,5)],[(4,1,0),(5,2,1),(6,4,4)],⟨11,22,37,152,112,352,196,387,267⟩,⟨11,22,37,152,112,352,196,384,264⟩,[⟨2,1224302334850771013600259,⟨395,411,441,152,112,368,200,384,264⟩⟩]⟩
theorem node440 : UpperPrefix a [3,4,5,7,6,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,6,8,2] 30 cert440 (by decide +kernel)

theorem node441 : UpperPrefix a [3,4,5,7,6,8] 30 :=
  branch_upper a [3,4,5,7,6,8] 30 (by decide) (fin9_cases _
  node438
  node439
  node440
  (invalid_upper a [3,4,5,7,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,8,8] 30 (by decide +kernel)))

theorem node442 : UpperPrefix a [3,4,5,7,6] 30 :=
  branch_upper a [3,4,5,7,6] 30 (by decide) (fin9_cases _
  node435
  node436
  node437
  (invalid_upper a [3,4,5,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,6,7] 30 (by decide +kernel))
  node441)

def cert443 : Leaf := ⟨⟨212,224,0,326,206,134,6,70,198⟩,[(2,5)],[(4,1,0),(5,2,1),(8,4,3),(0,5,2)],⟨11,22,37,152,304,97,198,454,334⟩,⟨11,22,37,152,304,97,192,384,264⟩,[⟨3,1210255463530797840212993,⟨103,214,37,210,502,101,192,384,256⟩⟩]⟩
theorem node443 : UpperPrefix a [3,4,5,7,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,8,0] 30 cert443 (by decide +kernel)

def cert444 : Leaf := ⟨⟨20,41,10,325,205,141,12,77,197⟩,[],[(4,1,0),(5,2,1),(8,4,3),(1,5,2)],⟨11,22,37,152,304,98,193,452,332⟩,⟨11,22,37,152,304,98,193,384,264⟩,[⟨6,1210106412362347083478281,⟨11,22,37,159,311,34,129,385,267⟩⟩,⟨7,1208926973663134279021833,⟨11,22,37,31,311,98,65,257,267⟩⟩]⟩
theorem node444 : UpperPrefix a [3,4,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,8,1,0] 30 cert444 (by decide +kernel)

def cert445 : Leaf := ⟨⟨144,169,138,321,201,141,9,73,193⟩,[],[(4,1,0),(5,2,1),(8,4,3),(1,5,2),(2,6,5)],⟨11,22,37,152,304,98,196,449,329⟩,⟨11,22,37,152,304,98,196,384,264⟩,[⟨6,1210106412362347083478281,⟨11,22,37,159,311,34,132,385,267⟩⟩]⟩
theorem node445 : UpperPrefix a [3,4,5,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,8,1,2] 30 cert445 (by decide +kernel)

theorem node446 : UpperPrefix a [3,4,5,7,8,1] 30 :=
  branch_upper a [3,4,5,7,8,1] 30 (by decide) (fin9_cases _
  node444
  (invalid_upper a [3,4,5,7,8,1,1] 30 (by decide +kernel))
  node445
  (invalid_upper a [3,4,5,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,1,8] 30 (by decide +kernel)))

def cert447 : Leaf := ⟨⟨16,41,10,323,203,139,11,75,195⟩,[],[(4,1,0),(5,2,1),(8,4,3)],⟨11,22,37,152,304,100,195,451,331⟩,⟨11,22,37,152,304,100,192,384,264⟩,[⟨2,1224302388892042396697603,⟨459,475,505,152,304,120,192,384,264⟩⟩,⟨6,1210106412362347083478281,⟨11,22,37,159,311,36,128,385,267⟩⟩,⟨7,1208926973663134279021833,⟨11,22,37,31,311,100,64,257,267⟩⟩]⟩
theorem node447 : UpperPrefix a [3,4,5,7,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,8,2] 30 cert447 (by decide +kernel)

#print axioms node447
end Delivery.FiniteExclusion.Sharp3x6
