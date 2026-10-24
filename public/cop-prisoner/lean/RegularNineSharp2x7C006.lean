import RegularNineSharp2x7Base
import RegularNineSharp2x7C000
import RegularNineSharp2x7C002
import RegularNineSharp2x7C004
import RegularNineSharp2x7C005
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
theorem node384 : UpperPrefix a [2,3,8,7,1,4] 30 :=
  branch_upper a [2,3,8,7,1,4] 30 (by decide) (fin9_cases _
  node382
  (invalid_upper a [2,3,8,7,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,4] 30 (by decide +kernel))
  node383
  (invalid_upper a [2,3,8,7,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,8] 30 (by decide +kernel)))

theorem node385 : UpperPrefix a [2,3,8,7,1] 30 :=
  branch_upper a [2,3,8,7,1] 30 (by decide) (fin9_cases _
  node381
  (invalid_upper a [2,3,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,3] 30 (by decide +kernel))
  node384
  (invalid_upper a [2,3,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,8] 30 (by decide +kernel)))

def cert386 : Leaf := ⟨⟨8,4,179,39,0,150,55,55,179⟩,[(4,5)],[(3,1,0),(6,4,4)],⟨7,11,268,152,112,97,242,434,310⟩,⟨7,11,268,152,112,97,192,384,260⟩,[⟨8,1184200358506666216709,⟨55,123,127,250,122,123,250,251,55⟩⟩,⟨4,1210107565282752174492933,⟨7,11,271,136,96,97,192,385,263⟩⟩,⟨5,1210107564157951779278085,⟨7,11,271,152,80,65,192,385,263⟩⟩,⟨7,1208926973665333298072837,⟨7,11,271,24,112,113,64,257,263⟩⟩]⟩
theorem node386 : UpperPrefix a [2,3,8,7,6,0] 30 :=
  Boolean.leaf_sound a [2,3,8,7,6,0] 30 cert386 (by decide +kernel)

def cert387 : Leaf := ⟨⟨8,4,179,39,0,149,55,55,179⟩,[(4,5)],[(3,1,0),(6,4,4)],⟨7,11,268,152,112,98,241,433,309⟩,⟨7,11,268,152,112,98,192,384,260⟩,[⟨8,1184058565074831346949,⟨7,59,63,250,120,122,250,251,7⟩⟩,⟨4,1210107565282752174492933,⟨7,11,271,136,96,98,192,385,263⟩⟩,⟨5,1210107564157951779278085,⟨7,11,271,152,80,66,192,385,263⟩⟩,⟨7,1208926973665333298072837,⟨7,11,271,24,112,114,64,257,263⟩⟩]⟩
theorem node387 : UpperPrefix a [2,3,8,7,6,1] 30 :=
  Boolean.leaf_sound a [2,3,8,7,6,1] 30 cert387 (by decide +kernel)

def cert388 : Leaf := ⟨⟨56,52,51,39,0,0,55,55,51⟩,[(4,5),(5,4)],[(3,1,0),(6,4,4),(6,4,5)],⟨7,11,268,152,112,112,227,419,295⟩,⟨7,11,268,152,112,112,192,384,260⟩,[⟨7,1246705908347438276025615,⟨7,271,271,319,112,112,112,257,263⟩⟩,⟨8,1184059128024784768261,⟨7,59,63,250,120,120,250,251,7⟩⟩]⟩
theorem node388 : UpperPrefix a [2,3,8,7,6,4] 30 :=
  Boolean.leaf_sound a [2,3,8,7,6,4] 30 cert388 (by decide +kernel)

theorem node389 : UpperPrefix a [2,3,8,7,6] 30 :=
  branch_upper a [2,3,8,7,6] 30 (by decide) (fin9_cases _
  node386
  node387
  (invalid_upper a [2,3,8,7,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,6,3] 30 (by decide +kernel))
  node388
  (invalid_upper a [2,3,8,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,6,8] 30 (by decide +kernel)))

theorem node390 : UpperPrefix a [2,3,8,7] 30 :=
  branch_upper a [2,3,8,7] 30 (by decide) (fin9_cases _
  node380
  node385
  (invalid_upper a [2,3,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,5] 30 (by decide +kernel))
  node389
  (invalid_upper a [2,3,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,8] 30 (by decide +kernel)))

theorem node391 : UpperPrefix a [2,3,8] 30 :=
  branch_upper a [2,3,8] 30 (by decide) (fin9_cases _
  node345
  node351
  (invalid_upper a [2,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,4] 30 (by decide +kernel))
  node356
  node375
  node390
  (invalid_upper a [2,3,8,8] 30 (by decide +kernel)))

theorem node392 : UpperPrefix a [2,3] 30 :=
  branch_upper a [2,3] 30 (by decide) (fin9_cases _
  node5
  node17
  (invalid_upper a [2,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,3] 30 (by decide +kernel))
  node50
  node161
  node263
  node344
  node391)

def cert393 : Leaf := ⟨⟨264,268,258,0,460,396,300,108,232⟩,[(3,1)],[(4,1,3),(0,2,0),(1,3,2)],⟨7,19,13,26,504,488,488,488,492⟩,⟨7,19,13,26,48,96,192,384,260⟩,[⟨5,1210107564157954202285087,⟨15,31,15,31,31,64,192,384,261⟩⟩,⟨6,1210106412362349502280735,⟨15,31,15,31,63,32,128,384,261⟩⟩,⟨7,1208926973663136697824287,⟨15,31,15,31,63,96,64,256,261⟩⟩]⟩
theorem node393 : UpperPrefix a [2,4,0,1] 30 :=
  Boolean.leaf_sound a [2,4,0,1] 30 cert393 (by decide +kernel)

def cert394 : Leaf := ⟨⟨408,396,400,0,396,396,268,76,200⟩,[(3,4)],[(0,2,0),(5,3,3),(1,4,1)],⟨7,19,13,56,50,488,456,456,460⟩,⟨7,19,13,56,50,96,192,384,260⟩,[⟨4,1229033996900709700731905,⟨487,3,493,40,34,96,192,384,484⟩⟩,⟨6,1210106412365102316027199,⟨7,31,31,63,63,63,128,385,263⟩⟩]⟩
theorem node394 : UpperPrefix a [2,4,0,5,1] 30 :=
  Boolean.leaf_sound a [2,4,0,5,1] 30 cert394 (by decide +kernel)

def cert395 : Leaf := ⟨⟨472,456,466,0,0,402,274,82,210⟩,[(3,4),(4,3)],[(0,2,0),(5,3,3),(5,3,4)],⟨7,19,13,56,56,482,450,450,454⟩,⟨7,19,13,56,56,96,192,384,260⟩,[⟨2,1212473369247699230002177,⟨3,27,27,56,56,120,216,504,506⟩⟩,⟨3,1214857656031579466630145,⟨487,499,485,48,48,96,192,384,260⟩⟩]⟩
theorem node395 : UpperPrefix a [2,4,0,5,3] 30 :=
  Boolean.leaf_sound a [2,4,0,5,3] 30 cert395 (by decide +kernel)

def cert396 : Leaf := ⟨⟨280,268,274,0,0,414,286,30,154⟩,[(3,4),(4,5)],[(0,2,0),(5,3,3),(6,4,3),(6,4,4)],⟨7,19,13,56,112,490,458,394,398⟩,⟨7,19,13,56,112,96,192,384,260⟩,[⟨7,1208926973665339755754559,⟨7,31,15,63,127,127,64,256,261⟩⟩]⟩
theorem node396 : UpperPrefix a [2,4,0,5,6] 30 :=
  Boolean.leaf_sound a [2,4,0,5,6] 30 cert396 (by decide +kernel)

def cert397 : Leaf := ⟨⟨216,204,208,0,76,156,284,92,216⟩,[(3,4)],[(0,2,0),(5,3,3)],⟨7,19,13,56,176,98,456,456,332⟩,⟨7,19,13,56,176,98,192,384,260⟩,[⟨1,1390130457594646010265601,⟨453,477,477,504,504,508,192,384,452⟩⟩,⟨8,1181747925435436037247,⟨7,31,15,63,191,127,255,128,5⟩⟩]⟩
theorem node397 : UpperPrefix a [2,4,0,5,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,5,7,1] 30 cert397 (by decide +kernel)

def cert398 : Leaf := ⟨⟨88,76,82,0,78,134,270,78,74⟩,[(3,4)],[(0,2,0),(5,3,3)],⟨7,19,13,56,176,104,450,450,326⟩,⟨7,19,13,56,176,104,192,384,260⟩,[⟨8,1181747925435436037247,⟨7,31,15,63,191,127,255,128,5⟩⟩,⟨4,1214857656065665400833025,⟨487,451,493,40,160,104,192,384,292⟩⟩,⟨7,1360042701114965084353599,⟨7,31,15,319,319,367,64,256,261⟩⟩]⟩
theorem node398 : UpperPrefix a [2,4,0,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,0,5,7,3] 30 cert398 (by decide +kernel)

def cert399 : Leaf := ⟨⟨24,12,18,0,334,158,30,94,218⟩,[(3,4)],[(0,2,0),(5,3,3),(8,5,4)],⟨7,19,13,56,176,352,202,458,334⟩,⟨7,19,13,56,176,352,192,384,260⟩,[⟨6,1210106412362349233583135,⟨7,31,15,63,191,288,128,384,261⟩⟩,⟨7,1208926973663136429126687,⟨7,31,15,63,63,352,64,256,261⟩⟩]⟩
theorem node399 : UpperPrefix a [2,4,0,5,7,8] 30 :=
  Boolean.leaf_sound a [2,4,0,5,7,8] 30 cert399 (by decide +kernel)

theorem node400 : UpperPrefix a [2,4,0,5,7] 30 :=
  branch_upper a [2,4,0,5,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,7,0] 30 (by decide +kernel))
  node397
  (invalid_upper a [2,4,0,5,7,2] 30 (by decide +kernel))
  node398
  (invalid_upper a [2,4,0,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,7] 30 (by decide +kernel))
  node399)

def cert401 : Leaf := ⟨⟨472,460,464,0,204,392,264,72,200⟩,[(3,4)],[(0,2,0),(5,3,3)],⟨7,19,13,56,304,98,200,456,460⟩,⟨7,19,13,56,304,98,192,384,260⟩,[⟨1,1390130457594646010265601,⟨453,477,477,504,504,508,192,384,452⟩⟩,⟨4,1229033996795156584465409,⟨487,35,493,40,288,98,192,384,452⟩⟩,⟨2,1210255607716358140199937,⟨107,251,105,248,504,106,192,384,256⟩⟩]⟩
theorem node401 : UpperPrefix a [2,4,0,5,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,5,8,1] 30 cert401 (by decide +kernel)

def cert402 : Leaf := ⟨⟨408,396,402,0,206,390,262,70,194⟩,[(3,4)],[(0,2,0),(5,3,3)],⟨7,19,13,56,304,104,194,450,454⟩,⟨7,19,13,56,304,104,192,384,260⟩,[⟨4,1214857656065665400833025,⟨487,451,493,40,288,104,192,384,292⟩⟩,⟨3,1214857655926026350363649,⟨455,467,453,48,304,96,192,384,260⟩⟩,⟨6,1210106412362349241971775,⟨7,31,15,63,319,47,128,384,261⟩⟩]⟩
theorem node402 : UpperPrefix a [2,4,0,5,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,5,8,3] 30 cert402 (by decide +kernel)

def cert403 : Local := ⟨⟨344,332,338,0,78,0,286,94,90⟩,[(3,4),(5,6)],[(0,2,0),(5,3,3),(7,5,5)]⟩
theorem node403 : UpperPrefix a [2,4,0,5,8,7] 30 :=
  local_sound a [2,4,0,5,8,7] 30 cert403 (by decide +kernel)

theorem node404 : UpperPrefix a [2,4,0,5,8] 30 :=
  branch_upper a [2,4,0,5,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,8,0] 30 (by decide +kernel))
  node401
  (invalid_upper a [2,4,0,5,8,2] 30 (by decide +kernel))
  node402
  (invalid_upper a [2,4,0,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,8,6] 30 (by decide +kernel))
  node403
  (invalid_upper a [2,4,0,5,8,8] 30 (by decide +kernel)))

theorem node405 : UpperPrefix a [2,4,0,5] 30 :=
  branch_upper a [2,4,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,0] 30 (by decide +kernel))
  node394
  (invalid_upper a [2,4,0,5,2] 30 (by decide +kernel))
  node395
  (invalid_upper a [2,4,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,5] 30 (by decide +kernel))
  node396
  node400
  node404)

def cert406 : Leaf := ⟨⟨88,76,80,36,76,396,300,108,232⟩,[],[(0,2,0),(1,4,1)],⟨7,19,13,88,50,488,488,424,428⟩,⟨7,19,13,88,50,96,192,384,260⟩,[⟨7,1208926973665337607746623,⟨7,23,15,95,63,127,64,256,261⟩⟩,⟨8,1181745671425844343871,⟨7,23,15,95,63,127,192,128,5⟩⟩,⟨4,1229033996900709700731905,⟨487,3,493,72,34,96,192,384,484⟩⟩,⟨5,1210107564157951781377037,⟨7,19,15,95,18,64,192,384,261⟩⟩]⟩
theorem node406 : UpperPrefix a [2,4,0,6,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,1] 30 cert406 (by decide +kernel)

def cert407 : Leaf := ⟨⟨56,44,50,38,70,390,294,38,162⟩,[],[(0,2,0),(6,3,4)],⟨7,19,13,88,56,482,482,418,422⟩,⟨7,19,13,88,56,96,192,384,260⟩,[⟨7,1208926973665337607746623,⟨7,23,15,95,63,127,64,256,261⟩⟩,⟨8,1181745671425844343871,⟨7,23,15,95,63,127,192,128,5⟩⟩,⟨3,1214857656031579466630145,⟨487,499,485,80,48,96,192,384,260⟩⟩,⟨4,1214857656030481028744193,⟨487,483,493,72,40,96,192,384,260⟩⟩]⟩
theorem node407 : UpperPrefix a [2,4,0,6,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,3] 30 cert407 (by decide +kernel)

def cert408 : Leaf := ⟨⟨120,108,112,164,76,12,300,108,104⟩,[],[(0,2,0),(7,4,3)],⟨7,19,13,88,176,98,488,424,300⟩,⟨7,19,13,88,176,98,192,384,260⟩,[⟨1,1361666879286783552258049,⟨13,221,13,216,504,508,192,384,260⟩⟩,⟨8,1181748206908264739967,⟨7,23,47,127,191,127,255,128,5⟩⟩,⟨4,1229033996795156584465409,⟨487,35,493,72,160,98,192,384,452⟩⟩]⟩
theorem node408 : UpperPrefix a [2,4,0,6,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,1] 30 cert408 (by decide +kernel)

def cert409 : Leaf := ⟨⟨56,44,50,166,14,0,302,46,42⟩,[(5,3)],[(0,2,0),(6,3,5),(7,4,3)],⟨7,19,13,88,176,104,482,418,294⟩,⟨7,19,13,88,176,104,192,384,260⟩,[⟨8,1181748206908264739967,⟨7,23,47,127,191,127,255,128,5⟩⟩,⟨4,1214839173574269649028097,⟨487,451,493,104,160,104,192,384,292⟩⟩]⟩
theorem node409 : UpperPrefix a [2,4,0,6,7,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,3] 30 cert409 (by decide +kernel)

def cert410 : Leaf := ⟨⟨88,76,82,132,332,14,12,108,106⟩,[],[(0,2,0),(7,4,3),(8,5,4)],⟨7,19,13,88,176,352,194,424,300⟩,⟨7,19,13,88,176,352,194,384,260⟩,[⟨5,1210107852388330370774111,⟨15,95,15,95,223,325,207,384,261⟩⟩,⟨4,1229033942892698544374785,⟨487,99,493,72,160,352,194,384,420⟩⟩,⟨1,1210402713191234357166081,⟨5,17,13,88,184,504,192,384,260⟩⟩]⟩
theorem node410 : UpperPrefix a [2,4,0,6,7,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,8,1] 30 cert410 (by decide +kernel)

def cert411 : Leaf := ⟨⟨56,44,48,164,268,28,52,62,58⟩,[],[(0,2,0),(7,4,3),(8,5,4)],⟨7,19,13,88,176,352,200,418,294⟩,⟨7,19,13,88,176,352,200,384,260⟩,[⟨6,1361664861674143797507181,⟨7,147,15,159,435,439,143,384,261⟩⟩,⟨1,1210110163874063299903489,⟨13,93,13,88,248,376,248,504,260⟩⟩]⟩
theorem node411 : UpperPrefix a [2,4,0,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,8,3] 30 cert411 (by decide +kernel)

def cert412 : Local := ⟨⟨88,76,82,166,0,30,0,94,90⟩,[(4,6),(6,4)],[(0,2,0),(7,4,3),(8,5,4),(8,5,6),(5,6,3)]⟩
theorem node412 : UpperPrefix a [2,4,0,6,7,8,5] 30 :=
  local_sound a [2,4,0,6,7,8,5] 30 cert412 (by decide +kernel)

theorem node413 : UpperPrefix a [2,4,0,6,7,8] 30 :=
  branch_upper a [2,4,0,6,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,7,8,0] 30 (by decide +kernel))
  node410
  (invalid_upper a [2,4,0,6,7,8,2] 30 (by decide +kernel))
  node411
  (invalid_upper a [2,4,0,6,7,8,4] 30 (by decide +kernel))
  node412
  (invalid_upper a [2,4,0,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,8,8] 30 (by decide +kernel)))

theorem node414 : UpperPrefix a [2,4,0,6,7] 30 :=
  branch_upper a [2,4,0,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,7,0] 30 (by decide +kernel))
  node408
  (invalid_upper a [2,4,0,6,7,2] 30 (by decide +kernel))
  node409
  (invalid_upper a [2,4,0,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,7] 30 (by decide +kernel))
  node413)

def cert415 : Leaf := ⟨⟨120,108,112,416,204,8,296,104,232⟩,[],[(0,2,0)],⟨7,19,13,88,304,98,232,424,428⟩,⟨7,19,13,88,304,98,192,384,260⟩,[⟨1,1361666879286783552258049,⟨13,221,13,216,504,508,192,384,260⟩⟩,⟨2,1210255463601170064344065,⟨107,251,41,216,504,106,192,384,256⟩⟩,⟨4,1229033996795156584465409,⟨487,35,493,72,288,98,192,384,452⟩⟩,⟨7,1208926973944609253626893,⟨7,19,47,127,304,98,64,256,261⟩⟩,⟨8,1181745950697490224141,⟨7,19,47,127,48,98,192,128,5⟩⟩]⟩
theorem node415 : UpperPrefix a [2,4,0,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,1] 30 cert415 (by decide +kernel)

def cert416 : Leaf := ⟨⟨24,12,18,422,142,0,302,46,170⟩,[(5,3)],[(0,2,0),(6,3,5)],⟨7,19,13,88,304,104,226,418,422⟩,⟨7,19,13,88,304,104,192,384,260⟩,[⟨4,1214839173574269649028097,⟨487,451,493,104,288,104,192,384,292⟩⟩,⟨5,1210107564157951789773885,⟨7,19,15,95,279,79,192,384,261⟩⟩,⟨7,1208926973944609262023741,⟨7,19,47,127,311,111,64,256,261⟩⟩,⟨8,1181745950697498620989,⟨7,19,47,127,55,111,192,128,5⟩⟩]⟩
theorem node416 : UpperPrefix a [2,4,0,6,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,3] 30 cert416 (by decide +kernel)

def cert417 : Leaf := ⟨⟨280,268,274,294,78,0,300,110,106⟩,[(5,6)],[(0,2,0),(7,5,5)],⟨7,19,13,88,304,224,194,424,300⟩,⟨7,19,13,88,304,224,194,384,260⟩,[⟨4,1229033945144498358060033,⟨487,99,493,104,288,224,226,384,420⟩⟩,⟨5,1210107564157951781377037,⟨7,19,15,95,272,192,194,384,261⟩⟩,⟨6,1210106412362347081372685,⟨7,19,15,31,304,160,130,384,261⟩⟩]⟩
theorem node417 : UpperPrefix a [2,4,0,6,8,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,7,1] 30 cert417 (by decide +kernel)

def cert418 : Leaf := ⟨⟨304,292,306,294,6,0,310,54,50⟩,[(5,6)],[(0,2,0),(7,5,5)],⟨7,19,13,88,304,224,200,418,294⟩,⟨7,19,13,88,304,224,200,384,260⟩,[⟨6,1361664861674143797507181,⟨7,147,15,159,435,439,143,384,261⟩⟩,⟨3,1229181501189615957192453,⟨407,147,439,242,435,224,224,387,407⟩⟩]⟩
theorem node418 : UpperPrefix a [2,4,0,6,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,7,3] 30 cert418 (by decide +kernel)

def cert419 : Local := ⟨⟨344,332,338,294,78,0,0,94,90⟩,[(5,6),(6,5)],[(0,2,0),(7,5,5),(7,5,6),(5,6,3)]⟩
theorem node419 : UpperPrefix a [2,4,0,6,8,7,5] 30 :=
  local_sound a [2,4,0,6,8,7,5] 30 cert419 (by decide +kernel)

theorem node420 : UpperPrefix a [2,4,0,6,8,7] 30 :=
  branch_upper a [2,4,0,6,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,8,7,0] 30 (by decide +kernel))
  node417
  (invalid_upper a [2,4,0,6,8,7,2] 30 (by decide +kernel))
  node418
  (invalid_upper a [2,4,0,6,8,7,4] 30 (by decide +kernel))
  node419
  (invalid_upper a [2,4,0,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,7,8] 30 (by decide +kernel)))

theorem node421 : UpperPrefix a [2,4,0,6,8] 30 :=
  branch_upper a [2,4,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,8,0] 30 (by decide +kernel))
  node415
  (invalid_upper a [2,4,0,6,8,2] 30 (by decide +kernel))
  node416
  (invalid_upper a [2,4,0,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,6] 30 (by decide +kernel))
  node420
  (invalid_upper a [2,4,0,6,8,8] 30 (by decide +kernel)))

theorem node422 : UpperPrefix a [2,4,0,6] 30 :=
  branch_upper a [2,4,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,0] 30 (by decide +kernel))
  node406
  (invalid_upper a [2,4,0,6,2] 30 (by decide +kernel))
  node407
  (invalid_upper a [2,4,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,6] 30 (by decide +kernel))
  node414
  node421)

def cert423 : Leaf := ⟨⟨24,12,16,356,460,396,300,108,232⟩,[],[(0,2,0),(1,4,1)],⟨7,19,13,152,50,360,488,488,364⟩,⟨7,19,13,152,50,96,192,384,260⟩,[⟨4,1229033996900709700731905,⟨487,3,493,136,34,96,192,384,484⟩⟩,⟨5,1210107564157951781377037,⟨7,19,15,159,18,64,192,384,261⟩⟩,⟨6,1210106412362347081372685,⟨7,19,15,159,50,32,128,384,261⟩⟩,⟨7,1208926973663134276916237,⟨7,19,15,31,50,96,64,256,261⟩⟩,⟨8,1181745669222513513485,⟨7,19,15,159,50,96,192,128,5⟩⟩]⟩
theorem node423 : UpperPrefix a [2,4,0,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,7,1] 30 cert423 (by decide +kernel)

def cert424 : Leaf := ⟨⟨216,204,208,100,196,132,292,100,224⟩,[],[(0,2,0)],⟨7,19,13,152,56,98,480,480,356⟩,⟨7,19,13,152,56,98,192,384,260⟩,[⟨1,1361666879286783552258049,⟨13,221,13,216,504,508,192,384,260⟩⟩,⟨8,1181747927628016317567,⟨7,23,15,159,63,127,255,128,5⟩⟩,⟨3,1233784087508799504516097,⟨487,499,485,144,48,226,192,384,452⟩⟩,⟨4,1233784087507701066630145,⟨487,483,493,136,40,226,192,384,452⟩⟩,⟨5,1210107564157951785579551,⟨7,23,15,159,31,67,192,384,261⟩⟩]⟩
theorem node424 : UpperPrefix a [2,4,0,7,3,1] 30 :=
  Boolean.leaf_sound a [2,4,0,7,3,1] 30 cert424 (by decide +kernel)

def cert425 : Leaf := ⟨⟨280,264,274,354,450,130,290,98,226⟩,[],[(0,2,0)],⟨7,19,13,152,56,352,226,482,358⟩,⟨7,19,13,152,56,352,192,384,260⟩,[⟨2,1212473373755703346334721,⟨3,19,27,184,56,504,248,504,506⟩⟩,⟨3,1214857656172316954985473,⟨487,499,485,144,48,352,192,384,292⟩⟩,⟨4,1214857656171218517099521,⟨487,483,493,136,40,352,192,384,292⟩⟩,⟨5,1210107564157951785579551,⟨7,23,15,159,31,320,192,384,261⟩⟩,⟨6,1210106412362347085575199,⟨7,23,15,159,63,288,128,384,261⟩⟩,⟨7,1208926973663134281118751,⟨7,23,15,31,63,352,64,256,261⟩⟩]⟩
theorem node425 : UpperPrefix a [2,4,0,7,3,8] 30 :=
  Boolean.leaf_sound a [2,4,0,7,3,8] 30 cert425 (by decide +kernel)

theorem node426 : UpperPrefix a [2,4,0,7,3] 30 :=
  branch_upper a [2,4,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,7,3,0] 30 (by decide +kernel))
  node424
  (invalid_upper a [2,4,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,3,7] 30 (by decide +kernel))
  node425)

def cert427 : Leaf := ⟨⟨184,172,176,36,0,156,316,60,184⟩,[(4,5)],[(0,2,0),(6,4,4)],⟨7,19,13,152,112,98,488,424,300⟩,⟨7,19,13,152,112,98,192,384,260⟩,[⟨1,1361666879286783552258049,⟨13,221,13,216,504,508,192,384,260⟩⟩,⟨8,1181748490577969738879,⟨7,55,15,191,127,127,255,128,5⟩⟩]⟩
theorem node427 : UpperPrefix a [2,4,0,7,6,1] 30 :=
  Boolean.leaf_sound a [2,4,0,7,6,1] 30 cert427 (by decide +kernel)

def cert428 : Leaf := ⟨⟨56,44,50,38,0,134,302,46,42⟩,[(4,5)],[(0,2,0),(7,3,5),(6,4,4)],⟨7,19,13,152,112,104,482,418,294⟩,⟨7,19,13,152,112,104,192,384,260⟩,[⟨8,1181748490577969738879,⟨7,55,15,191,127,127,255,128,5⟩⟩,⟨4,1214839173292794672317441,⟨487,451,493,136,96,104,192,384,292⟩⟩]⟩
theorem node428 : UpperPrefix a [2,4,0,7,6,3] 30 :=
  Boolean.leaf_sound a [2,4,0,7,6,3] 30 cert428 (by decide +kernel)

def cert429 : Leaf := ⟨⟨432,420,432,292,0,148,308,60,184⟩,[(4,5)],[(0,2,0),(6,4,4)],⟨7,19,13,152,112,352,194,424,300⟩,⟨7,19,13,152,112,352,194,384,260⟩,[⟨1,1522835220386811853144065,⟨397,445,13,184,504,504,508,384,260⟩⟩,⟨3,1210110019761590447983877,⟨7,19,87,242,114,371,242,499,263⟩⟩]⟩
theorem node429 : UpperPrefix a [2,4,0,7,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,7,6,8,1] 30 cert429 (by decide +kernel)

def cert430 : Local := ⟨⟨312,300,306,294,0,30,0,62,58⟩,[(4,5),(6,3)],[(0,2,0),(7,3,6),(6,4,4)]⟩
theorem node430 : UpperPrefix a [2,4,0,7,6,8,3] 30 :=
  local_sound a [2,4,0,7,6,8,3] 30 cert430 (by decide +kernel)

def cert431 : Local := ⟨⟨152,140,146,6,0,158,286,30,154⟩,[(4,5)],[(0,2,0),(6,4,4),(8,5,6),(5,6,4)]⟩
theorem node431 : UpperPrefix a [2,4,0,7,6,8,5] 30 :=
  local_sound a [2,4,0,7,6,8,5] 30 cert431 (by decide +kernel)

theorem node432 : UpperPrefix a [2,4,0,7,6,8] 30 :=
  branch_upper a [2,4,0,7,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,7,6,8,0] 30 (by decide +kernel))
  node429
  (invalid_upper a [2,4,0,7,6,8,2] 30 (by decide +kernel))
  node430
  (invalid_upper a [2,4,0,7,6,8,4] 30 (by decide +kernel))
  node431
  (invalid_upper a [2,4,0,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,6,8,8] 30 (by decide +kernel)))

theorem node433 : UpperPrefix a [2,4,0,7,6] 30 :=
  branch_upper a [2,4,0,7,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,7,6,0] 30 (by decide +kernel))
  node427
  (invalid_upper a [2,4,0,7,6,2] 30 (by decide +kernel))
  node428
  (invalid_upper a [2,4,0,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,6,7] 30 (by decide +kernel))
  node432)

def cert434 : Leaf := ⟨⟨216,204,208,352,204,136,40,104,232⟩,[],[(0,2,0),(8,4,3)],⟨7,19,13,152,304,98,232,488,364⟩,⟨7,19,13,152,304,98,192,384,260⟩,[⟨1,1361666879286783552258049,⟨13,221,13,216,504,508,192,384,260⟩⟩,⟨2,1210255463601170064344065,⟨107,251,41,216,504,106,192,384,256⟩⟩,⟨4,1229033996795156584465409,⟨487,35,493,136,288,98,192,384,452⟩⟩,⟨5,1210107564157951781377037,⟨7,19,15,159,272,66,192,384,261⟩⟩]⟩
theorem node434 : UpperPrefix a [2,4,0,7,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,7,8,1] 30 cert434 (by decide +kernel)

def cert435 : Leaf := ⟨⟨120,108,112,356,76,132,44,108,104⟩,[],[(0,2,0),(7,3,5),(8,4,3)],⟨7,19,13,152,304,104,194,480,356⟩,⟨7,19,13,152,304,104,194,384,260⟩,[⟨1,1513224466161458954633217,⟨5,29,13,152,440,504,508,384,260⟩⟩,⟨4,1233765568741217691239425,⟨487,451,493,136,288,104,194,384,420⟩⟩]⟩
theorem node435 : UpperPrefix a [2,4,0,7,8,3,1] 30 :=
  Boolean.leaf_sound a [2,4,0,7,8,3,1] 30 cert435 (by decide +kernel)

def cert436 : Leaf := ⟨⟨88,76,82,324,76,148,28,94,90⟩,[],[(0,2,0),(7,3,5),(8,4,3)],⟨7,19,13,152,304,104,224,450,326⟩,⟨7,19,13,152,304,104,224,384,260⟩,[⟨5,1361518439514961941640255,⟨7,31,15,159,415,463,453,384,261⟩⟩,⟨1,1210110022446074930659329,⟨37,17,109,248,304,104,248,504,308⟩⟩]⟩
theorem node436 : UpperPrefix a [2,4,0,7,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,0,7,8,3,5] 30 cert436 (by decide +kernel)

theorem node437 : UpperPrefix a [2,4,0,7,8,3] 30 :=
  branch_upper a [2,4,0,7,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,7,8,3,0] 30 (by decide +kernel))
  node435
  (invalid_upper a [2,4,0,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,8,3,4] 30 (by decide +kernel))
  node436
  (invalid_upper a [2,4,0,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,8,3,8] 30 (by decide +kernel)))

theorem node438 : UpperPrefix a [2,4,0,7,8] 30 :=
  branch_upper a [2,4,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,7,8,0] 30 (by decide +kernel))
  node434
  (invalid_upper a [2,4,0,7,8,2] 30 (by decide +kernel))
  node437
  (invalid_upper a [2,4,0,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,8,8] 30 (by decide +kernel)))

theorem node439 : UpperPrefix a [2,4,0,7] 30 :=
  branch_upper a [2,4,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,7,0] 30 (by decide +kernel))
  node423
  (invalid_upper a [2,4,0,7,2] 30 (by decide +kernel))
  node426
  (invalid_upper a [2,4,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,7,5] 30 (by decide +kernel))
  node433
  (invalid_upper a [2,4,0,7,7] 30 (by decide +kernel))
  node438)

def cert440 : Leaf := ⟨⟨408,392,400,224,456,392,296,104,232⟩,[],[(0,2,0),(1,4,1)],⟨7,19,13,280,50,232,232,488,492⟩,⟨7,19,13,280,50,96,192,384,260⟩,[⟨2,1212549685406189584649729,⟨115,19,251,504,50,96,232,504,506⟩⟩,⟨4,1229107928273667591504897,⟨487,3,493,488,34,96,192,384,484⟩⟩,⟨5,1210107564157951781377037,⟨7,19,15,287,18,64,192,384,261⟩⟩,⟨6,1210106412362347081372685,⟨7,19,15,287,50,32,128,384,261⟩⟩]⟩
theorem node440 : UpperPrefix a [2,4,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,8,1] 30 cert440 (by decide +kernel)

def cert441 : Leaf := ⟨⟨280,264,274,226,450,386,290,98,226⟩,[],[(0,2,0)],⟨7,19,13,280,56,226,226,482,486⟩,⟨7,19,13,280,56,96,192,384,260⟩,[⟨2,1212473369245493764295681,⟨3,19,27,504,56,96,216,504,506⟩⟩,⟨3,1214857656031579466630145,⟨487,499,485,272,48,96,192,384,260⟩⟩,⟨4,1214857656030481028744193,⟨487,483,493,264,40,96,192,384,260⟩⟩,⟨5,1210107564157951785579551,⟨7,23,15,287,31,64,192,384,261⟩⟩,⟨6,1210106412362347085575199,⟨7,23,15,287,63,32,128,384,261⟩⟩,⟨7,1208926973663134281118751,⟨7,23,15,287,63,96,64,256,261⟩⟩]⟩
theorem node441 : UpperPrefix a [2,4,0,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,8,3] 30 cert441 (by decide +kernel)

def cert442 : Leaf := ⟨⟨280,264,274,162,0,410,314,58,186⟩,[(4,5)],[(0,2,0),(6,4,4)],⟨7,19,13,280,112,234,234,426,430⟩,⟨7,19,13,280,112,96,192,384,260⟩,[⟨2,1212473369247692787551233,⟨3,19,27,504,112,112,216,504,506⟩⟩,⟨5,1210107564157951781377037,⟨7,19,15,287,80,64,192,384,261⟩⟩,⟨7,1208926973665333300171789,⟨7,19,15,287,112,112,64,256,261⟩⟩]⟩
theorem node442 : UpperPrefix a [2,4,0,8,6] 30 :=
  Boolean.leaf_sound a [2,4,0,8,6] 30 cert442 (by decide +kernel)

def cert443 : Leaf := ⟨⟨408,392,400,224,328,392,296,104,232⟩,[],[(0,2,0)],⟨7,19,13,280,176,98,232,488,364⟩,⟨7,19,13,280,176,98,192,384,260⟩,[⟨1,1361666879286783283560449,⟨5,221,13,472,504,508,192,384,260⟩⟩,⟨2,1212549966714521564220929,⟨115,115,251,504,248,98,216,504,506⟩⟩,⟨4,1229033996795156584465409,⟨487,35,493,264,160,98,192,384,452⟩⟩,⟨5,1210107564157951781377037,⟨7,19,15,287,144,66,192,384,261⟩⟩,⟨6,1210106412362347081372685,⟨7,19,15,287,176,34,128,384,261⟩⟩]⟩
theorem node443 : UpperPrefix a [2,4,0,8,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,8,7,1] 30 cert443 (by decide +kernel)

def cert444 : Leaf := ⟨⟨88,72,82,98,330,130,42,106,106⟩,[],[(0,2,0)],⟨7,19,13,280,176,104,226,482,358⟩,⟨7,19,13,280,176,104,192,384,260⟩,[⟨2,1212473376286766228573185,⟨3,19,59,504,184,120,248,504,506⟩⟩,⟨7,1360042701114965084353599,⟨7,31,15,287,319,367,64,256,261⟩⟩,⟨8,1182034181073650332733,⟨7,83,47,127,247,111,192,128,5⟩⟩,⟨4,1214839173292794672317441,⟨487,451,493,264,160,104,192,384,292⟩⟩,⟨5,1210107564157951789773885,⟨7,19,15,287,151,79,192,384,261⟩⟩]⟩
theorem node444 : UpperPrefix a [2,4,0,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,0,8,7,3] 30 cert444 (by decide +kernel)

theorem node445 : UpperPrefix a [2,4,0,8,7] 30 :=
  branch_upper a [2,4,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,8,7,0] 30 (by decide +kernel))
  node443
  (invalid_upper a [2,4,0,8,7,2] 30 (by decide +kernel))
  node444
  (invalid_upper a [2,4,0,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,8,7,8] 30 (by decide +kernel)))

theorem node446 : UpperPrefix a [2,4,0,8] 30 :=
  branch_upper a [2,4,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,8,0] 30 (by decide +kernel))
  node440
  (invalid_upper a [2,4,0,8,2] 30 (by decide +kernel))
  node441
  (invalid_upper a [2,4,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,8,5] 30 (by decide +kernel))
  node442
  node445
  (invalid_upper a [2,4,0,8,8] 30 (by decide +kernel)))

theorem node447 : UpperPrefix a [2,4,0] 30 :=
  branch_upper a [2,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,0] 30 (by decide +kernel))
  node393
  (invalid_upper a [2,4,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,4] 30 (by decide +kernel))
  node405
  node422
  node439
  node446)

#print axioms node447
end Delivery.FiniteExclusion.Sharp2x7
