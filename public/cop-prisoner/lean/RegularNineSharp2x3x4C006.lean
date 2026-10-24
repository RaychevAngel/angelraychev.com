import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C005
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def cert384 : Leaf := ⟨⟨0,28,179,39,0,15,0,63,31⟩,[(0,4),(4,0),(6,7)],[(7,3,2),(8,6,6)],⟨7,35,76,152,22,112,448,393,297⟩,⟨7,35,76,152,22,112,448,384,288⟩,[⟨6,1371137264753870174700561,⟨415,443,12,153,415,443,384,384,426⟩⟩]⟩
theorem node384 : UpperPrefix a [2,5,6,7,1,4,8] 30 :=
  Boolean.leaf_sound a [2,5,6,7,1,4,8] 30 cert384 (by decide +kernel)

theorem node385 : UpperPrefix a [2,5,6,7,1,4] 30 :=
  branch_upper a [2,5,6,7,1,4] 30 (by decide) (fin9_cases _
  node382
  (invalid_upper a [2,5,6,7,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,4,2] 30 (by decide +kernel))
  node383
  (invalid_upper a [2,5,6,7,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,4,7] 30 (by decide +kernel))
  node384)

def cert386 : Leaf := ⟨⟨0,92,146,70,0,30,30,126,94⟩,[(0,4),(4,0)],[(7,3,2)],⟨7,35,76,152,22,352,193,408,312⟩,⟨7,35,76,152,22,352,193,384,288⟩,[⟨0,1602903312610140649161728,⟨446,446,492,408,446,492,508,384,292⟩⟩,⟨8,1184195656239092483507,⟨23,55,76,221,23,127,221,223,55⟩⟩,⟨5,1210107708273354630759443,⟨23,23,76,221,23,332,221,384,260⟩⟩]⟩
theorem node386 : UpperPrefix a [2,5,6,7,1,8,0] 30 :=
  Boolean.leaf_sound a [2,5,6,7,1,8,0] 30 cert386 (by decide +kernel)

def cert387 : Local := ⟨⟨0,340,0,359,0,23,0,119,87⟩,[(0,4),(2,6),(4,0),(6,3)],[(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node387 : UpperPrefix a [2,5,6,7,1,8,3] 30 :=
  local_sound a [2,5,6,7,1,8,3] 30 cert387 (by decide +kernel)

def cert388 : Local := ⟨⟨0,332,435,0,0,15,0,111,79⟩,[(0,4),(3,6),(4,0),(6,3)],[(7,3,2),(4,6,2)]⟩
theorem node388 : UpperPrefix a [2,5,6,7,1,8,4] 30 :=
  local_sound a [2,5,6,7,1,8,4] 30 cert388 (by decide +kernel)

theorem node389 : UpperPrefix a [2,5,6,7,1,8] 30 :=
  branch_upper a [2,5,6,7,1,8] 30 (by decide) (fin9_cases _
  node386
  (invalid_upper a [2,5,6,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,2] 30 (by decide +kernel))
  node387
  node388
  (invalid_upper a [2,5,6,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,8] 30 (by decide +kernel)))

theorem node390 : UpperPrefix a [2,5,6,7,1] 30 :=
  branch_upper a [2,5,6,7,1] 30 (by decide) (fin9_cases _
  node380
  (invalid_upper a [2,5,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,2] 30 (by decide +kernel))
  node381
  node385
  (invalid_upper a [2,5,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,7] 30 (by decide +kernel))
  node389)

def cert391 : Leaf := ⟨⟨80,84,146,6,0,279,311,55,23⟩,[(4,2)],[(7,3,2),(3,4,4)],⟨7,35,76,152,28,371,467,403,307⟩,⟨7,35,76,152,28,96,192,384,288⟩,[⟨8,1181745676103074333987,⟨23,55,92,152,28,127,220,131,55⟩⟩,⟨5,1210107564164832342049795,⟨23,23,92,152,28,92,220,384,276⟩⟩,⟨6,1219578815444540934063105,⟨415,443,28,152,28,32,128,384,288⟩⟩,⟨0,1210107565290732248892416,⟨22,54,92,152,28,124,220,384,308⟩⟩]⟩
theorem node391 : UpperPrefix a [2,5,6,7,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3] 30 cert391 (by decide +kernel)

def cert392 : Leaf := ⟨⟨96,0,178,294,42,6,62,62,30⟩,[(1,5)],[(7,3,2),(8,4,3),(0,5,1)],⟨7,35,76,152,276,97,218,410,314⟩,⟨7,35,76,152,276,97,192,384,288⟩,[⟨6,1370989690801278350803969,⟨415,443,12,152,276,443,128,384,426⟩⟩,⟨3,1210107565424588100759061,⟨39,35,103,147,311,99,192,384,290⟩⟩,⟨4,1210107565423489662873109,⟨39,35,111,139,295,99,192,384,290⟩⟩]⟩
theorem node392 : UpperPrefix a [2,5,6,7,8,0] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,0] 30 cert392 (by decide +kernel)

def cert393 : Leaf := ⟨⟨80,84,145,261,9,21,29,29,29⟩,[],[(7,3,2),(8,4,3),(1,5,1)],⟨7,35,76,152,276,98,217,409,313⟩,⟨7,35,76,152,276,98,192,384,288⟩,[⟨5,1212473359111855715386403,⟨7,7,76,156,476,79,220,476,477⟩⟩,⟨6,1219578815444266056156161,⟨415,443,12,152,276,426,128,384,288⟩⟩,⟨3,1210107565424588100742677,⟨39,35,103,147,311,98,192,384,288⟩⟩]⟩
theorem node393 : UpperPrefix a [2,5,6,7,8,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,1] 30 cert393 (by decide +kernel)

def cert394 : Leaf := ⟨⟨120,92,0,295,35,0,55,55,23⟩,[(2,5),(5,2)],[(7,3,2),(7,3,5),(8,4,3)],⟨7,35,76,152,276,104,211,403,307⟩,⟨7,35,76,152,276,104,192,384,288⟩,[⟨3,1219580022408964715054081,⟨471,499,68,144,276,96,192,384,288⟩⟩,⟨6,1219578815444266056156161,⟨415,443,12,152,276,40,128,384,288⟩⟩]⟩
theorem node394 : UpperPrefix a [2,5,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,3] 30 cert394 (by decide +kernel)

def cert395 : Leaf := ⟨⟨88,92,144,324,72,12,30,124,92⟩,[],[(5,1,7),(7,3,2),(8,4,3),(1,7,6)],⟨7,35,76,152,276,112,193,386,296⟩,⟨7,35,76,152,276,112,193,386,288⟩,[⟨0,1696538985552769499268096,⟨446,446,380,152,308,380,508,410,308⟩⟩]⟩
theorem node395 : UpperPrefix a [2,5,6,7,8,4,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,4,0,1] 30 cert395 (by decide +kernel)

def cert396 : Leaf := ⟨⟨80,84,146,326,66,6,54,86,86⟩,[],[(7,3,2),(8,4,3)],⟨7,35,76,152,276,112,193,392,290⟩,⟨7,35,76,152,276,112,193,392,288⟩,[⟨0,1227401390267755620467712,⟨446,446,252,152,444,252,508,408,444⟩⟩,⟨3,2414311165205154093923861,⟨311,307,375,499,311,371,499,482,290⟩⟩,⟨5,1212616321369626471564291,⟨7,15,76,152,412,220,205,408,412⟩⟩]⟩
theorem node396 : UpperPrefix a [2,5,6,7,8,4,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,4,0,3] 30 cert396 (by decide +kernel)

theorem node397 : UpperPrefix a [2,5,6,7,8,4,0] 30 :=
  branch_upper a [2,5,6,7,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,7,8,4,0,0] 30 (by decide +kernel))
  node395
  (invalid_upper a [2,5,6,7,8,4,0,2] 30 (by decide +kernel))
  node396
  (invalid_upper a [2,5,6,7,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,0,8] 30 (by decide +kernel)))

def cert398 : Leaf := ⟨⟨112,84,176,356,104,4,53,116,92⟩,[],[(7,3,2),(8,4,3),(0,7,6)],⟨7,35,76,152,276,112,194,385,296⟩,⟨7,35,76,152,276,112,194,385,288⟩,[⟨1,1696538985552769499267073,⟨445,445,380,152,308,380,508,409,308⟩⟩,⟨3,1210256148887181749943317,⟨7,99,103,243,503,243,194,385,354⟩⟩]⟩
theorem node398 : UpperPrefix a [2,5,6,7,8,4,1,0] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,4,1,0] 30 cert398 (by decide +kernel)

def cert399 : Leaf := ⟨⟨80,84,145,325,65,5,53,85,85⟩,[],[(7,3,2),(8,4,3)],⟨7,35,76,152,276,112,194,392,289⟩,⟨7,35,76,152,276,112,194,392,288⟩,[⟨1,1227401390267755620466689,⟨445,445,252,152,444,252,508,408,444⟩⟩,⟨3,1507619104085391612870165,⟨311,307,375,499,311,371,450,482,290⟩⟩,⟨5,1212616321369626471564355,⟨7,15,77,152,412,221,207,408,412⟩⟩]⟩
theorem node399 : UpperPrefix a [2,5,6,7,8,4,1,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,4,1,3] 30 cert399 (by decide +kernel)

theorem node400 : UpperPrefix a [2,5,6,7,8,4,1] 30 :=
  branch_upper a [2,5,6,7,8,4,1] 30 (by decide) (fin9_cases _
  node398
  (invalid_upper a [2,5,6,7,8,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,1,2] 30 (by decide +kernel))
  node399
  (invalid_upper a [2,5,6,7,8,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,1,8] 30 (by decide +kernel)))

def cert401 : Local := ⟨⟨112,84,0,359,99,7,0,119,87⟩,[(2,6),(6,3)],[(7,3,2),(7,3,6),(8,4,3),(3,6,2)]⟩
theorem node401 : UpperPrefix a [2,5,6,7,8,4,3] 30 :=
  local_sound a [2,5,6,7,8,4,3] 30 cert401 (by decide +kernel)

theorem node402 : UpperPrefix a [2,5,6,7,8,4] 30 :=
  branch_upper a [2,5,6,7,8,4] 30 (by decide) (fin9_cases _
  node397
  node400
  (invalid_upper a [2,5,6,7,8,4,2] 30 (by decide +kernel))
  node401
  (invalid_upper a [2,5,6,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,8] 30 (by decide +kernel)))

theorem node403 : UpperPrefix a [2,5,6,7,8] 30 :=
  branch_upper a [2,5,6,7,8] 30 (by decide) (fin9_cases _
  node392
  node393
  (invalid_upper a [2,5,6,7,8,2] 30 (by decide +kernel))
  node394
  node402
  (invalid_upper a [2,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,8] 30 (by decide +kernel)))

theorem node404 : UpperPrefix a [2,5,6,7] 30 :=
  branch_upper a [2,5,6,7] 30 (by decide) (fin9_cases _
  node379
  node390
  (invalid_upper a [2,5,6,7,2] 30 (by decide +kernel))
  node391
  (invalid_upper a [2,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,7] 30 (by decide +kernel))
  node403)

def cert405 : Leaf := ⟨⟨464,464,400,193,0,401,280,88,217⟩,[(4,0)],[(2,0,4),(1,5,1)],⟨7,35,76,280,21,98,216,408,440⟩,⟨7,35,76,280,21,98,192,384,288⟩,[⟨5,1212549596039808744948769,⟨23,19,204,476,21,87,204,476,477⟩⟩,⟨0,1210181496375334602277888,⟨6,34,204,476,20,98,192,384,288⟩⟩,⟨3,1210107565424931698126357,⟨55,51,119,275,55,98,192,384,288⟩⟩]⟩
theorem node405 : UpperPrefix a [2,5,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,0,1] 30 cert405 (by decide +kernel)

def cert406 : Leaf := ⟨⟨504,472,0,163,0,0,307,51,147⟩,[(2,5),(4,0),(5,2)],[(2,0,4)],⟨7,35,76,280,21,104,210,402,434⟩,⟨7,35,76,280,21,104,192,384,288⟩,[⟨3,1219580022408964715054081,⟨471,499,68,272,213,96,192,384,288⟩⟩,⟨6,1219578815444266056156161,⟨415,443,12,280,157,40,128,384,288⟩⟩]⟩
theorem node406 : UpperPrefix a [2,5,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,0,3] 30 cert406 (by decide +kernel)

def cert407 : Leaf := ⟨⟨496,464,432,224,0,384,312,120,216⟩,[(4,0)],[(2,0,4)],⟨7,35,76,280,21,112,194,392,424⟩,⟨7,35,76,280,21,112,194,384,288⟩,[⟨0,1486937908204162864645120,⟨454,494,460,444,508,508,454,384,428⟩⟩,⟨1,1695321500278692309368833,⟨413,445,492,408,413,508,508,384,428⟩⟩,⟨3,1210107565424931698142741,⟨55,51,119,275,55,115,194,384,290⟩⟩]⟩
theorem node407 : UpperPrefix a [2,5,6,8,0,4,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,0,4,1] 30 cert407 (by decide +kernel)

def cert408 : Local := ⟨⟨240,208,0,227,0,131,307,115,211⟩,[(2,6),(4,0)],[(2,0,4),(8,3,6),(3,6,2)]⟩
theorem node408 : UpperPrefix a [2,5,6,8,0,4,3] 30 :=
  local_sound a [2,5,6,8,0,4,3] 30 cert408 (by decide +kernel)

theorem node409 : UpperPrefix a [2,5,6,8,0,4] 30 :=
  branch_upper a [2,5,6,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,8,0,4,0] 30 (by decide +kernel))
  node407
  (invalid_upper a [2,5,6,8,0,4,2] 30 (by decide +kernel))
  node408
  (invalid_upper a [2,5,6,8,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,0,4,8] 30 (by decide +kernel)))

def cert410 : Leaf := ⟨⟨368,336,307,35,0,0,315,59,27⟩,[(4,0),(5,6)],[(2,0,4),(7,5,5)],⟨7,35,76,280,21,224,218,410,314⟩,⟨7,35,76,280,21,224,192,384,288⟩,[⟨6,1219578815444266056156161,⟨415,443,12,280,157,160,128,384,288⟩⟩,⟨3,1210107567535994023447573,⟨23,51,119,273,23,224,224,384,288⟩⟩]⟩
theorem node410 : UpperPrefix a [2,5,6,8,0,7] 30 :=
  Boolean.leaf_sound a [2,5,6,8,0,7] 30 cert410 (by decide +kernel)

theorem node411 : UpperPrefix a [2,5,6,8,0] 30 :=
  branch_upper a [2,5,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,8,0,0] 30 (by decide +kernel))
  node405
  (invalid_upper a [2,5,6,8,0,2] 30 (by decide +kernel))
  node406
  node409
  (invalid_upper a [2,5,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,0,6] 30 (by decide +kernel))
  node410
  (invalid_upper a [2,5,6,8,0,8] 30 (by decide +kernel)))

def cert412 : Leaf := ⟨⟨0,0,400,230,0,414,284,92,222⟩,[(0,4),(1,5),(4,0)],[(0,5,1)],⟨7,35,76,280,22,97,216,408,440⟩,⟨7,35,76,280,22,97,192,384,288⟩,[⟨1,1210181496375334602276865,⟨5,33,204,476,20,97,192,384,288⟩⟩,⟨5,1210181495249503414912017,⟨23,19,204,477,23,81,192,384,256⟩⟩]⟩
theorem node412 : UpperPrefix a [2,5,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,0] 30 cert412 (by decide +kernel)

def cert413 : Leaf := ⟨⟨0,476,0,231,0,0,311,119,215⟩,[(0,4),(2,5),(4,0),(5,2)],[],⟨7,35,76,280,22,104,209,401,433⟩,⟨7,35,76,280,22,104,192,384,288⟩,[⟨3,1219801815683413457241105,⟨471,499,196,465,471,224,192,384,288⟩⟩]⟩
theorem node413 : UpperPrefix a [2,5,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,3] 30 cert413 (by decide +kernel)

def cert414 : Leaf := ⟨⟨0,260,387,167,0,263,271,15,159⟩,[(0,4),(4,0)],[],⟨7,35,76,280,22,112,201,393,425⟩,⟨7,35,76,280,22,112,192,384,288⟩,[⟨4,1210181496374235090666513,⟨7,35,204,461,7,99,192,384,290⟩⟩,⟨6,1371211051730165012907025,⟨415,443,140,409,415,443,128,384,426⟩⟩,⟨5,1210181495249503414912017,⟨23,19,204,477,23,81,192,384,256⟩⟩,⟨3,1210107565424931698142741,⟨55,51,119,275,55,115,192,384,290⟩⟩,⟨7,1208926973804215360581141,⟨55,51,127,283,55,115,64,256,290⟩⟩]⟩
theorem node414 : UpperPrefix a [2,5,6,8,1,4] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,4] 30 cert414 (by decide +kernel)

def cert415 : Leaf := ⟨⟨0,348,275,39,0,0,287,31,31⟩,[(0,4),(4,0),(5,6)],[(7,5,5)],⟨7,35,76,280,22,224,217,409,313⟩,⟨7,35,76,280,22,224,192,384,288⟩,[⟨5,1210181495249503414912017,⟨23,19,204,477,23,192,192,384,256⟩⟩,⟨6,1219800176373152718259217,⟨415,443,140,409,415,160,128,384,288⟩⟩]⟩
theorem node415 : UpperPrefix a [2,5,6,8,1,7] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,7] 30 cert415 (by decide +kernel)

theorem node416 : UpperPrefix a [2,5,6,8,1] 30 :=
  branch_upper a [2,5,6,8,1] 30 (by decide) (fin9_cases _
  node412
  (invalid_upper a [2,5,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,2] 30 (by decide +kernel))
  node413
  node414
  (invalid_upper a [2,5,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,6] 30 (by decide +kernel))
  node415
  (invalid_upper a [2,5,6,8,1,8] 30 (by decide +kernel)))

def cert417 : Leaf := ⟨⟨480,0,434,166,0,390,310,54,150⟩,[(1,5),(4,2)],[(3,4,4),(0,5,1)],⟨7,35,76,280,28,97,210,402,434⟩,⟨7,35,76,280,28,97,192,384,288⟩,[⟨6,1370989690801553228710913,⟨415,443,28,280,28,443,128,384,426⟩⟩,⟨4,1210107565423489662873109,⟨39,35,111,267,47,99,192,384,290⟩⟩]⟩
theorem node417 : UpperPrefix a [2,5,6,8,3,0] 30 :=
  Boolean.leaf_sound a [2,5,6,8,3,0] 30 cert417 (by decide +kernel)

def cert418 : Leaf := ⟨⟨448,452,401,133,0,389,277,21,149⟩,[(4,2)],[(3,4,4),(1,5,1)],⟨7,35,76,280,28,98,209,401,433⟩,⟨7,35,76,280,28,98,192,384,288⟩,[⟨5,1212473359117067647714337,⟨23,3,92,476,28,87,220,476,477⟩⟩,⟨4,1210107565423489662856725,⟨39,35,111,267,47,98,192,384,288⟩⟩,⟨6,1219578815444540934063105,⟨415,443,28,280,28,426,128,384,288⟩⟩]⟩
theorem node418 : UpperPrefix a [2,5,6,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,3,1] 30 cert418 (by decide +kernel)

def cert419 : Leaf := ⟨⟨352,324,419,167,0,263,291,35,131⟩,[(4,2)],[(3,4,4)],⟨7,35,76,280,28,112,195,387,419⟩,⟨7,35,76,280,28,112,192,384,288⟩,[⟨4,1373431200244494031275049,⟨455,483,205,463,205,487,192,450,483⟩⟩,⟨2,1219580022408897068270593,⟨451,483,72,280,24,112,192,384,288⟩⟩,⟨6,1219578815444540934063105,⟨415,443,28,280,28,48,128,384,288⟩⟩,⟨7,1208926973804146641104405,⟨55,35,127,283,63,115,64,256,290⟩⟩]⟩
theorem node419 : UpperPrefix a [2,5,6,8,3,4] 30 :=
  Boolean.leaf_sound a [2,5,6,8,3,4] 30 cert419 (by decide +kernel)

def cert420 : Leaf := ⟨⟨336,340,275,7,0,0,311,55,23⟩,[(4,2),(5,6)],[(3,4,4),(7,5,5)],⟨7,35,76,280,28,224,211,403,307⟩,⟨7,35,76,280,28,224,192,384,288⟩,[⟨5,1210107564182467477767171,⟨23,23,92,280,28,220,220,408,284⟩⟩,⟨6,1219578815444540934063105,⟨415,443,28,280,28,160,128,384,288⟩⟩]⟩
theorem node420 : UpperPrefix a [2,5,6,8,3,7] 30 :=
  Boolean.leaf_sound a [2,5,6,8,3,7] 30 cert420 (by decide +kernel)

theorem node421 : UpperPrefix a [2,5,6,8,3] 30 :=
  branch_upper a [2,5,6,8,3] 30 (by decide) (fin9_cases _
  node417
  node418
  (invalid_upper a [2,5,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,3,3] 30 (by decide +kernel))
  node419
  (invalid_upper a [2,5,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,3,6] 30 (by decide +kernel))
  node420
  (invalid_upper a [2,5,6,8,3,8] 30 (by decide +kernel)))

def cert422 : Leaf := ⟨⟨360,0,416,36,296,270,300,60,28⟩,[(1,5)],[(0,5,1),(1,6,5)],⟨7,35,76,280,148,97,194,408,312⟩,⟨7,35,76,280,148,97,194,384,288⟩,[⟨4,1210107854498290746818077,⟨39,35,111,367,231,99,194,384,290⟩⟩,⟨6,1371063477777848066917377,⟨415,443,156,408,148,443,394,384,426⟩⟩,⟨7,1284484837529788234100245,⟨39,35,111,283,319,99,66,256,290⟩⟩]⟩
theorem node422 : UpperPrefix a [2,5,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,0,1] 30 cert422 (by decide +kernel)

def cert423 : Leaf := ⟨⟨240,0,0,166,34,150,310,54,150⟩,[(1,5),(2,6)],[(8,3,6),(0,5,1),(3,6,2)],⟨7,35,76,280,148,97,200,402,306⟩,⟨7,35,76,280,148,97,200,384,288⟩,[⟨6,1370989690801278350803969,⟨415,443,12,280,148,443,136,384,426⟩⟩]⟩
theorem node423 : UpperPrefix a [2,5,6,8,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,0,3] 30 cert423 (by decide +kernel)

def cert424 : Local := ⟨⟨360,0,306,102,362,270,0,110,78⟩,[(1,5),(6,4)],[(7,4,6),(0,5,1),(4,6,2)]⟩
theorem node424 : UpperPrefix a [2,5,6,8,7,0,4] 30 :=
  local_sound a [2,5,6,8,7,0,4] 30 cert424 (by decide +kernel)

theorem node425 : UpperPrefix a [2,5,6,8,7,0] 30 :=
  branch_upper a [2,5,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,8,7,0,0] 30 (by decide +kernel))
  node422
  (invalid_upper a [2,5,6,8,7,0,2] 30 (by decide +kernel))
  node423
  node424
  (invalid_upper a [2,5,6,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,0,8] 30 (by decide +kernel)))

def cert426 : Leaf := ⟨⟨320,324,401,5,265,261,285,29,29⟩,[],[(1,5,1)],⟨7,35,76,280,148,98,217,409,313⟩,⟨7,35,76,280,148,98,192,384,288⟩,[⟨5,1212473359116792769807393,⟨7,3,92,476,156,87,220,476,477⟩⟩,⟨7,1284484837529788234083861,⟨39,35,111,283,319,98,64,256,288⟩⟩,⟨6,1219578815444266056156161,⟨415,443,12,280,148,426,128,384,288⟩⟩,⟨3,1210107565424588100742677,⟨39,35,103,275,183,98,192,384,288⟩⟩,⟨4,1210107565423489662856725,⟨39,35,111,267,167,98,192,384,288⟩⟩]⟩
theorem node426 : UpperPrefix a [2,5,6,8,7,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,1] 30 cert426 (by decide +kernel)

def cert427 : Leaf := ⟨⟨120,92,0,39,291,0,55,55,23⟩,[(2,5),(5,2)],[],⟨7,35,76,280,148,104,211,403,307⟩,⟨7,35,76,280,148,104,192,384,288⟩,[⟨3,1219580022408964715054081,⟨471,499,68,272,148,96,192,384,288⟩⟩,⟨6,1219578815444266056156161,⟨415,443,12,280,148,40,128,384,288⟩⟩,⟨7,1284484837529788242620215,⟨39,39,111,283,319,111,64,259,295⟩⟩,⟨8,1182034321811138838335,⟨39,39,111,127,247,111,192,131,39⟩⟩]⟩
theorem node427 : UpperPrefix a [2,5,6,8,7,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,3] 30 cert427 (by decide +kernel)

def cert428 : Leaf := ⟨⟨336,340,272,68,320,388,278,116,92⟩,[],[(5,1,7),(7,4,5),(1,7,6)],⟨7,35,76,280,148,112,193,386,296⟩,⟨7,35,76,280,148,112,193,386,288⟩,[⟨0,1772096849258624714802176,⟨446,446,380,280,444,380,508,410,300⟩⟩,⟨3,1212543040925360207232533,⟨119,35,247,499,247,115,227,386,418⟩⟩]⟩
theorem node428 : UpperPrefix a [2,5,6,8,7,4,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,4,0,1] 30 cert428 (by decide +kernel)

def cert429 : Leaf := ⟨⟨112,84,50,102,106,134,54,0,86⟩,[(7,3)],[(8,3,7),(7,4,5),(3,7,4)],⟨7,35,76,280,148,112,193,392,290⟩,⟨7,35,76,280,148,112,193,392,288⟩,[⟨0,1227327603293927704101888,⟨446,446,252,408,188,252,508,408,444⟩⟩]⟩
theorem node429 : UpperPrefix a [2,5,6,8,7,4,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,4,0,3] 30 cert429 (by decide +kernel)

theorem node430 : UpperPrefix a [2,5,6,8,7,4,0] 30 :=
  branch_upper a [2,5,6,8,7,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,8,7,4,0,0] 30 (by decide +kernel))
  node428
  (invalid_upper a [2,5,6,8,7,4,0,2] 30 (by decide +kernel))
  node429
  (invalid_upper a [2,5,6,8,7,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,0,8] 30 (by decide +kernel)))

def cert431 : Leaf := ⟨⟨112,84,48,100,352,132,53,116,92⟩,[],[(7,4,5),(0,7,6)],⟨7,35,76,280,148,112,194,385,296⟩,⟨7,35,76,280,148,112,194,385,288⟩,[⟨1,1772096849258624714801153,⟨445,445,380,280,444,380,508,409,300⟩⟩,⟨3,1210184163526934598352405,⟨119,35,247,499,247,115,194,483,290⟩⟩,⟨8,1182034744023595383837,⟨7,35,111,127,247,115,194,129,34⟩⟩]⟩
theorem node431 : UpperPrefix a [2,5,6,8,7,4,1,0] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,4,1,0] 30 cert431 (by decide +kernel)

def cert432 : Leaf := ⟨⟨112,84,49,101,105,133,53,0,85⟩,[(7,3)],[(8,3,7),(7,4,5),(3,7,4)],⟨7,35,76,280,148,112,194,392,289⟩,⟨7,35,76,280,148,112,194,392,288⟩,[⟨1,1227327603293927704100865,⟨445,445,252,408,188,252,508,408,444⟩⟩]⟩
theorem node432 : UpperPrefix a [2,5,6,8,7,4,1,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,4,1,3] 30 cert432 (by decide +kernel)

theorem node433 : UpperPrefix a [2,5,6,8,7,4,1] 30 :=
  branch_upper a [2,5,6,8,7,4,1] 30 (by decide) (fin9_cases _
  node431
  (invalid_upper a [2,5,6,8,7,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,1,2] 30 (by decide +kernel))
  node432
  (invalid_upper a [2,5,6,8,7,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,1,8] 30 (by decide +kernel)))

def cert434 : Leaf := ⟨⟨96,68,0,102,98,134,294,103,71⟩,[(2,6)],[(8,3,6),(7,4,5),(3,6,2)],⟨7,35,76,280,148,112,200,387,291⟩,⟨7,35,76,280,148,112,200,384,288⟩,[⟨4,1373426030112121822528553,⟨455,419,205,463,196,487,205,386,419⟩⟩,⟨0,1210110167111010287092736,⟨38,34,124,380,252,116,252,508,288⟩⟩]⟩
theorem node434 : UpperPrefix a [2,5,6,8,7,4,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,4,3] 30 cert434 (by decide +kernel)

theorem node435 : UpperPrefix a [2,5,6,8,7,4] 30 :=
  branch_upper a [2,5,6,8,7,4] 30 (by decide) (fin9_cases _
  node430
  node433
  (invalid_upper a [2,5,6,8,7,4,2] 30 (by decide +kernel))
  node434
  (invalid_upper a [2,5,6,8,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,4,8] 30 (by decide +kernel)))

theorem node436 : UpperPrefix a [2,5,6,8,7] 30 :=
  branch_upper a [2,5,6,8,7] 30 (by decide) (fin9_cases _
  node425
  node426
  (invalid_upper a [2,5,6,8,7,2] 30 (by decide +kernel))
  node427
  node435
  (invalid_upper a [2,5,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,8] 30 (by decide +kernel)))

theorem node437 : UpperPrefix a [2,5,6,8] 30 :=
  branch_upper a [2,5,6,8] 30 (by decide) (fin9_cases _
  node411
  node416
  (invalid_upper a [2,5,6,8,2] 30 (by decide +kernel))
  node421
  (invalid_upper a [2,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,6] 30 (by decide +kernel))
  node436
  (invalid_upper a [2,5,6,8,8] 30 (by decide +kernel)))

theorem node438 : UpperPrefix a [2,5,6] 30 :=
  branch_upper a [2,5,6] 30 (by decide) (fin9_cases _
  node342
  node371
  (invalid_upper a [2,5,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,6] 30 (by decide +kernel))
  node404
  node437)

def cert439 : Leaf := ⟨⟨0,408,304,422,0,408,312,120,216⟩,[(0,4),(4,0)],[(2,0,3),(1,4,3)],⟨7,35,140,25,22,376,472,472,376⟩,⟨7,35,140,25,22,96,192,384,288⟩,[⟨0,1247960428519835460174848,⟨22,50,492,508,22,96,192,384,288⟩⟩,⟨6,1210106412373478477022385,⟨31,59,157,25,31,63,157,415,315⟩⟩]⟩
theorem node439 : UpperPrefix a [2,5,7,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,0,1] 30 cert439 (by decide +kernel)

def cert440 : Leaf := ⟨⟨176,144,50,166,0,402,306,114,210⟩,[(4,2)],[(2,0,3),(3,4,4)],⟨7,35,140,25,28,370,466,466,370⟩,⟨7,35,140,25,28,96,192,384,288⟩,[⟨0,1214839173189165703496704,⟨502,482,156,508,28,96,192,384,288⟩⟩,⟨6,1210106412378149253956769,⟨31,59,157,25,28,63,157,415,315⟩⟩,⟨8,1181745685024686097569,⟨31,59,157,25,28,127,221,159,59⟩⟩]⟩
theorem node440 : UpperPrefix a [2,5,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,0,3] 30 cert440 (by decide +kernel)

def cert441 : Leaf := ⟨⟨120,88,112,100,168,24,312,120,88⟩,[],[(2,0,3),(7,2,4),(1,5,1)],⟨7,35,140,25,84,98,472,408,312⟩,⟨7,35,140,25,84,98,192,384,288⟩,[⟨0,1247997393820110946305024,⟨246,50,476,508,212,98,192,384,288⟩⟩,⟨8,1181748490619059369205,⟨15,59,143,59,127,127,255,143,59⟩⟩]⟩
theorem node441 : UpperPrefix a [2,5,7,0,6,1] 30 :=
  Boolean.leaf_sound a [2,5,7,0,6,1] 30 cert441 (by decide +kernel)

def cert442 : Leaf := ⟨⟨120,88,112,100,168,16,56,120,88⟩,[],[(2,0,3),(7,2,4)],⟨7,35,140,25,84,104,194,400,304⟩,⟨7,35,140,25,84,104,194,384,288⟩,[⟨8,1184131079901340237557,⟨127,59,255,59,127,127,255,255,59⟩⟩,⟨0,1430869029313596198224896,⟨470,502,444,508,468,508,466,384,436⟩⟩,⟨1,1751943781219319525670913,⟨397,445,140,413,500,508,508,384,436⟩⟩]⟩
theorem node442 : UpperPrefix a [2,5,7,0,6,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,0,6,3,1] 30 cert442 (by decide +kernel)

def cert443 : Leaf := ⟨⟨104,72,98,102,170,18,42,106,74⟩,[],[(2,0,3),(7,2,4),(4,6,5)],⟨7,35,140,25,84,104,208,386,290⟩,⟨7,35,140,25,84,104,208,384,288⟩,[⟨8,1184131079901340237557,⟨127,59,255,59,127,127,255,255,59⟩⟩,⟨0,1224302605489853671932928,⟨502,498,252,508,116,124,208,384,304⟩⟩]⟩
theorem node443 : UpperPrefix a [2,5,7,0,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,0,6,3,4] 30 cert443 (by decide +kernel)

def cert444 : Leaf := ⟨⟨120,88,114,102,170,18,0,122,90⟩,[(6,7)],[(2,0,3),(7,2,4),(8,6,6)],⟨7,35,140,25,84,104,448,402,306⟩,⟨7,35,140,25,84,104,448,384,288⟩,[⟨0,1224304839275268847698944,⟨502,498,252,508,116,124,448,448,304⟩⟩]⟩
theorem node444 : UpperPrefix a [2,5,7,0,6,3,8] 30 :=
  Boolean.leaf_sound a [2,5,7,0,6,3,8] 30 cert444 (by decide +kernel)

theorem node445 : UpperPrefix a [2,5,7,0,6,3] 30 :=
  branch_upper a [2,5,7,0,6,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,6,3,0] 30 (by decide +kernel))
  node442
  (invalid_upper a [2,5,7,0,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,6,3,3] 30 (by decide +kernel))
  node443
  (invalid_upper a [2,5,7,0,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,6,3,7] 30 (by decide +kernel))
  node444)

def cert446 : Leaf := ⟨⟨48,16,51,38,171,0,315,59,27⟩,[(5,4)],[(2,0,3),(7,2,4),(6,4,5)],⟨7,35,140,25,84,112,458,394,298⟩,⟨7,35,140,25,84,112,192,384,288⟩,[⟨8,1181748490619059369205,⟨15,59,143,59,127,127,255,143,59⟩⟩,⟨3,1210107565846800565826581,⟨7,35,135,51,119,115,192,384,290⟩⟩]⟩
theorem node446 : UpperPrefix a [2,5,7,0,6,4] 30 :=
  Boolean.leaf_sound a [2,5,7,0,6,4] 30 cert446 (by decide +kernel)

def cert447 : Leaf := ⟨⟨344,344,336,324,392,24,280,88,88⟩,[],[(2,0,3),(7,2,4)],⟨7,35,140,25,84,352,194,408,312⟩,⟨7,35,140,25,84,352,194,384,288⟩,[⟨0,1266886662437355975083008,⟨502,114,444,508,500,352,194,384,288⟩⟩,⟨1,1560245217368279810310145,⟨397,445,396,445,500,500,508,384,304⟩⟩,⟨5,1212763931340181729707075,⟨95,223,140,25,93,477,223,388,412⟩⟩]⟩
theorem node447 : UpperPrefix a [2,5,7,0,6,8,1] 30 :=
  Boolean.leaf_sound a [2,5,7,0,6,8,1] 30 cert447 (by decide +kernel)

#print axioms node447
end Delivery.FiniteExclusion.Sharp2x3x4
