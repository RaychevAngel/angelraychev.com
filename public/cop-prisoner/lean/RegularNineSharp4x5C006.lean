import RegularNineSharp4x5Base
import RegularNineSharp4x5C005
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert384 : Local := ⟨⟨0,489,0,466,329,409,312,0,233⟩,[(0,1),(2,7),(7,2)],[(2,0,0),(1,5,3)]⟩
theorem node384 : UpperPrefix a [2,4,8,5,7,1,0,3] 30 :=
  local_sound a [2,4,8,5,7,1,0,3] 30 cert384 (by decide +kernel)

def cert385 : Leaf := ⟨⟨0,417,177,402,321,401,304,49,169⟩,[(0,1)],[(2,0,0),(1,5,3),(6,7,4)],⟨7,22,268,41,176,98,193,448,280⟩,⟨7,22,268,41,176,98,193,448,272⟩,[⟨3,1210144587666028168744455,⟨247,247,503,115,176,115,243,496,272⟩⟩]⟩
theorem node385 : UpperPrefix a [2,4,8,5,7,1,0,6] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,1,0,6] 30 cert385 (by decide +kernel)

theorem node386 : UpperPrefix a [2,4,8,5,7,1,0] 30 :=
  branch_upper a [2,4,8,5,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,5,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,0,2] 30 (by decide +kernel))
  node384
  (invalid_upper a [2,4,8,5,7,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,0,5] 30 (by decide +kernel))
  node385
  (invalid_upper a [2,4,8,5,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,0,8] 30 (by decide +kernel)))

def cert387 : Leaf := ⟨⟨0,417,177,386,321,393,289,113,225⟩,[(0,1)],[(2,0,0),(1,5,3)],⟨7,22,268,41,176,98,200,449,337⟩,⟨7,22,268,41,176,98,200,384,272⟩,[⟨3,1361518440643607391112199,⟨7,23,279,433,432,499,208,384,272⟩⟩,⟨4,1210107853583501768000515,⟨47,111,268,41,232,107,200,384,320⟩⟩,⟨6,1210106412362353588962695,⟨7,31,271,41,185,43,137,391,287⟩⟩]⟩
theorem node387 : UpperPrefix a [2,4,8,5,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,1,3] 30 cert387 (by decide +kernel)

theorem node388 : UpperPrefix a [2,4,8,5,7,1] 30 :=
  branch_upper a [2,4,8,5,7,1] 30 (by decide) (fin9_cases _
  node386
  (invalid_upper a [2,4,8,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,2] 30 (by decide +kernel))
  node387
  (invalid_upper a [2,4,8,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,8] 30 (by decide +kernel)))

def cert389 : Leaf := ⟨⟨0,289,51,274,323,275,275,83,195⟩,[(0,1)],[(2,0,0)],⟨7,22,268,41,176,104,195,451,339⟩,⟨7,22,268,41,176,104,192,384,272⟩,[⟨3,1238506453886665789279239,⟨455,471,471,241,176,112,192,384,272⟩⟩,⟨7,1208926975914944893158791,⟨7,31,271,41,57,104,105,263,287⟩⟩,⟨5,1219580021282997162476547,⟨455,471,268,201,144,72,192,384,272⟩⟩,⟨6,1210106412362349293995399,⟨7,31,271,41,185,40,129,391,287⟩⟩]⟩
theorem node389 : UpperPrefix a [2,4,8,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,3] 30 cert389 (by decide +kernel)

theorem node390 : UpperPrefix a [2,4,8,5,7] 30 :=
  branch_upper a [2,4,8,5,7] 30 (by decide) (fin9_cases _
  node383
  node388
  (invalid_upper a [2,4,8,5,7,2] 30 (by decide +kernel))
  node389
  (invalid_upper a [2,4,8,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,8] 30 (by decide +kernel)))

theorem node391 : UpperPrefix a [2,4,8,5] 30 :=
  branch_upper a [2,4,8,5] 30 (by decide) (fin9_cases _
  node372
  node376
  (invalid_upper a [2,4,8,5,2] 30 (by decide +kernel))
  node377
  (invalid_upper a [2,4,8,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,5] 30 (by decide +kernel))
  node382
  node390
  (invalid_upper a [2,4,8,5,8] 30 (by decide +kernel)))

def cert392 : Leaf := ⟨⟨0,97,241,48,66,17,313,121,233⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,22,268,73,49,98,232,424,440⟩,⟨7,22,268,73,49,98,192,384,272⟩,[⟨7,1208926973947637203471879,⟨23,23,319,123,59,123,64,256,272⟩⟩,⟨8,1181745953725440069127,⟨23,23,63,123,59,123,192,128,16⟩⟩,⟨3,1210107565568349246066183,⟨23,23,311,115,51,115,192,384,272⟩⟩]⟩
theorem node392 : UpperPrefix a [2,4,8,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,1] 30 cert392 (by decide +kernel)

def cert393 : Leaf := ⟨⟨0,41,179,434,8,0,315,59,171⟩,[(0,1),(5,3)],[(2,0,0),(6,3,5)],⟨7,22,268,73,49,104,226,418,434⟩,⟨7,22,268,73,49,104,192,384,272⟩,[⟨7,1208926973945433885249031,⟨23,23,319,123,51,120,64,256,272⟩⟩,⟨8,1181745951522121846279,⟨23,23,63,123,51,120,192,128,16⟩⟩,⟨1,1210107565565876418641921,⟨5,20,316,121,49,120,192,384,272⟩⟩]⟩
theorem node393 : UpperPrefix a [2,4,8,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,3] 30 cert393 (by decide +kernel)

def cert394 : Leaf := ⟨⟨0,97,115,306,64,0,315,123,107⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,22,268,73,49,224,234,426,314⟩,⟨7,22,268,73,49,224,192,384,272⟩,[⟨3,1210107567536200181877767,⟨7,23,279,113,49,224,224,384,272⟩⟩,⟨8,1181747921572080913415,⟨7,23,31,121,49,224,224,128,16⟩⟩,⟨1,1210107567536201255616513,⟨5,20,284,121,49,224,224,384,272⟩⟩]⟩
theorem node394 : UpperPrefix a [2,4,8,6,0,7] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,7] 30 cert394 (by decide +kernel)

theorem node395 : UpperPrefix a [2,4,8,6,0] 30 :=
  branch_upper a [2,4,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,0,0] 30 (by decide +kernel))
  node392
  (invalid_upper a [2,4,8,6,0,2] 30 (by decide +kernel))
  node393
  (invalid_upper a [2,4,8,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,6] 30 (by decide +kernel))
  node394
  (invalid_upper a [2,4,8,6,0,8] 30 (by decide +kernel)))

def cert396 : Leaf := ⟨⟨0,489,225,0,457,0,297,105,233⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,22,268,73,50,97,232,424,440⟩,⟨7,22,268,73,50,97,192,384,272⟩,[⟨1,1285850275069535586353153,⟨237,468,492,105,508,105,192,384,468⟩⟩,⟨4,1212510380749127368573955,⟨239,239,492,105,107,105,192,452,492⟩⟩]⟩
theorem node396 : UpperPrefix a [2,4,8,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,0] 30 cert396 (by decide +kernel)

def cert397 : Leaf := ⟨⟨0,424,179,434,392,0,307,51,163⟩,[(0,1),(5,3)],[(2,0,0),(6,3,5)],⟨7,22,268,73,50,104,225,417,433⟩,⟨7,22,268,73,50,104,192,384,272⟩,[⟨3,1285813291192730763920387,⟨7,471,260,65,499,96,192,384,464⟩⟩,⟨0,1210107565566151296552448,⟨22,22,318,122,50,120,192,384,272⟩⟩]⟩
theorem node397 : UpperPrefix a [2,4,8,6,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,3] 30 cert397 (by decide +kernel)

def cert398 : Local := ⟨⟨0,360,114,0,328,0,314,122,106⟩,[(0,1),(3,6),(5,6)],[(2,0,0),(7,5,5),(0,6,3)]⟩
theorem node398 : UpperPrefix a [2,4,8,6,1,7,0] 30 :=
  local_sound a [2,4,8,6,1,7,0] 30 cert398 (by decide +kernel)

def cert399 : Leaf := ⟨⟨0,353,115,306,321,0,307,115,99⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,22,268,73,50,224,200,417,305⟩,⟨7,22,268,73,50,224,200,384,272⟩,[⟨3,1342592083755332036201991,⟨407,407,439,499,435,224,496,384,400⟩⟩]⟩
theorem node399 : UpperPrefix a [2,4,8,6,1,7,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,7,3] 30 cert399 (by decide +kernel)

def cert400 : Local := ⟨⟨0,361,115,306,329,0,0,123,107⟩,[(0,1),(5,6),(6,5)],[(2,0,0),(7,5,5),(7,5,6)]⟩
theorem node400 : UpperPrefix a [2,4,8,6,1,7,5] 30 :=
  local_sound a [2,4,8,6,1,7,5] 30 cert400 (by decide +kernel)

theorem node401 : UpperPrefix a [2,4,8,6,1,7] 30 :=
  branch_upper a [2,4,8,6,1,7] 30 (by decide) (fin9_cases _
  node398
  (invalid_upper a [2,4,8,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,2] 30 (by decide +kernel))
  node399
  (invalid_upper a [2,4,8,6,1,7,4] 30 (by decide +kernel))
  node400
  (invalid_upper a [2,4,8,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,8] 30 (by decide +kernel)))

theorem node402 : UpperPrefix a [2,4,8,6,1] 30 :=
  branch_upper a [2,4,8,6,1] 30 (by decide) (fin9_cases _
  node396
  (invalid_upper a [2,4,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,2] 30 (by decide +kernel))
  node397
  (invalid_upper a [2,4,8,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,6] 30 (by decide +kernel))
  node401
  (invalid_upper a [2,4,8,6,1,8] 30 (by decide +kernel)))

def cert403 : Local := ⟨⟨0,424,178,0,451,0,306,50,162⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(6,3,4),(3,4,1),(0,5,4)]⟩
theorem node403 : UpperPrefix a [2,4,8,6,3,0] 30 :=
  local_sound a [2,4,8,6,3,0] 30 cert403 (by decide +kernel)

def cert404 : Leaf := ⟨⟨0,41,179,50,67,17,307,51,163⟩,[(0,1)],[(2,0,0),(6,3,4),(3,4,1)],⟨7,22,268,73,56,98,225,417,433⟩,⟨7,22,268,73,56,98,192,384,272⟩,[⟨7,1208926973947637203471879,⟨23,23,319,123,56,123,64,256,272⟩⟩,⟨8,1181745953725440069127,⟨23,23,63,123,56,123,192,128,16⟩⟩]⟩
theorem node404 : UpperPrefix a [2,4,8,6,3,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,1] 30 cert404 (by decide +kernel)

def cert405 : Local := ⟨⟨0,297,51,306,323,0,307,51,35⟩,[(0,1),(5,6)],[(2,0,0),(6,3,4),(3,4,1),(7,5,5)]⟩
theorem node405 : UpperPrefix a [2,4,8,6,3,7] 30 :=
  local_sound a [2,4,8,6,3,7] 30 cert405 (by decide +kernel)

theorem node406 : UpperPrefix a [2,4,8,6,3] 30 :=
  branch_upper a [2,4,8,6,3] 30 (by decide) (fin9_cases _
  node403
  node404
  (invalid_upper a [2,4,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,6] 30 (by decide +kernel))
  node405
  (invalid_upper a [2,4,8,6,3,8] 30 (by decide +kernel)))

def cert407 : Local := ⟨⟨0,489,241,0,329,0,313,121,233⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(1,6,3),(1,6,5)]⟩
theorem node407 : UpperPrefix a [2,4,8,6,7,0,1] 30 :=
  local_sound a [2,4,8,6,7,0,1] 30 cert407 (by decide +kernel)

def cert408 : Leaf := ⟨⟨0,481,243,0,323,0,307,115,227⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,22,268,73,176,97,200,418,306⟩,⟨7,22,268,73,176,97,200,384,272⟩,[⟨3,1418297519188633292115463,⟨407,407,439,499,432,499,496,384,272⟩⟩]⟩
theorem node408 : UpperPrefix a [2,4,8,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,0,3] 30 cert408 (by decide +kernel)

def cert409 : Local := ⟨⟨0,489,243,0,0,0,0,123,235⟩,[(0,1),(3,5),(4,6),(5,3),(6,4)],[(2,0,0)]⟩
theorem node409 : UpperPrefix a [2,4,8,6,7,0,5] 30 :=
  local_sound a [2,4,8,6,7,0,5] 30 cert409 (by decide +kernel)

theorem node410 : UpperPrefix a [2,4,8,6,7,0] 30 :=
  branch_upper a [2,4,8,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,7,0,0] 30 (by decide +kernel))
  node407
  (invalid_upper a [2,4,8,6,7,0,2] 30 (by decide +kernel))
  node408
  (invalid_upper a [2,4,8,6,7,0,4] 30 (by decide +kernel))
  node409
  (invalid_upper a [2,4,8,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,8] 30 (by decide +kernel)))

def cert411 : Leaf := ⟨⟨0,488,240,0,328,408,314,120,232⟩,[(0,1),(3,6)],[(2,0,0),(0,6,3)],⟨7,22,268,73,176,98,193,424,312⟩,⟨7,22,268,73,176,98,193,384,272⟩,[⟨1,1361518440643067307360257,⟨5,20,268,73,436,508,201,384,272⟩⟩]⟩
theorem node411 : UpperPrefix a [2,4,8,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,0] 30 cert411 (by decide +kernel)

def cert412 : Leaf := ⟨⟨0,321,83,258,323,385,259,115,99⟩,[(0,1)],[(2,0,0)],⟨7,22,268,73,176,98,200,417,305⟩,⟨7,22,268,73,176,98,200,384,272⟩,[⟨3,1418297519188633292115463,⟨407,407,439,499,432,499,496,384,272⟩⟩,⟨5,1210110158231404085912983,⟨15,95,271,73,223,75,205,463,351⟩⟩,⟨7,1284484837389052897535255,⟨7,279,271,73,319,107,72,259,279⟩⟩,⟨4,1210107853583501633782787,⟨47,111,268,73,232,107,200,384,320⟩⟩]⟩
theorem node412 : UpperPrefix a [2,4,8,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,3] 30 cert412 (by decide +kernel)

def cert413 : Leaf := ⟨⟨0,457,211,402,0,409,0,91,203⟩,[(0,1),(4,6),(6,4)],[(2,0,0)],⟨7,22,268,73,176,98,224,393,281⟩,⟨7,22,268,73,176,98,224,384,272⟩,[⟨5,1285849895324607497512215,⟨135,407,399,73,415,75,200,387,407⟩⟩]⟩
theorem node413 : UpperPrefix a [2,4,8,6,7,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,5] 30 cert413 (by decide +kernel)

theorem node414 : UpperPrefix a [2,4,8,6,7,1] 30 :=
  branch_upper a [2,4,8,6,7,1] 30 (by decide) (fin9_cases _
  node411
  (invalid_upper a [2,4,8,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,2] 30 (by decide +kernel))
  node412
  (invalid_upper a [2,4,8,6,7,1,4] 30 (by decide +kernel))
  node413
  (invalid_upper a [2,4,8,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,8] 30 (by decide +kernel)))

def cert415 : Local := ⟨⟨0,424,178,0,266,0,314,58,170⟩,[(0,1),(3,6),(5,3)],[(2,0,0),(6,3,5),(0,6,3),(0,6,5)]⟩
theorem node415 : UpperPrefix a [2,4,8,6,7,3,0] 30 :=
  local_sound a [2,4,8,6,7,3,0] 30 cert415 (by decide +kernel)

def cert416 : Local := ⟨⟨0,425,177,434,265,0,313,57,169⟩,[(0,1),(5,3)],[(2,0,0),(6,3,5),(1,6,3)]⟩
theorem node416 : UpperPrefix a [2,4,8,6,7,3,1] 30 :=
  local_sound a [2,4,8,6,7,3,1] 30 cert416 (by decide +kernel)

def cert417 : Local := ⟨⟨0,425,179,434,0,0,0,59,171⟩,[(0,1),(4,6),(5,3),(6,4)],[(2,0,0),(6,3,5)]⟩
theorem node417 : UpperPrefix a [2,4,8,6,7,3,5] 30 :=
  local_sound a [2,4,8,6,7,3,5] 30 cert417 (by decide +kernel)

theorem node418 : UpperPrefix a [2,4,8,6,7,3] 30 :=
  branch_upper a [2,4,8,6,7,3] 30 (by decide) (fin9_cases _
  node415
  node416
  (invalid_upper a [2,4,8,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,4] 30 (by decide +kernel))
  node417
  (invalid_upper a [2,4,8,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,8] 30 (by decide +kernel)))

theorem node419 : UpperPrefix a [2,4,8,6,7] 30 :=
  branch_upper a [2,4,8,6,7] 30 (by decide) (fin9_cases _
  node410
  node414
  (invalid_upper a [2,4,8,6,7,2] 30 (by decide +kernel))
  node418
  (invalid_upper a [2,4,8,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,8] 30 (by decide +kernel)))

theorem node420 : UpperPrefix a [2,4,8,6] 30 :=
  branch_upper a [2,4,8,6] 30 (by decide) (fin9_cases _
  node395
  node402
  (invalid_upper a [2,4,8,6,2] 30 (by decide +kernel))
  node406
  (invalid_upper a [2,4,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,6] 30 (by decide +kernel))
  node419
  (invalid_upper a [2,4,8,6,8] 30 (by decide +kernel)))

def cert421 : Local := ⟨⟨0,361,113,368,330,281,0,121,105⟩,[(0,1),(6,3)],[(2,0,0),(7,3,6),(1,5,4)]⟩
theorem node421 : UpperPrefix a [2,4,8,7,0,1,3] 30 :=
  local_sound a [2,4,8,7,0,1,3] 30 cert421 (by decide +kernel)

def cert422 : Leaf := ⟨⟨0,225,241,352,194,129,1,105,233⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,22,268,137,49,98,224,456,344⟩,⟨7,22,268,137,49,98,224,384,272⟩,[⟨3,1210107709824480968707591,⟨55,55,375,243,51,115,240,384,272⟩⟩,⟨4,1210144657034836716815363,⟨239,239,460,233,105,107,224,384,256⟩⟩,⟨8,1181890209852867743239,⟨55,55,127,251,51,115,240,128,16⟩⟩]⟩
theorem node422 : UpperPrefix a [2,4,8,7,0,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,1,5] 30 cert422 (by decide +kernel)

theorem node423 : UpperPrefix a [2,4,8,7,0,1] 30 :=
  branch_upper a [2,4,8,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,1,2] 30 (by decide +kernel))
  node421
  (invalid_upper a [2,4,8,7,0,1,4] 30 (by decide +kernel))
  node422
  (invalid_upper a [2,4,8,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,1,8] 30 (by decide +kernel)))

def cert424 : Leaf := ⟨⟨0,105,115,114,74,146,56,90,106⟩,[(0,1)],[(2,0,0),(7,3,5)],⟨7,22,268,137,49,104,194,416,336⟩,⟨7,22,268,137,49,104,194,416,272⟩,[⟨8,1181892463860294618631,⟨55,55,127,251,51,120,251,160,16⟩⟩,⟨0,1295294683740912900637696,⟨454,470,428,232,496,104,450,416,400⟩⟩]⟩
theorem node424 : UpperPrefix a [2,4,8,7,0,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,3,1,5] 30 cert424 (by decide +kernel)

def cert425 : Leaf := ⟨⟨0,265,19,274,266,403,281,27,43⟩,[(0,1)],[(2,0,0),(7,3,5)],⟨7,22,268,137,49,104,194,448,304⟩,⟨7,22,268,137,49,104,194,448,272⟩,[⟨5,1212512684517412398302663,⟨207,223,463,205,89,73,207,463,479⟩⟩,⟨6,1436780003542314884555891,⟨7,279,268,141,311,319,143,397,275⟩⟩]⟩
theorem node425 : UpperPrefix a [2,4,8,7,0,3,1,6] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,3,1,6] 30 cert425 (by decide +kernel)

theorem node426 : UpperPrefix a [2,4,8,7,0,3,1] 30 :=
  branch_upper a [2,4,8,7,0,3,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,0,3,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,1,4] 30 (by decide +kernel))
  node424
  node425
  (invalid_upper a [2,4,8,7,0,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,1,8] 30 (by decide +kernel)))

def cert427 : Leaf := ⟨⟨0,105,115,370,72,144,24,122,106⟩,[(0,1)],[(2,0,0),(7,3,5)],⟨7,22,268,137,49,104,224,450,338⟩,⟨7,22,268,137,49,104,224,384,272⟩,[⟨0,1219580455176673761952768,⟨486,502,364,232,240,104,224,384,336⟩⟩,⟨8,1181890207653844487687,⟨55,55,127,251,51,120,224,128,16⟩⟩,⟨1,1210107709821870702329857,⟨53,52,380,249,49,120,224,384,272⟩⟩]⟩
theorem node427 : UpperPrefix a [2,4,8,7,0,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,3,5] 30 cert427 (by decide +kernel)

theorem node428 : UpperPrefix a [2,4,8,7,0,3] 30 :=
  branch_upper a [2,4,8,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,0,3,0] 30 (by decide +kernel))
  node426
  (invalid_upper a [2,4,8,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,4] 30 (by decide +kernel))
  node427
  (invalid_upper a [2,4,8,7,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,8] 30 (by decide +kernel)))

theorem node429 : UpperPrefix a [2,4,8,7,0] 30 :=
  branch_upper a [2,4,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,0,0] 30 (by decide +kernel))
  node423
  (invalid_upper a [2,4,8,7,0,2] 30 (by decide +kernel))
  node428
  (invalid_upper a [2,4,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,8] 30 (by decide +kernel)))

def cert430 : Leaf := ⟨⟨0,361,115,352,329,264,0,105,107⟩,[(0,1),(6,3)],[(2,0,0),(7,3,6)],⟨7,22,268,137,50,97,200,480,368⟩,⟨7,22,268,137,50,97,200,384,272⟩,[⟨1,1210144693275839211503617,⟨237,212,492,233,48,105,232,384,272⟩⟩,⟨4,1210144729936855684875267,⟨239,239,492,233,107,105,232,384,288⟩⟩]⟩
theorem node430 : UpperPrefix a [2,4,8,7,1,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,0,3] 30 cert430 (by decide +kernel)

def cert431 : Leaf := ⟨⟨0,225,243,352,193,128,1,105,235⟩,[(0,1)],[(2,0,0)],⟨7,22,268,137,50,97,224,456,344⟩,⟨7,22,268,137,50,97,224,384,272⟩,[⟨1,1210144693275839211503617,⟨237,212,492,233,48,105,224,384,272⟩⟩,⟨3,1210107709824480968707591,⟨55,55,375,243,51,115,240,384,272⟩⟩,⟨4,1210144729936855684875267,⟨239,239,492,233,107,105,224,384,288⟩⟩,⟨8,1181890209852867743239,⟨55,55,127,251,51,115,240,128,16⟩⟩]⟩
theorem node431 : UpperPrefix a [2,4,8,7,1,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,0,5] 30 cert431 (by decide +kernel)

theorem node432 : UpperPrefix a [2,4,8,7,1,0] 30 :=
  branch_upper a [2,4,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,0,2] 30 (by decide +kernel))
  node430
  (invalid_upper a [2,4,8,7,1,0,4] 30 (by decide +kernel))
  node431
  (invalid_upper a [2,4,8,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,0,8] 30 (by decide +kernel)))

def cert433 : Leaf := ⟨⟨0,105,115,370,73,129,33,115,99⟩,[(0,1)],[(2,0,0),(7,3,5)],⟨7,22,268,137,50,104,225,481,369⟩,⟨7,22,268,137,50,104,192,384,272⟩,[⟨8,1181890207653844487687,⟨55,55,127,251,51,120,192,128,16⟩⟩,⟨3,1285813291192730763920387,⟨7,471,260,129,499,96,192,384,464⟩⟩,⟨1,1210107709821252227039233,⟨37,52,364,233,48,104,192,384,272⟩⟩,⟨4,1210107709820152715412483,⟨39,39,364,233,35,104,192,384,256⟩⟩]⟩
theorem node433 : UpperPrefix a [2,4,8,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,3] 30 cert433 (by decide +kernel)

theorem node434 : UpperPrefix a [2,4,8,7,1] 30 :=
  branch_upper a [2,4,8,7,1] 30 (by decide) (fin9_cases _
  node432
  (invalid_upper a [2,4,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,2] 30 (by decide +kernel))
  node433
  (invalid_upper a [2,4,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,8] 30 (by decide +kernel)))

def cert435 : Local := ⟨⟨0,488,240,368,449,402,304,112,224⟩,[(0,1)],[(2,0,0),(3,4,1),(0,5,4),(1,6,5)]⟩
theorem node435 : UpperPrefix a [2,4,8,7,3,0,1] 30 :=
  local_sound a [2,4,8,7,3,0,1] 30 cert435 (by decide +kernel)

def cert436 : Leaf := ⟨⟨0,232,242,370,193,144,16,114,226⟩,[(0,1)],[(2,0,0),(3,4,1),(0,5,4)],⟨7,22,268,137,56,97,224,450,338⟩,⟨7,22,268,137,56,97,224,384,272⟩,[⟨8,1181890207447686057479,⟨55,55,127,251,120,99,224,128,16⟩⟩,⟨1,1210107709681339372404737,⟨21,20,380,249,120,97,224,384,272⟩⟩]⟩
theorem node436 : UpperPrefix a [2,4,8,7,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,0,5] 30 cert436 (by decide +kernel)

theorem node437 : UpperPrefix a [2,4,8,7,3,0] 30 :=
  branch_upper a [2,4,8,7,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,3,0,0] 30 (by decide +kernel))
  node435
  (invalid_upper a [2,4,8,7,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,4] 30 (by decide +kernel))
  node436
  (invalid_upper a [2,4,8,7,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,8] 30 (by decide +kernel)))

def cert438 : Leaf := ⟨⟨0,489,241,0,449,401,0,113,225⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(3,4,1)],⟨7,22,268,137,56,98,193,480,368⟩,⟨7,22,268,137,56,98,193,384,272⟩,[⟨1,1437224022436759387242497,⟨5,404,332,201,508,508,201,384,404⟩⟩]⟩
theorem node438 : UpperPrefix a [2,4,8,7,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,1,0] 30 cert438 (by decide +kernel)

def cert439 : Local := ⟨⟨0,488,242,0,450,400,274,114,226⟩,[(0,1),(3,7)],[(2,0,0),(3,4,1),(0,7,3)]⟩
theorem node439 : UpperPrefix a [2,4,8,7,3,1,5,0] 30 :=
  local_sound a [2,4,8,7,3,1,5,0] 30 cert439 (by decide +kernel)

def cert440 : Leaf := ⟨⟨0,424,179,306,386,400,274,50,163⟩,[(0,1)],[(2,0,0),(3,4,1),(6,7,6)],⟨7,22,268,137,56,98,224,448,273⟩,⟨7,22,268,137,56,98,224,448,272⟩,[⟨0,1210144729516566962507264,⟨246,246,510,250,120,98,224,448,272⟩⟩]⟩
theorem node440 : UpperPrefix a [2,4,8,7,3,1,5,6] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,1,5,6] 30 cert440 (by decide +kernel)

theorem node441 : UpperPrefix a [2,4,8,7,3,1,5] 30 :=
  branch_upper a [2,4,8,7,3,1,5] 30 (by decide) (fin9_cases _
  node439
  (invalid_upper a [2,4,8,7,3,1,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,5] 30 (by decide +kernel))
  node440
  (invalid_upper a [2,4,8,7,3,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,8] 30 (by decide +kernel)))

theorem node442 : UpperPrefix a [2,4,8,7,3,1] 30 :=
  branch_upper a [2,4,8,7,3,1] 30 (by decide) (fin9_cases _
  node438
  (invalid_upper a [2,4,8,7,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,4] 30 (by decide +kernel))
  node441
  (invalid_upper a [2,4,8,7,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,8] 30 (by decide +kernel)))

theorem node443 : UpperPrefix a [2,4,8,7,3] 30 :=
  branch_upper a [2,4,8,7,3] 30 (by decide) (fin9_cases _
  node437
  node442
  (invalid_upper a [2,4,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,8] 30 (by decide +kernel)))

def cert444 : Local := ⟨⟨0,425,177,304,0,410,313,57,169⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(1,6,5)]⟩
theorem node444 : UpperPrefix a [2,4,8,7,6,0,1] 30 :=
  local_sound a [2,4,8,7,6,0,1] 30 cert444 (by decide +kernel)

def cert445 : Local := ⟨⟨0,297,51,306,0,282,0,59,43⟩,[(0,1),(4,5),(6,3)],[(2,0,0),(7,3,6),(6,4,4)]⟩
theorem node445 : UpperPrefix a [2,4,8,7,6,0,3] 30 :=
  local_sound a [2,4,8,7,6,0,3] 30 cert445 (by decide +kernel)

def cert446 : Local := ⟨⟨0,393,147,274,0,410,283,27,139⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(5,6,4)]⟩
theorem node446 : UpperPrefix a [2,4,8,7,6,0,5] 30 :=
  local_sound a [2,4,8,7,6,0,5] 30 cert446 (by decide +kernel)

theorem node447 : UpperPrefix a [2,4,8,7,6,0] 30 :=
  branch_upper a [2,4,8,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,6,0,0] 30 (by decide +kernel))
  node444
  (invalid_upper a [2,4,8,7,6,0,2] 30 (by decide +kernel))
  node445
  (invalid_upper a [2,4,8,7,6,0,4] 30 (by decide +kernel))
  node446
  (invalid_upper a [2,4,8,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,0,8] 30 (by decide +kernel)))

#print axioms node447
end Delivery.FiniteExclusion.Sharp4x5
