import RegularNineSharp4x5Base
import RegularNineSharp4x5C001
import RegularNineSharp4x5C004
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert320 : Leaf := ⟨⟨0,137,19,146,195,147,275,19,131⟩,[(0,1)],[(2,0,0),(6,3,4),(3,4,1),(8,5,6)],⟨7,22,140,73,56,352,224,387,275⟩,⟨7,22,140,73,56,352,224,384,272⟩,[⟨5,1297941736064932725794099,⟨391,407,140,205,415,463,205,387,407⟩⟩]⟩
theorem node320 : UpperPrefix a [2,4,7,6,3,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,8,5] 30 cert320 (by decide +kernel)

theorem node321 : UpperPrefix a [2,4,7,6,3,8] 30 :=
  branch_upper a [2,4,7,6,3,8] 30 (by decide) (fin9_cases _
  node318
  node319
  (invalid_upper a [2,4,7,6,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,4] 30 (by decide +kernel))
  node320
  (invalid_upper a [2,4,7,6,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,8] 30 (by decide +kernel)))

theorem node322 : UpperPrefix a [2,4,7,6,3] 30 :=
  branch_upper a [2,4,7,6,3] 30 (by decide) (fin9_cases _
  node316
  node317
  (invalid_upper a [2,4,7,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,7] 30 (by decide +kernel))
  node321)

def cert323 : Local := ⟨⟨0,489,369,0,201,0,313,121,233⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(1,6,3),(1,6,5)]⟩
theorem node323 : UpperPrefix a [2,4,7,6,8,0,1] 30 :=
  local_sound a [2,4,7,6,8,0,1] 30 cert323 (by decide +kernel)

def cert324 : Local := ⟨⟨0,489,0,0,203,0,0,123,235⟩,[(0,1),(2,6),(3,5),(5,3),(6,2)],[(2,0,0)]⟩
theorem node324 : UpperPrefix a [2,4,7,6,8,0,3] 30 :=
  local_sound a [2,4,7,6,8,0,3] 30 cert324 (by decide +kernel)

def cert325 : Leaf := ⟨⟨0,457,339,0,203,0,283,91,203⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,22,140,73,304,97,224,394,282⟩,⟨7,22,140,73,304,97,224,384,272⟩,[⟨5,1285813001836460095186195,⟨7,407,140,77,415,77,204,387,407⟩⟩]⟩
theorem node325 : UpperPrefix a [2,4,7,6,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,5] 30 cert325 (by decide +kernel)

theorem node326 : UpperPrefix a [2,4,7,6,8,0] 30 :=
  branch_upper a [2,4,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,8,0,0] 30 (by decide +kernel))
  node323
  (invalid_upper a [2,4,7,6,8,0,2] 30 (by decide +kernel))
  node324
  (invalid_upper a [2,4,7,6,8,0,4] 30 (by decide +kernel))
  node325
  (invalid_upper a [2,4,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,8] 30 (by decide +kernel)))

def cert327 : Leaf := ⟨⟨0,488,368,0,200,408,314,120,232⟩,[(0,1),(3,6)],[(2,0,0),(0,6,3)],⟨7,22,140,73,304,98,193,424,312⟩,⟨7,22,140,73,304,98,193,384,272⟩,[⟨1,1361518440643067324137473,⟨5,20,140,77,436,508,205,384,272⟩⟩]⟩
theorem node327 : UpperPrefix a [2,4,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,0] 30 cert327 (by decide +kernel)

def cert328 : Leaf := ⟨⟨0,481,0,434,195,401,0,115,227⟩,[(0,1),(2,6),(6,2)],[(2,0,0)],⟨7,22,140,73,304,98,200,417,305⟩,⟨7,22,140,73,304,98,200,384,272⟩,[⟨3,1418297519188633292115463,⟨407,407,439,499,432,499,496,384,272⟩⟩]⟩
theorem node328 : UpperPrefix a [2,4,7,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,3] 30 cert328 (by decide +kernel)

def cert329 : Leaf := ⟨⟨0,329,323,258,75,265,267,75,75⟩,[(0,1)],[(2,0,0)],⟨7,22,140,73,304,98,224,393,281⟩,⟨7,22,140,73,304,98,224,384,272⟩,[⟨4,1210255463600083661489187,⟨111,239,140,109,493,111,237,388,460⟩⟩,⟨5,1285813001836468685120819,⟨7,407,140,77,415,79,205,387,407⟩⟩,⟨7,1416711099198299639385607,⟨279,279,319,379,312,379,376,256,272⟩⟩]⟩
theorem node329 : UpperPrefix a [2,4,7,6,8,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,5] 30 cert329 (by decide +kernel)

theorem node330 : UpperPrefix a [2,4,7,6,8,1] 30 :=
  branch_upper a [2,4,7,6,8,1] 30 (by decide) (fin9_cases _
  node327
  (invalid_upper a [2,4,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,2] 30 (by decide +kernel))
  node328
  (invalid_upper a [2,4,7,6,8,1,4] 30 (by decide +kernel))
  node329
  (invalid_upper a [2,4,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,8] 30 (by decide +kernel)))

def cert331 : Local := ⟨⟨0,424,306,0,138,0,314,58,170⟩,[(0,1),(3,6),(5,3)],[(2,0,0),(6,3,5),(0,6,3),(0,6,5)]⟩
theorem node331 : UpperPrefix a [2,4,7,6,8,3,0] 30 :=
  local_sound a [2,4,7,6,8,3,0] 30 cert331 (by decide +kernel)

def cert332 : Local := ⟨⟨0,425,305,434,137,0,313,57,169⟩,[(0,1),(5,3)],[(2,0,0),(6,3,5),(1,6,3)]⟩
theorem node332 : UpperPrefix a [2,4,7,6,8,3,1] 30 :=
  local_sound a [2,4,7,6,8,3,1] 30 cert332 (by decide +kernel)

def cert333 : Leaf := ⟨⟨0,297,275,434,11,0,283,27,11⟩,[(0,1),(5,3)],[(2,0,0),(6,3,5)],⟨7,22,140,73,304,104,224,387,275⟩,⟨7,22,140,73,304,104,224,384,272⟩,[⟨5,1219579967239801636127747,⟨391,407,140,205,272,76,192,384,272⟩⟩,⟨7,1279762471190677586710023,⟨279,279,319,379,304,376,112,256,272⟩⟩]⟩
theorem node333 : UpperPrefix a [2,4,7,6,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,5] 30 cert333 (by decide +kernel)

theorem node334 : UpperPrefix a [2,4,7,6,8,3] 30 :=
  branch_upper a [2,4,7,6,8,3] 30 (by decide) (fin9_cases _
  node331
  node332
  (invalid_upper a [2,4,7,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,4] 30 (by decide +kernel))
  node333
  (invalid_upper a [2,4,7,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,8] 30 (by decide +kernel)))

theorem node335 : UpperPrefix a [2,4,7,6,8] 30 :=
  branch_upper a [2,4,7,6,8] 30 (by decide) (fin9_cases _
  node326
  node330
  (invalid_upper a [2,4,7,6,8,2] 30 (by decide +kernel))
  node334
  (invalid_upper a [2,4,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,8] 30 (by decide +kernel)))

theorem node336 : UpperPrefix a [2,4,7,6] 30 :=
  branch_upper a [2,4,7,6] 30 (by decide) (fin9_cases _
  node308
  node315
  (invalid_upper a [2,4,7,6,2] 30 (by decide +kernel))
  node322
  (invalid_upper a [2,4,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,7] 30 (by decide +kernel))
  node335)

def cert337 : Local := ⟨⟨0,233,0,240,202,153,0,121,233⟩,[(0,1),(2,6),(6,2)],[(2,0,0),(8,3,2),(8,3,6),(1,5,4)]⟩
theorem node337 : UpperPrefix a [2,4,7,8,0,1,3] 30 :=
  local_sound a [2,4,7,8,0,1,3] 30 cert337 (by decide +kernel)

def cert338 : Leaf := ⟨⟨0,225,369,112,66,145,17,121,105⟩,[(0,1)],[(2,0,0),(8,3,2),(1,5,4)],⟨7,22,140,265,49,98,224,456,344⟩,⟨7,22,140,265,49,98,224,384,272⟩,[⟨3,1210107637590965070335495,⟨119,119,247,307,51,115,240,384,272⟩⟩,⟨7,1662274156020825681036291,⟨7,31,12,265,313,379,376,256,280⟩⟩]⟩
theorem node338 : UpperPrefix a [2,4,7,8,0,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,0,1,5] 30 cert338 (by decide +kernel)

theorem node339 : UpperPrefix a [2,4,7,8,0,1] 30 :=
  branch_upper a [2,4,7,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,1,2] 30 (by decide +kernel))
  node337
  (invalid_upper a [2,4,7,8,0,1,4] 30 (by decide +kernel))
  node338
  (invalid_upper a [2,4,7,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,1,8] 30 (by decide +kernel)))

def cert340 : Leaf := ⟨⟨0,232,370,114,74,18,56,122,106⟩,[(0,1)],[(2,0,0),(8,3,2)],⟨7,22,140,265,49,104,194,480,368⟩,⟨7,22,140,265,49,104,194,384,272⟩,[⟨0,1285891726165317109425152,⟨70,470,172,492,502,236,194,448,466⟩⟩,⟨7,1662274158274828812944387,⟨7,31,12,265,313,376,379,256,280⟩⟩]⟩
theorem node340 : UpperPrefix a [2,4,7,8,0,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,8,0,3,1] 30 cert340 (by decide +kernel)

def cert341 : Leaf := ⟨⟨0,233,370,242,200,128,8,122,234⟩,[(0,1)],[(2,0,0),(8,3,2)],⟨7,22,140,265,49,104,224,450,338⟩,⟨7,22,140,265,49,104,224,384,272⟩,[⟨0,1219580527234267801977856,⟨486,502,236,492,240,108,224,384,336⟩⟩,⟨1,1210107637482251931877377,⟨117,116,236,281,49,104,224,384,272⟩⟩,⟨4,1210107637481083700773891,⟨103,103,236,265,33,104,224,384,256⟩⟩]⟩
theorem node341 : UpperPrefix a [2,4,7,8,0,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,0,3,5] 30 cert341 (by decide +kernel)

theorem node342 : UpperPrefix a [2,4,7,8,0,3] 30 :=
  branch_upper a [2,4,7,8,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,0,3,0] 30 (by decide +kernel))
  node340
  (invalid_upper a [2,4,7,8,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,3,4] 30 (by decide +kernel))
  node341
  (invalid_upper a [2,4,7,8,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,3,8] 30 (by decide +kernel)))

theorem node343 : UpperPrefix a [2,4,7,8,0] 30 :=
  branch_upper a [2,4,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,0,0] 30 (by decide +kernel))
  node339
  (invalid_upper a [2,4,7,8,0,2] 30 (by decide +kernel))
  node342
  (invalid_upper a [2,4,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,8] 30 (by decide +kernel)))

def cert344 : Local := ⟨⟨0,233,0,242,201,154,0,123,235⟩,[(0,1),(2,6),(6,2)],[(2,0,0),(8,3,2),(8,3,6)]⟩
theorem node344 : UpperPrefix a [2,4,7,8,1,0,3] 30 :=
  local_sound a [2,4,7,8,1,0,3] 30 cert344 (by decide +kernel)

def cert345 : Leaf := ⟨⟨0,225,353,242,193,128,1,105,235⟩,[(0,1)],[(2,0,0),(8,3,2)],⟨7,22,140,265,50,97,224,456,344⟩,⟨7,22,140,265,50,97,224,384,272⟩,[⟨1,1210181568749587989004289,⟨101,84,236,493,48,97,224,384,272⟩⟩,⟨3,1210107637590965070335495,⟨119,119,247,307,51,115,240,384,272⟩⟩,⟨4,1210181568818857221555203,⟨103,103,236,493,35,97,224,384,256⟩⟩]⟩
theorem node345 : UpperPrefix a [2,4,7,8,1,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,1,0,5] 30 cert345 (by decide +kernel)

theorem node346 : UpperPrefix a [2,4,7,8,1,0] 30 :=
  branch_upper a [2,4,7,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,0,2] 30 (by decide +kernel))
  node344
  (invalid_upper a [2,4,7,8,1,0,4] 30 (by decide +kernel))
  node345
  (invalid_upper a [2,4,7,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,0,8] 30 (by decide +kernel)))

def cert347 : Leaf := ⟨⟨0,233,353,226,201,129,33,97,227⟩,[(0,1)],[(2,0,0),(8,3,2)],⟨7,22,140,265,50,104,225,481,369⟩,⟨7,22,140,265,50,104,192,384,272⟩,[⟨4,1212547305234734156612627,⟨39,39,236,493,39,236,228,492,493⟩⟩,⟨1,1210181496797547075731457,⟨37,52,236,493,52,236,192,384,272⟩⟩,⟨3,1285813291192730763920387,⟨7,471,132,257,499,96,192,384,464⟩⟩]⟩
theorem node347 : UpperPrefix a [2,4,7,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,8,1,3] 30 cert347 (by decide +kernel)

theorem node348 : UpperPrefix a [2,4,7,8,1] 30 :=
  branch_upper a [2,4,7,8,1] 30 (by decide) (fin9_cases _
  node346
  (invalid_upper a [2,4,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,2] 30 (by decide +kernel))
  node347
  (invalid_upper a [2,4,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,8] 30 (by decide +kernel)))

def cert349 : Local := ⟨⟨0,232,368,240,193,146,48,112,224⟩,[(0,1)],[(2,0,0),(8,3,2),(3,4,1),(0,5,4),(1,6,5)]⟩
theorem node349 : UpperPrefix a [2,4,7,8,3,0,1] 30 :=
  local_sound a [2,4,7,8,3,0,1] 30 cert349 (by decide +kernel)

def cert350 : Local := ⟨⟨0,232,354,226,195,130,2,112,226⟩,[(0,1)],[(2,0,0),(4,1,7),(8,3,2),(3,4,1),(0,5,4)]⟩
theorem node350 : UpperPrefix a [2,4,7,8,3,0,5,1] 30 :=
  local_sound a [2,4,7,8,3,0,5,1] 30 cert350 (by decide +kernel)

def cert351 : Local := ⟨⟨0,168,306,178,131,146,18,50,162⟩,[(0,1)],[(2,0,0),(8,3,2),(3,4,1),(0,5,4),(6,7,6)]⟩
theorem node351 : UpperPrefix a [2,4,7,8,3,0,5,6] 30 :=
  local_sound a [2,4,7,8,3,0,5,6] 30 cert351 (by decide +kernel)

theorem node352 : UpperPrefix a [2,4,7,8,3,0,5] 30 :=
  branch_upper a [2,4,7,8,3,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,3,0,5,0] 30 (by decide +kernel))
  node350
  (invalid_upper a [2,4,7,8,3,0,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,5,5] 30 (by decide +kernel))
  node351
  (invalid_upper a [2,4,7,8,3,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,5,8] 30 (by decide +kernel)))

theorem node353 : UpperPrefix a [2,4,7,8,3,0] 30 :=
  branch_upper a [2,4,7,8,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,3,0,0] 30 (by decide +kernel))
  node349
  (invalid_upper a [2,4,7,8,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,4] 30 (by decide +kernel))
  node352
  (invalid_upper a [2,4,7,8,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,8] 30 (by decide +kernel)))

def cert354 : Leaf := ⟨⟨0,41,307,50,3,145,50,83,99⟩,[(0,1)],[(2,0,0),(8,3,2),(3,4,1)],⟨7,22,140,265,56,98,193,416,336⟩,⟨7,22,140,265,56,98,193,416,272⟩,[⟨6,1210106412371160402595047,⟨7,23,159,265,57,39,159,447,272⟩⟩,⟨7,1662274156029628216511495,⟨7,23,31,265,312,379,345,312,272⟩⟩]⟩
theorem node354 : UpperPrefix a [2,4,7,8,3,1,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,1,0,5] 30 cert354 (by decide +kernel)

def cert355 : Leaf := ⟨⟨0,201,339,210,195,145,18,19,227⟩,[(0,1)],[(2,0,0),(8,3,2),(3,4,1)],⟨7,22,140,265,56,98,193,448,304⟩,⟨7,22,140,265,56,98,193,448,272⟩,[⟨5,1212549956307919010145723,⟨71,87,205,463,223,71,205,463,479⟩⟩]⟩
theorem node355 : UpperPrefix a [2,4,7,8,3,1,0,6] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,1,0,6] 30 cert355 (by decide +kernel)

theorem node356 : UpperPrefix a [2,4,7,8,3,1,0] 30 :=
  branch_upper a [2,4,7,8,3,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,3,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,4] 30 (by decide +kernel))
  node354
  node355
  (invalid_upper a [2,4,7,8,3,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,8] 30 (by decide +kernel)))

def cert357 : Leaf := ⟨⟨0,232,371,114,66,144,18,115,99⟩,[(0,1)],[(2,0,0),(8,3,2),(3,4,1)],⟨7,22,140,265,56,98,224,449,337⟩,⟨7,22,140,265,56,98,224,384,272⟩,[⟨0,1210107637588560962391552,⟨118,118,254,314,56,98,224,384,272⟩⟩,⟨7,1360042701121564286387203,⟨7,23,12,265,312,379,376,256,272⟩⟩]⟩
theorem node357 : UpperPrefix a [2,4,7,8,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,1,5] 30 cert357 (by decide +kernel)

theorem node358 : UpperPrefix a [2,4,7,8,3,1] 30 :=
  branch_upper a [2,4,7,8,3,1] 30 (by decide) (fin9_cases _
  node356
  (invalid_upper a [2,4,7,8,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,4] 30 (by decide +kernel))
  node357
  (invalid_upper a [2,4,7,8,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,8] 30 (by decide +kernel)))

theorem node359 : UpperPrefix a [2,4,7,8,3] 30 :=
  branch_upper a [2,4,7,8,3] 30 (by decide) (fin9_cases _
  node353
  node358
  (invalid_upper a [2,4,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,8] 30 (by decide +kernel)))

def cert360 : Local := ⟨⟨0,169,305,176,0,154,57,57,169⟩,[(0,1),(4,5)],[(2,0,0),(8,3,2),(6,4,4),(1,6,5)]⟩
theorem node360 : UpperPrefix a [2,4,7,8,6,0,1] 30 :=
  local_sound a [2,4,7,8,6,0,1] 30 cert360 (by decide +kernel)

def cert361 : Local := ⟨⟨0,169,0,178,0,154,0,59,171⟩,[(0,1),(2,6),(4,5),(6,2)],[(2,0,0),(8,3,2),(8,3,6),(6,4,4)]⟩
theorem node361 : UpperPrefix a [2,4,7,8,6,0,3] 30 :=
  local_sound a [2,4,7,8,6,0,3] 30 cert361 (by decide +kernel)

def cert362 : Local := ⟨⟨0,137,275,146,0,154,27,27,139⟩,[(0,1),(4,5)],[(2,0,0),(8,3,2),(6,4,4),(5,6,4)]⟩
theorem node362 : UpperPrefix a [2,4,7,8,6,0,5] 30 :=
  local_sound a [2,4,7,8,6,0,5] 30 cert362 (by decide +kernel)

theorem node363 : UpperPrefix a [2,4,7,8,6,0] 30 :=
  branch_upper a [2,4,7,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,6,0,0] 30 (by decide +kernel))
  node360
  (invalid_upper a [2,4,7,8,6,0,2] 30 (by decide +kernel))
  node361
  (invalid_upper a [2,4,7,8,6,0,4] 30 (by decide +kernel))
  node362
  (invalid_upper a [2,4,7,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,0,8] 30 (by decide +kernel)))

def cert364 : Leaf := ⟨⟨0,169,307,50,0,153,59,59,43⟩,[(0,1),(4,5)],[(2,0,0),(8,3,2),(6,4,4)],⟨7,22,140,265,112,98,233,425,313⟩,⟨7,22,140,265,112,98,192,384,272⟩,[⟨7,1360042701117166239876099,⟨7,23,12,265,376,379,64,256,272⟩⟩]⟩
theorem node364 : UpperPrefix a [2,4,7,8,6,1] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,1] 30 cert364 (by decide +kernel)

def cert365 : Local := ⟨⟨0,168,306,178,0,147,58,58,170⟩,[(0,1),(4,5)],[(2,0,0),(8,3,2),(6,4,4),(0,6,5)]⟩
theorem node365 : UpperPrefix a [2,4,7,8,6,3,0] 30 :=
  local_sound a [2,4,7,8,6,3,0] 30 cert365 (by decide +kernel)

def cert366 : Leaf := ⟨⟨0,168,307,178,0,146,56,59,171⟩,[(0,1),(4,5)],[(2,0,0),(8,3,2),(6,4,4)],⟨7,22,140,265,112,104,194,417,305⟩,⟨7,22,140,265,112,104,194,384,272⟩,[⟨0,1210107637484863271996928,⟨118,118,254,282,112,120,210,384,272⟩⟩]⟩
theorem node366 : UpperPrefix a [2,4,7,8,6,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,3,1] 30 cert366 (by decide +kernel)

def cert367 : Local := ⟨⟨0,137,275,146,0,147,27,27,139⟩,[(0,1),(4,5)],[(2,0,0),(8,3,2),(6,4,4),(5,6,4)]⟩
theorem node367 : UpperPrefix a [2,4,7,8,6,3,5] 30 :=
  local_sound a [2,4,7,8,6,3,5] 30 cert367 (by decide +kernel)

theorem node368 : UpperPrefix a [2,4,7,8,6,3] 30 :=
  branch_upper a [2,4,7,8,6,3] 30 (by decide) (fin9_cases _
  node365
  node366
  (invalid_upper a [2,4,7,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,4] 30 (by decide +kernel))
  node367
  (invalid_upper a [2,4,7,8,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,8] 30 (by decide +kernel)))

theorem node369 : UpperPrefix a [2,4,7,8,6] 30 :=
  branch_upper a [2,4,7,8,6] 30 (by decide) (fin9_cases _
  node363
  node364
  (invalid_upper a [2,4,7,8,6,2] 30 (by decide +kernel))
  node368
  (invalid_upper a [2,4,7,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,8] 30 (by decide +kernel)))

theorem node370 : UpperPrefix a [2,4,7,8] 30 :=
  branch_upper a [2,4,7,8] 30 (by decide) (fin9_cases _
  node343
  node348
  (invalid_upper a [2,4,7,8,2] 30 (by decide +kernel))
  node359
  (invalid_upper a [2,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,5] 30 (by decide +kernel))
  node369
  (invalid_upper a [2,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,8] 30 (by decide +kernel)))

theorem node371 : UpperPrefix a [2,4,7] 30 :=
  branch_upper a [2,4,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [2,4,7,1] [2,3,4,7] 30 (by decide +kernel) node80)
  (invalid_upper a [2,4,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,4] 30 (by decide +kernel))
  node301
  node336
  (invalid_upper a [2,4,7,7] 30 (by decide +kernel))
  node370)

def cert372 : Leaf := ⟨⟨0,289,49,0,0,411,315,123,235⟩,[(0,1),(3,4),(4,3)],[(2,0,0)],⟨7,22,268,41,49,234,202,458,474⟩,⟨7,22,268,41,49,96,192,384,272⟩,[⟨6,1210106412362899049811335,⟨7,31,287,57,57,32,129,391,287⟩⟩,⟨7,1208926973663686245354887,⟨7,31,287,57,57,96,65,263,287⟩⟩,⟨1,1210107565284403656523777,⟨5,28,284,57,57,96,192,388,284⟩⟩,⟨3,1210107565284400368192519,⟨7,23,279,49,49,96,192,384,272⟩⟩]⟩
theorem node372 : UpperPrefix a [2,4,8,5,0] 30 :=
  Boolean.leaf_sound a [2,4,8,5,0] 30 cert372 (by decide +kernel)

def cert373 : Leaf := ⟨⟨0,488,240,0,456,408,312,120,232⟩,[(0,1),(3,5)],[(2,0,0),(0,5,3)],⟨7,22,268,41,50,97,200,456,472⟩,⟨7,22,268,41,50,97,192,384,272⟩,[⟨1,1285850275069535586353153,⟨237,468,492,105,508,105,192,384,468⟩⟩]⟩
theorem node373 : UpperPrefix a [2,4,8,5,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,5,1,0] 30 cert373 (by decide +kernel)

def cert374 : Leaf := ⟨⟨0,297,35,258,457,275,275,83,195⟩,[(0,1)],[(2,0,0)],⟨7,22,268,41,50,104,193,449,465⟩,⟨7,22,268,41,50,104,192,384,272⟩,[⟨7,1208926975914944893158791,⟨7,31,271,41,59,104,105,263,287⟩⟩,⟨3,1295285892432964222977027,⟨455,471,324,225,499,96,192,384,464⟩⟩,⟨5,1295285891307065389876227,⟨455,471,332,201,467,72,192,384,464⟩⟩,⟨6,1210106412362349293995399,⟨7,31,271,41,59,40,129,391,287⟩⟩,⟨4,1210107565282754389083139,⟨7,15,268,41,43,104,192,388,268⟩⟩]⟩
theorem node374 : UpperPrefix a [2,4,8,5,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,1,3] 30 cert374 (by decide +kernel)

def cert375 : Leaf := ⟨⟨0,297,35,258,329,0,315,123,107⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,22,268,41,50,224,201,457,345⟩,⟨7,22,268,41,50,224,192,384,272⟩,[⟨6,1210106412362353588962695,⟨7,31,271,41,59,169,129,391,287⟩⟩,⟨4,1210107567534554202768387,⟨7,15,268,41,43,224,224,388,268⟩⟩]⟩
theorem node375 : UpperPrefix a [2,4,8,5,1,7] 30 :=
  Boolean.leaf_sound a [2,4,8,5,1,7] 30 cert375 (by decide +kernel)

theorem node376 : UpperPrefix a [2,4,8,5,1] 30 :=
  branch_upper a [2,4,8,5,1] 30 (by decide) (fin9_cases _
  node373
  (invalid_upper a [2,4,8,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,2] 30 (by decide +kernel))
  node374
  (invalid_upper a [2,4,8,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,6] 30 (by decide +kernel))
  node375
  (invalid_upper a [2,4,8,5,1,8] 30 (by decide +kernel)))

def cert377 : Leaf := ⟨⟨0,392,211,466,0,403,275,83,195⟩,[(0,1),(4,3)],[(2,0,0),(5,3,4),(3,4,1)],⟨7,22,268,41,56,227,195,451,467⟩,⟨7,22,268,41,56,96,192,384,272⟩,[⟨0,1210107565284401441934336,⟨6,22,286,56,56,96,192,384,272⟩⟩,⟨6,1210106412362896835087367,⟨7,23,287,57,56,32,128,384,272⟩⟩]⟩
theorem node377 : UpperPrefix a [2,4,8,5,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,3] 30 cert377 (by decide +kernel)

def cert378 : Local := ⟨⟨0,424,178,0,0,410,314,58,170⟩,[(0,1),(3,5),(4,5)],[(2,0,0),(6,4,4),(0,5,3)]⟩
theorem node378 : UpperPrefix a [2,4,8,5,6,0] 30 :=
  local_sound a [2,4,8,5,6,0] 30 cert378 (by decide +kernel)

def cert379 : Leaf := ⟨⟨0,297,49,274,0,281,313,57,169⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(1,5,3)],⟨7,22,268,41,112,98,201,393,409⟩,⟨7,22,268,41,112,98,192,384,272⟩,[⟨7,1208926976484530873075143,⟨15,63,271,57,123,123,127,271,319⟩⟩]⟩
theorem node379 : UpperPrefix a [2,4,8,5,6,1] 30 :=
  Boolean.leaf_sound a [2,4,8,5,6,1] 30 cert379 (by decide +kernel)

def cert380 : Leaf := ⟨⟨0,289,51,274,0,275,307,51,163⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,22,268,41,112,104,195,387,403⟩,⟨7,22,268,41,112,104,192,384,272⟩,[⟨3,1238506453888864812534791,⟨455,471,471,241,112,112,192,384,272⟩⟩,⟨7,1208926976484530873075143,⟨15,63,271,57,123,123,127,271,319⟩⟩]⟩
theorem node380 : UpperPrefix a [2,4,8,5,6,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,6,3] 30 cert380 (by decide +kernel)

def cert381 : Local := ⟨⟨0,297,51,274,0,0,315,59,43⟩,[(0,1),(4,5),(5,6)],[(2,0,0),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node381 : UpperPrefix a [2,4,8,5,6,7] 30 :=
  local_sound a [2,4,8,5,6,7] 30 cert381 (by decide +kernel)

theorem node382 : UpperPrefix a [2,4,8,5,6] 30 :=
  branch_upper a [2,4,8,5,6] 30 (by decide) (fin9_cases _
  node378
  node379
  (invalid_upper a [2,4,8,5,6,2] 30 (by decide +kernel))
  node380
  (invalid_upper a [2,4,8,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,6,6] 30 (by decide +kernel))
  node381
  (invalid_upper a [2,4,8,5,6,8] 30 (by decide +kernel)))

def cert383 : Leaf := ⟨⟨0,296,50,0,330,282,314,122,234⟩,[(0,1),(3,5)],[(2,0,0),(0,5,3)],⟨7,22,268,41,176,97,202,458,346⟩,⟨7,22,268,41,176,97,192,384,272⟩,[⟨7,1208926975914949188126087,⟨7,31,271,41,57,105,105,263,287⟩⟩,⟨6,1210106412362353588962695,⟨7,31,271,41,185,41,129,391,287⟩⟩]⟩
theorem node383 : UpperPrefix a [2,4,8,5,7,0] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,0] 30 cert383 (by decide +kernel)

#print axioms node383
end Delivery.FiniteExclusion.Sharp4x5
