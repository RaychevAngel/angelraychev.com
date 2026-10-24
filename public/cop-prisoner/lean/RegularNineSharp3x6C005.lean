import RegularNineSharp3x6Base
import RegularNineSharp3x6C003
import RegularNineSharp3x6C004
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert320 : Leaf := ⟨⟨0,497,376,96,322,401,304,120,112⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,14,133,280,49,98,240,496,376⟩,⟨7,14,133,280,49,98,192,384,264⟩,[⟨0,1285813291192733985145856,⟨6,14,132,472,504,98,192,384,264⟩⟩,⟨3,1210107637449677826163715,⟨119,119,245,272,49,115,192,384,256⟩⟩,⟨7,1360042701117168387359747,⟨7,15,5,280,313,379,64,256,264⟩⟩]⟩
theorem node320 : UpperPrefix a [2,3,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,7,8,0,1] 30 cert320 (by decide +kernel)

def cert321 : Leaf := ⟨⟨0,497,368,96,322,259,313,120,112⟩,[(0,1)],[(2,0,0)],⟨7,14,133,280,49,112,194,480,360⟩,⟨7,14,133,280,49,112,194,384,264⟩,[⟨1,1361518440640866132426753,⟨5,12,133,284,445,508,192,384,264⟩⟩,⟨7,1662274158274833107911683,⟨7,15,5,280,313,376,379,256,264⟩⟩,⟨0,1361518440640866128233472,⟨6,14,132,280,440,504,194,384,264⟩⟩,⟨3,1210107567542247512605763,⟨7,7,133,272,49,117,247,384,256⟩⟩]⟩
theorem node321 : UpperPrefix a [2,3,7,8,0,4,1] 30 :=
  Boolean.leaf_sound a [2,3,7,8,0,4,1] 30 cert321 (by decide +kernel)

def cert322 : Leaf := ⟨⟨0,465,346,195,448,384,272,90,210⟩,[(0,1)],[(2,0,0),(5,6,5)],⟨7,14,133,280,49,112,224,450,330⟩,⟨7,14,133,280,49,112,224,384,264⟩,[⟨0,1219580293469299641680896,⟨454,494,132,376,240,112,224,384,296⟩⟩,⟨1,1210107637588079926050817,⟨117,124,245,280,49,112,224,384,264⟩⟩,⟨3,1210107637588216291263491,⟨119,119,245,272,49,112,224,384,256⟩⟩]⟩
theorem node322 : UpperPrefix a [2,3,7,8,0,4,5] 30 :=
  Boolean.leaf_sound a [2,3,7,8,0,4,5] 30 cert322 (by decide +kernel)

theorem node323 : UpperPrefix a [2,3,7,8,0,4] 30 :=
  branch_upper a [2,3,7,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,8,0,4,0] 30 (by decide +kernel))
  node321
  (invalid_upper a [2,3,7,8,0,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,0,4,4] 30 (by decide +kernel))
  node322
  (invalid_upper a [2,3,7,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,0,4,8] 30 (by decide +kernel)))

theorem node324 : UpperPrefix a [2,3,7,8,0] 30 :=
  branch_upper a [2,3,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,8,0,0] 30 (by decide +kernel))
  node320
  (invalid_upper a [2,3,7,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,0,3] 30 (by decide +kernel))
  node323
  (invalid_upper a [2,3,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,0,8] 30 (by decide +kernel)))

def cert325 : Leaf := ⟨⟨0,497,370,224,193,146,48,112,240⟩,[(0,1)],[(2,0,0)],⟨7,14,133,280,50,97,240,496,376⟩,⟨7,14,133,280,50,97,192,384,264⟩,[⟨3,1210181605552646279136275,⟨119,247,245,501,119,113,192,384,484⟩⟩,⟨0,1285813291192733985145856,⟨6,14,132,472,506,96,192,384,264⟩⟩,⟨1,1285813291192733985144833,⟨5,12,133,472,504,97,192,384,264⟩⟩,⟨8,1181817973313312392195,⟨119,127,245,24,51,113,192,128,8⟩⟩]⟩
theorem node325 : UpperPrefix a [2,3,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,7,8,1,0] 30 cert325 (by decide +kernel)

def cert326 : Leaf := ⟨⟨0,497,0,226,457,395,0,122,242⟩,[(0,1),(2,6),(6,2)],[(2,0,0)],⟨7,14,133,280,50,112,193,480,360⟩,⟨7,14,133,280,50,112,193,384,264⟩,[⟨0,1361518440640866128233472,⟨6,14,132,280,442,504,192,384,264⟩⟩]⟩
theorem node326 : UpperPrefix a [2,3,7,8,1,4,0] 30 :=
  Boolean.leaf_sound a [2,3,7,8,1,4,0] 30 cert326 (by decide +kernel)

def cert327 : Leaf := ⟨⟨0,465,338,195,192,130,18,83,211⟩,[(0,1)],[(2,0,0),(5,6,5)],⟨7,14,133,280,50,112,224,449,329⟩,⟨7,14,133,280,50,112,224,384,264⟩,[⟨3,1210186217238664706524179,⟨119,247,245,501,119,113,224,448,484⟩⟩,⟨0,1210107637587942487098368,⟨118,126,244,280,50,112,224,384,264⟩⟩,⟨8,1181817973313312392195,⟨119,127,245,24,51,112,224,128,8⟩⟩]⟩
theorem node327 : UpperPrefix a [2,3,7,8,1,4,5] 30 :=
  Boolean.leaf_sound a [2,3,7,8,1,4,5] 30 cert327 (by decide +kernel)

theorem node328 : UpperPrefix a [2,3,7,8,1,4] 30 :=
  branch_upper a [2,3,7,8,1,4] 30 (by decide) (fin9_cases _
  node326
  (invalid_upper a [2,3,7,8,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,4,4] 30 (by decide +kernel))
  node327
  (invalid_upper a [2,3,7,8,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,4,8] 30 (by decide +kernel)))

theorem node329 : UpperPrefix a [2,3,7,8,1] 30 :=
  branch_upper a [2,3,7,8,1] 30 (by decide) (fin9_cases _
  node325
  (invalid_upper a [2,3,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,3] 30 (by decide +kernel))
  node328
  (invalid_upper a [2,3,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,1,8] 30 (by decide +kernel)))

def cert330 : Local := ⟨⟨0,433,312,161,0,410,313,57,177⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(1,6,5)]⟩
theorem node330 : UpperPrefix a [2,3,7,8,6,0,1] 30 :=
  local_sound a [2,3,7,8,6,0,1] 30 cert330 (by decide +kernel)

def cert331 : Leaf := ⟨⟨0,433,314,163,0,400,289,59,179⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,133,280,112,97,208,418,298⟩,⟨7,14,133,280,112,97,208,384,264⟩,[⟨1,1210107637520047644082177,⟨117,124,245,280,112,113,208,384,264⟩⟩,⟨3,1210107637590415314519043,⟨119,119,245,272,112,113,208,384,256⟩⟩]⟩
theorem node331 : UpperPrefix a [2,3,7,8,6,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,8,6,0,4] 30 cert331 (by decide +kernel)

def cert332 : Local := ⟨⟨0,401,282,131,0,410,283,27,147⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(5,6,4)]⟩
theorem node332 : UpperPrefix a [2,3,7,8,6,0,5] 30 :=
  local_sound a [2,3,7,8,6,0,5] 30 cert332 (by decide +kernel)

theorem node333 : UpperPrefix a [2,3,7,8,6,0] 30 :=
  branch_upper a [2,3,7,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,8,6,0,0] 30 (by decide +kernel))
  node330
  (invalid_upper a [2,3,7,8,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,6,0,3] 30 (by decide +kernel))
  node331
  node332
  (invalid_upper a [2,3,7,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,6,0,8] 30 (by decide +kernel)))

def cert334 : Leaf := ⟨⟨0,433,314,35,0,145,51,59,51⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,133,280,112,98,241,433,313⟩,⟨7,14,133,280,112,98,192,384,264⟩,[⟨3,1210107637449677826163715,⟨119,119,245,272,112,115,192,384,256⟩⟩,⟨7,1360042701117168387359747,⟨7,15,5,280,376,379,64,256,264⟩⟩,⟨8,1181817835049725199363,⟨119,127,245,24,112,115,192,128,8⟩⟩]⟩
theorem node334 : UpperPrefix a [2,3,7,8,6,1] 30 :=
  Boolean.leaf_sound a [2,3,7,8,6,1] 30 cert334 (by decide +kernel)

def cert335 : Local := ⟨⟨0,433,314,163,0,0,315,59,179⟩,[(0,1),(4,5),(5,4)],[(2,0,0),(6,4,4),(6,4,5)]⟩
theorem node335 : UpperPrefix a [2,3,7,8,6,4] 30 :=
  local_sound a [2,3,7,8,6,4] 30 cert335 (by decide +kernel)

theorem node336 : UpperPrefix a [2,3,7,8,6] 30 :=
  branch_upper a [2,3,7,8,6] 30 (by decide) (fin9_cases _
  node333
  node334
  (invalid_upper a [2,3,7,8,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,6,3] 30 (by decide +kernel))
  node335
  (invalid_upper a [2,3,7,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,6,8] 30 (by decide +kernel)))

theorem node337 : UpperPrefix a [2,3,7,8] 30 :=
  branch_upper a [2,3,7,8] 30 (by decide) (fin9_cases _
  node324
  node329
  (invalid_upper a [2,3,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,5] 30 (by decide +kernel))
  node336
  (invalid_upper a [2,3,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,8,8] 30 (by decide +kernel)))

theorem node338 : UpperPrefix a [2,3,7] 30 :=
  branch_upper a [2,3,7] 30 (by decide) (fin9_cases _
  node251
  node269
  (invalid_upper a [2,3,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,4] 30 (by decide +kernel))
  node291
  node319
  (invalid_upper a [2,3,7,7] 30 (by decide +kernel))
  node337)

def cert339 : Leaf := ⟨⟨0,465,216,450,448,400,304,112,240⟩,[(0,1)],[(2,0,0),(0,3,1),(1,4,3)],⟨7,14,261,25,50,240,240,496,504⟩,⟨7,14,261,25,50,96,192,384,264⟩,[⟨3,1210144585119284360905731,⟨247,247,501,113,115,96,192,384,256⟩⟩,⟨5,1210107564157954027554183,⟨7,15,263,25,27,64,197,391,271⟩⟩]⟩
theorem node339 : UpperPrefix a [2,3,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,8,0,1] 30 cert339 (by decide +kernel)

def cert340 : Leaf := ⟨⟨0,417,170,418,0,410,314,58,178⟩,[(0,1),(4,5)],[(2,0,0),(0,3,1),(6,4,4)],⟨7,14,261,25,112,242,242,434,442⟩,⟨7,14,261,25,112,96,192,384,264⟩,[⟨4,1210107565282752275285383,⟨7,15,263,9,96,96,197,391,271⟩⟩]⟩
theorem node340 : UpperPrefix a [2,3,8,0,6] 30 :=
  Boolean.leaf_sound a [2,3,8,0,6] 30 cert340 (by decide +kernel)

def cert341 : Leaf := ⟨⟨0,257,10,258,330,410,314,122,242⟩,[(0,1)],[(2,0,0),(0,3,1)],⟨7,14,261,25,176,114,242,498,378⟩,⟨7,14,261,25,176,96,192,384,264⟩,[⟨5,1210107564157954027562391,⟨7,15,263,27,159,64,197,391,271⟩⟩,⟨6,1210106412362349327558039,⟨7,15,263,27,191,32,133,391,271⟩⟩,⟨7,1208926973663136523101591,⟨7,15,263,27,63,96,69,263,271⟩⟩,⟨4,1210107565282752275285383,⟨7,15,263,9,165,96,197,391,271⟩⟩]⟩
theorem node341 : UpperPrefix a [2,3,8,0,7] 30 :=
  Boolean.leaf_sound a [2,3,8,0,7] 30 cert341 (by decide +kernel)

theorem node342 : UpperPrefix a [2,3,8,0] 30 :=
  branch_upper a [2,3,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,8,0,0] 30 (by decide +kernel))
  node339
  (invalid_upper a [2,3,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,0,5] 30 (by decide +kernel))
  node340
  node341
  (invalid_upper a [2,3,8,0,8] 30 (by decide +kernel)))

def cert343 : Leaf := ⟨⟨0,481,232,481,448,400,304,112,240⟩,[(0,1)],[(2,0,0)],⟨7,14,261,26,49,240,240,496,504⟩,⟨7,14,261,26,49,96,192,384,264⟩,[⟨1,1257470140230513886232577,⟨501,508,501,504,245,96,192,384,488⟩⟩,⟨0,1247960428519766738600960,⟨6,494,260,506,48,96,192,384,488⟩⟩,⟨3,1212510389054761499362307,⟨247,247,501,115,113,96,192,480,496⟩⟩,⟨4,1210107565282752275285383,⟨7,15,263,11,33,96,197,391,271⟩⟩]⟩
theorem node343 : UpperPrefix a [2,3,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,8,1,0] 30 cert343 (by decide +kernel)

def cert344 : Leaf := ⟨⟨0,433,186,417,0,401,305,49,179⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,261,26,112,241,241,433,441⟩,⟨7,14,261,26,112,96,192,384,264⟩,[⟨1,1210144549022593572667393,⟨245,252,501,24,112,112,192,384,264⟩⟩,⟨3,1210144585122308017882115,⟨247,247,501,115,112,112,192,384,272⟩⟩]⟩
theorem node344 : UpperPrefix a [2,3,8,1,6] 30 :=
  Boolean.leaf_sound a [2,3,8,1,6] 30 cert344 (by decide +kernel)

def cert345 : Leaf := ⟨⟨0,273,26,257,321,401,305,113,243⟩,[(0,1)],[(2,0,0)],⟨7,14,261,26,176,113,241,497,377⟩,⟨7,14,261,26,176,96,192,384,264⟩,[⟨1,1210144549020394549411841,⟨245,252,501,24,176,96,192,384,264⟩⟩,⟨3,1210144585401034215523331,⟨247,247,501,115,176,96,192,384,288⟩⟩,⟨5,1210107564157954027562391,⟨7,15,263,27,159,64,197,391,271⟩⟩,⟨6,1210106412362349327558039,⟨7,15,263,27,191,32,133,391,271⟩⟩,⟨7,1208926973663136523101591,⟨7,15,263,27,63,96,69,263,271⟩⟩]⟩
theorem node345 : UpperPrefix a [2,3,8,1,7] 30 :=
  Boolean.leaf_sound a [2,3,8,1,7] 30 cert345 (by decide +kernel)

theorem node346 : UpperPrefix a [2,3,8,1] 30 :=
  branch_upper a [2,3,8,1] 30 (by decide) (fin9_cases _
  node343
  (invalid_upper a [2,3,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,1,5] 30 (by decide +kernel))
  node344
  node345
  (invalid_upper a [2,3,8,1,8] 30 (by decide +kernel)))

def cert347 : Leaf := ⟨⟨0,257,10,0,458,411,283,91,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,261,56,49,242,210,466,474⟩,⟨7,14,261,56,49,96,192,384,264⟩,[⟨4,1210107565282752275285383,⟨7,15,263,40,33,96,197,391,271⟩⟩,⟨6,1210106412362349327549831,⟨7,15,263,56,57,32,133,391,271⟩⟩,⟨7,1208926973663136523093383,⟨7,15,263,56,57,96,69,263,271⟩⟩]⟩
theorem node347 : UpperPrefix a [2,3,8,5,0] 30 :=
  Boolean.leaf_sound a [2,3,8,5,0] 30 cert347 (by decide +kernel)

def cert348 : Leaf := ⟨⟨0,449,202,0,449,403,275,83,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,261,56,50,241,209,465,473⟩,⟨7,14,261,56,50,96,192,384,264⟩,[⟨3,1210144585119284360905731,⟨247,247,501,48,115,96,192,384,256⟩⟩,⟨4,1210107565282752275285383,⟨7,15,263,40,35,96,197,391,271⟩⟩]⟩
theorem node348 : UpperPrefix a [2,3,8,5,1] 30 :=
  Boolean.leaf_sound a [2,3,8,5,1] 30 cert348 (by decide +kernel)

def cert349 : Local := ⟨⟨0,401,154,0,0,411,283,27,147⟩,[(0,1),(3,4),(4,5)],[(2,0,0),(5,3,3),(6,4,3),(6,4,4)]⟩
theorem node349 : UpperPrefix a [2,3,8,5,6] 30 :=
  local_sound a [2,3,8,5,6] 30 cert349 (by decide +kernel)

def cert350 : Leaf := ⟨⟨0,257,10,0,331,411,283,91,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,261,56,176,115,211,467,347⟩,⟨7,14,261,56,176,96,192,384,264⟩,[⟨4,1210107565282752275285383,⟨7,15,263,40,165,96,197,391,271⟩⟩,⟨6,1210106412362349327558039,⟨7,15,263,59,191,32,133,391,271⟩⟩,⟨7,1208926973663136523101591,⟨7,15,263,59,63,96,69,263,271⟩⟩]⟩
theorem node350 : UpperPrefix a [2,3,8,5,7] 30 :=
  Boolean.leaf_sound a [2,3,8,5,7] 30 cert350 (by decide +kernel)

theorem node351 : UpperPrefix a [2,3,8,5] 30 :=
  branch_upper a [2,3,8,5] 30 (by decide) (fin9_cases _
  node347
  node348
  (invalid_upper a [2,3,8,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,5,5] 30 (by decide +kernel))
  node349
  node350
  (invalid_upper a [2,3,8,5,8] 30 (by decide +kernel)))

def cert352 : Leaf := ⟨⟨0,369,120,288,322,273,304,112,240⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,14,261,88,49,98,240,432,440⟩,⟨7,14,261,88,49,98,192,384,264⟩,[⟨7,1208926976221298501518791,⟨23,63,279,123,57,123,127,279,319⟩⟩,⟨0,1285813291192733985145856,⟨6,14,260,472,504,98,192,384,264⟩⟩,⟨3,1210144584981020773712899,⟨247,247,501,80,113,115,192,384,256⟩⟩]⟩
theorem node352 : UpperPrefix a [2,3,8,6,0,1] 30 :=
  Boolean.leaf_sound a [2,3,8,6,0,1] 30 cert352 (by decide +kernel)

def cert353 : Leaf := ⟨⟨0,369,122,0,330,0,314,122,242⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,14,261,88,49,112,226,418,426⟩,⟨7,14,261,88,49,112,192,384,264⟩,[⟨0,1219570781303940976739328,⟨454,494,260,120,56,120,192,384,296⟩⟩,⟨7,1208926976221298501518791,⟨23,63,279,123,57,123,127,279,319⟩⟩]⟩
theorem node353 : UpperPrefix a [2,3,8,6,0,4] 30 :=
  Boolean.leaf_sound a [2,3,8,6,0,4] 30 cert353 (by decide +kernel)

def cert354 : Leaf := ⟨⟨0,289,42,291,266,0,315,123,115⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,14,261,88,49,224,242,434,314⟩,⟨7,14,261,88,49,224,192,384,264⟩,[⟨6,1210106412364546203321735,⟨7,15,263,24,49,181,133,391,271⟩⟩,⟨4,1210107567534552088970631,⟨7,15,263,104,33,229,229,391,271⟩⟩]⟩
theorem node354 : UpperPrefix a [2,3,8,6,0,7] 30 :=
  Boolean.leaf_sound a [2,3,8,6,0,7] 30 cert354 (by decide +kernel)

theorem node355 : UpperPrefix a [2,3,8,6,0] 30 :=
  branch_upper a [2,3,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,8,6,0,0] 30 (by decide +kernel))
  node352
  (invalid_upper a [2,3,8,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,0,3] 30 (by decide +kernel))
  node353
  (invalid_upper a [2,3,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,0,6] 30 (by decide +kernel))
  node354
  (invalid_upper a [2,3,8,6,0,8] 30 (by decide +kernel)))

def cert356 : Leaf := ⟨⟨0,369,122,288,321,274,304,112,240⟩,[(0,1)],[(2,0,0)],⟨7,14,261,88,50,97,240,432,440⟩,⟨7,14,261,88,50,97,192,384,264⟩,[⟨7,1208926976221298501518791,⟨23,63,279,123,59,123,127,279,319⟩⟩,⟨0,1285813291192733985145856,⟨6,14,260,472,506,96,192,384,264⟩⟩,⟨1,1285813291192733985144833,⟨5,12,261,472,504,97,192,384,264⟩⟩,⟨3,1210144585682234314327043,⟨247,247,501,112,115,113,192,384,256⟩⟩]⟩
theorem node356 : UpperPrefix a [2,3,8,6,1,0] 30 :=
  Boolean.leaf_sound a [2,3,8,6,1,0] 30 cert356 (by decide +kernel)

def cert357 : Leaf := ⟨⟨0,369,122,0,321,0,307,115,243⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,14,261,88,50,112,225,417,425⟩,⟨7,14,261,88,50,112,192,384,264⟩,[⟨3,1210144585963709291037699,⟨247,247,501,112,115,112,192,384,288⟩⟩,⟨7,1208926976221298501518791,⟨23,63,279,123,59,123,127,279,319⟩⟩]⟩
theorem node357 : UpperPrefix a [2,3,8,6,1,4] 30 :=
  Boolean.leaf_sound a [2,3,8,6,1,4] 30 cert357 (by decide +kernel)

def cert358 : Leaf := ⟨⟨0,353,106,291,321,0,307,115,115⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,14,261,88,50,224,241,433,313⟩,⟨7,14,261,88,50,224,192,384,264⟩,[⟨3,1210144587371084174590979,⟨247,247,501,112,115,224,224,384,256⟩⟩,⟨4,1210107567534552088970631,⟨7,15,263,104,35,229,229,391,271⟩⟩]⟩
theorem node358 : UpperPrefix a [2,3,8,6,1,7] 30 :=
  Boolean.leaf_sound a [2,3,8,6,1,7] 30 cert358 (by decide +kernel)

theorem node359 : UpperPrefix a [2,3,8,6,1] 30 :=
  branch_upper a [2,3,8,6,1] 30 (by decide) (fin9_cases _
  node356
  (invalid_upper a [2,3,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,1,3] 30 (by decide +kernel))
  node357
  (invalid_upper a [2,3,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,1,6] 30 (by decide +kernel))
  node358
  (invalid_upper a [2,3,8,6,1,8] 30 (by decide +kernel)))

def cert360 : Leaf := ⟨⟨0,369,120,416,320,274,305,112,112⟩,[(0,1)],[(2,0,0),(7,4,3),(1,6,5)],⟨7,14,261,88,176,97,194,432,312⟩,⟨7,14,261,88,176,97,194,384,264⟩,[⟨0,1437223878321567003837440,⟨6,14,260,472,440,504,194,384,264⟩⟩,⟨3,1210144515318163061081091,⟨247,247,501,112,176,113,243,384,256⟩⟩]⟩
theorem node360 : UpperPrefix a [2,3,8,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,3,8,6,7,0,1] 30 cert360 (by decide +kernel)

def cert361 : Local := ⟨⟨0,353,106,0,331,266,0,107,99⟩,[(0,1),(3,6),(6,4)],[(2,0,0),(7,4,3),(7,4,6),(4,6,3)]⟩
theorem node361 : UpperPrefix a [2,3,8,6,7,0,4] 30 :=
  local_sound a [2,3,8,6,7,0,4] 30 cert361 (by decide +kernel)

def cert362 : Local := ⟨⟨0,337,90,419,0,282,0,91,83⟩,[(0,1),(4,6),(6,4)],[(2,0,0),(7,4,3),(5,6,3)]⟩
theorem node362 : UpperPrefix a [2,3,8,6,7,0,5] 30 :=
  local_sound a [2,3,8,6,7,0,5] 30 cert362 (by decide +kernel)

theorem node363 : UpperPrefix a [2,3,8,6,7,0] 30 :=
  branch_upper a [2,3,8,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,8,6,7,0,0] 30 (by decide +kernel))
  node360
  (invalid_upper a [2,3,8,6,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,0,3] 30 (by decide +kernel))
  node361
  node362
  (invalid_upper a [2,3,8,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,0,8] 30 (by decide +kernel)))

def cert364 : Leaf := ⟨⟨0,369,122,416,320,273,306,112,112⟩,[(0,1)],[(2,0,0),(7,4,3)],⟨7,14,261,88,176,98,193,432,312⟩,⟨7,14,261,88,176,98,193,384,264⟩,[⟨0,1437223878321567003837440,⟨6,14,260,472,440,506,192,384,264⟩⟩,⟨1,1437223878321567003836417,⟨5,12,261,472,440,504,193,384,264⟩⟩,⟨3,1210144584983219796968451,⟨247,247,501,80,176,115,241,384,256⟩⟩]⟩
theorem node364 : UpperPrefix a [2,3,8,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,8,6,7,1,0] 30 cert364 (by decide +kernel)

def cert365 : Local := ⟨⟨0,353,106,0,331,265,0,107,99⟩,[(0,1),(3,6),(6,4)],[(2,0,0),(7,4,3),(7,4,6),(4,6,3)]⟩
theorem node365 : UpperPrefix a [2,3,8,6,7,1,4] 30 :=
  local_sound a [2,3,8,6,7,1,4] 30 cert365 (by decide +kernel)

def cert366 : Local := ⟨⟨0,337,90,419,0,281,0,91,83⟩,[(0,1),(4,6),(6,4)],[(2,0,0),(7,4,3),(5,6,3)]⟩
theorem node366 : UpperPrefix a [2,3,8,6,7,1,5] 30 :=
  local_sound a [2,3,8,6,7,1,5] 30 cert366 (by decide +kernel)

theorem node367 : UpperPrefix a [2,3,8,6,7,1] 30 :=
  branch_upper a [2,3,8,6,7,1] 30 (by decide) (fin9_cases _
  node364
  (invalid_upper a [2,3,8,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,1,3] 30 (by decide +kernel))
  node365
  node366
  (invalid_upper a [2,3,8,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,1,8] 30 (by decide +kernel)))

def cert368 : Leaf := ⟨⟨0,353,106,0,331,0,315,123,115⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(7,4,3),(7,4,5)],⟨7,14,261,88,176,112,227,419,299⟩,⟨7,14,261,88,176,112,192,384,264⟩,[⟨4,1210107565282752275285383,⟨7,15,263,72,165,96,197,391,271⟩⟩]⟩
theorem node368 : UpperPrefix a [2,3,8,6,7,4] 30 :=
  Boolean.leaf_sound a [2,3,8,6,7,4] 30 cert368 (by decide +kernel)

theorem node369 : UpperPrefix a [2,3,8,6,7] 30 :=
  branch_upper a [2,3,8,6,7] 30 (by decide) (fin9_cases _
  node363
  node367
  (invalid_upper a [2,3,8,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,3] 30 (by decide +kernel))
  node368
  (invalid_upper a [2,3,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,7,8] 30 (by decide +kernel)))

theorem node370 : UpperPrefix a [2,3,8,6] 30 :=
  branch_upper a [2,3,8,6] 30 (by decide) (fin9_cases _
  node355
  node359
  (invalid_upper a [2,3,8,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,6,6] 30 (by decide +kernel))
  node369
  (invalid_upper a [2,3,8,6,8] 30 (by decide +kernel)))

def cert371 : Leaf := ⟨⟨0,433,184,352,386,401,304,112,240⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,14,261,152,49,98,240,496,376⟩,⟨7,14,261,152,49,98,192,384,264⟩,[⟨0,1285813291192733985145856,⟨6,14,260,472,504,98,192,384,264⟩⟩,⟨3,1210144584981020773712899,⟨247,247,501,144,113,115,192,384,256⟩⟩,⟨6,1210106412364546203325839,⟨7,15,263,159,49,51,133,391,271⟩⟩]⟩
theorem node371 : UpperPrefix a [2,3,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,3,8,7,0,1] 30 cert371 (by decide +kernel)

def cert372 : Leaf := ⟨⟨0,369,120,352,322,259,305,112,240⟩,[(0,1)],[(2,0,0)],⟨7,14,261,152,49,112,194,480,360⟩,⟨7,14,261,152,49,112,194,384,264⟩,[⟨1,1361518440640866132426753,⟨5,12,261,156,445,508,192,384,264⟩⟩,⟨3,1210144515881113014502403,⟨247,247,501,176,113,112,243,384,256⟩⟩,⟨7,1208926975921531259065807,⟨7,15,263,31,49,113,119,263,271⟩⟩,⟨0,1361518440640866128233472,⟨6,14,260,152,440,504,194,384,264⟩⟩]⟩
theorem node372 : UpperPrefix a [2,3,8,7,0,4,1] 30 :=
  Boolean.leaf_sound a [2,3,8,7,0,4,1] 30 cert372 (by decide +kernel)

def cert373 : Leaf := ⟨⟨0,401,154,258,394,394,282,90,210⟩,[(0,1)],[(2,0,0),(5,6,5)],⟨7,14,261,152,49,112,224,450,330⟩,⟨7,14,261,152,49,112,224,384,264⟩,[⟨0,1219580437584489865020416,⟨454,494,388,248,248,120,224,384,360⟩⟩,⟨6,1210106412368952839804367,⟨7,15,263,159,49,59,191,391,271⟩⟩]⟩
theorem node373 : UpperPrefix a [2,3,8,7,0,4,5] 30 :=
  Boolean.leaf_sound a [2,3,8,7,0,4,5] 30 cert373 (by decide +kernel)

theorem node374 : UpperPrefix a [2,3,8,7,0,4] 30 :=
  branch_upper a [2,3,8,7,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,8,7,0,4,0] 30 (by decide +kernel))
  node372
  (invalid_upper a [2,3,8,7,0,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,0,4,4] 30 (by decide +kernel))
  node373
  (invalid_upper a [2,3,8,7,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,0,4,8] 30 (by decide +kernel)))

theorem node375 : UpperPrefix a [2,3,8,7,0] 30 :=
  branch_upper a [2,3,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,8,7,0,0] 30 (by decide +kernel))
  node371
  (invalid_upper a [2,3,8,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,0,3] 30 (by decide +kernel))
  node374
  (invalid_upper a [2,3,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,0,8] 30 (by decide +kernel)))

def cert376 : Leaf := ⟨⟨0,481,234,352,449,386,304,112,240⟩,[(0,1)],[(2,0,0)],⟨7,14,261,152,50,97,240,496,376⟩,⟨7,14,261,152,50,97,192,384,264⟩,[⟨0,1285813291192733985145856,⟨6,14,260,472,506,96,192,384,264⟩⟩,⟨1,1285813291192733985144833,⟨5,12,261,472,504,97,192,384,264⟩⟩,⟨3,1210144729797422390182915,⟨247,247,501,240,115,113,192,384,320⟩⟩,⟨4,1210107567534552088974735,⟨7,15,263,143,35,97,229,391,271⟩⟩]⟩
theorem node376 : UpperPrefix a [2,3,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,8,7,1,0] 30 cert376 (by decide +kernel)

def cert377 : Leaf := ⟨⟨0,449,202,352,449,387,258,112,240⟩,[(0,1)],[(2,0,0)],⟨7,14,261,152,50,112,193,480,360⟩,⟨7,14,261,152,50,112,193,384,264⟩,[⟨3,1210144587934034128012291,⟨247,247,501,176,115,112,241,384,256⟩⟩,⟨0,1361518440640866128233472,⟨6,14,260,152,442,504,192,384,264⟩⟩,⟨1,1361518440640866128232449,⟨5,12,261,152,440,504,193,384,264⟩⟩,⟨4,1210110015240949564839311,⟨7,79,263,207,35,96,197,455,335⟩⟩,⟨5,1210110014116149169624463,⟨7,79,263,223,19,80,197,455,335⟩⟩]⟩
theorem node377 : UpperPrefix a [2,3,8,7,1,4,0] 30 :=
  Boolean.leaf_sound a [2,3,8,7,1,4,0] 30 cert377 (by decide +kernel)

def cert378 : Leaf := ⟨⟨0,401,154,259,384,386,274,83,211⟩,[(0,1)],[(2,0,0),(5,6,5)],⟨7,14,261,152,50,112,224,449,329⟩,⟨7,14,261,152,50,112,224,384,264⟩,[⟨3,1210144730078897366893571,⟨247,247,501,240,115,112,224,384,352⟩⟩,⟨6,1210106412368952839804367,⟨7,15,263,159,51,59,191,391,271⟩⟩,⟨0,1210107709751089641292800,⟨54,126,276,248,50,112,224,384,360⟩⟩]⟩
theorem node378 : UpperPrefix a [2,3,8,7,1,4,5] 30 :=
  Boolean.leaf_sound a [2,3,8,7,1,4,5] 30 cert378 (by decide +kernel)

theorem node379 : UpperPrefix a [2,3,8,7,1,4] 30 :=
  branch_upper a [2,3,8,7,1,4] 30 (by decide) (fin9_cases _
  node377
  (invalid_upper a [2,3,8,7,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,4] 30 (by decide +kernel))
  node378
  (invalid_upper a [2,3,8,7,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,4,8] 30 (by decide +kernel)))

theorem node380 : UpperPrefix a [2,3,8,7,1] 30 :=
  branch_upper a [2,3,8,7,1] 30 (by decide) (fin9_cases _
  node376
  (invalid_upper a [2,3,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,3] 30 (by decide +kernel))
  node379
  (invalid_upper a [2,3,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,1,8] 30 (by decide +kernel)))

def cert381 : Leaf := ⟨⟨0,257,10,291,0,411,315,59,179⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,261,152,112,115,243,435,315⟩,⟨7,14,261,152,112,96,192,384,264⟩,[⟨4,1210107565282752275289487,⟨7,15,263,143,96,96,197,391,271⟩⟩,⟨5,1210107564157951880074639,⟨7,15,263,159,80,64,197,391,271⟩⟩,⟨7,1208926973665333398869391,⟨7,15,263,31,112,112,69,263,271⟩⟩]⟩
theorem node381 : UpperPrefix a [2,3,8,7,6] 30 :=
  Boolean.leaf_sound a [2,3,8,7,6] 30 cert381 (by decide +kernel)

theorem node382 : UpperPrefix a [2,3,8,7] 30 :=
  branch_upper a [2,3,8,7] 30 (by decide) (fin9_cases _
  node375
  node380
  (invalid_upper a [2,3,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,5] 30 (by decide +kernel))
  node381
  (invalid_upper a [2,3,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,7,8] 30 (by decide +kernel)))

theorem node383 : UpperPrefix a [2,3,8] 30 :=
  branch_upper a [2,3,8] 30 (by decide) (fin9_cases _
  node342
  node346
  (invalid_upper a [2,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,8,4] 30 (by decide +kernel))
  node351
  node370
  node382
  (invalid_upper a [2,3,8,8] 30 (by decide +kernel)))

#print axioms node383
end Delivery.FiniteExclusion.Sharp3x6
