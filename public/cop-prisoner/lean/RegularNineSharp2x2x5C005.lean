import RegularNineSharp2x2x5Base
import RegularNineSharp2x2x5C004
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x5
open Bounds BoundTreeRows Extremal
def cert320 : Leaf := ⟨⟨496,480,0,465,449,145,0,113,225⟩,[(2,6),(6,2)],[(1,4,1)],⟨7,19,140,44,50,352,200,449,337⟩,⟨7,19,140,44,50,352,200,384,272⟩,[⟨3,1512929318256813251009549,⟨7,19,151,55,50,498,499,384,272⟩⟩,⟨2,1214839227231742753506817,⟨499,435,200,104,50,352,200,384,272⟩⟩]⟩
theorem node320 : UpperPrefix a [2,4,7,5,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,8,3] 30 cert320 (by decide +kernel)

theorem node321 : UpperPrefix a [2,4,7,5,1,8] 30 :=
  branch_upper a [2,4,7,5,1,8] 30 (by decide) (fin9_cases _
  node319
  (invalid_upper a [2,4,7,5,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,2] 30 (by decide +kernel))
  node320
  (invalid_upper a [2,4,7,5,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,8] 30 (by decide +kernel)))

theorem node322 : UpperPrefix a [2,4,7,5,1] 30 :=
  branch_upper a [2,4,7,5,1] 30 (by decide) (fin9_cases _
  node317
  (invalid_upper a [2,4,7,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,2] 30 (by decide +kernel))
  node318
  (invalid_upper a [2,4,7,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,7] 30 (by decide +kernel))
  node321)

def cert323 : Leaf := ⟨⟨216,204,82,210,0,146,274,82,194⟩,[(4,3)],[(5,3,4)],⟨7,19,140,44,56,97,450,450,338⟩,⟨7,19,140,44,56,97,192,384,272⟩,[⟨0,1219580022411652299752448,⟨454,478,156,60,60,252,192,384,280⟩⟩,⟨8,1181747928182052420717,⟨7,19,159,63,59,127,255,128,18⟩⟩,⟨2,1219580022514999940350977,⟨483,499,152,56,56,225,192,384,272⟩⟩,⟨3,1219580022514449111843841,⟨487,499,132,36,48,225,192,384,272⟩⟩]⟩
theorem node323 : UpperPrefix a [2,4,7,5,3,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,3,0] 30 cert323 (by decide +kernel)

def cert324 : Leaf := ⟨⟨216,204,81,209,0,145,273,81,193⟩,[(4,3)],[(5,3,4)],⟨7,19,140,44,56,98,449,449,337⟩,⟨7,19,140,44,56,98,192,384,272⟩,[⟨1,1219580022411652299751425,⟨453,477,156,60,60,508,192,384,280⟩⟩,⟨8,1181747928182052420717,⟨7,19,159,63,59,127,255,128,18⟩⟩,⟨2,1219580022514999940350977,⟨483,499,152,56,56,482,192,384,272⟩⟩,⟨3,1219580022514449111843841,⟨487,499,132,36,48,482,192,384,272⟩⟩]⟩
theorem node324 : UpperPrefix a [2,4,7,5,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,3,1] 30 cert324 (by decide +kernel)

def cert325 : Leaf := ⟨⟨24,12,339,467,0,147,19,83,195⟩,[(4,3)],[(5,3,4)],⟨7,19,140,44,56,352,195,451,339⟩,⟨7,19,140,44,56,352,192,384,272⟩,[⟨2,1219580022514999940350977,⟨483,499,152,56,56,352,192,384,272⟩⟩,⟨3,1219580022514449111843841,⟨487,499,132,36,48,352,192,384,272⟩⟩,⟨8,1181817727366305168397,⟨71,19,223,127,59,96,192,128,18⟩⟩,⟨6,1210106412362896835099661,⟨7,19,159,63,59,288,128,384,274⟩⟩,⟨7,1208926973663684030643213,⟨7,19,31,63,59,352,64,256,274⟩⟩]⟩
theorem node325 : UpperPrefix a [2,4,7,5,3,8] 30 :=
  Boolean.leaf_sound a [2,4,7,5,3,8] 30 cert325 (by decide +kernel)

theorem node326 : UpperPrefix a [2,4,7,5,3] 30 :=
  branch_upper a [2,4,7,5,3] 30 (by decide) (fin9_cases _
  node323
  node324
  (invalid_upper a [2,4,7,5,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,3,7] 30 (by decide +kernel))
  node325)

def cert327 : Leaf := ⟨⟨184,172,48,144,0,158,60,60,172⟩,[(4,5)],[(6,4,4),(1,6,5)],⟨7,19,140,44,112,97,194,392,280⟩,⟨7,19,140,44,112,97,194,384,272⟩,[⟨8,1184131361891444588285,⟨127,59,255,127,127,127,255,255,59⟩⟩,⟨0,1486937907643412003685376,⟨454,478,396,444,508,508,454,388,412⟩⟩]⟩
theorem node327 : UpperPrefix a [2,4,7,5,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,0,1] 30 cert327 (by decide +kernel)

def cert328 : Leaf := ⟨⟨432,420,0,403,0,406,0,55,167⟩,[(2,6),(4,5),(6,2)],[(6,4,4)],⟨7,19,140,44,112,97,200,386,274⟩,⟨7,19,140,44,112,97,200,384,272⟩,[⟨3,1787407646701024768480269,⟨391,403,391,439,498,499,499,384,400⟩⟩]⟩
theorem node328 : UpperPrefix a [2,4,7,5,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,0,3] 30 cert328 (by decide +kernel)

def cert329 : Leaf := ⟨⟨184,168,51,147,0,154,0,59,171⟩,[(4,5),(6,7)],[(6,4,4),(8,6,6)],⟨7,19,140,44,112,97,448,394,282⟩,⟨7,19,140,44,112,97,448,384,272⟩,[⟨2,1247962806176896883115521,⟨115,51,472,506,114,115,448,448,272⟩⟩]⟩
theorem node329 : UpperPrefix a [2,4,7,5,6,0,8] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,0,8] 30 cert329 (by decide +kernel)

theorem node330 : UpperPrefix a [2,4,7,5,6,0] 30 :=
  branch_upper a [2,4,7,5,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,6,0,0] 30 (by decide +kernel))
  node327
  (invalid_upper a [2,4,7,5,6,0,2] 30 (by decide +kernel))
  node328
  (invalid_upper a [2,4,7,5,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,0,7] 30 (by decide +kernel))
  node329)

def cert331 : Leaf := ⟨⟨48,36,49,145,0,157,317,61,45⟩,[(4,5)],[(6,4,4)],⟨7,19,140,44,112,98,457,393,281⟩,⟨7,19,140,44,112,98,192,384,272⟩,[⟨1,1219570781024667179679745,⟨453,477,140,60,124,508,192,384,280⟩⟩,⟨8,1181748490584397640829,⟨7,59,143,63,127,127,255,130,59⟩⟩,⟨7,1246705905528290459784205,⟨7,19,271,319,112,114,64,256,272⟩⟩,⟨3,1210107565286049635636237,⟨7,19,135,55,112,114,192,384,272⟩⟩]⟩
theorem node331 : UpperPrefix a [2,4,7,5,6,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,1] 30 cert331 (by decide +kernel)

def cert332 : Leaf := ⟨⟨176,164,48,144,0,148,311,55,167⟩,[(4,5)],[(6,4,4),(3,5,3)],⟨7,19,140,44,112,104,451,387,275⟩,⟨7,19,140,44,112,104,192,384,272⟩,[⟨8,1181748490584397640829,⟨7,59,143,63,127,127,255,130,59⟩⟩,⟨0,1210107568105213572154368,⟨6,58,140,60,124,124,252,384,312⟩⟩,⟨1,1210107568105213572153345,⟨5,57,140,60,124,124,252,384,312⟩⟩]⟩
theorem node332 : UpperPrefix a [2,4,7,5,6,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,3] 30 cert332 (by decide +kernel)

def cert333 : Leaf := ⟨⟨424,428,288,384,0,140,302,60,172⟩,[(4,5)],[(4,1,7),(6,4,4),(1,7,6)],⟨7,19,140,44,112,352,193,386,280⟩,⟨7,19,140,44,112,352,193,386,272⟩,[⟨0,1786263949131421155329024,⟨398,446,396,316,380,380,508,398,312⟩⟩]⟩
theorem node333 : UpperPrefix a [2,4,7,5,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,8,0,1] 30 cert333 (by decide +kernel)

def cert334 : Leaf := ⟨⟨432,416,0,403,0,147,310,51,163⟩,[(2,7),(4,5)],[(6,4,4),(3,7,2)],⟨7,19,140,44,112,352,193,392,274⟩,⟨7,19,140,44,112,352,193,392,272⟩,[⟨2,1748531134128632914543617,⟨259,307,136,440,370,370,499,392,304⟩⟩]⟩
theorem node334 : UpperPrefix a [2,4,7,5,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,8,0,3] 30 cert334 (by decide +kernel)

theorem node335 : UpperPrefix a [2,4,7,5,6,8,0] 30 :=
  branch_upper a [2,4,7,5,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,6,8,0,0] 30 (by decide +kernel))
  node333
  (invalid_upper a [2,4,7,5,6,8,0,2] 30 (by decide +kernel))
  node334
  (invalid_upper a [2,4,7,5,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,0,8] 30 (by decide +kernel)))

def cert336 : Leaf := ⟨⟨48,36,305,401,0,157,53,61,45⟩,[(4,5)],[(6,4,4)],⟨7,19,140,44,112,352,194,393,281⟩,⟨7,19,140,44,112,352,194,384,272⟩,[⟨1,1219570747252076619235329,⟨389,413,140,60,124,380,508,384,280⟩⟩,⟨3,1210107637344193429380109,⟨71,19,215,119,112,368,194,384,272⟩⟩,⟨7,1246705905528290459784205,⟨7,19,271,319,112,368,66,256,272⟩⟩,⟨8,1181817729565328415757,⟨71,19,223,127,112,112,194,128,16⟩⟩]⟩
theorem node336 : UpperPrefix a [2,4,7,5,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,8,1] 30 cert336 (by decide +kernel)

def cert337 : Leaf := ⟨⟨432,420,0,403,0,151,0,55,167⟩,[(2,6),(4,5),(6,2)],[(6,4,4)],⟨7,19,140,44,112,352,200,387,275⟩,⟨7,19,140,44,112,352,200,384,272⟩,[⟨3,1560291334228462722389005,⟨391,435,391,439,498,498,499,384,304⟩⟩]⟩
theorem node337 : UpperPrefix a [2,4,7,5,6,8,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,8,3] 30 cert337 (by decide +kernel)

theorem node338 : UpperPrefix a [2,4,7,5,6,8] 30 :=
  branch_upper a [2,4,7,5,6,8] 30 (by decide) (fin9_cases _
  node335
  node336
  (invalid_upper a [2,4,7,5,6,8,2] 30 (by decide +kernel))
  node337
  (invalid_upper a [2,4,7,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,8] 30 (by decide +kernel)))

theorem node339 : UpperPrefix a [2,4,7,5,6] 30 :=
  branch_upper a [2,4,7,5,6] 30 (by decide) (fin9_cases _
  node330
  node331
  (invalid_upper a [2,4,7,5,6,2] 30 (by decide +kernel))
  node332
  (invalid_upper a [2,4,7,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,7] 30 (by decide +kernel))
  node338)

def cert340 : Leaf := ⟨⟨496,480,0,464,192,402,304,112,224⟩,[(2,7)],[(1,6,5),(3,7,2)],⟨7,19,140,44,304,97,194,392,336⟩,⟨7,19,140,44,304,97,194,392,272⟩,[⟨2,2338863997396631834084865,⟨499,371,472,506,306,371,498,472,272⟩⟩,⟨0,1373564218566942888821760,⟨454,478,156,444,444,508,454,412,412⟩⟩]⟩
theorem node340 : UpperPrefix a [2,4,7,5,8,0,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,0,1,3] 30 cert340 (by decide +kernel)

def cert341 : Leaf := ⟨⟨424,424,352,448,136,394,312,56,168⟩,[],[(1,6,5)],⟨7,19,140,44,304,97,194,448,280⟩,⟨7,19,140,44,304,97,194,448,272⟩,[⟨0,1503807455099369077343232,⟨454,478,412,444,444,508,454,448,284⟩⟩,⟨2,1269405687064474689750529,⟨499,243,472,506,498,243,226,448,464⟩⟩,⟨4,1210107572038182267520065,⟨15,3,172,44,296,109,239,493,256⟩⟩,⟨6,1266774810157332577655821,⟨263,19,415,319,304,33,130,384,272⟩⟩]⟩
theorem node341 : UpperPrefix a [2,4,7,5,8,0,1,6] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,0,1,6] 30 cert341 (by decide +kernel)

theorem node342 : UpperPrefix a [2,4,7,5,8,0,1] 30 :=
  branch_upper a [2,4,7,5,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,1,2] 30 (by decide +kernel))
  node340
  (invalid_upper a [2,4,7,5,8,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,1,5] 30 (by decide +kernel))
  node341
  (invalid_upper a [2,4,7,5,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,1,8] 30 (by decide +kernel)))

def cert343 : Leaf := ⟨⟨368,352,0,467,67,274,0,115,99⟩,[(2,6),(6,2)],[],⟨7,19,140,44,304,97,200,450,338⟩,⟨7,19,140,44,304,97,200,384,272⟩,[⟨3,1664340193613821250690061,⟨7,19,151,439,434,499,499,384,272⟩⟩,⟨2,1404102965545939608028673,⟨499,435,472,506,434,499,472,384,272⟩⟩,⟨7,1662274158277566854650893,⟨7,19,31,319,306,371,379,256,272⟩⟩]⟩
theorem node343 : UpperPrefix a [2,4,7,5,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,0,3] 30 cert343 (by decide +kernel)

theorem node344 : UpperPrefix a [2,4,7,5,8,0] 30 :=
  branch_upper a [2,4,7,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,8,0,0] 30 (by decide +kernel))
  node342
  (invalid_upper a [2,4,7,5,8,0,2] 30 (by decide +kernel))
  node343
  (invalid_upper a [2,4,7,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,8] 30 (by decide +kernel)))

def cert345 : Leaf := ⟨⟨496,480,0,464,192,401,308,112,224⟩,[(2,7)],[(0,6,5),(3,7,2)],⟨7,19,140,44,304,98,193,392,336⟩,⟨7,19,140,44,304,98,193,392,272⟩,[⟨1,1373564218566942888820737,⟨453,477,156,444,444,508,197,412,412⟩⟩,⟨2,1663528536874579103089665,⟨3,19,152,440,304,370,499,408,272⟩⟩]⟩
theorem node345 : UpperPrefix a [2,4,7,5,8,1,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,1,0,3] 30 cert345 (by decide +kernel)

def cert346 : Leaf := ⟨⟨360,360,352,320,72,265,296,40,104⟩,[],[(0,6,5)],⟨7,19,140,44,304,98,193,448,280⟩,⟨7,19,140,44,304,98,193,448,272⟩,[⟨1,1503217159289010371690497,⟨453,477,412,444,444,508,193,448,284⟩⟩,⟨2,1266785247364161814431233,⟨499,243,440,312,304,98,243,498,272⟩⟩,⟨4,1212616646841518517650467,⟨111,239,140,45,493,111,237,460,460⟩⟩,⟨7,1270317744709858413813261,⟨287,275,319,319,304,114,371,370,272⟩⟩]⟩
theorem node346 : UpperPrefix a [2,4,7,5,8,1,0,6] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,1,0,6] 30 cert346 (by decide +kernel)

theorem node347 : UpperPrefix a [2,4,7,5,8,1,0] 30 :=
  branch_upper a [2,4,7,5,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,0,2] 30 (by decide +kernel))
  node345
  (invalid_upper a [2,4,7,5,8,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,0,5] 30 (by decide +kernel))
  node346
  (invalid_upper a [2,4,7,5,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,0,8] 30 (by decide +kernel)))

def cert348 : Leaf := ⟨⟨368,352,0,467,67,273,0,115,99⟩,[(2,6),(6,2)],[],⟨7,19,140,44,304,98,200,449,337⟩,⟨7,19,140,44,304,98,200,384,272⟩,[⟨3,1512929318256263495193613,⟨7,19,135,55,304,498,499,384,272⟩⟩,⟨2,1214839227231742753506817,⟨499,435,200,104,304,114,200,384,272⟩⟩,⟨7,1511158430825188451980301,⟨7,19,15,63,304,370,379,256,272⟩⟩]⟩
theorem node348 : UpperPrefix a [2,4,7,5,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,1,3] 30 cert348 (by decide +kernel)

theorem node349 : UpperPrefix a [2,4,7,5,8,1] 30 :=
  branch_upper a [2,4,7,5,8,1] 30 (by decide) (fin9_cases _
  node347
  (invalid_upper a [2,4,7,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,2] 30 (by decide +kernel))
  node348
  (invalid_upper a [2,4,7,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,8] 30 (by decide +kernel)))

def cert350 : Leaf := ⟨⟨368,356,96,192,71,132,275,83,67⟩,[],[(3,5,3)],⟨7,19,140,44,304,104,195,451,339⟩,⟨7,19,140,44,304,104,192,384,272⟩,[⟨7,1360042701117711700745229,⟨7,19,31,319,306,379,64,256,272⟩⟩,⟨0,1210107567535664401482752,⟨6,18,140,44,312,108,236,384,272⟩⟩,⟨1,1210107567535664401481729,⟨5,17,140,44,312,108,236,384,272⟩⟩,⟨2,1219580022408897068270593,⟨451,467,136,40,304,104,192,384,272⟩⟩,⟨4,1210107567534564889854977,⟨7,3,140,44,296,108,236,384,256⟩⟩,⟨5,1219580021282997162476545,⟨455,467,140,12,272,72,192,384,272⟩⟩,⟨8,1181747921035226776577,⟨7,19,140,44,56,108,236,128,16⟩⟩]⟩
theorem node350 : UpperPrefix a [2,4,7,5,8,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,3] 30 cert350 (by decide +kernel)

theorem node351 : UpperPrefix a [2,4,7,5,8] 30 :=
  branch_upper a [2,4,7,5,8] 30 (by decide) (fin9_cases _
  node344
  node349
  (invalid_upper a [2,4,7,5,8,2] 30 (by decide +kernel))
  node350
  (invalid_upper a [2,4,7,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,8] 30 (by decide +kernel)))

theorem node352 : UpperPrefix a [2,4,7,5] 30 :=
  branch_upper a [2,4,7,5] 30 (by decide) (fin9_cases _
  node316
  node322
  (invalid_upper a [2,4,7,5,2] 30 (by decide +kernel))
  node326
  (invalid_upper a [2,4,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,5] 30 (by decide +kernel))
  node339
  (invalid_upper a [2,4,7,5,7] 30 (by decide +kernel))
  node351)

def cert353 : Leaf := ⟨⟨112,0,112,176,70,20,316,124,108⟩,[(1,4)],[(7,2,3),(0,4,1),(1,5,4)],⟨7,19,140,76,49,98,488,424,312⟩,⟨7,19,140,76,49,98,192,384,272⟩,[⟨8,1181748209931907038829,⟨23,19,191,127,59,127,255,128,18⟩⟩,⟨3,1210107565566150222822925,⟨23,19,183,119,51,98,192,384,274⟩⟩]⟩
theorem node353 : UpperPrefix a [2,4,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,1] 30 cert353 (by decide +kernel)

def cert354 : Leaf := ⟨⟨56,0,50,178,14,0,318,62,46⟩,[(1,4),(5,3)],[(7,2,3),(6,3,5),(0,4,1)],⟨7,19,140,76,49,104,482,418,306⟩,⟨7,19,140,76,49,104,192,384,272⟩,[⟨8,1181748209931907038829,⟨23,19,191,127,59,127,255,128,18⟩⟩]⟩
theorem node354 : UpperPrefix a [2,4,7,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,3] 30 cert354 (by decide +kernel)

def cert355 : Leaf := ⟨⟨104,0,96,160,78,30,316,108,108⟩,[(1,4)],[(7,2,3),(0,4,1)],⟨7,19,140,76,49,352,194,424,312⟩,⟨7,19,140,76,49,352,194,384,272⟩,[⟨1,1286108150867547953037313,⟨5,405,140,76,445,492,204,384,404⟩⟩,⟨4,1210402713187944441578563,⟨7,7,140,77,173,493,207,384,260⟩⟩,⟨8,1181745671434436371553,⟨7,19,140,77,59,127,207,128,18⟩⟩]⟩
theorem node355 : UpperPrefix a [2,4,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,1] 30 cert355 (by decide +kernel)

def cert356 : Local := ⟨⟨368,0,0,434,326,22,0,118,102⟩,[(1,4),(2,6),(6,2)],[(7,2,3),(0,4,1),(3,6,3)]⟩
theorem node356 : UpperPrefix a [2,4,7,6,0,8,3] 30 :=
  local_sound a [2,4,7,6,0,8,3] 30 cert356 (by decide +kernel)

def cert357 : Leaf := ⟨⟨88,0,80,144,78,28,284,94,78⟩,[(1,4)],[(7,2,3),(0,4,1),(8,5,6)],⟨7,19,140,76,49,352,224,394,282⟩,⟨7,19,140,76,49,352,224,384,272⟩,[⟨5,1286108149741648046335283,⟨7,407,140,76,415,463,205,387,407⟩⟩,⟨1,1210109947688085351301121,⟨77,25,236,76,57,364,236,492,272⟩⟩]⟩
theorem node357 : UpperPrefix a [2,4,7,6,0,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,5] 30 cert357 (by decide +kernel)

theorem node358 : UpperPrefix a [2,4,7,6,0,8] 30 :=
  branch_upper a [2,4,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,0,8,0] 30 (by decide +kernel))
  node355
  (invalid_upper a [2,4,7,6,0,8,2] 30 (by decide +kernel))
  node356
  (invalid_upper a [2,4,7,6,0,8,4] 30 (by decide +kernel))
  node357
  (invalid_upper a [2,4,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,8] 30 (by decide +kernel)))

theorem node359 : UpperPrefix a [2,4,7,6,0] 30 :=
  branch_upper a [2,4,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,0,0] 30 (by decide +kernel))
  node353
  (invalid_upper a [2,4,7,6,0,2] 30 (by decide +kernel))
  node354
  (invalid_upper a [2,4,7,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,7] 30 (by decide +kernel))
  node358)

def cert360 : Leaf := ⟨⟨112,96,112,176,65,20,316,124,108⟩,[],[(7,2,3),(1,4,1),(0,5,4)],⟨7,19,140,76,50,97,488,424,312⟩,⟨7,19,140,76,50,97,192,384,272⟩,[⟨8,1181748209931907038829,⟨23,19,191,127,59,127,255,128,18⟩⟩,⟨3,1210107565568349246086669,⟨23,19,183,119,50,115,192,384,272⟩⟩,⟨2,1210107565286050708341761,⟨3,19,136,72,50,115,192,384,272⟩⟩]⟩
theorem node360 : UpperPrefix a [2,4,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,0] 30 cert360 (by decide +kernel)

def cert361 : Leaf := ⟨⟨56,44,48,176,13,0,317,61,45⟩,[(5,3)],[(7,2,3),(6,3,5),(1,4,1)],⟨7,19,140,76,50,104,481,417,305⟩,⟨7,19,140,76,50,104,192,384,272⟩,[⟨8,1181748209931907038829,⟨23,19,191,127,59,127,255,128,18⟩⟩,⟨0,1210107567817139378193408,⟨6,18,172,108,58,108,236,384,272⟩⟩]⟩
theorem node361 : UpperPrefix a [2,4,7,6,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,3] 30 cert361 (by decide +kernel)

def cert362 : Leaf := ⟨⟨104,104,97,161,73,9,296,105,105⟩,[],[(7,2,3),(1,4,1)],⟨7,19,140,76,50,352,193,424,312⟩,⟨7,19,140,76,50,352,193,384,272⟩,[⟨2,1266886661881140527269377,⟨499,115,440,506,50,370,243,384,272⟩⟩,⟨4,1212768809856626781586451,⟨15,79,172,76,239,492,237,492,493⟩⟩,⟨8,1181745671434436371489,⟨7,19,140,76,59,127,205,128,18⟩⟩]⟩
theorem node362 : UpperPrefix a [2,4,7,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,0] 30 cert362 (by decide +kernel)

def cert363 : Local := ⟨⟨368,356,0,433,325,21,0,117,101⟩,[(2,6),(6,2)],[(7,2,3),(1,4,1),(3,6,3)]⟩
theorem node363 : UpperPrefix a [2,4,7,6,1,8,3] 30 :=
  local_sound a [2,4,7,6,1,8,3] 30 cert363 (by decide +kernel)

def cert364 : Leaf := ⟨⟨72,76,65,129,77,13,269,77,77⟩,[],[(7,2,3),(1,4,1),(8,5,6)],⟨7,19,140,76,50,352,224,393,281⟩,⟨7,19,140,76,50,352,224,384,272⟩,[⟨4,1212476328082427230553105,⟨79,11,236,76,111,492,236,492,493⟩⟩,⟨5,1286108149741648046335283,⟨7,407,140,76,415,463,205,387,407⟩⟩]⟩
theorem node364 : UpperPrefix a [2,4,7,6,1,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,5] 30 cert364 (by decide +kernel)

theorem node365 : UpperPrefix a [2,4,7,6,1,8] 30 :=
  branch_upper a [2,4,7,6,1,8] 30 (by decide) (fin9_cases _
  node362
  (invalid_upper a [2,4,7,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,2] 30 (by decide +kernel))
  node363
  (invalid_upper a [2,4,7,6,1,8,4] 30 (by decide +kernel))
  node364
  (invalid_upper a [2,4,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,8] 30 (by decide +kernel)))

theorem node366 : UpperPrefix a [2,4,7,6,1] 30 :=
  branch_upper a [2,4,7,6,1] 30 (by decide) (fin9_cases _
  node360
  (invalid_upper a [2,4,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,2] 30 (by decide +kernel))
  node361
  (invalid_upper a [2,4,7,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,7] 30 (by decide +kernel))
  node365)

def cert367 : Leaf := ⟨⟨56,44,48,176,68,275,307,51,35⟩,[],[(7,2,3),(6,3,4)],⟨7,19,140,76,56,355,483,419,307⟩,⟨7,19,140,76,56,96,192,384,272⟩,[⟨8,1181745671434436371489,⟨7,19,140,76,59,127,204,128,18⟩⟩,⟨2,1219580022514450184537089,⟨483,499,136,72,56,96,192,384,272⟩⟩,⟨3,1219580022514449111843841,⟨487,499,132,68,48,96,192,384,272⟩⟩,⟨0,1210107565286063611053056,⟨6,18,140,76,56,124,204,384,272⟩⟩,⟨1,1210107565286063611052033,⟨5,17,140,76,56,124,204,384,272⟩⟩]⟩
theorem node367 : UpperPrefix a [2,4,7,6,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3] 30 cert367 (by decide +kernel)

def cert368 : Leaf := ⟨⟨104,364,96,160,76,14,300,108,108⟩,[],[(7,2,3),(1,6,5)],⟨7,19,140,76,304,97,194,424,312⟩,⟨7,19,140,76,304,97,194,384,272⟩,[⟨0,1437223914350373045273600,⟨78,478,140,76,444,508,206,384,404⟩⟩,⟨4,1210255177902980085580867,⟨111,239,172,109,428,109,239,384,388⟩⟩,⟨8,1181748202510203487297,⟨7,19,172,109,56,109,239,128,16⟩⟩]⟩
theorem node368 : UpperPrefix a [2,4,7,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,1] 30 cert368 (by decide +kernel)

def cert369 : Leaf := ⟨⟨368,352,0,435,67,274,0,115,99⟩,[(2,6),(6,2)],[(7,2,3),(3,6,3)],⟨7,19,140,76,304,97,200,418,306⟩,⟨7,19,140,76,304,97,200,384,272⟩,[⟨2,1451418719979266776253953,⟨499,435,200,72,434,499,200,384,400⟩⟩]⟩
theorem node369 : UpperPrefix a [2,4,7,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,3] 30 cert369 (by decide +kernel)

def cert370 : Leaf := ⟨⟨328,328,322,386,74,266,266,88,74⟩,[],[(4,1,7),(7,2,3)],⟨7,19,140,76,304,97,224,386,280⟩,⟨7,19,140,76,304,97,224,386,272⟩,[⟨0,1786264522777423397782528,⟨390,414,396,348,380,508,508,390,280⟩⟩,⟨2,1229157053231707923170817,⟨499,243,472,328,498,243,242,498,464⟩⟩,⟨5,1288192631821977217279251,⟨135,407,140,76,415,77,204,387,407⟩⟩]⟩
theorem node370 : UpperPrefix a [2,4,7,6,8,0,5,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,5,1] 30 cert370 (by decide +kernel)

def cert371 : Leaf := ⟨⟨320,324,0,387,71,262,263,71,71⟩,[(2,7)],[(7,2,3),(3,7,2)],⟨7,19,140,76,304,97,224,392,274⟩,⟨7,19,140,76,304,97,224,392,272⟩,[⟨4,1212616646841552877388803,⟨111,239,140,76,492,109,236,396,460⟩⟩,⟨5,1295257734802208009102739,⟨263,407,141,76,415,77,205,399,407⟩⟩]⟩
theorem node371 : UpperPrefix a [2,4,7,6,8,0,5,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,5,3] 30 cert371 (by decide +kernel)

theorem node372 : UpperPrefix a [2,4,7,6,8,0,5] 30 :=
  branch_upper a [2,4,7,6,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,8,0,5,0] 30 (by decide +kernel))
  node370
  (invalid_upper a [2,4,7,6,8,0,5,2] 30 (by decide +kernel))
  node371
  (invalid_upper a [2,4,7,6,8,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,5,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,5,8] 30 (by decide +kernel)))

theorem node373 : UpperPrefix a [2,4,7,6,8,0] 30 :=
  branch_upper a [2,4,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,8,0,0] 30 (by decide +kernel))
  node368
  (invalid_upper a [2,4,7,6,8,0,2] 30 (by decide +kernel))
  node369
  (invalid_upper a [2,4,7,6,8,0,4] 30 (by decide +kernel))
  node372
  (invalid_upper a [2,4,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,8] 30 (by decide +kernel)))

def cert374 : Leaf := ⟨⟨360,360,352,416,72,265,296,104,104⟩,[],[(7,2,3),(0,6,5)],⟨7,19,140,76,304,98,193,424,312⟩,⟨7,19,140,76,304,98,193,384,272⟩,[⟨1,1437223914350373045272577,⟨77,477,140,76,444,508,205,384,404⟩⟩,⟨2,1266886664196849454319105,⟨499,115,440,506,304,98,243,384,272⟩⟩,⟨4,1210255463600118054781987,⟨111,239,140,76,493,111,237,396,460⟩⟩]⟩
theorem node374 : UpperPrefix a [2,4,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,0] 30 cert374 (by decide +kernel)

def cert375 : Leaf := ⟨⟨368,352,0,435,67,273,0,115,99⟩,[(2,6),(6,2)],[(7,2,3),(3,6,3)],⟨7,19,140,76,304,98,200,417,305⟩,⟨7,19,140,76,304,98,200,384,272⟩,[⟨2,1224302406943754776741377,⟨499,435,200,72,304,498,200,384,272⟩⟩]⟩
theorem node375 : UpperPrefix a [2,4,7,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,3] 30 cert375 (by decide +kernel)

def cert376 : Leaf := ⟨⟨72,76,65,129,77,269,269,77,77⟩,[],[(7,2,3)],⟨7,19,140,76,304,98,224,393,281⟩,⟨7,19,140,76,304,98,224,384,272⟩,[⟨1,1219571321456631070851073,⟨389,413,140,76,380,508,252,384,280⟩⟩,⟨4,1210255463600118054781987,⟨111,239,140,76,493,111,237,396,460⟩⟩,⟨5,1285813001836468685120819,⟨7,407,140,76,415,79,205,387,407⟩⟩,⟨8,1181745669235413099553,⟨7,19,140,76,59,111,237,128,18⟩⟩]⟩
theorem node376 : UpperPrefix a [2,4,7,6,8,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,5] 30 cert376 (by decide +kernel)

theorem node377 : UpperPrefix a [2,4,7,6,8,1] 30 :=
  branch_upper a [2,4,7,6,8,1] 30 (by decide) (fin9_cases _
  node374
  (invalid_upper a [2,4,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,2] 30 (by decide +kernel))
  node375
  (invalid_upper a [2,4,7,6,8,1,4] 30 (by decide +kernel))
  node376
  (invalid_upper a [2,4,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,8] 30 (by decide +kernel)))

def cert378 : Leaf := ⟨⟨312,300,0,128,15,0,318,63,47⟩,[(5,3)],[(7,2,3),(6,3,5)],⟨7,19,140,76,304,104,193,418,306⟩,⟨7,19,140,76,304,104,193,384,272⟩,[⟨0,1210107567817139378193408,⟨6,18,172,108,312,108,236,384,272⟩⟩,⟨1,1210107567817139378192385,⟨5,17,172,108,312,108,237,384,272⟩⟩,⟨4,1210107567816039866565633,⟨7,3,172,108,296,108,237,384,256⟩⟩,⟨5,1210107564157964680954881,⟨7,19,140,76,280,76,205,384,272⟩⟩,⟨8,1181748202510203487233,⟨7,19,172,108,56,108,237,128,16⟩⟩]⟩
theorem node378 : UpperPrefix a [2,4,7,6,8,3,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,0] 30 cert378 (by decide +kernel)

def cert379 : Leaf := ⟨⟨8,300,2,130,15,0,317,63,47⟩,[(5,3)],[(7,2,3),(6,3,5)],⟨7,19,140,76,304,104,194,417,305⟩,⟨7,19,140,76,304,104,194,384,272⟩,[⟨4,1210107567816039866565697,⟨7,3,172,109,296,109,239,384,256⟩⟩,⟨5,1210107564157964680954945,⟨7,19,140,77,280,77,207,384,272⟩⟩,⟨8,1181748202510203487297,⟨7,19,172,109,56,109,239,128,16⟩⟩,⟨0,1210107567817139378193408,⟨6,18,172,108,312,108,238,384,272⟩⟩]⟩
theorem node379 : UpperPrefix a [2,4,7,6,8,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,1] 30 cert379 (by decide +kernel)

def cert380 : Leaf := ⟨⟨272,260,275,403,7,0,279,23,7⟩,[(5,3)],[(7,2,3),(6,3,5)],⟨7,19,140,76,304,104,224,387,275⟩,⟨7,19,140,76,304,104,224,384,272⟩,[⟨3,1408881320747833410737165,⟨391,467,391,471,498,499,498,384,336⟩⟩,⟨5,1297646588159753362482451,⟨391,407,140,76,415,76,204,387,407⟩⟩]⟩
theorem node380 : UpperPrefix a [2,4,7,6,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,5] 30 cert380 (by decide +kernel)

theorem node381 : UpperPrefix a [2,4,7,6,8,3] 30 :=
  branch_upper a [2,4,7,6,8,3] 30 (by decide) (fin9_cases _
  node378
  node379
  (invalid_upper a [2,4,7,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,4] 30 (by decide +kernel))
  node380
  (invalid_upper a [2,4,7,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,8] 30 (by decide +kernel)))

theorem node382 : UpperPrefix a [2,4,7,6,8] 30 :=
  branch_upper a [2,4,7,6,8] 30 (by decide) (fin9_cases _
  node373
  node377
  (invalid_upper a [2,4,7,6,8,2] 30 (by decide +kernel))
  node381
  (invalid_upper a [2,4,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,8] 30 (by decide +kernel)))

theorem node383 : UpperPrefix a [2,4,7,6] 30 :=
  branch_upper a [2,4,7,6] 30 (by decide) (fin9_cases _
  node359
  node366
  (invalid_upper a [2,4,7,6,2] 30 (by decide +kernel))
  node367
  (invalid_upper a [2,4,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,7] 30 (by decide +kernel))
  node382)

#print axioms node383
end Delivery.FiniteExclusion.Sharp2x2x5
