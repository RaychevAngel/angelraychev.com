import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C003
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert256 : Leaf := ⟨⟨0,104,434,242,67,18,306,114,226⟩,[(0,1)],[(2,0,0),(3,4,1),(0,5,4)],⟨7,22,76,265,56,97,226,418,434⟩,⟨7,22,76,265,56,97,192,384,272⟩,[⟨7,1208926973804146641079815,⟨55,55,127,267,56,99,64,256,272⟩⟩,⟨8,1181745810234877677063,⟨55,55,127,11,56,99,192,128,16⟩⟩]⟩
theorem node256 : UpperPrefix a [2,4,6,8,3,0] 30 :=
  Boolean.leaf_sound a [2,4,6,8,3,0] 30 cert256 (by decide +kernel)

def cert257 : Leaf := ⟨⟨0,104,435,178,2,16,307,51,163⟩,[(0,1)],[(2,0,0),(3,4,1)],⟨7,22,76,265,56,98,225,417,433⟩,⟨7,22,76,265,56,98,192,384,272⟩,[⟨6,1361517287721558397158403,⟨7,23,12,265,440,443,128,384,272⟩⟩,⟨0,1210107565424864052383232,⟨54,54,126,266,56,98,192,384,272⟩⟩,⟨7,1208926973804146641079815,⟨55,55,127,267,56,99,64,256,272⟩⟩,⟨8,1181745810234877677063,⟨55,55,127,11,56,99,192,128,16⟩⟩]⟩
theorem node257 : UpperPrefix a [2,4,6,8,3,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,3,1] 30 cert257 (by decide +kernel)

def cert258 : Leaf := ⟨⟨0,360,307,114,322,0,307,115,99⟩,[(0,1),(5,6)],[(2,0,0),(3,4,1),(7,5,5)],⟨7,22,76,265,56,224,227,419,307⟩,⟨7,22,76,265,56,224,192,384,272⟩,[⟨0,1210107567535926377713152,⟨22,22,126,266,56,224,224,384,272⟩⟩]⟩
theorem node258 : UpperPrefix a [2,4,6,8,3,7] 30 :=
  Boolean.leaf_sound a [2,4,6,8,3,7] 30 cert258 (by decide +kernel)

theorem node259 : UpperPrefix a [2,4,6,8,3] 30 :=
  branch_upper a [2,4,6,8,3] 30 (by decide) (fin9_cases _
  node256
  node257
  (invalid_upper a [2,4,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,6] 30 (by decide +kernel))
  node258
  (invalid_upper a [2,4,6,8,3,8] 30 (by decide +kernel)))

def cert260 : Leaf := ⟨⟨0,329,273,80,329,282,281,121,105⟩,[(0,1)],[(2,0,0),(1,6,5)],⟨7,22,76,265,176,97,194,424,312⟩,⟨7,22,76,265,176,97,194,384,272⟩,[⟨7,1293929572747370715685971,⟨303,319,109,265,319,109,367,264,283⟩⟩,⟨5,1210110158231388806063579,⟨7,87,77,271,223,69,207,463,351⟩⟩]⟩
theorem node260 : UpperPrefix a [2,4,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,0,1] 30 cert260 (by decide +kernel)

def cert261 : Local := ⟨⟨0,225,0,242,67,146,307,115,227⟩,[(0,1),(2,6)],[(2,0,0),(8,3,6),(3,6,2)]⟩
theorem node261 : UpperPrefix a [2,4,6,8,7,0,3] 30 :=
  local_sound a [2,4,6,8,7,0,3] 30 cert261 (by decide +kernel)

def cert262 : Leaf := ⟨⟨0,457,403,210,0,410,0,91,203⟩,[(0,1),(4,6),(6,4)],[(2,0,0)],⟨7,22,76,265,176,97,224,394,282⟩,⟨7,22,76,265,176,97,224,384,272⟩,[⟨5,1297646588159777374741523,⟨399,415,76,393,415,205,196,392,411⟩⟩]⟩
theorem node262 : UpperPrefix a [2,4,6,8,7,0,5] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,0,5] 30 cert262 (by decide +kernel)

theorem node263 : UpperPrefix a [2,4,6,8,7,0] 30 :=
  branch_upper a [2,4,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,8,7,0,0] 30 (by decide +kernel))
  node260
  (invalid_upper a [2,4,6,8,7,0,2] 30 (by decide +kernel))
  node261
  (invalid_upper a [2,4,6,8,7,0,4] 30 (by decide +kernel))
  node262
  (invalid_upper a [2,4,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,0,8] 30 (by decide +kernel)))

def cert264 : Leaf := ⟨⟨0,328,275,18,266,408,282,58,42⟩,[(0,1)],[(2,0,0),(0,6,2)],⟨7,22,76,265,176,98,193,424,312⟩,⟨7,22,76,265,176,98,193,384,272⟩,[⟨5,1210110158231388806063547,⟨7,87,77,271,223,71,205,463,351⟩⟩,⟨6,1437222725400062665425923,⟨15,415,12,265,440,443,129,384,400⟩⟩,⟨7,1284484837389085382288435,⟨15,287,76,265,319,111,65,264,283⟩⟩]⟩
theorem node264 : UpperPrefix a [2,4,6,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,1,0] 30 cert264 (by decide +kernel)

def cert265 : Local := ⟨⟨0,225,0,242,67,145,307,115,227⟩,[(0,1),(2,6)],[(2,0,0),(8,3,6),(3,6,2)]⟩
theorem node265 : UpperPrefix a [2,4,6,8,7,1,3] 30 :=
  local_sound a [2,4,6,8,7,1,3] 30 cert265 (by decide +kernel)

def cert266 : Leaf := ⟨⟨0,457,403,210,0,409,0,91,203⟩,[(0,1),(4,6),(6,4)],[(2,0,0)],⟨7,22,76,265,176,98,224,393,281⟩,⟨7,22,76,265,176,98,224,384,272⟩,[⟨5,1298015523041255877518387,⟨399,415,204,393,415,463,205,392,411⟩⟩]⟩
theorem node266 : UpperPrefix a [2,4,6,8,7,1,5] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,1,5] 30 cert266 (by decide +kernel)

theorem node267 : UpperPrefix a [2,4,6,8,7,1] 30 :=
  branch_upper a [2,4,6,8,7,1] 30 (by decide) (fin9_cases _
  node264
  (invalid_upper a [2,4,6,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,1,2] 30 (by decide +kernel))
  node265
  (invalid_upper a [2,4,6,8,7,1,4] 30 (by decide +kernel))
  node266
  (invalid_upper a [2,4,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,1,8] 30 (by decide +kernel)))

def cert268 : Leaf := ⟨⟨0,329,0,82,331,0,315,123,107⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,22,76,265,176,104,227,419,307⟩,⟨7,22,76,265,176,104,192,384,272⟩,[⟨7,1293929570495562295288851,⟨303,319,108,265,319,108,64,264,283⟩⟩,⟨5,1210107564157986147410963,⟨7,23,76,265,151,76,192,392,283⟩⟩]⟩
theorem node268 : UpperPrefix a [2,4,6,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,3] 30 cert268 (by decide +kernel)

theorem node269 : UpperPrefix a [2,4,6,8,7] 30 :=
  branch_upper a [2,4,6,8,7] 30 (by decide) (fin9_cases _
  node263
  node267
  (invalid_upper a [2,4,6,8,7,2] 30 (by decide +kernel))
  node268
  (invalid_upper a [2,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,8] 30 (by decide +kernel)))

theorem node270 : UpperPrefix a [2,4,6,8] 30 :=
  branch_upper a [2,4,6,8] 30 (by decide) (fin9_cases _
  node251
  node255
  (invalid_upper a [2,4,6,8,2] 30 (by decide +kernel))
  node259
  (invalid_upper a [2,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,6] 30 (by decide +kernel))
  node269
  (invalid_upper a [2,4,6,8,8] 30 (by decide +kernel)))

theorem node271 : UpperPrefix a [2,4,6] 30 :=
  branch_upper a [2,4,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [2,4,6,1] [2,3,4,6] 30 (by decide +kernel) node61)
  (invalid_upper a [2,4,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,4] 30 (by decide +kernel))
  node212
  (invalid_upper a [2,4,6,6] 30 (by decide +kernel))
  node244
  node270)

def cert272 : Leaf := ⟨⟨0,489,353,0,0,409,297,105,233⟩,[(0,1),(3,4),(4,3)],[(2,0,0),(1,5,3),(1,5,4)],⟨7,22,140,41,49,98,456,456,344⟩,⟨7,22,140,41,49,98,192,384,272⟩,[⟨4,1212473360210211934045187,⟨7,15,140,41,41,107,192,452,460⟩⟩]⟩
theorem node272 : UpperPrefix a [2,4,7,5,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,0,1] 30 cert272 (by decide +kernel)

def cert273 : Leaf := ⟨⟨0,489,370,0,0,402,314,122,234⟩,[(0,1),(3,4),(4,3)],[(2,0,0)],⟨7,22,140,41,49,104,450,450,338⟩,⟨7,22,140,41,49,104,192,384,272⟩,[⟨0,1219580022690372048126976,⟨454,470,172,236,240,108,192,384,272⟩⟩]⟩
theorem node273 : UpperPrefix a [2,4,7,5,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,0,3] 30 cert273 (by decide +kernel)

def cert274 : Leaf := ⟨⟨0,33,371,0,0,155,59,123,235⟩,[(0,1),(3,4),(4,3)],[(2,0,0)],⟨7,22,140,41,49,352,202,458,346⟩,⟨7,22,140,41,49,352,192,384,272⟩,[⟨8,1181817727368452639751,⟨71,95,223,57,57,96,192,128,24⟩⟩,⟨3,1210107565284400368192519,⟨7,23,151,49,49,352,192,384,272⟩⟩,⟨6,1210106412362898982571015,⟨7,31,159,57,57,288,128,384,280⟩⟩,⟨7,1208926973663686178114567,⟨7,31,31,57,57,352,64,256,280⟩⟩]⟩
theorem node274 : UpperPrefix a [2,4,7,5,0,8] 30 :=
  Boolean.leaf_sound a [2,4,7,5,0,8] 30 cert274 (by decide +kernel)

theorem node275 : UpperPrefix a [2,4,7,5,0] 30 :=
  branch_upper a [2,4,7,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,0,0] 30 (by decide +kernel))
  node272
  (invalid_upper a [2,4,7,5,0,2] 30 (by decide +kernel))
  node273
  (invalid_upper a [2,4,7,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,7] 30 (by decide +kernel))
  node274)

def cert276 : Leaf := ⟨⟨0,488,368,0,456,410,312,120,232⟩,[(0,1),(3,5)],[(2,0,0),(0,5,3)],⟨7,22,140,41,50,97,456,456,344⟩,⟨7,22,140,41,50,97,192,384,272⟩,[⟨1,1285813291192736136822785,⟨5,468,140,41,508,105,192,384,468⟩⟩]⟩
theorem node276 : UpperPrefix a [2,4,7,5,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,0] 30 cert276 (by decide +kernel)

def cert277 : Leaf := ⟨⟨0,233,83,2,201,147,275,83,195⟩,[(0,1)],[(2,0,0)],⟨7,22,140,41,50,104,449,449,337⟩,⟨7,22,140,41,50,104,192,384,272⟩,[⟨8,1181747928184199892071,⟨7,31,159,59,59,127,255,128,24⟩⟩,⟨5,1295285747191877316117507,⟨455,471,140,205,467,76,192,384,464⟩⟩,⟨3,1295285748317776147121155,⟨455,471,132,225,499,96,192,384,464⟩⟩,⟨4,1210107565282754321974275,⟨7,15,140,41,43,104,192,384,264⟩⟩,⟨6,1210106412362349226755075,⟨7,31,140,41,59,40,128,384,280⟩⟩,⟨7,1208926973663136422298627,⟨7,31,12,41,59,104,64,256,280⟩⟩]⟩
theorem node277 : UpperPrefix a [2,4,7,5,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,3] 30 cert277 (by decide +kernel)

def cert278 : Leaf := ⟨⟨0,480,0,466,448,146,306,114,226⟩,[(0,1),(2,7)],[(2,0,0),(3,7,2)],⟨7,22,140,41,50,352,193,392,336⟩,⟨7,22,140,41,50,352,193,392,272⟩,[⟨0,1663528536874579139861504,⟨6,22,158,446,306,370,502,414,272⟩⟩]⟩
theorem node278 : UpperPrefix a [2,4,7,5,1,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,8,0,3] 30 cert278 (by decide +kernel)

def cert279 : Leaf := ⟨⟨0,488,370,466,456,0,314,0,234⟩,[(0,1),(5,7),(7,5)],[(2,0,0)],⟨7,22,140,41,50,352,193,448,280⟩,⟨7,22,140,41,50,352,193,448,272⟩,[⟨0,1267071115492289091214848,⟨278,278,446,446,178,496,242,496,272⟩⟩]⟩
theorem node279 : UpperPrefix a [2,4,7,5,1,8,0,6] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,8,0,6] 30 cert279 (by decide +kernel)

theorem node280 : UpperPrefix a [2,4,7,5,1,8,0] 30 :=
  branch_upper a [2,4,7,5,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,0,2] 30 (by decide +kernel))
  node278
  (invalid_upper a [2,4,7,5,1,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,0,5] 30 (by decide +kernel))
  node279
  (invalid_upper a [2,4,7,5,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,0,8] 30 (by decide +kernel)))

def cert281 : Leaf := ⟨⟨0,489,0,450,457,139,0,107,235⟩,[(0,1),(2,6),(6,2)],[(2,0,0)],⟨7,22,140,41,50,352,200,449,337⟩,⟨7,22,140,41,50,352,200,384,272⟩,[⟨4,1212476328082396494693395,⟨71,79,236,109,111,492,236,492,493⟩⟩]⟩
theorem node281 : UpperPrefix a [2,4,7,5,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,8,3] 30 cert281 (by decide +kernel)

theorem node282 : UpperPrefix a [2,4,7,5,1,8] 30 :=
  branch_upper a [2,4,7,5,1,8] 30 (by decide) (fin9_cases _
  node280
  (invalid_upper a [2,4,7,5,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,2] 30 (by decide +kernel))
  node281
  (invalid_upper a [2,4,7,5,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,8,8] 30 (by decide +kernel)))

theorem node283 : UpperPrefix a [2,4,7,5,1] 30 :=
  branch_upper a [2,4,7,5,1] 30 (by decide) (fin9_cases _
  node276
  (invalid_upper a [2,4,7,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,2] 30 (by decide +kernel))
  node277
  (invalid_upper a [2,4,7,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,7] 30 (by decide +kernel))
  node282)

def cert284 : Leaf := ⟨⟨0,392,339,466,0,403,275,83,195⟩,[(0,1),(4,3)],[(2,0,0),(5,3,4),(3,4,1)],⟨7,22,140,41,56,355,451,451,339⟩,⟨7,22,140,41,56,96,192,384,272⟩,[⟨0,1210107565284401441934336,⟨6,22,158,56,56,96,192,384,272⟩⟩,⟨6,1210106412362896835087367,⟨7,23,159,57,56,32,128,384,272⟩⟩]⟩
theorem node284 : UpperPrefix a [2,4,7,5,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,3] 30 cert284 (by decide +kernel)

def cert285 : Local := ⟨⟨0,424,306,0,0,410,314,58,170⟩,[(0,1),(3,5),(4,5)],[(2,0,0),(6,4,4),(0,5,3)]⟩
theorem node285 : UpperPrefix a [2,4,7,5,6,0] 30 :=
  local_sound a [2,4,7,5,6,0] 30 cert285 (by decide +kernel)

def cert286 : Leaf := ⟨⟨0,169,49,146,0,153,313,57,169⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(1,5,3)],⟨7,22,140,41,112,98,457,393,281⟩,⟨7,22,140,41,112,98,192,384,272⟩,[⟨8,1181748490619059233907,⟨15,63,140,59,127,127,255,140,59⟩⟩]⟩
theorem node286 : UpperPrefix a [2,4,7,5,6,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,1] 30 cert286 (by decide +kernel)

def cert287 : Leaf := ⟨⟨0,417,275,402,0,403,275,19,131⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,22,140,41,112,104,451,387,275⟩,⟨7,22,140,41,112,104,192,384,272⟩,[⟨3,1238506453888864812534791,⟨455,471,471,241,112,112,192,384,272⟩⟩,⟨5,1219580021282997164573699,⟨455,471,140,205,80,76,192,384,272⟩⟩]⟩
theorem node287 : UpperPrefix a [2,4,7,5,6,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,3] 30 cert287 (by decide +kernel)

def cert288 : Leaf := ⟨⟨0,424,306,402,0,155,314,58,170⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,22,140,41,112,352,193,394,282⟩,⟨7,22,140,41,112,352,193,384,272⟩,[⟨0,1247997177613450130494464,⟨134,150,398,446,112,368,192,384,272⟩⟩]⟩
theorem node288 : UpperPrefix a [2,4,7,5,6,8,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,8,0] 30 cert288 (by decide +kernel)

def cert289 : Leaf := ⟨⟨0,425,305,274,0,27,313,57,41⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,22,140,41,112,352,194,393,281⟩,⟨7,22,140,41,112,352,194,384,272⟩,[⟨1,1247960284125302711386113,⟨5,20,396,445,112,368,192,384,272⟩⟩,⟨7,1558382096216843715871747,⟨271,319,268,313,376,376,379,256,304⟩⟩]⟩
theorem node289 : UpperPrefix a [2,4,7,5,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,8,1] 30 cert289 (by decide +kernel)

def cert290 : Local := ⟨⟨0,425,0,402,0,155,0,59,171⟩,[(0,1),(2,6),(4,5),(6,2)],[(2,0,0),(6,4,4)]⟩
theorem node290 : UpperPrefix a [2,4,7,5,6,8,3] 30 :=
  local_sound a [2,4,7,5,6,8,3] 30 cert290 (by decide +kernel)

theorem node291 : UpperPrefix a [2,4,7,5,6,8] 30 :=
  branch_upper a [2,4,7,5,6,8] 30 (by decide) (fin9_cases _
  node288
  node289
  (invalid_upper a [2,4,7,5,6,8,2] 30 (by decide +kernel))
  node290
  (invalid_upper a [2,4,7,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,8] 30 (by decide +kernel)))

theorem node292 : UpperPrefix a [2,4,7,5,6] 30 :=
  branch_upper a [2,4,7,5,6] 30 (by decide) (fin9_cases _
  node285
  node286
  (invalid_upper a [2,4,7,5,6,2] 30 (by decide +kernel))
  node287
  (invalid_upper a [2,4,7,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,7] 30 (by decide +kernel))
  node291)

def cert293 : Local := ⟨⟨0,488,368,0,200,410,312,120,232⟩,[(0,1),(3,5)],[(2,0,0),(0,5,3),(1,6,5)]⟩
theorem node293 : UpperPrefix a [2,4,7,5,8,0,1] 30 :=
  local_sound a [2,4,7,5,8,0,1] 30 cert293 (by decide +kernel)

def cert294 : Local := ⟨⟨0,488,0,0,202,410,0,122,234⟩,[(0,1),(2,6),(3,5),(6,2)],[(2,0,0),(0,5,3)]⟩
theorem node294 : UpperPrefix a [2,4,7,5,8,0,3] 30 :=
  local_sound a [2,4,7,5,8,0,3] 30 cert294 (by decide +kernel)

theorem node295 : UpperPrefix a [2,4,7,5,8,0] 30 :=
  branch_upper a [2,4,7,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,8,0,0] 30 (by decide +kernel))
  node293
  (invalid_upper a [2,4,7,5,8,0,2] 30 (by decide +kernel))
  node294
  (invalid_upper a [2,4,7,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,8] 30 (by decide +kernel)))

def cert296 : Leaf := ⟨⟨0,361,353,258,73,393,297,105,105⟩,[(0,1)],[(2,0,0),(1,5,3)],⟨7,22,140,41,304,98,201,457,345⟩,⟨7,22,140,41,304,98,192,384,272⟩,[⟨4,1210255463600075054777379,⟨111,239,140,41,493,111,192,388,460⟩⟩,⟨7,1360042701117715995692039,⟨7,23,31,313,312,379,64,256,272⟩⟩,⟨6,1210106412362351374238723,⟨7,23,140,41,312,43,128,384,272⟩⟩]⟩
theorem node296 : UpperPrefix a [2,4,7,5,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,1] 30 cert296 (by decide +kernel)

def cert297 : Leaf := ⟨⟨0,488,336,464,202,401,274,82,194⟩,[(0,1)],[(2,0,0),(0,6,5)],⟨7,22,140,41,304,104,193,450,338⟩,⟨7,22,140,41,304,104,193,384,272⟩,[⟨5,1219580165398185240429571,⟨455,471,204,205,272,76,193,384,272⟩⟩,⟨1,1210107567535660106514433,⟨5,20,140,41,304,108,237,384,272⟩⟩,⟨3,1219580166524084071433219,⟨455,471,196,225,304,96,193,384,272⟩⟩]⟩
theorem node297 : UpperPrefix a [2,4,7,5,8,3,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,3,0] 30 cert297 (by decide +kernel)

def cert298 : Leaf := ⟨⟨0,449,339,338,67,275,273,83,67⟩,[(0,1)],[(2,0,0)],⟨7,22,140,41,304,104,194,449,337⟩,⟨7,22,140,41,304,104,194,384,272⟩,[⟨3,1276949468538475518102535,⟨455,471,471,497,304,496,451,384,272⟩⟩,⟨5,1298241837929689280160787,⟨455,471,140,205,471,204,451,448,467⟩⟩,⟨7,1511158430825197041878019,⟨7,23,12,57,304,376,379,256,272⟩⟩]⟩
theorem node298 : UpperPrefix a [2,4,7,5,8,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,3,1] 30 cert298 (by decide +kernel)

theorem node299 : UpperPrefix a [2,4,7,5,8,3] 30 :=
  branch_upper a [2,4,7,5,8,3] 30 (by decide) (fin9_cases _
  node297
  node298
  (invalid_upper a [2,4,7,5,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,8] 30 (by decide +kernel)))

theorem node300 : UpperPrefix a [2,4,7,5,8] 30 :=
  branch_upper a [2,4,7,5,8] 30 (by decide) (fin9_cases _
  node295
  node296
  (invalid_upper a [2,4,7,5,8,2] 30 (by decide +kernel))
  node299
  (invalid_upper a [2,4,7,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,8] 30 (by decide +kernel)))

theorem node301 : UpperPrefix a [2,4,7,5] 30 :=
  branch_upper a [2,4,7,5] 30 (by decide) (fin9_cases _
  node275
  node283
  (invalid_upper a [2,4,7,5,2] 30 (by decide +kernel))
  node284
  (invalid_upper a [2,4,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,5] 30 (by decide +kernel))
  node292
  (invalid_upper a [2,4,7,5,7] 30 (by decide +kernel))
  node300)

def cert302 : Leaf := ⟨⟨0,105,113,48,74,25,313,121,105⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,22,140,73,49,98,488,424,312⟩,⟨7,22,140,73,49,98,192,384,272⟩,[⟨7,1492268962919815916293639,⟨279,279,319,379,315,379,64,256,272⟩⟩,⟨8,1181748209931907030639,⟨23,23,191,127,59,127,255,128,16⟩⟩]⟩
theorem node302 : UpperPrefix a [2,4,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,1] 30 cert302 (by decide +kernel)

def cert303 : Leaf := ⟨⟨0,41,51,178,10,0,315,59,43⟩,[(0,1),(5,3)],[(2,0,0),(6,3,5)],⟨7,22,140,73,49,104,482,418,306⟩,⟨7,22,140,73,49,104,192,384,272⟩,[⟨8,1181748209931907030639,⟨23,23,191,127,59,127,255,128,16⟩⟩,⟨7,1341153235465783951232519,⟨279,279,319,379,307,376,64,256,272⟩⟩]⟩
theorem node303 : UpperPrefix a [2,4,7,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,3] 30 cert303 (by decide +kernel)

def cert304 : Leaf := ⟨⟨0,105,113,50,72,25,313,121,105⟩,[(0,1)],[(2,0,0),(1,6,3)],⟨7,22,140,73,49,352,194,424,312⟩,⟨7,22,140,73,49,352,194,384,272⟩,[⟨7,1718942556351562018459143,⟨279,279,319,379,307,376,379,256,272⟩⟩,⟨8,1181745671434436363363,⟨7,23,140,77,59,127,207,128,16⟩⟩]⟩
theorem node304 : UpperPrefix a [2,4,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,1] 30 cert304 (by decide +kernel)

def cert305 : Leaf := ⟨⟨0,481,0,434,450,147,0,115,227⟩,[(0,1),(2,6),(6,2)],[(2,0,0)],⟨7,22,140,73,49,352,200,418,306⟩,⟨7,22,140,73,49,352,200,384,272⟩,[⟨3,1342592083755332036201991,⟨407,407,439,499,435,352,496,384,400⟩⟩]⟩
theorem node305 : UpperPrefix a [2,4,7,6,0,8,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,3] 30 cert305 (by decide +kernel)

def cert306 : Leaf := ⟨⟨0,65,83,146,66,19,275,91,75⟩,[(0,1)],[(2,0,0),(8,5,6)],⟨7,22,140,73,49,352,224,394,282⟩,⟨7,22,140,73,49,352,224,384,272⟩,[⟨5,1286108149741648046335283,⟨7,407,140,77,415,463,205,387,407⟩⟩,⟨3,1210109947688328369278471,⟨87,87,247,67,51,352,224,480,272⟩⟩,⟨7,1265595371739869627813383,⟨279,279,319,379,51,352,96,256,272⟩⟩]⟩
theorem node306 : UpperPrefix a [2,4,7,6,0,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,5] 30 cert306 (by decide +kernel)

theorem node307 : UpperPrefix a [2,4,7,6,0,8] 30 :=
  branch_upper a [2,4,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,0,8,0] 30 (by decide +kernel))
  node304
  (invalid_upper a [2,4,7,6,0,8,2] 30 (by decide +kernel))
  node305
  (invalid_upper a [2,4,7,6,0,8,4] 30 (by decide +kernel))
  node306
  (invalid_upper a [2,4,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,8] 30 (by decide +kernel)))

theorem node308 : UpperPrefix a [2,4,7,6,0] 30 :=
  branch_upper a [2,4,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,0,0] 30 (by decide +kernel))
  node302
  (invalid_upper a [2,4,7,6,0,2] 30 (by decide +kernel))
  node303
  (invalid_upper a [2,4,7,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,7] 30 (by decide +kernel))
  node307)

def cert309 : Leaf := ⟨⟨0,361,369,0,329,0,313,121,105⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,22,140,73,50,97,488,424,312⟩,⟨7,22,140,73,50,97,192,384,272⟩,[⟨1,1285813291474211113533441,⟨5,468,172,105,508,105,192,384,468⟩⟩,⟨7,1492268962919815916293639,⟨279,279,319,379,315,379,64,256,272⟩⟩]⟩
theorem node309 : UpperPrefix a [2,4,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,0] 30 cert309 (by decide +kernel)

def cert310 : Leaf := ⟨⟨0,169,51,178,137,0,307,51,163⟩,[(0,1),(5,3)],[(2,0,0),(6,3,5)],⟨7,22,140,73,50,104,481,417,305⟩,⟨7,22,140,73,50,104,192,384,272⟩,[⟨8,1181748209931907030639,⟨23,23,191,127,59,127,255,128,16⟩⟩,⟨3,1285813291192730763920387,⟨7,471,132,65,499,96,192,384,464⟩⟩]⟩
theorem node310 : UpperPrefix a [2,4,7,6,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,3] 30 cert310 (by decide +kernel)

def cert311 : Leaf := ⟨⟨0,488,354,0,456,138,298,106,234⟩,[(0,1),(3,6)],[(2,0,0),(0,6,3)],⟨7,22,140,73,50,352,193,424,312⟩,⟨7,22,140,73,50,352,193,384,272⟩,[⟨4,1212768809856605306749971,⟨15,79,172,77,239,492,237,492,493⟩⟩]⟩
theorem node311 : UpperPrefix a [2,4,7,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,0] 30 cert311 (by decide +kernel)

def cert312 : Leaf := ⟨⟨0,481,0,434,449,147,0,115,227⟩,[(0,1),(2,6),(6,2)],[(2,0,0)],⟨7,22,140,73,50,352,200,417,305⟩,⟨7,22,140,73,50,352,200,384,272⟩,[⟨3,1342592083755332036201991,⟨407,407,439,499,435,352,496,384,400⟩⟩]⟩
theorem node312 : UpperPrefix a [2,4,7,6,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,3] 30 cert312 (by decide +kernel)

def cert313 : Leaf := ⟨⟨0,201,67,130,201,139,267,75,203⟩,[(0,1)],[(2,0,0),(8,5,6)],⟨7,22,140,73,50,352,224,393,281⟩,⟨7,22,140,73,50,352,224,384,272⟩,[⟨4,1212476328082396880569363,⟨79,79,236,73,111,492,228,492,493⟩⟩,⟨5,1286108149741648046335283,⟨7,407,140,77,415,463,205,387,407⟩⟩]⟩
theorem node313 : UpperPrefix a [2,4,7,6,1,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,5] 30 cert313 (by decide +kernel)

theorem node314 : UpperPrefix a [2,4,7,6,1,8] 30 :=
  branch_upper a [2,4,7,6,1,8] 30 (by decide) (fin9_cases _
  node311
  (invalid_upper a [2,4,7,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,2] 30 (by decide +kernel))
  node312
  (invalid_upper a [2,4,7,6,1,8,4] 30 (by decide +kernel))
  node313
  (invalid_upper a [2,4,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,8] 30 (by decide +kernel)))

theorem node315 : UpperPrefix a [2,4,7,6,1] 30 :=
  branch_upper a [2,4,7,6,1] 30 (by decide) (fin9_cases _
  node309
  (invalid_upper a [2,4,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,2] 30 (by decide +kernel))
  node310
  (invalid_upper a [2,4,7,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,7] 30 (by decide +kernel))
  node314)

def cert316 : Local := ⟨⟨0,424,306,0,451,0,306,50,162⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(6,3,4),(3,4,1),(0,5,4)]⟩
theorem node316 : UpperPrefix a [2,4,7,6,3,0] 30 :=
  local_sound a [2,4,7,6,3,0] 30 cert316 (by decide +kernel)

def cert317 : Leaf := ⟨⟨0,41,51,50,67,17,307,51,35⟩,[(0,1)],[(2,0,0),(6,3,4),(3,4,1)],⟨7,22,140,73,56,98,481,417,305⟩,⟨7,22,140,73,56,98,192,384,272⟩,[⟨7,1416711099193901592874503,⟨279,279,319,379,312,379,64,256,272⟩⟩,⟨8,1181748209931907030639,⟨23,23,191,127,59,127,255,128,16⟩⟩]⟩
theorem node317 : UpperPrefix a [2,4,7,6,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,1] 30 cert317 (by decide +kernel)

def cert318 : Local := ⟨⟨0,424,306,0,450,146,306,50,162⟩,[(0,1),(3,6)],[(2,0,0),(6,3,4),(3,4,1),(0,6,3)]⟩
theorem node318 : UpperPrefix a [2,4,7,6,3,8,0] 30 :=
  local_sound a [2,4,7,6,3,8,0] 30 cert318 (by decide +kernel)

def cert319 : Leaf := ⟨⟨0,297,305,306,321,17,305,49,33⟩,[(0,1)],[(2,0,0),(6,3,4),(3,4,1),(1,6,3)],⟨7,22,140,73,56,352,194,417,305⟩,⟨7,22,140,73,56,352,194,384,272⟩,[⟨7,1567826828901932394876423,⟨279,279,319,379,312,376,379,256,272⟩⟩]⟩
theorem node319 : UpperPrefix a [2,4,7,6,3,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,8,1] 30 cert319 (by decide +kernel)

#print axioms node319
end Delivery.FiniteExclusion.Sharp4x5
