import RegularNineSharp2x7Base
import RegularNineSharp2x7C016
import RegularNineSharp2x7C017
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert1152 : Leaf := ⟨⟨312,280,306,162,0,0,314,58,186⟩,[(4,5),(5,4)],[(0,2,0),(6,4,4),(6,4,5)],⟨7,35,13,280,112,112,202,394,398⟩,⟨7,35,13,280,112,112,192,384,260⟩,[⟨2,1212473376851915205250049,⟨3,51,59,504,112,112,248,504,506⟩⟩,⟨7,1208926976484481113789453,⟨7,51,15,319,112,112,112,256,261⟩⟩]⟩
theorem node1152 : UpperPrefix a [2,5,0,8,6,4] 30 :=
  Boolean.leaf_sound a [2,5,0,8,6,4] 30 cert1152 (by decide +kernel)

def cert1153 : Local := ⟨⟨312,284,306,38,0,0,318,62,58⟩,[(4,5),(5,6)],[(0,2,0),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node1153 : UpperPrefix a [2,5,0,8,6,7] 30 :=
  local_sound a [2,5,0,8,6,7] 30 cert1153 (by decide +kernel)

theorem node1154 : UpperPrefix a [2,5,0,8,6] 30 :=
  branch_upper a [2,5,0,8,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,8,6,0] 30 (by decide +kernel))
  node1150
  (invalid_upper a [2,5,0,8,6,2] 30 (by decide +kernel))
  node1151
  node1152
  (invalid_upper a [2,5,0,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,6,6] 30 (by decide +kernel))
  node1153
  (invalid_upper a [2,5,0,8,6,8] 30 (by decide +kernel)))

def cert1155 : Leaf := ⟨⟨232,200,224,224,72,136,304,120,248⟩,[],[(0,2,0),(8,3,6),(1,5,1)],⟨7,35,13,280,176,98,200,464,340⟩,⟨7,35,13,280,176,98,200,384,260⟩,[⟨2,1212549966644152820043265,⟨115,35,251,504,248,98,216,504,506⟩⟩,⟨4,1210107567534552007107689,⟨7,35,13,271,163,103,239,384,260⟩⟩]⟩
theorem node1155 : UpperPrefix a [2,5,0,8,7,1,3] 30 :=
  Boolean.leaf_sound a [2,5,0,8,7,1,3] 30 cert1155 (by decide +kernel)

def cert1156 : Leaf := ⟨⟨376,344,368,96,328,280,0,120,120⟩,[(6,4)],[(0,2,0),(7,4,6),(1,5,1)],⟨7,35,13,280,176,98,208,456,332⟩,⟨7,35,13,280,176,98,208,384,260⟩,[⟨2,1212549966644152820043265,⟨115,35,251,504,248,98,216,504,506⟩⟩]⟩
theorem node1156 : UpperPrefix a [2,5,0,8,7,1,4] 30 :=
  Boolean.leaf_sound a [2,5,0,8,7,1,4] 30 cert1156 (by decide +kernel)

theorem node1157 : UpperPrefix a [2,5,0,8,7,1] 30 :=
  branch_upper a [2,5,0,8,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,8,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,1,2] 30 (by decide +kernel))
  node1155
  node1156
  (invalid_upper a [2,5,0,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,1,8] 30 (by decide +kernel)))

def cert1158 : Leaf := ⟨⟨168,136,162,226,322,146,50,114,242⟩,[],[(0,2,0)],⟨7,35,13,280,176,104,210,466,342⟩,⟨7,35,13,280,176,104,192,384,260⟩,[⟨2,1212473376286766228573185,⟨3,35,59,504,184,120,248,504,506⟩⟩,⟨8,1182034181073650351423,⟨7,39,47,127,247,111,192,129,7⟩⟩,⟨3,1214857655926163789317121,⟨471,499,453,272,176,96,192,384,260⟩⟩,⟨4,1210107565282752185001019,⟨7,39,13,271,167,111,192,384,260⟩⟩,⟨6,1210106412362347089781819,⟨7,39,13,287,183,47,128,384,260⟩⟩]⟩
theorem node1158 : UpperPrefix a [2,5,0,8,7,3] 30 :=
  Boolean.leaf_sound a [2,5,0,8,7,3] 30 cert1158 (by decide +kernel)

def cert1159 : Leaf := ⟨⟨344,344,336,64,328,392,280,88,88⟩,[],[(0,2,0),(7,4,5)],⟨7,35,13,280,176,112,194,456,332⟩,⟨7,35,13,280,176,112,194,384,260⟩,[⟨1,1513224466161594246103041,⟨21,189,13,280,184,504,508,384,260⟩⟩,⟨2,1212547235496851843059201,⟨115,35,251,504,184,112,250,504,506⟩⟩,⟨5,1389908032687600758686787,⟨455,463,461,280,412,477,455,384,388⟩⟩]⟩
theorem node1159 : UpperPrefix a [2,5,0,8,7,4,1] 30 :=
  Boolean.leaf_sound a [2,5,0,8,7,4,1] 30 cert1159 (by decide +kernel)

def cert1160 : Leaf := ⟨⟨104,72,98,98,74,138,290,106,106⟩,[],[(0,2,0),(8,3,6),(7,4,5)],⟨7,35,13,280,176,112,200,450,326⟩,⟨7,35,13,280,176,112,200,384,260⟩,[⟨2,1212476115179027111611905,⟨35,35,123,504,248,112,248,504,506⟩⟩,⟨4,1404102965506700806743081,⟨455,419,461,463,419,487,461,384,324⟩⟩]⟩
theorem node1160 : UpperPrefix a [2,5,0,8,7,4,3] 30 :=
  Boolean.leaf_sound a [2,5,0,8,7,4,3] 30 cert1160 (by decide +kernel)

theorem node1161 : UpperPrefix a [2,5,0,8,7,4] 30 :=
  branch_upper a [2,5,0,8,7,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,8,7,4,0] 30 (by decide +kernel))
  node1159
  (invalid_upper a [2,5,0,8,7,4,2] 30 (by decide +kernel))
  node1160
  (invalid_upper a [2,5,0,8,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,4,8] 30 (by decide +kernel)))

theorem node1162 : UpperPrefix a [2,5,0,8,7] 30 :=
  branch_upper a [2,5,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,8,7,0] 30 (by decide +kernel))
  node1157
  (invalid_upper a [2,5,0,8,7,2] 30 (by decide +kernel))
  node1158
  node1161
  (invalid_upper a [2,5,0,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,7,8] 30 (by decide +kernel)))

theorem node1163 : UpperPrefix a [2,5,0,8] 30 :=
  branch_upper a [2,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,8,0] 30 (by decide +kernel))
  node1145
  (invalid_upper a [2,5,0,8,2] 30 (by decide +kernel))
  node1149
  (invalid_upper a [2,5,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,5] 30 (by decide +kernel))
  node1154
  node1162
  (invalid_upper a [2,5,0,8,8] 30 (by decide +kernel)))

theorem node1164 : UpperPrefix a [2,5,0] 30 :=
  branch_upper a [2,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,0] 30 (by decide +kernel))
  node1083
  (invalid_upper a [2,5,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,5] 30 (by decide +kernel))
  node1108
  node1141
  node1163)

def cert1165 : Leaf := ⟨⟨0,28,49,36,4,412,316,124,248⟩,[(0,2)],[(1,2,0),(0,3,2)],⟨7,35,14,25,56,496,464,464,468⟩,⟨7,35,14,25,56,96,192,384,260⟩,[⟨6,1210106412364690938946623,⟨31,63,31,31,63,63,128,384,269⟩⟩,⟨7,1208926973665478134490175,⟨31,63,31,31,63,127,64,256,269⟩⟩,⟨8,1181745671566371087423,⟨31,63,31,31,63,127,192,128,13⟩⟩]⟩
theorem node1165 : UpperPrefix a [2,5,1,0,3] 30 :=
  Boolean.leaf_sound a [2,5,1,0,3] 30 cert1165 (by decide +kernel)

def cert1166 : Leaf := ⟨⟨0,284,305,292,0,412,316,60,184⟩,[(0,2),(4,5)],[(1,2,0),(0,3,2),(6,4,4)],⟨7,35,14,25,112,504,472,408,412⟩,⟨7,35,14,25,112,96,192,384,260⟩,[⟨7,1208926973665340024448063,⟨15,63,15,31,127,127,64,256,261⟩⟩]⟩
theorem node1166 : UpperPrefix a [2,5,1,0,6] 30 :=
  Boolean.leaf_sound a [2,5,1,0,6] 30 cert1166 (by decide +kernel)

def cert1167 : Leaf := ⟨⟨0,156,177,164,68,148,308,116,240⟩,[(0,2)],[(1,2,0),(0,3,2)],⟨7,35,14,25,176,104,464,464,340⟩,⟨7,35,14,25,176,104,192,384,260⟩,[⟨8,1181747925435436033151,⟨7,47,15,31,191,127,255,128,5⟩⟩,⟨3,1233858018497065764520965,⟨471,499,471,465,176,240,192,384,453⟩⟩,⟨6,1210106412362349241459775,⟨7,39,15,31,191,47,128,384,261⟩⟩]⟩
theorem node1167 : UpperPrefix a [2,5,1,0,7,3] 30 :=
  Boolean.leaf_sound a [2,5,1,0,7,3] 30 cert1167 (by decide +kernel)

def cert1168 : Leaf := ⟨⟨0,92,113,100,76,140,300,108,104⟩,[(0,2)],[(1,2,0),(0,3,2),(7,4,5)],⟨7,35,14,25,176,112,456,456,332⟩,⟨7,35,14,25,176,112,192,384,260⟩,[⟨8,1181747925435436033151,⟨7,47,15,31,191,127,255,128,5⟩⟩,⟨4,1229033996759972212376581,⟨455,35,463,9,160,96,192,384,453⟩⟩]⟩
theorem node1168 : UpperPrefix a [2,5,1,0,7,4] 30 :=
  Boolean.leaf_sound a [2,5,1,0,7,4] 30 cert1168 (by decide +kernel)

def cert1169 : Leaf := ⟨⟨0,28,49,36,332,156,60,124,248⟩,[(0,2)],[(1,2,0),(0,3,2),(8,5,4)],⟨7,35,14,25,176,352,216,472,348⟩,⟨7,35,14,25,176,352,192,384,260⟩,[⟨6,1210106412362349233054749,⟨7,35,15,31,191,288,128,384,261⟩⟩,⟨7,1208926973663136428598301,⟨7,35,15,31,63,352,64,256,261⟩⟩]⟩
theorem node1169 : UpperPrefix a [2,5,1,0,7,8] 30 :=
  Boolean.leaf_sound a [2,5,1,0,7,8] 30 cert1169 (by decide +kernel)

theorem node1170 : UpperPrefix a [2,5,1,0,7] 30 :=
  branch_upper a [2,5,1,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,1,0,7,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,7,2] 30 (by decide +kernel))
  node1167
  node1168
  (invalid_upper a [2,5,1,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,7,7] 30 (by decide +kernel))
  node1169)

def cert1171 : Leaf := ⟨⟨0,408,433,420,192,400,304,112,240⟩,[(0,2)],[(1,2,0),(0,3,2)],⟨7,35,14,25,304,104,208,464,468⟩,⟨7,35,14,25,304,104,192,384,260⟩,[⟨2,1212623672792272703854081,⟨35,35,106,251,496,106,192,464,496⟩⟩,⟨3,1234005880677832569390085,⟨471,499,471,465,496,224,192,384,453⟩⟩,⟨6,1210106412362349241459775,⟨7,39,15,31,319,47,128,384,261⟩⟩]⟩
theorem node1171 : UpperPrefix a [2,5,1,0,8,3] 30 :=
  Boolean.leaf_sound a [2,5,1,0,8,3] 30 cert1171 (by decide +kernel)

def cert1172 : Leaf := ⟨⟨0,284,305,292,204,396,268,76,200⟩,[(0,2)],[(1,2,0),(0,3,2)],⟨7,35,14,25,304,112,200,456,460⟩,⟨7,35,14,25,304,112,192,384,260⟩,[⟨4,1229033996759972212376581,⟨455,35,463,9,288,96,192,384,453⟩⟩,⟨5,1229033995635171817161733,⟨455,3,463,25,272,80,192,384,453⟩⟩,⟨6,1210106412362353536951359,⟨7,47,15,31,319,63,128,384,261⟩⟩,⟨7,1208926973663140732494911,⟨7,47,15,31,319,127,64,256,261⟩⟩]⟩
theorem node1172 : UpperPrefix a [2,5,1,0,8,4] 30 :=
  Boolean.leaf_sound a [2,5,1,0,8,4] 30 cert1172 (by decide +kernel)

def cert1173 : Leaf := ⟨⟨0,284,305,292,76,0,316,124,120⟩,[(0,2),(5,6)],[(1,2,0),(0,3,2),(7,5,5)],⟨7,35,14,25,304,224,216,472,348⟩,⟨7,35,14,25,304,224,192,384,260⟩,[⟨6,1210106412362349233054749,⟨7,35,15,31,319,160,128,384,261⟩⟩]⟩
theorem node1173 : UpperPrefix a [2,5,1,0,8,7] 30 :=
  Boolean.leaf_sound a [2,5,1,0,8,7] 30 cert1173 (by decide +kernel)

theorem node1174 : UpperPrefix a [2,5,1,0,8] 30 :=
  branch_upper a [2,5,1,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,1,0,8,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,8,2] 30 (by decide +kernel))
  node1171
  node1172
  (invalid_upper a [2,5,1,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,8,6] 30 (by decide +kernel))
  node1173
  (invalid_upper a [2,5,1,0,8,8] 30 (by decide +kernel)))

theorem node1175 : UpperPrefix a [2,5,1,0] 30 :=
  branch_upper a [2,5,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,2] 30 (by decide +kernel))
  node1165
  (invalid_upper a [2,5,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,0,5] 30 (by decide +kernel))
  node1166
  node1170
  node1174)

def cert1176 : Leaf := ⟨⟨0,0,305,293,0,413,317,61,185⟩,[(0,2),(1,4),(4,1)],[(1,2,0)],⟨7,35,14,88,49,504,472,408,412⟩,⟨7,35,14,88,49,96,192,384,260⟩,[⟨6,1266885490621362520204301,⟨407,51,415,415,51,32,128,384,389⟩⟩,⟨7,1208926973665475047220287,⟨23,63,31,95,63,127,64,256,261⟩⟩]⟩
theorem node1176 : UpperPrefix a [2,5,1,6,0] 30 :=
  Boolean.leaf_sound a [2,5,1,6,0] 30 cert1176 (by decide +kernel)

def cert1177 : Leaf := ⟨⟨0,28,48,32,64,413,317,61,185⟩,[(0,2)],[(1,2,0),(6,3,4)],⟨7,35,14,88,56,497,465,401,405⟩,⟨7,35,14,88,56,96,192,384,260⟩,[⟨7,1208926973665475047220287,⟨23,63,31,95,63,127,64,256,261⟩⟩,⟨8,1181745671563283817535,⟨23,63,31,95,63,127,192,128,5⟩⟩,⟨0,1210107565286192443819008,⟨22,62,30,88,56,120,192,384,260⟩⟩,⟨2,1210107565286192442246145,⟨19,59,26,88,56,120,192,384,256⟩⟩]⟩
theorem node1177 : UpperPrefix a [2,5,1,6,3] 30 :=
  Boolean.leaf_sound a [2,5,1,6,3] 30 cert1177 (by decide +kernel)

def cert1178 : Local := ⟨⟨0,0,368,420,332,284,316,124,120⟩,[(0,2),(1,5)],[(1,2,0),(7,4,3),(0,5,1)]⟩
theorem node1178 : UpperPrefix a [2,5,1,6,7,0] 30 :=
  local_sound a [2,5,1,6,7,0] 30 cert1178 (by decide +kernel)

def cert1179 : Leaf := ⟨⟨0,284,305,421,261,0,309,53,49⟩,[(0,2),(5,3)],[(1,2,0),(6,3,5),(7,4,3)],⟨7,35,14,88,176,104,465,401,277⟩,⟨7,35,14,88,176,104,192,384,260⟩,[⟨3,1233784087403383827203077,⟨471,499,471,80,176,96,192,384,453⟩⟩]⟩
theorem node1179 : UpperPrefix a [2,5,1,6,7,3] 30 :=
  Boolean.leaf_sound a [2,5,1,6,7,3] 30 cert1179 (by decide +kernel)

def cert1180 : Leaf := ⟨⟨0,348,337,0,333,0,285,93,89⟩,[(0,2),(3,5),(5,3)],[(1,2,0),(7,4,3),(7,4,5)],⟨7,35,14,88,176,112,457,393,269⟩,⟨7,35,14,88,176,112,192,384,260⟩,[⟨5,1238497211373786131596295,⟨455,463,463,88,152,88,192,384,453⟩⟩]⟩
theorem node1180 : UpperPrefix a [2,5,1,6,7,4] 30 :=
  Boolean.leaf_sound a [2,5,1,6,7,4] 30 cert1180 (by decide +kernel)

def cert1181 : Leaf := ⟨⟨0,92,112,160,328,29,56,120,120⟩,[(0,2)],[(1,2,0),(7,4,3),(8,5,4)],⟨7,35,14,88,176,352,193,408,284⟩,⟨7,35,14,88,176,352,193,384,260⟩,[⟨0,1238792252320810796581888,⟨406,446,414,88,184,504,192,384,388⟩⟩,⟨2,1210402749220169753560065,⟨91,251,90,88,184,504,201,384,264⟩⟩]⟩
theorem node1181 : UpperPrefix a [2,5,1,6,7,8,0] 30 :=
  Boolean.leaf_sound a [2,5,1,6,7,8,0] 30 cert1181 (by decide +kernel)

def cert1182 : Leaf := ⟨⟨0,92,112,160,328,24,48,125,121⟩,[(0,2)],[(1,2,0),(7,4,3),(8,5,4)],⟨7,35,14,88,176,352,200,401,277⟩,⟨7,35,14,88,176,352,200,384,260⟩,[⟨0,1210110163874063031206912,⟨6,46,14,88,248,376,248,504,260⟩⟩,⟨2,1210110163874063029634049,⟨3,43,10,88,248,376,248,504,256⟩⟩]⟩
theorem node1182 : UpperPrefix a [2,5,1,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,1,6,7,8,3] 30 cert1182 (by decide +kernel)

def cert1183 : Local := ⟨⟨0,76,97,0,333,13,0,109,105⟩,[(0,2),(3,6),(6,4)],[(1,2,0),(7,4,3),(7,4,6),(8,5,4),(4,6,3)]⟩
theorem node1183 : UpperPrefix a [2,5,1,6,7,8,4] 30 :=
  local_sound a [2,5,1,6,7,8,4] 30 cert1183 (by decide +kernel)

theorem node1184 : UpperPrefix a [2,5,1,6,7,8] 30 :=
  branch_upper a [2,5,1,6,7,8] 30 (by decide) (fin9_cases _
  node1181
  (invalid_upper a [2,5,1,6,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,7,8,2] 30 (by decide +kernel))
  node1182
  node1183
  (invalid_upper a [2,5,1,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,7,8,8] 30 (by decide +kernel)))

theorem node1185 : UpperPrefix a [2,5,1,6,7] 30 :=
  branch_upper a [2,5,1,6,7] 30 (by decide) (fin9_cases _
  node1178
  (invalid_upper a [2,5,1,6,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,7,2] 30 (by decide +kernel))
  node1179
  node1180
  (invalid_upper a [2,5,1,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,7,7] 30 (by decide +kernel))
  node1184)

def cert1186 : Leaf := ⟨⟨0,0,496,416,204,412,312,120,248⟩,[(0,2),(1,5)],[(1,2,0),(0,5,1)],⟨7,35,14,88,304,97,216,408,412⟩,⟨7,35,14,88,304,97,192,384,260⟩,[⟨2,1210255571582007736550401,⟨3,35,74,216,506,99,192,384,256⟩⟩]⟩
theorem node1186 : UpperPrefix a [2,5,1,6,8,0] 30 :=
  Boolean.leaf_sound a [2,5,1,6,8,0] 30 cert1186 (by decide +kernel)

def cert1187 : Leaf := ⟨⟨0,396,417,421,133,0,309,53,177⟩,[(0,2),(5,3)],[(1,2,0),(6,3,5)],⟨7,35,14,88,304,104,209,401,405⟩,⟨7,35,14,88,304,104,192,384,260⟩,[⟨3,1233784087403383827203077,⟨471,499,471,80,304,96,192,384,453⟩⟩,⟨4,1210107565564227161718079,⟨7,39,47,111,295,111,192,385,263⟩⟩]⟩
theorem node1187 : UpperPrefix a [2,5,1,6,8,3] 30 :=
  Boolean.leaf_sound a [2,5,1,6,8,3] 30 cert1187 (by decide +kernel)

def cert1188 : Leaf := ⟨⟨0,476,465,0,205,0,269,77,201⟩,[(0,2),(3,5),(5,3)],[(1,2,0)],⟨7,35,14,88,304,112,201,393,397⟩,⟨7,35,14,88,304,112,192,384,260⟩,[⟨5,1238497211373786131596295,⟨455,463,463,88,280,88,192,384,453⟩⟩,⟨4,1229033996759972212376581,⟨455,35,463,72,288,96,192,384,453⟩⟩]⟩
theorem node1188 : UpperPrefix a [2,5,1,6,8,4] 30 :=
  Boolean.leaf_sound a [2,5,1,6,8,4] 30 cert1188 (by decide +kernel)

def cert1189 : Leaf := ⟨⟨0,76,97,293,77,0,316,125,121⟩,[(0,2),(5,6)],[(1,2,0),(7,5,5)],⟨7,35,14,88,304,224,193,408,284⟩,⟨7,35,14,88,304,224,193,384,260⟩,[⟨4,1210107567534551990309901,⟨7,35,15,111,288,226,227,384,261⟩⟩,⟨8,1181747921022327231501,⟨7,35,15,127,48,226,227,128,5⟩⟩]⟩
theorem node1189 : UpperPrefix a [2,5,1,6,8,7,0] 30 :=
  Boolean.leaf_sound a [2,5,1,6,8,7,0] 30 cert1189 (by decide +kernel)

def cert1190 : Leaf := ⟨⟨0,348,368,292,76,0,308,125,121⟩,[(0,2),(5,6)],[(1,2,0),(7,5,5)],⟨7,35,14,88,304,224,200,401,277⟩,⟨7,35,14,88,304,224,200,384,260⟩,[⟨0,1210110454351840950092800,⟨6,110,14,120,376,248,248,504,260⟩⟩]⟩
theorem node1190 : UpperPrefix a [2,5,1,6,8,7,3] 30 :=
  Boolean.leaf_sound a [2,5,1,6,8,7,3] 30 cert1190 (by decide +kernel)

def cert1191 : Local := ⟨⟨0,76,97,0,77,0,301,109,105⟩,[(0,2),(3,6),(5,6)],[(1,2,0),(8,4,6),(7,5,5),(4,6,3)]⟩
theorem node1191 : UpperPrefix a [2,5,1,6,8,7,4] 30 :=
  local_sound a [2,5,1,6,8,7,4] 30 cert1191 (by decide +kernel)

theorem node1192 : UpperPrefix a [2,5,1,6,8,7] 30 :=
  branch_upper a [2,5,1,6,8,7] 30 (by decide) (fin9_cases _
  node1189
  (invalid_upper a [2,5,1,6,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,8,7,2] 30 (by decide +kernel))
  node1190
  node1191
  (invalid_upper a [2,5,1,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,8,7,8] 30 (by decide +kernel)))

theorem node1193 : UpperPrefix a [2,5,1,6,8] 30 :=
  branch_upper a [2,5,1,6,8] 30 (by decide) (fin9_cases _
  node1186
  (invalid_upper a [2,5,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,8,2] 30 (by decide +kernel))
  node1187
  node1188
  (invalid_upper a [2,5,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,8,6] 30 (by decide +kernel))
  node1192
  (invalid_upper a [2,5,1,6,8,8] 30 (by decide +kernel)))

theorem node1194 : UpperPrefix a [2,5,1,6] 30 :=
  branch_upper a [2,5,1,6] 30 (by decide) (fin9_cases _
  node1176
  (invalid_upper a [2,5,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,2] 30 (by decide +kernel))
  node1177
  (invalid_upper a [2,5,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,6] 30 (by decide +kernel))
  node1185
  node1193)

def cert1195 : Leaf := ⟨⟨0,0,369,357,0,405,309,117,113⟩,[(0,2),(1,4),(4,1)],[(1,2,0),(7,3,5)],⟨7,35,14,152,49,104,464,464,340⟩,⟨7,35,14,152,49,104,192,384,260⟩,[⟨3,1233931949586349655335941,⟨471,499,471,210,499,96,192,384,453⟩⟩]⟩
theorem node1195 : UpperPrefix a [2,5,1,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,1,7,0,3] 30 cert1195 (by decide +kernel)

def cert1196 : Leaf := ⟨⟨0,0,481,357,0,397,301,109,233⟩,[(0,2),(1,4),(4,1)],[(1,2,0)],⟨7,35,14,152,49,112,456,456,332⟩,⟨7,35,14,152,49,112,192,384,260⟩,[⟨4,1266886859714412290253837,⟨455,35,463,463,35,98,192,384,453⟩⟩]⟩
theorem node1196 : UpperPrefix a [2,5,1,7,0,4] 30 :=
  Boolean.leaf_sound a [2,5,1,7,0,4] 30 cert1196 (by decide +kernel)

def cert1197 : Leaf := ⟨⟨0,0,241,357,0,157,56,125,249⟩,[(0,2),(1,4),(4,1)],[(1,2,0)],⟨7,35,14,152,49,352,216,472,348⟩,⟨7,35,14,152,49,352,192,384,260⟩,[⟨8,1181889784548028326925,⟨23,51,95,223,51,96,192,128,5⟩⟩,⟨0,1210107709399039761974272,⟨6,34,78,216,48,352,192,384,260⟩⟩,⟨2,1210107709399177199887361,⟨19,51,90,218,51,352,192,384,256⟩⟩]⟩
theorem node1197 : UpperPrefix a [2,5,1,7,0,8] 30 :=
  Boolean.leaf_sound a [2,5,1,7,0,8] 30 cert1197 (by decide +kernel)

theorem node1198 : UpperPrefix a [2,5,1,7,0] 30 :=
  branch_upper a [2,5,1,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,1,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,0,2] 30 (by decide +kernel))
  node1195
  node1196
  (invalid_upper a [2,5,1,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,0,7] 30 (by decide +kernel))
  node1197)

def cert1199 : Leaf := ⟨⟨0,0,240,100,196,156,316,124,248⟩,[(0,2),(1,5)],[(1,2,0),(0,5,1)],⟨7,35,14,152,56,97,464,464,340⟩,⟨7,35,14,152,56,97,192,384,260⟩,[⟨8,1181747927628016313471,⟨7,55,15,159,63,127,255,128,5⟩⟩]⟩
theorem node1199 : UpperPrefix a [2,5,1,7,3,0] 30 :=
  Boolean.leaf_sound a [2,5,1,7,3,0] 30 cert1199 (by decide +kernel)

def cert1200 : Leaf := ⟨⟨0,196,225,101,197,133,293,101,225⟩,[(0,2)],[(1,2,0),(4,5,4)],⟨7,35,14,152,56,112,449,449,325⟩,⟨7,35,14,152,56,112,192,384,260⟩,[⟨3,1236152188455183828651269,⟨455,483,487,240,48,112,192,449,455⟩⟩,⟨8,1181747927628016313471,⟨7,55,15,159,63,127,255,128,5⟩⟩]⟩
theorem node1200 : UpperPrefix a [2,5,1,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,1,7,3,4] 30 cert1200 (by decide +kernel)

def cert1201 : Leaf := ⟨⟨0,204,224,352,448,156,40,120,248⟩,[(0,2)],[(1,2,0)],⟨7,35,14,152,56,352,193,464,340⟩,⟨7,35,14,152,56,352,193,384,260⟩,[⟨0,1513224466161596662285312,⟨30,190,30,152,184,504,508,384,260⟩⟩,⟨2,1210402749220171229955073,⟨91,251,90,152,184,504,193,384,256⟩⟩,⟨4,1210107709397940256646173,⟨7,35,79,207,111,352,193,384,261⟩⟩,⟨8,1181889784410593567773,⟨7,35,79,223,127,96,193,128,5⟩⟩]⟩
theorem node1201 : UpperPrefix a [2,5,1,7,3,8,0] 30 :=
  Boolean.leaf_sound a [2,5,1,7,3,8,0] 30 cert1201 (by decide +kernel)

def cert1202 : Leaf := ⟨⟨0,460,481,0,453,141,0,109,233⟩,[(0,2),(3,6),(6,3)],[(1,2,0)],⟨7,35,14,152,56,352,208,449,325⟩,⟨7,35,14,152,56,352,208,384,260⟩,[⟨4,1513224466153747346678877,⟨7,163,15,143,175,483,487,384,261⟩⟩]⟩
theorem node1202 : UpperPrefix a [2,5,1,7,3,8,4] 30 :=
  Boolean.leaf_sound a [2,5,1,7,3,8,4] 30 cert1202 (by decide +kernel)

theorem node1203 : UpperPrefix a [2,5,1,7,3,8] 30 :=
  branch_upper a [2,5,1,7,3,8] 30 (by decide) (fin9_cases _
  node1201
  (invalid_upper a [2,5,1,7,3,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,8,3] 30 (by decide +kernel))
  node1202
  (invalid_upper a [2,5,1,7,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,8,8] 30 (by decide +kernel)))

theorem node1204 : UpperPrefix a [2,5,1,7,3] 30 :=
  branch_upper a [2,5,1,7,3] 30 (by decide) (fin9_cases _
  node1199
  (invalid_upper a [2,5,1,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,3] 30 (by decide +kernel))
  node1200
  (invalid_upper a [2,5,1,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,3,7] 30 (by decide +kernel))
  node1203)

def cert1205 : Local := ⟨⟨0,0,432,292,0,412,316,60,184⟩,[(0,2),(1,5),(4,5)],[(1,2,0),(6,4,4),(0,5,1)]⟩
theorem node1205 : UpperPrefix a [2,5,1,7,6,0] 30 :=
  local_sound a [2,5,1,7,6,0] 30 cert1205 (by decide +kernel)

def cert1206 : Leaf := ⟨⟨0,28,49,37,0,149,317,61,57⟩,[(0,2),(4,5)],[(1,2,0),(7,3,5),(6,4,4)],⟨7,35,14,152,112,104,465,401,277⟩,⟨7,35,14,152,112,104,192,384,260⟩,[⟨8,1181748490577969738879,⟨7,55,15,191,127,127,255,128,5⟩⟩]⟩
theorem node1206 : UpperPrefix a [2,5,1,7,6,3] 30 :=
  Boolean.leaf_sound a [2,5,1,7,6,3] 30 cert1206 (by decide +kernel)

def cert1207 : Local := ⟨⟨0,412,433,293,0,0,317,61,185⟩,[(0,2),(4,5),(5,4)],[(1,2,0),(6,4,4),(6,4,5)]⟩
theorem node1207 : UpperPrefix a [2,5,1,7,6,4] 30 :=
  local_sound a [2,5,1,7,6,4] 30 cert1207 (by decide +kernel)

def cert1208 : Leaf := ⟨⟨0,412,432,292,0,156,316,60,184⟩,[(0,2),(4,5)],[(1,2,0),(6,4,4)],⟨7,35,14,152,112,352,193,408,284⟩,⟨7,35,14,152,112,352,193,384,260⟩,[⟨0,1522835220386811853145088,⟨398,446,398,184,504,504,508,384,260⟩⟩]⟩
theorem node1208 : UpperPrefix a [2,5,1,7,6,8,0] 30 :=
  Boolean.leaf_sound a [2,5,1,7,6,8,0] 30 cert1208 (by decide +kernel)

def cert1209 : Local := ⟨⟨0,284,305,293,0,29,0,61,57⟩,[(0,2),(4,5),(6,3)],[(1,2,0),(7,3,6),(6,4,4)]⟩
theorem node1209 : UpperPrefix a [2,5,1,7,6,8,3] 30 :=
  local_sound a [2,5,1,7,6,8,3] 30 cert1209 (by decide +kernel)

def cert1210 : Local := ⟨⟨0,412,433,0,0,157,0,61,185⟩,[(0,2),(3,6),(4,5),(6,3)],[(1,2,0),(6,4,4)]⟩
theorem node1210 : UpperPrefix a [2,5,1,7,6,8,4] 30 :=
  local_sound a [2,5,1,7,6,8,4] 30 cert1210 (by decide +kernel)

theorem node1211 : UpperPrefix a [2,5,1,7,6,8] 30 :=
  branch_upper a [2,5,1,7,6,8] 30 (by decide) (fin9_cases _
  node1208
  (invalid_upper a [2,5,1,7,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,8,2] 30 (by decide +kernel))
  node1209
  node1210
  (invalid_upper a [2,5,1,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,8,8] 30 (by decide +kernel)))

theorem node1212 : UpperPrefix a [2,5,1,7,6] 30 :=
  branch_upper a [2,5,1,7,6] 30 (by decide) (fin9_cases _
  node1205
  (invalid_upper a [2,5,1,7,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,2] 30 (by decide +kernel))
  node1206
  node1207
  (invalid_upper a [2,5,1,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,7] 30 (by decide +kernel))
  node1211)

def cert1213 : Local := ⟨⟨0,0,240,356,204,156,60,124,248⟩,[(0,2),(1,5)],[(1,2,0),(8,4,3),(0,5,1)]⟩
theorem node1213 : UpperPrefix a [2,5,1,7,8,0] 30 :=
  local_sound a [2,5,1,7,8,0] 30 cert1213 (by decide +kernel)

def cert1214 : Leaf := ⟨⟨0,12,33,357,69,149,53,117,113⟩,[(0,2)],[(1,2,0),(7,3,5),(8,4,3)],⟨7,35,14,152,304,104,209,465,341⟩,⟨7,35,14,152,304,104,192,384,260⟩,[⟨3,1233784087403383827203077,⟨471,499,471,144,304,96,192,384,453⟩⟩,⟨4,1210107565282752185001023,⟨7,39,15,143,295,111,192,384,261⟩⟩,⟨6,1210106412362347089781823,⟨7,39,15,159,311,47,128,384,261⟩⟩]⟩
theorem node1214 : UpperPrefix a [2,5,1,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,1,7,8,3] 30 cert1214 (by decide +kernel)

def cert1215 : Leaf := ⟨⟨0,220,208,324,204,140,28,92,216⟩,[(0,2)],[(1,2,0),(8,4,3)],⟨7,35,14,152,304,112,193,456,332⟩,⟨7,35,14,152,304,112,193,384,260⟩,[⟨0,1513224466161459223331840,⟨14,190,14,152,440,504,508,384,260⟩⟩,⟨5,1238649415026794892362759,⟨455,463,463,152,472,216,193,448,453⟩⟩]⟩
theorem node1215 : UpperPrefix a [2,5,1,7,8,4,0] 30 :=
  Boolean.leaf_sound a [2,5,1,7,8,4,0] 30 cert1215 (by decide +kernel)

#print axioms node1215
end Delivery.FiniteExclusion.Sharp2x7
