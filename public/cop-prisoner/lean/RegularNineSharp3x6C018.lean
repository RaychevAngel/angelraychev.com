import RegularNineSharp3x6Base
import RegularNineSharp3x6C017
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert1152 : Leaf := ⟨⟨228,168,0,98,202,138,266,106,226⟩,[(2,4)],[(0,4,2),(8,5,6)],⟨11,70,21,152,49,352,224,388,266⟩,⟨11,70,21,152,49,352,224,388,264⟩,[⟨4,1252648329129510466292745,⟨363,230,487,491,289,352,226,486,361⟩⟩,⟨2,1214832395271262651286529,⟨379,82,305,248,305,352,232,504,360⟩⟩]⟩
theorem node1152 : UpperPrefix a [3,6,4,7,0,8,5,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,0,8,5,2] 30 cert1152 (by decide +kernel)

theorem node1153 : UpperPrefix a [3,6,4,7,0,8,5] 30 :=
  branch_upper a [3,6,4,7,0,8,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,7,0,8,5,0] 30 (by decide +kernel))
  node1151
  node1152
  (invalid_upper a [3,6,4,7,0,8,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,8,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,8,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,8,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,8,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,8,5,8] 30 (by decide +kernel)))

theorem node1154 : UpperPrefix a [3,6,4,7,0,8] 30 :=
  branch_upper a [3,6,4,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,7,0,8,0] 30 (by decide +kernel))
  node1149
  node1150
  (invalid_upper a [3,6,4,7,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,8,4] 30 (by decide +kernel))
  node1153
  (invalid_upper a [3,6,4,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,8,8] 30 (by decide +kernel)))

theorem node1155 : UpperPrefix a [3,6,4,7,0] 30 :=
  branch_upper a [3,6,4,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,7,0,0] 30 (by decide +kernel))
  node1147
  node1148
  (invalid_upper a [3,6,4,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,0,7] 30 (by decide +kernel))
  node1154)

def cert1156 : Leaf := ⟨⟨176,0,170,33,201,152,57,57,177⟩,[(1,6)],[(6,1,4),(1,4,2),(2,6,1)],⟨11,70,21,152,50,97,196,416,296⟩,⟨11,70,21,152,50,97,196,384,264⟩,[⟨8,1184211811088633681899,⟨127,127,55,255,55,127,255,255,127⟩⟩]⟩
theorem node1156 : UpperPrefix a [3,6,4,7,1,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,1,0,2] 30 cert1156 (by decide +kernel)

def cert1157 : Leaf := ⟨⟨148,184,138,4,205,156,28,28,148⟩,[],[(6,1,4),(1,4,2)],⟨11,70,21,152,50,97,224,388,268⟩,⟨11,70,21,152,50,97,224,384,264⟩,[⟨8,1184211811088633681899,⟨127,127,55,255,55,127,255,255,127⟩⟩,⟨0,1238497392643669522123776,⟨394,462,478,216,506,96,224,384,264⟩⟩,⟨5,1359148032901490792203283,⟨399,463,413,413,415,449,192,384,396⟩⟩]⟩
theorem node1157 : UpperPrefix a [3,6,4,7,1,0,5] 30 :=
  Boolean.leaf_sound a [3,6,4,7,1,0,5] 30 cert1157 (by decide +kernel)

def cert1158 : Leaf := ⟨⟨148,145,130,37,197,156,0,61,181⟩,[(6,7)],[(6,1,4),(1,4,2),(8,6,6)],⟨11,70,21,152,50,97,448,420,300⟩,⟨11,70,21,152,50,97,448,384,264⟩,[⟨3,1210109871129058857731073,⟨3,70,21,208,54,119,448,448,256⟩⟩,⟨5,1210109870000960995071241,⟨15,70,21,223,18,65,449,449,271⟩⟩]⟩
theorem node1158 : UpperPrefix a [3,6,4,7,1,0,8] 30 :=
  Boolean.leaf_sound a [3,6,4,7,1,0,8] 30 cert1158 (by decide +kernel)

theorem node1159 : UpperPrefix a [3,6,4,7,1,0] 30 :=
  branch_upper a [3,6,4,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,0,1] 30 (by decide +kernel))
  node1156
  (invalid_upper a [3,6,4,7,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,0,4] 30 (by decide +kernel))
  node1157
  (invalid_upper a [3,6,4,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,0,7] 30 (by decide +kernel))
  node1158)

def cert1160 : Leaf := ⟨⟨176,0,170,33,205,0,313,57,177⟩,[(1,5),(5,1)],[(6,1,4),(1,4,2),(2,5,4)],⟨11,70,21,152,50,100,481,417,297⟩,⟨11,70,21,152,50,100,192,384,264⟩,[⟨8,1181747998202917602403,⟨63,127,21,156,55,127,255,128,8⟩⟩]⟩
theorem node1160 : UpperPrefix a [3,6,4,7,1,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,1,2] 30 cert1160 (by decide +kernel)

def cert1161 : Leaf := ⟨⟨416,425,426,288,456,136,300,40,160⟩,[],[(6,1,4),(1,4,2),(0,6,1)],⟨11,70,21,152,50,352,193,388,296⟩,⟨11,70,21,152,50,352,193,388,264⟩,[⟨4,1252645989509504047320073,⟨363,230,487,491,34,352,483,486,361⟩⟩,⟨2,1677621849410329867453443,⟨315,379,273,152,307,360,505,384,264⟩⟩]⟩
theorem node1161 : UpperPrefix a [3,6,4,7,1,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,1,8,0,2] 30 cert1161 (by decide +kernel)

def cert1162 : Local := ⟨⟨148,153,138,36,204,156,28,0,148⟩,[(7,5)],[(6,1,4),(1,4,2),(8,5,7),(0,6,1),(5,7,3)]⟩
theorem node1162 : UpperPrefix a [3,6,4,7,1,8,0,5] 30 :=
  local_sound a [3,6,4,7,1,8,0,5] 30 cert1162 (by decide +kernel)

theorem node1163 : UpperPrefix a [3,6,4,7,1,8,0] 30 :=
  branch_upper a [3,6,4,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,8,0,1] 30 (by decide +kernel))
  node1161
  (invalid_upper a [3,6,4,7,1,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,8,0,4] 30 (by decide +kernel))
  node1162
  (invalid_upper a [3,6,4,7,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,8,0,8] 30 (by decide +kernel)))

def cert1164 : Leaf := ⟨⟨432,0,426,289,457,137,297,41,161⟩,[(1,6)],[(6,1,4),(1,4,2),(2,6,1)],⟨11,70,21,152,50,352,196,417,297⟩,⟨11,70,21,152,50,352,196,384,264⟩,[⟨4,1214876156888119010954241,⟨491,230,487,136,98,354,230,384,264⟩⟩]⟩
theorem node1164 : UpperPrefix a [3,6,4,7,1,8,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,1,8,2] 30 cert1164 (by decide +kernel)

def cert1165 : Leaf := ⟨⟨148,185,138,5,205,144,272,29,149⟩,[],[(6,1,4),(1,4,2),(8,5,6)],⟨11,70,21,152,50,352,224,389,269⟩,⟨11,70,21,152,50,352,224,384,264⟩,[⟨5,1356786849660055969596435,⟨399,463,413,413,415,320,192,384,396⟩⟩,⟨0,1210110028752847857779712,⟨74,70,20,248,50,352,224,480,360⟩⟩,⟨2,1210110028752847856731137,⟨75,66,17,248,50,352,224,480,360⟩⟩,⟨3,1210110028752846784037889,⟨67,70,21,240,50,352,224,480,352⟩⟩]⟩
theorem node1165 : UpperPrefix a [3,6,4,7,1,8,5] 30 :=
  Boolean.leaf_sound a [3,6,4,7,1,8,5] 30 cert1165 (by decide +kernel)

theorem node1166 : UpperPrefix a [3,6,4,7,1,8] 30 :=
  branch_upper a [3,6,4,7,1,8] 30 (by decide) (fin9_cases _
  node1163
  (invalid_upper a [3,6,4,7,1,8,1] 30 (by decide +kernel))
  node1164
  (invalid_upper a [3,6,4,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,8,4] 30 (by decide +kernel))
  node1165
  (invalid_upper a [3,6,4,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,8,8] 30 (by decide +kernel)))

theorem node1167 : UpperPrefix a [3,6,4,7,1] 30 :=
  branch_upper a [3,6,4,7,1] 30 (by decide) (fin9_cases _
  node1159
  (invalid_upper a [3,6,4,7,1,1] 30 (by decide +kernel))
  node1160
  (invalid_upper a [3,6,4,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,1,7] 30 (by decide +kernel))
  node1166)

def cert1168 : Leaf := ⟨⟨224,32,98,98,67,138,298,106,226⟩,[],[(0,5,4)],⟨11,70,21,152,52,97,482,418,298⟩,⟨11,70,21,152,52,97,192,384,264⟩,[⟨2,1224302389138057854977027,⟨491,491,505,152,56,481,192,384,264⟩⟩,⟨4,1252729011116834808671241,⟨491,230,487,491,230,481,192,416,489⟩⟩,⟨8,1181747998202917602403,⟨63,127,21,156,55,127,255,128,8⟩⟩,⟨3,1210107565286049644037121,⟨3,70,21,144,54,119,192,384,256⟩⟩,⟨7,1208926973665333306475521,⟨11,70,21,24,54,119,64,256,264⟩⟩]⟩
theorem node1168 : UpperPrefix a [3,6,4,7,2,0] 30 :=
  Boolean.leaf_sound a [3,6,4,7,2,0] 30 cert1168 (by decide +kernel)

def cert1169 : Leaf := ⟨⟨160,169,170,35,139,0,299,43,163⟩,[(5,1)],[(6,1,5)],⟨11,70,21,152,52,98,481,417,297⟩,⟨11,70,21,152,52,98,192,384,264⟩,[⟨2,1243524544840474208240643,⟨491,491,505,152,504,483,192,384,264⟩⟩,⟨4,1255094797670407501523977,⟨491,230,487,491,230,98,192,448,489⟩⟩,⟨8,1181747998202917602403,⟨63,127,21,156,55,127,255,128,8⟩⟩]⟩
theorem node1169 : UpperPrefix a [3,6,4,7,2,1] 30 :=
  Boolean.leaf_sound a [3,6,4,7,2,1] 30 cert1169 (by decide +kernel)

def cert1170 : Leaf := ⟨⟨192,137,202,354,202,138,10,106,226⟩,[],[(0,6,1)],⟨11,70,21,152,52,352,193,418,298⟩,⟨11,70,21,152,52,352,193,384,264⟩,[⟨2,1224302463447451706590211,⟨491,491,505,152,120,352,481,384,264⟩⟩,⟨4,1252733629558252677114889,⟨491,230,487,491,230,352,481,480,489⟩⟩,⟨8,1184195629618834855689,⟨79,70,23,223,54,119,195,195,79⟩⟩,⟨5,1210110014116149071058697,⟨79,70,23,223,20,323,195,451,335⟩⟩]⟩
theorem node1170 : UpperPrefix a [3,6,4,7,2,8,0] 30 :=
  Boolean.leaf_sound a [3,6,4,7,2,8,0] 30 cert1170 (by decide +kernel)

def cert1171 : Leaf := ⟨⟨448,385,448,321,449,129,257,72,225⟩,[],[(3,0,7)],⟨11,70,21,152,52,352,194,385,296⟩,⟨11,70,21,152,52,352,194,385,264⟩,[⟨1,1753225830000846813003777,⟨445,508,413,412,444,376,508,413,264⟩⟩,⟨2,1357155846712315634254851,⟨491,491,505,440,440,480,483,481,264⟩⟩,⟨4,1255090523121042429324297,⟨491,230,487,491,230,480,226,481,489⟩⟩,⟨5,1212771821639912280702749,⟨79,71,95,223,223,451,194,451,463⟩⟩]⟩
theorem node1171 : UpperPrefix a [3,6,4,7,2,8,1,0] 30 :=
  Boolean.leaf_sound a [3,6,4,7,2,8,1,0] 30 cert1171 (by decide +kernel)

def cert1172 : Leaf := ⟨⟨208,153,200,97,201,153,25,0,209⟩,[(7,5)],[(8,5,7),(5,7,3)],⟨11,70,21,152,52,352,194,416,265⟩,⟨11,70,21,152,52,352,194,416,264⟩,[⟨1,1234189789742666085564417,⟨445,508,413,152,444,488,248,416,264⟩⟩,⟨2,1244261768477613550994435,⟨491,491,505,152,440,480,483,416,264⟩⟩]⟩
theorem node1172 : UpperPrefix a [3,6,4,7,2,8,1,5] 30 :=
  Boolean.leaf_sound a [3,6,4,7,2,8,1,5] 30 cert1172 (by decide +kernel)

theorem node1173 : UpperPrefix a [3,6,4,7,2,8,1] 30 :=
  branch_upper a [3,6,4,7,2,8,1] 30 (by decide) (fin9_cases _
  node1171
  (invalid_upper a [3,6,4,7,2,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,1,4] 30 (by decide +kernel))
  node1172
  (invalid_upper a [3,6,4,7,2,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,1,8] 30 (by decide +kernel)))

def cert1174 : Leaf := ⟨⟨128,169,234,3,203,138,266,11,131⟩,[],[(8,5,6)],⟨11,70,21,152,52,352,224,387,267⟩,⟨11,70,21,152,52,352,224,384,264⟩,[⟨2,1224304924664648064566275,⟨491,491,505,248,120,352,224,480,360⟩⟩,⟨4,1252736257408635247799305,⟨491,230,487,491,230,352,224,480,489⟩⟩,⟨5,1224302333722671816115203,⟨395,463,413,152,28,320,192,384,264⟩⟩,⟨6,1224301181927067116110851,⟨395,399,413,152,60,288,160,384,264⟩⟩,⟨0,1210110028752847857779712,⟨74,70,20,248,52,352,224,480,360⟩⟩]⟩
theorem node1174 : UpperPrefix a [3,6,4,7,2,8,5] 30 :=
  Boolean.leaf_sound a [3,6,4,7,2,8,5] 30 cert1174 (by decide +kernel)

theorem node1175 : UpperPrefix a [3,6,4,7,2,8] 30 :=
  branch_upper a [3,6,4,7,2,8] 30 (by decide) (fin9_cases _
  node1170
  node1173
  (invalid_upper a [3,6,4,7,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,4] 30 (by decide +kernel))
  node1174
  (invalid_upper a [3,6,4,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,8,8] 30 (by decide +kernel)))

theorem node1176 : UpperPrefix a [3,6,4,7,2] 30 :=
  branch_upper a [3,6,4,7,2] 30 (by decide) (fin9_cases _
  node1168
  node1169
  (invalid_upper a [3,6,4,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,2,7] 30 (by decide +kernel))
  node1175)

def cert1177 : Leaf := ⟨⟨192,137,200,321,201,138,13,73,225⟩,[],[(8,4,3),(1,6,5),(2,7,6)],⟨11,70,21,152,304,97,194,388,296⟩,⟨11,70,21,152,304,97,194,388,264⟩,[⟨4,1252648324625910838922249,⟨363,230,487,491,288,353,194,486,361⟩⟩,⟨5,1212623743284164875730847,⟨79,79,223,223,479,67,195,463,463⟩⟩]⟩
theorem node1177 : UpperPrefix a [3,6,4,7,8,0,1,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,0,1,2] 30 cert1177 (by decide +kernel)

def cert1178 : Local := ⟨⟨212,153,200,357,0,158,29,0,213⟩,[(4,7),(7,4)],[(8,4,3),(1,6,5),(5,7,3)]⟩
theorem node1178 : UpperPrefix a [3,6,4,7,8,0,1,5] 30 :=
  local_sound a [3,6,4,7,8,0,1,5] 30 cert1178 (by decide +kernel)

theorem node1179 : UpperPrefix a [3,6,4,7,8,0,1] 30 :=
  branch_upper a [3,6,4,7,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,7,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,1,1] 30 (by decide +kernel))
  node1177
  (invalid_upper a [3,6,4,7,8,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,1,4] 30 (by decide +kernel))
  node1178
  (invalid_upper a [3,6,4,7,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,1,8] 30 (by decide +kernel)))

def cert1180 : Leaf := ⟨⟨208,0,202,354,202,138,11,106,226⟩,[(1,6)],[(8,4,3),(2,6,1)],⟨11,70,21,152,304,97,196,418,298⟩,⟨11,70,21,152,304,97,196,384,264⟩,[⟨0,1361518440643065151521792,⟨10,70,28,152,440,506,198,384,264⟩⟩,⟨4,1215171304793298363780097,⟨491,230,487,136,416,483,230,384,264⟩⟩,⟨5,1210107708273139861591817,⟨79,70,23,223,279,67,198,387,335⟩⟩]⟩
theorem node1180 : UpperPrefix a [3,6,4,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,0,2] 30 cert1180 (by decide +kernel)

def cert1181 : Leaf := ⟨⟨144,185,168,256,137,154,26,28,148⟩,[],[(8,4,3)],⟨11,70,21,152,304,97,224,386,268⟩,⟨11,70,21,152,304,97,224,386,264⟩,[⟨6,2414337535616827960853635,⟨399,415,413,413,316,445,445,399,268⟩⟩,⟨2,1210110022410890557523075,⟨107,107,49,249,304,105,249,507,376⟩⟩,⟨0,1238470010757932962022400,⟨394,462,412,152,368,224,224,386,264⟩⟩,⟨1,1672899480611682585149441,⟨265,348,21,152,308,381,508,384,264⟩⟩,⟨5,1238469433171280751756291,⟨395,463,413,152,272,193,192,387,264⟩⟩]⟩
theorem node1181 : UpperPrefix a [3,6,4,7,8,0,5,1] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,0,5,1] 30 cert1181 (by decide +kernel)

def cert1182 : Leaf := ⟨⟨160,169,170,290,138,138,15,42,162⟩,[],[(8,4,3)],⟨11,70,21,152,304,97,224,388,266⟩,⟨11,70,21,152,304,97,224,388,264⟩,[⟨4,1252648324625910838922249,⟨363,230,487,491,288,353,226,486,361⟩⟩,⟨6,1224771573903160773706755,⟨395,399,413,152,444,445,188,396,264⟩⟩,⟨2,1224274664805243136508931,⟨315,379,273,152,304,377,248,384,264⟩⟩,⟨0,1224330004966889900475392,⟨394,462,412,152,304,376,248,396,264⟩⟩]⟩
theorem node1182 : UpperPrefix a [3,6,4,7,8,0,5,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,0,5,2] 30 cert1182 (by decide +kernel)

theorem node1183 : UpperPrefix a [3,6,4,7,8,0,5] 30 :=
  branch_upper a [3,6,4,7,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,7,8,0,5,0] 30 (by decide +kernel))
  node1181
  node1182
  (invalid_upper a [3,6,4,7,8,0,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,5,8] 30 (by decide +kernel)))

theorem node1184 : UpperPrefix a [3,6,4,7,8,0] 30 :=
  branch_upper a [3,6,4,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,7,8,0,0] 30 (by decide +kernel))
  node1179
  node1180
  (invalid_upper a [3,6,4,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,4] 30 (by decide +kernel))
  node1183
  (invalid_upper a [3,6,4,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,0,8] 30 (by decide +kernel)))

def cert1185 : Leaf := ⟨⟨148,25,10,294,14,0,30,62,54⟩,[(5,1)],[(6,1,5),(8,4,3),(0,6,1)],⟨11,70,21,152,304,98,193,420,300⟩,⟨11,70,21,152,304,98,193,384,264⟩,[⟨5,1210110014116149075253001,⟨79,70,23,223,279,66,195,451,335⟩⟩,⟨7,1213649342472639260967937,⟨319,118,277,24,306,118,375,256,264⟩⟩]⟩
theorem node1185 : UpperPrefix a [3,6,4,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,1,0] 30 cert1185 (by decide +kernel)

def cert1186 : Local := ⟨⟨176,0,170,291,139,0,59,59,179⟩,[(1,6),(5,1)],[(6,1,5),(8,4,3),(2,6,1),(2,6,5)]⟩
theorem node1186 : UpperPrefix a [3,6,4,7,8,1,2] 30 :=
  local_sound a [3,6,4,7,8,1,2] 30 cert1186 (by decide +kernel)

def cert1187 : Leaf := ⟨⟨148,185,42,261,15,0,31,29,21⟩,[(5,1)],[(6,1,5),(8,4,3)],⟨11,70,21,152,304,98,224,389,269⟩,⟨11,70,21,152,304,98,224,384,264⟩,[⟨5,1238497103287391316083715,⟨395,463,413,152,272,451,192,384,264⟩⟩,⟨1,1229033924703478222946305,⟨9,460,413,152,304,96,224,384,264⟩⟩,⟨7,1213649340216441383945217,⟨319,102,277,24,304,98,96,256,264⟩⟩]⟩
theorem node1187 : UpperPrefix a [3,6,4,7,8,1,5] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,1,5] 30 cert1187 (by decide +kernel)

theorem node1188 : UpperPrefix a [3,6,4,7,8,1] 30 :=
  branch_upper a [3,6,4,7,8,1] 30 (by decide) (fin9_cases _
  node1185
  (invalid_upper a [3,6,4,7,8,1,1] 30 (by decide +kernel))
  node1186
  (invalid_upper a [3,6,4,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,1,4] 30 (by decide +kernel))
  node1187
  (invalid_upper a [3,6,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,1,8] 30 (by decide +kernel)))

def cert1189 : Leaf := ⟨⟨212,0,74,358,78,0,14,110,102⟩,[(1,5),(5,1)],[(8,4,3),(0,6,1),(0,6,5)],⟨11,70,21,152,304,100,193,418,298⟩,⟨11,70,21,152,304,100,193,384,264⟩,[⟨4,1215023712861494549957633,⟨491,230,487,136,418,230,449,384,264⟩⟩,⟨5,1210110014116149075269385,⟨79,70,23,223,279,70,195,451,335⟩⟩,⟨7,1213649342472639260967937,⟨319,118,277,24,306,118,375,256,264⟩⟩]⟩
theorem node1189 : UpperPrefix a [3,6,4,7,8,2,0] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,2,0] 30 cert1189 (by decide +kernel)

def cert1190 : Leaf := ⟨⟨212,0,200,357,205,0,13,109,229⟩,[(1,5),(5,1)],[(8,4,3)],⟨11,70,21,152,304,100,194,417,297⟩,⟨11,70,21,152,304,100,194,384,264⟩,[⟨1,1214839155209196321112065,⟨445,108,413,152,304,108,224,384,264⟩⟩,⟨4,1214876751398454195932161,⟨491,230,487,136,354,230,226,384,264⟩⟩,⟨5,1210110014116149075269385,⟨79,70,23,223,279,70,194,451,335⟩⟩]⟩
theorem node1190 : UpperPrefix a [3,6,4,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,2,1] 30 cert1190 (by decide +kernel)

def cert1191 : Leaf := ⟨⟨144,0,202,259,207,0,31,27,147⟩,[(1,5),(5,1)],[(8,4,3)],⟨11,70,21,152,304,100,224,387,267⟩,⟨11,70,21,152,304,100,224,384,264⟩,[⟨5,1452008942568544675054643,⟨399,463,413,413,415,463,451,384,268⟩⟩,⟨2,1224302334848571721909251,⟨395,459,409,152,304,104,224,384,264⟩⟩,⟨6,1224301181927067116110851,⟨395,399,413,152,304,44,160,384,264⟩⟩]⟩
theorem node1191 : UpperPrefix a [3,6,4,7,8,2,5] 30 :=
  Boolean.leaf_sound a [3,6,4,7,8,2,5] 30 cert1191 (by decide +kernel)

theorem node1192 : UpperPrefix a [3,6,4,7,8,2] 30 :=
  branch_upper a [3,6,4,7,8,2] 30 (by decide) (fin9_cases _
  node1189
  node1190
  (invalid_upper a [3,6,4,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,2,4] 30 (by decide +kernel))
  node1191
  (invalid_upper a [3,6,4,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,2,8] 30 (by decide +kernel)))

theorem node1193 : UpperPrefix a [3,6,4,7,8] 30 :=
  branch_upper a [3,6,4,7,8] 30 (by decide) (fin9_cases _
  node1184
  node1188
  node1192
  (invalid_upper a [3,6,4,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,8,8] 30 (by decide +kernel)))

theorem node1194 : UpperPrefix a [3,6,4,7] 30 :=
  branch_upper a [3,6,4,7] 30 (by decide) (fin9_cases _
  node1155
  node1167
  node1176
  (invalid_upper a [3,6,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,7,7] 30 (by decide +kernel))
  node1193)

def cert1195 : Leaf := ⟨⟨436,432,0,164,390,0,308,52,180⟩,[(2,4),(5,1)],[(6,1,5),(0,4,2),(1,5,4)],⟨11,70,21,280,49,98,228,420,428⟩,⟨11,70,21,280,49,98,192,384,264⟩,[⟨3,1210181524487990427270657,⟨247,118,119,502,119,98,192,416,482⟩⟩]⟩
theorem node1195 : UpperPrefix a [3,6,4,8,0,1] 30 :=
  Boolean.leaf_sound a [3,6,4,8,0,1] 30 cert1195 (by decide +kernel)

def cert1196 : Leaf := ⟨⟨500,0,0,230,454,0,294,102,230⟩,[(1,5),(2,4),(5,1)],[(0,4,2)],⟨11,70,21,280,49,100,226,418,426⟩,⟨11,70,21,280,49,100,192,384,264⟩,[⟨3,1212547310408244422540801,⟨247,118,119,502,119,118,192,448,482⟩⟩,⟨4,1215024613581420024056833,⟨491,230,487,456,483,230,192,384,264⟩⟩]⟩
theorem node1196 : UpperPrefix a [3,6,4,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,8,0,2] 30 cert1196 (by decide +kernel)

def cert1197 : Leaf := ⟨⟨372,312,0,100,332,0,316,124,116⟩,[(2,4),(5,6)],[(0,4,2),(7,5,5)],⟨11,70,21,280,49,224,194,420,300⟩,⟨11,70,21,280,49,224,194,384,264⟩,[⟨1,1300007774849315286286337,⟨445,492,413,412,445,224,480,384,264⟩⟩]⟩
theorem node1197 : UpperPrefix a [3,6,4,8,0,7,1] 30 :=
  Boolean.leaf_sound a [3,6,4,8,0,7,1] 30 cert1197 (by decide +kernel)

def cert1198 : Local := ⟨⟨368,0,0,98,330,0,314,122,114⟩,[(1,6),(2,4),(5,6)],[(0,4,2),(7,5,5),(2,6,1)]⟩
theorem node1198 : UpperPrefix a [3,6,4,8,0,7,2] 30 :=
  local_sound a [3,6,4,8,0,7,2] 30 cert1198 (by decide +kernel)

def cert1199 : Local := ⟨⟨372,312,0,102,334,0,0,126,118⟩,[(2,4),(5,6),(6,5)],[(0,4,2),(7,5,5),(7,5,6)]⟩
theorem node1199 : UpperPrefix a [3,6,4,8,0,7,5] 30 :=
  local_sound a [3,6,4,8,0,7,5] 30 cert1199 (by decide +kernel)

theorem node1200 : UpperPrefix a [3,6,4,8,0,7] 30 :=
  branch_upper a [3,6,4,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,8,0,7,0] 30 (by decide +kernel))
  node1197
  node1198
  (invalid_upper a [3,6,4,8,0,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,0,7,4] 30 (by decide +kernel))
  node1199
  (invalid_upper a [3,6,4,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,0,7,8] 30 (by decide +kernel)))

theorem node1201 : UpperPrefix a [3,6,4,8,0] 30 :=
  branch_upper a [3,6,4,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,8,0,0] 30 (by decide +kernel))
  node1195
  node1196
  (invalid_upper a [3,6,4,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,0,6] 30 (by decide +kernel))
  node1200
  (invalid_upper a [3,6,4,8,0,8] 30 (by decide +kernel)))

def cert1202 : Leaf := ⟨⟨432,0,426,160,456,408,312,56,176⟩,[(1,6)],[(6,1,4),(1,4,2),(2,6,1)],⟨11,70,21,280,50,97,196,416,424⟩,⟨11,70,21,280,50,97,196,384,264⟩,[⟨0,1437223950379163726154752,⟨10,78,478,408,442,506,206,384,264⟩⟩]⟩
theorem node1202 : UpperPrefix a [3,6,4,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,8,1,0,2] 30 cert1202 (by decide +kernel)

def cert1203 : Leaf := ⟨⟨404,304,258,132,325,412,284,28,148⟩,[],[(6,1,4),(1,4,2)],⟨11,70,21,280,50,97,224,388,396⟩,⟨11,70,21,280,50,97,224,384,264⟩,[⟨0,1238497392643669522123776,⟨394,462,478,344,506,96,224,384,264⟩⟩,⟨5,1359148032901490792203283,⟨399,463,413,413,415,449,192,384,396⟩⟩,⟨3,1210107565290447690580993,⟨3,86,21,272,54,119,246,384,256⟩⟩,⟨7,1208926973669731353019393,⟨11,86,21,280,54,119,118,256,264⟩⟩]⟩
theorem node1203 : UpperPrefix a [3,6,4,8,1,0,5] 30 :=
  Boolean.leaf_sound a [3,6,4,8,1,0,5] 30 cert1203 (by decide +kernel)

theorem node1204 : UpperPrefix a [3,6,4,8,1,0] 30 :=
  branch_upper a [3,6,4,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,1,0,1] 30 (by decide +kernel))
  node1202
  (invalid_upper a [3,6,4,8,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,1,0,4] 30 (by decide +kernel))
  node1203
  (invalid_upper a [3,6,4,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,1,0,8] 30 (by decide +kernel)))

def cert1205 : Leaf := ⟨⟨432,0,426,161,461,0,297,41,161⟩,[(1,5),(5,1)],[(6,1,4),(1,4,2),(2,5,4)],⟨11,70,21,280,50,100,225,417,425⟩,⟨11,70,21,280,50,100,192,384,264⟩,[⟨4,1214876138908904873544705,⟨491,230,487,264,34,230,192,384,264⟩⟩]⟩
theorem node1205 : UpperPrefix a [3,6,4,8,1,2] 30 :=
  Boolean.leaf_sound a [3,6,4,8,1,2] 30 cert1205 (by decide +kernel)

def cert1206 : Leaf := ⟨⟨308,313,34,37,64,0,317,61,53⟩,[(5,6)],[(6,1,4),(1,4,2),(7,5,5)],⟨11,70,21,280,50,224,229,421,301⟩,⟨11,70,21,280,50,224,192,384,264⟩,[⟨3,1210107567535787865277441,⟨23,118,21,272,50,224,224,384,256⟩⟩,⟨8,1181747921159764313089,⟨31,118,21,24,50,224,224,128,8⟩⟩,⟨0,1210107567535788938757120,⟨26,118,20,280,50,224,224,384,264⟩⟩,⟨2,1210107567535788937708545,⟨27,114,17,280,50,224,224,384,264⟩⟩]⟩
theorem node1206 : UpperPrefix a [3,6,4,8,1,7] 30 :=
  Boolean.leaf_sound a [3,6,4,8,1,7] 30 cert1206 (by decide +kernel)

theorem node1207 : UpperPrefix a [3,6,4,8,1] 30 :=
  branch_upper a [3,6,4,8,1] 30 (by decide) (fin9_cases _
  node1204
  (invalid_upper a [3,6,4,8,1,1] 30 (by decide +kernel))
  node1205
  (invalid_upper a [3,6,4,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,1,6] 30 (by decide +kernel))
  node1206
  (invalid_upper a [3,6,4,8,1,8] 30 (by decide +kernel)))

def cert1208 : Leaf := ⟨⟨480,32,96,226,65,394,298,106,226⟩,[],[(0,5,4)],⟨11,70,21,280,52,97,226,418,426⟩,⟨11,70,21,280,52,97,192,384,264⟩,[⟨2,1224302389138057854977027,⟨491,491,505,280,56,481,192,384,264⟩⟩,⟨4,1252729335376007979346953,⟨491,230,487,491,230,481,192,416,489⟩⟩,⟨3,1210107565286049644037121,⟨3,70,21,272,54,119,192,384,256⟩⟩,⟨7,1208926973665333306475521,⟨11,70,21,280,54,119,64,256,264⟩⟩,⟨8,1181745671421543072769,⟨11,70,21,24,54,119,192,128,8⟩⟩,⟨1,1210107565286050717761537,⟨9,68,21,280,52,117,192,384,264⟩⟩]⟩
theorem node1208 : UpperPrefix a [3,6,4,8,2,0] 30 :=
  Boolean.leaf_sound a [3,6,4,8,2,0] 30 cert1208 (by decide +kernel)

def cert1209 : Leaf := ⟨⟨416,425,34,163,3,0,299,43,163⟩,[(5,1)],[(6,1,5)],⟨11,70,21,280,52,98,225,417,425⟩,⟨11,70,21,280,52,98,192,384,264⟩,[⟨2,1243524544840474208240643,⟨491,491,505,280,504,483,192,384,264⟩⟩,⟨4,1255094797670407501523977,⟨491,230,487,491,230,98,192,448,489⟩⟩,⟨3,1210107565354425515246593,⟨55,118,21,272,52,114,192,384,256⟩⟩,⟨7,1208926973733709177684993,⟨63,118,21,280,52,114,64,256,264⟩⟩,⟨8,1181745739797414282241,⟨63,118,21,24,52,114,192,128,8⟩⟩]⟩
theorem node1209 : UpperPrefix a [3,6,4,8,2,1] 30 :=
  Boolean.leaf_sound a [3,6,4,8,2,1] 30 cert1209 (by decide +kernel)

def cert1210 : Leaf := ⟨⟨352,297,96,99,65,0,299,107,99⟩,[(5,6)],[(7,5,5)],⟨11,70,21,280,52,224,227,419,299⟩,⟨11,70,21,280,52,224,192,384,264⟩,[⟨2,1224302391389857668662275,⟨491,491,505,280,56,224,224,384,264⟩⟩,⟨4,1252729014001953319955465,⟨491,230,487,491,230,224,224,416,489⟩⟩,⟨1,1210107567535788939018241,⟨29,116,21,280,52,224,224,384,264⟩⟩,⟨3,1210107567535787865277441,⟨23,118,21,272,52,224,224,384,256⟩⟩,⟨8,1181747921159764313089,⟨31,118,21,24,52,224,224,128,8⟩⟩]⟩
theorem node1210 : UpperPrefix a [3,6,4,8,2,7] 30 :=
  Boolean.leaf_sound a [3,6,4,8,2,7] 30 cert1210 (by decide +kernel)

theorem node1211 : UpperPrefix a [3,6,4,8,2] 30 :=
  branch_upper a [3,6,4,8,2] 30 (by decide) (fin9_cases _
  node1208
  node1209
  (invalid_upper a [3,6,4,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,2,6] 30 (by decide +kernel))
  node1210
  (invalid_upper a [3,6,4,8,2,8] 30 (by decide +kernel)))

def cert1212 : Leaf := ⟨⟨176,184,168,160,9,154,60,56,176⟩,[],[(1,6,5),(2,7,6)],⟨11,70,21,280,176,97,194,388,296⟩,⟨11,70,21,280,176,97,194,388,264⟩,[⟨6,1437259618888212508836867,⟨11,143,413,408,444,445,131,396,264⟩⟩,⟨8,1184344681614152957193,⟨47,118,119,127,246,119,246,247,47⟩⟩,⟨0,1285705024657692535360512,⟨74,206,478,344,506,96,194,462,264⟩⟩]⟩
theorem node1212 : UpperPrefix a [3,6,4,8,7,0,1,2] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,0,1,2] 30 cert1212 (by decide +kernel)

def cert1213 : Leaf := ⟨⟨148,153,136,133,0,158,29,29,149⟩,[(4,7)],[(1,6,5),(5,7,4)],⟨11,70,21,280,176,97,194,416,268⟩,⟨11,70,21,280,176,97,194,416,264⟩,[⟨6,2372251289017076721648707,⟨267,271,413,408,444,445,415,444,264⟩⟩,⟨8,1184344681614152957193,⟨47,118,119,127,246,119,246,247,47⟩⟩]⟩
theorem node1213 : UpperPrefix a [3,6,4,8,7,0,1,5] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,0,1,5] 30 cert1213 (by decide +kernel)

theorem node1214 : UpperPrefix a [3,6,4,8,7,0,1] 30 :=
  branch_upper a [3,6,4,8,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,8,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,0,1,1] 30 (by decide +kernel))
  node1212
  (invalid_upper a [3,6,4,8,7,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,0,1,4] 30 (by decide +kernel))
  node1213
  (invalid_upper a [3,6,4,8,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,0,1,8] 30 (by decide +kernel)))

def cert1215 : Leaf := ⟨⟨240,0,224,226,64,144,49,122,242⟩,[(1,6)],[(2,6,1)],⟨11,70,21,280,176,97,196,418,298⟩,⟨11,70,21,280,176,97,196,384,264⟩,[⟨8,1184344681614152957193,⟨47,118,119,127,246,119,246,247,47⟩⟩,⟨0,1361518440643065151521792,⟨10,70,28,280,440,506,198,384,264⟩⟩,⟨1,1210107853659363381084161,⟨9,116,117,344,244,117,244,384,264⟩⟩,⟨3,1210107853659362307402753,⟨3,118,119,338,246,119,246,384,256⟩⟩]⟩
theorem node1215 : UpperPrefix a [3,6,4,8,7,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,0,2] 30 cert1215 (by decide +kernel)

#print axioms node1215
end Delivery.FiniteExclusion.Sharp3x6
