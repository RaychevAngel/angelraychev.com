import SixTypeObjective02Transfer
import SixTypeObjective02Delivery0
import SixTypeObjective02Delivery1
import SixTypeObjective02Delivery2
import SixTypeObjective02Delivery3
import SixTypeObjective02Delivery4
import SixTypeObjective02Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate02
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern02.pattern := by
  constructor
  · exact ⟨SixTypeObjective02Transfer.data, SixTypeObjective02Transfer.checked, SixTypeObjective02Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective02Delivery0.data, SixTypeObjective02Delivery0.checked, SixTypeObjective02Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective02Delivery1.data, SixTypeObjective02Delivery1.checked, SixTypeObjective02Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective02Delivery2.data, SixTypeObjective02Delivery2.checked, SixTypeObjective02Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective02Delivery3.data, SixTypeObjective02Delivery3.checked, SixTypeObjective02Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective02Delivery4.data, SixTypeObjective02Delivery4.checked, SixTypeObjective02Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective02Delivery5.data, SixTypeObjective02Delivery5.checked, SixTypeObjective02Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate02
