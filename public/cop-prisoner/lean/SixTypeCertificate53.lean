import SixTypeObjective53Transfer
import SixTypeObjective53Delivery0
import SixTypeObjective53Delivery1
import SixTypeObjective53Delivery2
import SixTypeObjective53Delivery3
import SixTypeObjective53Delivery4
import SixTypeObjective53Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate53
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern53.pattern := by
  constructor
  · exact ⟨SixTypeObjective53Transfer.data, SixTypeObjective53Transfer.checked, SixTypeObjective53Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective53Delivery0.data, SixTypeObjective53Delivery0.checked, SixTypeObjective53Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective53Delivery1.data, SixTypeObjective53Delivery1.checked, SixTypeObjective53Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective53Delivery2.data, SixTypeObjective53Delivery2.checked, SixTypeObjective53Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective53Delivery3.data, SixTypeObjective53Delivery3.checked, SixTypeObjective53Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective53Delivery4.data, SixTypeObjective53Delivery4.checked, SixTypeObjective53Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective53Delivery5.data, SixTypeObjective53Delivery5.checked, SixTypeObjective53Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate53
