import OddEndpointObjective073Transfer
import OddEndpointObjective073Delivery0
import OddEndpointObjective073Delivery1
import OddEndpointObjective073Delivery2
import OddEndpointObjective073Delivery3
import OddEndpointObjective073Delivery4
import OddEndpointObjective073Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate073
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern073
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective073Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective073Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective073Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective073Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective073Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective073Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective073Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate073
