import FiveFullTransfer
import FiveFullDelivery0
import FiveFullDelivery1
import FiveFullDelivery2
import FiveFullDelivery3
import FiveFullDelivery4
namespace Delivery.FiveFullCertificates
open FiveTypeWindow FiveFullArena
noncomputable def delivery (t : Fin 5) : LocalArena.Data R C :=
  if t=0 then FiveFullDelivery0.data else if t=1 then FiveFullDelivery1.data else
  if t=2 then FiveFullDelivery2.data else if t=3 then FiveFullDelivery3.data else FiveFullDelivery4.data
noncomputable def certificates : Certificates arena 24 where
  transfer := FiveFullTransfer.data
  transfer_checked := FiveFullTransfer.checked
  transfer_entries := FiveFullTransfer.entries
  delivery := delivery
  delivery_checked := by
    intro t
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl
    · simpa [delivery] using FiveFullDelivery0.checked
    · simpa [delivery] using FiveFullDelivery1.checked
    · simpa [delivery] using FiveFullDelivery2.checked
    · simpa [delivery] using FiveFullDelivery3.checked
    · simpa [delivery] using FiveFullDelivery4.checked
  delivery_entries := by
    intro t r c entry safe
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl
    · have result := FiveFullDelivery0.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 24≤24))⟩
    · have result := FiveFullDelivery1.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 16≤24))⟩
    · have result := FiveFullDelivery2.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 16≤24))⟩
    · have result := FiveFullDelivery3.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 17≤24))⟩
    · have result := FiveFullDelivery4.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 18≤24))⟩

#print axioms certificates
end Delivery.FiveFullCertificates
