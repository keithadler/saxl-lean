import Mathlib

/-!
# Dominance order on partitions

Milestone 4 groundwork (paper §2, eq. (2.1)).  Partitions are `YoungDiagram`s; `λ ⊵ μ` means
every initial sum of row lengths of `λ` is at least that of `μ`.
-/

namespace OAI.Saxl

open YoungDiagram

/-- Sum of the first `k` row lengths. -/
def rowSum (μ : YoungDiagram) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, μ.rowLen i

/-- `Dominates λ μ` : `λ ⊵ μ`. -/
def Dominates (lam mu : YoungDiagram) : Prop := ∀ k, rowSum mu k ≤ rowSum lam k

namespace Dominates

theorem refl (lam : YoungDiagram) : Dominates lam lam := fun _ => le_rfl

theorem trans {a b c : YoungDiagram} (h₁ : Dominates a b) (h₂ : Dominates b c) :
    Dominates a c := fun k => (h₂ k).trans (h₁ k)

end Dominates

end OAI.Saxl
