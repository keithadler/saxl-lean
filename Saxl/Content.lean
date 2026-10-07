import Mathlib
import Saxl.Statement
import Saxl.Polytabloid

/-!
# Content of words and the permutation module `M^λ`

`content w i` counts the positions carrying letter `i`.  The position action preserves content, so
the functions supported on words of a fixed content form a subrepresentation `contentSub c` of
`wordRep n d`.  The polytabloid has the content of its row word (the row lengths of `μ`), hence
`spechtSub t ≤ contentSub (rowContent t)`.
-/

namespace OAI.Saxl

open Equiv

variable {n d : ℕ}

/-- Number of positions of `w` carrying the letter `i`. -/
def content (w : Fin n → Fin d) (i : Fin d) : ℕ := (Finset.univ.filter fun j => w j = i).card

/-- Precomposing with a permutation of positions preserves content. -/
theorem content_comp_perm (w : Fin n → Fin d) (g : Perm (Fin n)) :
    content (w ∘ g) = content w := by
  ext i
  unfold content
  exact Finset.card_equiv g (fun j => by simp)

/-- Functions supported on words of content `c`, as a subrepresentation of `wordRep n d`. -/
def contentSub (c : Fin d → ℕ) : Subrepresentation (wordRep n d) where
  toSubmodule :=
    { carrier := {f | ∀ w, content w ≠ c → f w = 0}
      add_mem' := fun {f g} hf hg w hw => by simp [hf w hw, hg w hw]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun a {f} hf w hw => by simp [hf w hw] }
  apply_mem_toSubmodule g {f} hf w hw := by
    show f (w ∘ g) = 0
    exact hf _ (by rwa [content_comp_perm])

/-- Unfolding membership in `contentSub c`. -/
theorem mem_contentSub {c : Fin d → ℕ} {f : WordSpace n d} :
    f ∈ contentSub c ↔ ∀ w, content w ≠ c → f w = 0 := Iff.rfl

/-- A basis word lies in the content space of its own content. -/
theorem single_mem_contentSub (w : Fin n → Fin d) :
    (Pi.single w (1 : ℂ) : WordSpace n d) ∈ contentSub (content w) := by
  intro w' hw'
  exact Pi.single_eq_of_ne (fun h => hw' (by rw [h])) _

variable {μ : YoungDiagram} (t : Tableau n μ)

/-- The polytabloid has the content of its row word. -/
theorem polytabloid_mem_contentSub :
    polytabloid t ∈ contentSub (content (rowWord t)) := by
  rw [polytabloid_eq_sum]
  refine Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_
  have := single_mem_contentSub (n := n) (rowWord t ∘ ((g : Perm (Fin n))⁻¹ : Perm (Fin n)))
  rwa [content_comp_perm] at this

/-- `S^λ ≤ M^λ`: the Specht module lies in the content-`λ` subrepresentation. -/
theorem spechtSub_le_contentSub :
    (spechtSub t).toSubmodule ≤ (contentSub (content (rowWord t))).toSubmodule := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact (contentSub _).apply_mem_toSubmodule g (polytabloid_mem_contentSub t)

/-- The content of the row word is the sequence of row lengths. -/
theorem content_rowWord (i : Fin (μ.colLen 0)) : content (rowWord t) i = μ.rowLen i := by
  unfold content
  rw [YoungDiagram.rowLen_eq_card]
  refine Finset.card_bij (fun j _ => (t j).val) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [YoungDiagram.mem_row_iff]
    exact ⟨(t j).2, by rw [← hj]; rfl⟩
  · intro j₁ _ j₂ _ h
    exact t.injective (Subtype.ext h)
  · intro c hc
    rw [YoungDiagram.mem_row_iff] at hc
    refine ⟨t.symm ⟨c, hc.1⟩, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    rw [rowWord_apply]
    simp [hc.2]

end OAI.Saxl
