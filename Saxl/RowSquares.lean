import Mathlib

/-!
# The sum-of-squares argument of Prop 3.2 (paper eq. (3.9))

Positions are partitioned into rows `row : Fin N → ℕ` of lengths `len (row p)`.  Two assignments
`a b : Fin N → ℕ` each sum, on every row of length `r`, to `0 + 1 + ⋯ + (r - 1)`.  If
`∑ (a + b)² = ∑ (len - 1)²`, then `a + b = len - 1` everywhere.
-/

namespace OAI.Saxl

open Finset

theorem two_mul_sum_range_id (n : ℕ) : 2 * ∑ j ∈ range n, (j : ℤ) = (n : ℤ) * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

theorem eq_of_sum_sq_eq {N : ℕ} (row : Fin N → ℕ) (len : ℕ → ℕ) (a b : Fin N → ℕ)
    (hcard : ∀ i ∈ univ.image row, (univ.filter fun p => row p = i).card = len i)
    (ha : ∀ i ∈ univ.image row,
      ∑ p ∈ univ.filter (fun p => row p = i), (a p : ℤ) = ∑ j ∈ range (len i), (j : ℤ))
    (hb : ∀ i ∈ univ.image row,
      ∑ p ∈ univ.filter (fun p => row p = i), (b p : ℤ) = ∑ j ∈ range (len i), (j : ℤ))
    (hsq : ∑ p, ((a p : ℤ) + b p) ^ 2 = ∑ p, ((len (row p) : ℤ) - 1) ^ 2) :
    ∀ p, (a p : ℤ) + b p = (len (row p) : ℤ) - 1 := by
  -- cross term equals the square term of `k = len - 1`
  have hcross : ∑ p, ((a p : ℤ) + b p) * ((len (row p) : ℤ) - 1) =
      ∑ p, ((len (row p) : ℤ) - 1) ^ 2 := by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image row) (g := row)
        (fun p _ => mem_image_of_mem row (mem_univ p)),
      ← sum_fiberwise_of_maps_to (s := univ) (t := univ.image row) (g := row)
        (fun p _ => mem_image_of_mem row (mem_univ p))]
    refine sum_congr rfl fun i hi => ?_
    have h1 : ∑ p ∈ univ.filter (fun p => row p = i), ((a p : ℤ) + b p) * ((len (row p) : ℤ) - 1) =
        ((len i : ℤ) - 1) * (∑ p ∈ univ.filter (fun p => row p = i), (a p : ℤ) +
          ∑ p ∈ univ.filter (fun p => row p = i), (b p : ℤ)) := by
      rw [← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun p hp => ?_
      rw [(mem_filter.1 hp).2]; ring
    have h2 : ∑ p ∈ univ.filter (fun p => row p = i), ((len (row p) : ℤ) - 1) ^ 2 =
        (len i : ℤ) * ((len i : ℤ) - 1) ^ 2 := by
      rw [sum_congr rfl fun p hp => by rw [(mem_filter.1 hp).2], sum_const, hcard i hi,
        nsmul_eq_mul]
    rw [h1, h2, ha i hi, hb i hi, ← two_mul, two_mul_sum_range_id]
    ring
  have hzero : ∑ p, (((a p : ℤ) + b p) - ((len (row p) : ℤ) - 1)) ^ 2 = 0 := by
    have : ∀ p, (((a p : ℤ) + b p) - ((len (row p) : ℤ) - 1)) ^ 2 =
        ((a p : ℤ) + b p) ^ 2 - 2 * (((a p : ℤ) + b p) * ((len (row p) : ℤ) - 1)) +
          ((len (row p) : ℤ) - 1) ^ 2 := fun p => by ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hsq, hcross]
    ring
  intro p
  have := (sum_eq_zero_iff_of_nonneg fun p _ => sq_nonneg _).1 hzero p (mem_univ p)
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

end OAI.Saxl
