import NLS.SequenceSpaces.MultiplierCoordinateContinuity
import NLS.SequenceSpaces.CompactLpMultiplier
import NLS.SequenceSpaces.HolderEmbedding

/-!
# Compact lower Sobolev realizations of bounded stronger families

Raw coordinates need only be continuous. A uniform bound in one stronger
Sobolev norm supplies norm continuity in every strictly lower Sobolev norm.
On compact parameter spaces these exact lower realizations have compact range.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Positive inverse Sobolev weights have uniformly vanishing tails.
The auxiliary finite exponent is selected after the positive order. -/
theorem inverse_sobolev_vanishing_tails (d : ℝ) (hd : 0 < d) :
    ∀ ε > (0:ℝ), ∃ S : Finset ℤ, ∀ n ∉ S,
      ‖(Weight.sobolev d n:ℂ)⁻¹‖ ≤ ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/d))
  have hN1 : 1 ≤ N := by
    have h : (1:ℝ) ≤ N := (le_max_left _ _).trans hN.le
    exact_mod_cast h
  let q : ℝ≥0∞ := N
  let : Fact (1 ≤ q) := ⟨by
    change (1:ℝ≥0∞) ≤ (N:ℝ≥0∞)
    exact_mod_cast hN1⟩
  have hq : q ≠ ⊤ := by simp [q]
  have hqR : q.toReal = (N:ℝ) := by simp [q]
  have hq0 : 0 < q.toReal := by rw [hqR]; exact_mod_cast (by omega : 0 < N)
  have hdq : 1 < d*q.toReal := by
    rw [hqR]
    have h := (div_lt_iff₀ hd).mp ((le_max_right 1 (1/d)).trans_lt hN)
    nlinarith only [h]
  let a : Coeff q := ⟨fun n => (Weight.sobolev d n:ℂ)⁻¹,Weight.inverse_sobolev_memlp hq0 hdq⟩
  simpa only [a,exponentInclusion_apply] using exponentInclusion_top_vanishing_tails hq a

/-- A bounded higher Sobolev realization and continuous raw coordinates
produce a continuous exact realization at every strictly lower order. -/
theorem exists_continuous_lower_sobolev_family
    {X : Type*} [TopologicalSpace X] (f : X → ℤ → ℂ)
    (hc : ∀ n : ℤ, Continuous (fun x => f x n))
    (a b : ℝ) (hab : b < a) (F : X → Coeff p)
    (hF : ∀ x n, F x n = (Weight.sobolev a n:ℂ)*f x n)
    (R : ℝ) (hR : 0 ≤ R) (hB : ∀ x, ‖F x‖ ≤ R) :
    ∃ G : X → Coeff p, Continuous G ∧
      ∀ x n, G x n = (Weight.sobolev b n:ℂ)*f x n := by
  let d := a-b
  have hd : 0 < d := sub_pos.mpr hab
  let m : Coeff ⊤ := ⟨fun n => (Weight.sobolev d n:ℂ)⁻¹,
    Weight.inverse_sobolev_memlp_top hd.le⟩
  have hm : ∀ ε > (0:ℝ), ∃ S : Finset ℤ, ∀ n ∉ S, ‖m n‖ ≤ ε :=
    inverse_sobolev_vanishing_tails d hd
  have hcoord : ∀ n : ℤ, Continuous (fun x => F x n) := by
    intro n
    have he : (fun x => F x n) = fun x => (Weight.sobolev a n:ℂ)*f x n := funext fun x => hF x n
    rw [he]
    exact continuous_const.mul (hc n)
  refine ⟨fun x => multiplier m (F x),
    continuous_multiplier_of_bounded_coordinates m hm F R hR hB hcoord,?_⟩
  intro x n
  rw [multiplier_apply,hF]
  change (Weight.sobolev (a-b) n:ℂ)⁻¹*((Weight.sobolev a n:ℂ)*f x n) = _
  rw [← Weight.sobolev_ratio a b n]
  have hne : (Weight.sobolev a n:ℂ) ≠ 0 := (Weight.sobolev a).complex_ne_zero n
  calc
    _ = ((Weight.sobolev b n:ℂ)/(Weight.sobolev a n:ℂ)*
        (Weight.sobolev a n:ℂ))*f x n := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hne]

/-- On compact parameter spaces, every exact lower Sobolev realization
supplied by a bounded stronger family is continuous and has compact range. -/
theorem exists_compact_lower_sobolev_family
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (f : X → ℤ → ℂ)
    (hc : ∀ n : ℤ, Continuous (fun x => f x n))
    (a b : ℝ) (hab : b < a) (F : X → Coeff p)
    (hF : ∀ x n, F x n = (Weight.sobolev a n:ℂ)*f x n)
    (R : ℝ) (hR : 0 ≤ R) (hB : ∀ x, ‖F x‖ ≤ R) :
    ∃ G : X → Coeff p, Continuous G ∧
      (∀ x n, G x n = (Weight.sobolev b n:ℂ)*f x n) ∧ IsCompact (range G) := by
  obtain ⟨G,hG,he⟩ := exists_continuous_lower_sobolev_family f hc a b hab F hF R hR hB
  exact ⟨G,hG,he,isCompact_range hG⟩

end NLS.Coeff
