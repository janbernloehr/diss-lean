import NLS.ComplexAnalysis.DiscBounds
import Mathlib.Topology.Algebra.Order.Field

/-!
# Vanishing from decay on expanding circles

The maximum-modulus step in the interpolation lemma needs only an
entire function whose boundary values tend uniformly to zero on
circles escaping to infinity. Each fixed value is bounded by those
boundary values and therefore vanishes.
-/

noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

/-- An entire function with arbitrarily small values on enclosing
circles vanishes identically. -/
theorem entire_eq_zero_of_arbitrarily_small_sphere
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsmall : ∀ z : ℂ, ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, ‖z‖ < R ∧
        ∀ w ∈ sphere (0 : ℂ) R, ‖F w‖ ≤ ε) :
    F = 0 := by
  funext z
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R,hR,hbound⟩ := hsmall z ε hε
  have hRpos : 0 < R := (norm_nonneg z).trans_lt hR
  have hz : ‖z-(0:ℂ)‖ ≤ R := by simpa using hR.le
  have hle := norm_le_of_sphere_bound hF 0 hRpos ε hbound hz
  simpa using hle

/-- Uniform decay on a sequence of expanding circles supplies the
arbitrarily small enclosing circles above. -/
theorem entire_eq_zero_of_small_on_expanding_circles
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ w ∈ sphere (0 : ℂ) (R n), ‖F w‖ ≤ ε) :
    F = 0 := by
  apply entire_eq_zero_of_arbitrarily_small_sphere hF
  intro z ε hε
  have hlarge : ∀ᶠ n : ℕ in atTop, ‖z‖ < R n :=
    hR.eventually (eventually_gt_atTop ‖z‖)
  obtain ⟨n,hn⟩ := ((hsmall ε hε).and hlarge).exists
  exact ⟨R n,hn.2,hn.1⟩

/-- If an entire quotient has the expected factorization, decay of
the ordinary quotient on expanding zero-free circles forces the
numerator to vanish. This is the final maximum-modulus step of the
interpolation uniqueness argument. -/
theorem entire_numerator_eq_zero_of_quotient_circle_decay
    (F G H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hfactor : ∀ z : ℂ, F z = H z * G z)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hG : ∀ n : ℕ, ∀ z ∈ sphere (0 : ℂ) (R n), G z ≠ 0)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ z ∈ sphere (0 : ℂ) (R n), ‖F z / G z‖ ≤ ε) :
    F = 0 := by
  have hHzero : H = 0 := by
    apply entire_eq_zero_of_small_on_expanding_circles hH R hR
    intro ε hε
    filter_upwards [hsmall ε hε] with n hn z hz
    have hq : F z / G z = H z := by
      rw [hfactor z]
      exact mul_div_cancel_right₀ (H z) (hG n z hz)
    rw [← hq]
    exact hn z hz
  funext z
  simp [hfactor z,hHzero]

end NLS.ComplexAnalysis
