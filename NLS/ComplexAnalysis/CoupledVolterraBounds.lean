import NLS.ComplexAnalysis.IntegratedDecayBounds
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Linarith

/-!
# Closing the coupled slow and fast coordinate bounds

The fast equation gains an inverse decay rate. Feeding it into the slow
equation gives a small multiple of the slow supremum norm, which can be
absorbed when the decay rate is at least twice the squared coupling bound.
-/

noncomputable section
open Set Complex intervalIntegral
namespace NLS.ComplexAnalysis

/-- Quantitative bounds for two coupled Volterra equations, with no assumed
bound on either unknown coordinate. -/
theorem coupled_volterra_bounds (u v p q : ℝ → ℂ) (c : ℂ) (a M : ℝ)
    (hu : Continuous u) (ha : 0 < a) (hM : 0 ≤ M) (hc : c.re = -a)
    (hlarge : 2 * M^2 ≤ a)
    (hp : ∀ s ∈ Icc (0 : ℝ) 1, ‖p s‖ ≤ M)
    (hq : ∀ s ∈ Icc (0 : ℝ) 1, ‖q s‖ ≤ M)
    (hu_eq : ∀ t : Icc (0 : ℝ) 1, u t = u 0 + ∫ s in 0..t.val, p s * v s)
    (hv_eq : ∀ t : Icc (0 : ℝ) 1, v t = exp (c * t.val) * v 0 +
      ∫ s in 0..t.val, exp (c * (t.val - s)) * (q s * u s)) :
    let K := 2 * (‖u 0‖ + M * ‖v 0‖ / a)
    ∀ t : Icc (0 : ℝ) 1,
      ‖u t‖ ≤ K ∧
      ‖u t - u 0‖ ≤ M * (‖v 0‖ / a + M * K / a) ∧
      ‖v t - exp (c * t.val) * v 0‖ ≤ M * K / a := by
  dsimp only
  let U : C(Icc (0 : ℝ) 1, ℂ) := ⟨fun t => u t, hu.comp continuous_subtype_val⟩
  let C := ‖U‖
  have hC0 : 0 ≤ C := norm_nonneg U
  have hub (s : Icc (0 : ℝ) 1) : ‖u s‖ ≤ C := U.norm_coe_le_norm s
  have hfast (t : Icc (0 : ℝ) 1) :
      ‖v t - exp (c * t.val) * v 0‖ ≤ M * C / a := by
    rw [hv_eq t, add_sub_cancel_left]
    apply norm_integral_exp_propagator_mul_le c a t.val (M*C) ha t.property.1
      (mul_nonneg hM hC0) hc
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans t.property.2⟩
    rw [norm_mul]
    exact mul_le_mul (hq s hs') (hub ⟨s, hs'⟩) (norm_nonneg _) hM
  have hvb (s : Icc (0 : ℝ) 1) :
      ‖v s‖ ≤ Real.exp (-a * s.val) * ‖v 0‖ + M*C/a := by
    have he : ‖exp (c * s.val)‖ = Real.exp (-a * s.val) := by
      simpa only [sub_zero, Complex.ofReal_zero] using norm_exp_propagator c a s.val 0 hc
    calc
      ‖v s‖ ≤ ‖v s - exp (c * s.val) * v 0‖ + ‖exp (c * s.val) * v 0‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ M*C/a + Real.exp (-a * s.val) * ‖v 0‖ := by
        rw [norm_mul, he]
        exact add_le_add (hfast s) le_rfl
      _ = _ := by ring
  have hslow (t : Icc (0 : ℝ) 1) :
      ‖u t - u 0‖ ≤ M * (‖v 0‖/a + M*C/a) := by
    rw [hu_eq t, add_sub_cancel_left]
    apply norm_integral_mul_le_of_decay p v a t.val M ‖v 0‖ (M*C/a)
      ha t.property hM (norm_nonneg _) (by positivity)
    · intro s hs
      exact hp s ⟨hs.1, hs.2.trans t.property.2⟩
    · intro s hs
      exact hvb ⟨s, ⟨hs.1, hs.2.trans t.property.2⟩⟩
  have hsup : C ≤ ‖u 0‖ + M * (‖v 0‖/a + M*C/a) := by
    apply (ContinuousMap.norm_le U (by positivity)).mpr
    intro t
    exact (norm_le_norm_sub_add (u t) (u 0)).trans
      ((add_le_add (hslow t) le_rfl).trans_eq (add_comm _ _))
  have hratio : M^2/a ≤ 1/2 := (div_le_iff₀ ha).mpr (by linarith)
  have hsmall := mul_le_mul_of_nonneg_right hratio hC0
  have hsup' : C ≤ (‖u 0‖ + M*‖v 0‖/a) + (M^2/a)*C := by
    convert! hsup using 1
    ring
  have hC : C ≤ 2 * (‖u 0‖ + M*‖v 0‖/a) := by nlinarith
  have herr := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hC hM) ha.le
  intro t
  exact ⟨(hub t).trans hC,
    (hslow t).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl herr) hM),
    (hfast t).trans herr⟩

end NLS.ComplexAnalysis
