import NLS.SequenceSpaces.Weighted

/-! # Exact norm-convergence criterion at the infinity endpoint

Section 2's unrestricted norm-convergence sentence needs a finite exponent,
or vanishing weighted coefficients at infinity. A constant weighted sequence
has truncation error exactly one for every finite set of frequencies.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- At infinity, finite Fourier sums converge in norm exactly for c₀ coefficients. -/
theorem tendsto_truncate_top_iff (a : Coeff ⊤) :
    Tendsto (fun S : Finset ℤ => truncate S a) atTop (𝓝 a) ↔
      ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℤ, ∀ n ∉ S, ‖a n‖ ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨S,hS⟩ := Metric.tendsto_atTop.mp h ε hε
    refine ⟨S,fun n hn => ?_⟩
    have hb := lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) (truncate S a-a) n
    have he := hS S le_rfl
    rw [dist_eq_norm] at he
    simpa [hn] using hb.trans he.le
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨S,hS⟩ := h (ε/2) (by positivity)
    refine ⟨S,fun T hST => ?_⟩
    rw [dist_eq_norm]
    have hb : ‖truncate T a-a‖ ≤ ε/2 := by
      apply lp.norm_le_of_forall_le (by positivity)
      intro n
      by_cases hn : n ∈ T
      · simpa [hn] using (show (0 : ℝ) ≤ ε/2 by positivity)
      · simpa [hn] using hS n (fun hs => hn (hST hs))
    linarith

/-- Every finite truncation of the constant-one coefficient sequence has error one. -/
theorem norm_one_sub_truncate (S : Finset ℤ) :
    ‖(1 : Coeff ⊤)-truncate S 1‖ = 1 := by
  apply le_antisymm
  · simpa using norm_sub_truncate_le (by simp : (⊤ : ℝ≥0∞) ≠ 0) S (1 : Coeff ⊤)
  · obtain ⟨n,hn⟩ := S.exists_notMem
    have hb := lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0)
      ((1 : Coeff ⊤)-truncate S 1) n
    change ‖(1 : ℂ)-truncate S 1 n‖ ≤ _ at hb
    simpa [hn] using hb

/-- Section 2's norm convergence fails at infinity even with unit norm. -/
theorem not_tendsto_truncate_one :
    ¬Tendsto (fun S : Finset ℤ => truncate S (1 : Coeff ⊤)) atTop (𝓝 1) := by
  intro h
  obtain ⟨S,hS⟩ := (tendsto_truncate_top_iff 1).mp h (1/2) (by norm_num)
  obtain ⟨n,hn⟩ := S.exists_notMem
  have hb := hS n hn
  norm_num at hb

end NLS.Coeff
namespace NLS.WeightedCoeff

/-- The exact infinity-endpoint criterion for every positive weight. -/
theorem tendsto_truncate_top_iff (w : Weight) (a : WeightedCoeff w ⊤) :
    Tendsto (fun S : Finset ℤ => truncate w ⊤ S a) atTop (𝓝 a) ↔
      ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℤ, ∀ n ∉ S, ‖(w n : ℂ)*a.val n‖ ≤ ε := by
  have he : Tendsto (fun S : Finset ℤ => truncate w ⊤ S a) atTop (𝓝 a) ↔
      Tendsto (fun S : Finset ℤ => Coeff.truncate S (weightEquiv w ⊤ a))
        atTop (𝓝 (weightEquiv w ⊤ a)) := by
    constructor
    · intro h
      simpa only [Function.comp_def,weightIsometry,LinearIsometryEquiv.coe_mk,truncate,LinearEquiv.apply_symm_apply] using
        ((weightIsometry w ⊤).continuous.tendsto a).comp h
    · intro h
      have ht := ((weightIsometry w ⊤).symm.continuous.tendsto (weightEquiv w ⊤ a)).comp h
      change Tendsto (fun S : Finset ℤ => truncate w ⊤ S a) atTop
        (𝓝 ((weightEquiv w ⊤).symm (weightEquiv w ⊤ a))) at ht
      simpa only [LinearEquiv.symm_apply_apply] using ht
  exact he.trans (Coeff.tendsto_truncate_top_iff _)

/-- Coefficients inverse to the weight: their weighted values are identically one. -/
def inverseWeightCoefficients (w : Weight) : WeightedCoeff w ⊤ :=
  (weightEquiv w ⊤).symm 1

@[simp] theorem inverseWeightCoefficients_val (w : Weight) (n : ℤ) :
    (inverseWeightCoefficients w).val n = (w n : ℂ)⁻¹ := by
  change (1 : Coeff ⊤) n / (w n : ℂ) = _
  simp

@[simp] theorem norm_inverseWeightCoefficients (w : Weight) :
    ‖inverseWeightCoefficients w‖ = 1 := by
  rw [norm_eq,inverseWeightCoefficients,LinearEquiv.apply_symm_apply]
  exact norm_one

/-- The weighted norm error is exactly one for every finite Fourier sum. -/
theorem norm_inverseWeightCoefficients_sub_truncate (w : Weight) (S : Finset ℤ) :
    ‖inverseWeightCoefficients w-truncate w ⊤ S (inverseWeightCoefficients w)‖ = 1 := by
  rw [norm_eq,map_sub,truncate,inverseWeightCoefficients,LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact Coeff.norm_one_sub_truncate S

/-- Every positive weighted infinity space contains this norm-convergence counterexample. -/
theorem not_tendsto_truncate_inverseWeightCoefficients (w : Weight) :
    ¬Tendsto (fun S : Finset ℤ => truncate w ⊤ S (inverseWeightCoefficients w))
      atTop (𝓝 (inverseWeightCoefficients w)) := by
  intro h
  have he := ((weightIsometry w ⊤).continuous.tendsto (inverseWeightCoefficients w)).comp h
  apply Coeff.not_tendsto_truncate_one
  change Tendsto (fun S : Finset ℤ => weightEquiv w ⊤ (truncate w ⊤ S (inverseWeightCoefficients w)))
    atTop (𝓝 (weightEquiv w ⊤ (inverseWeightCoefficients w))) at he
  simpa only [truncate,inverseWeightCoefficients,LinearEquiv.apply_symm_apply] using he

/-- Section 2's universal norm-convergence assertion holds exactly at finite Banach exponents. -/
theorem forall_tendsto_truncate_iff (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (∀ a : WeightedCoeff w p,
      Tendsto (fun S : Finset ℤ => truncate w p S a) atTop (𝓝 a)) ↔ p ≠ ⊤ := by
  constructor
  · intro h hp
    subst p
    exact not_tendsto_truncate_inverseWeightCoefficients w (h (inverseWeightCoefficients w))
  · intro hp a
    exact tendsto_truncate w p hp a

end NLS.WeightedCoeff
