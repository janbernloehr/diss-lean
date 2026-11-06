import NLS.Articles.KdVConvexity.BaseContourTailSeries
import NLS.Articles.KdVConvexity.BaseContourSeries
import NLS.SequenceSpaces.WeightedScalarActionFamilyDescent

/-! # The common-neighborhood action extension step

Local analytic cubic moments in normalized Birkhoff coordinates descend
and glue on one neighborhood of the full weighted action cone. Their
literal weighted series is then analytic near the positive ell2 quadrant.
The real action-fiber invariance and coordinate-space period estimates
are explicit inputs. No KdV Birkhoff map or physical energy identity is
asserted in this file.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace NLS.Articles.KdVConvexity

/-- The original weighted actions of normalized Hilbert Birkhoff pairs. -/
abbrev normalizedCoordinateActions :=
  WeightedCoeff.actionsFromNormalizedCoordinates baseActionWeight

/-- Derive the global positive-ell2 analytic contour extension from
coordinate-space analyticity, real action invariance and local tail
bounds. The action neighborhood is constructed and is independent of n. -/
theorem global_contour_extension_from_coordinate_moments
    (M : ℕ+ → (Coeff 2 × Coeff 2) → ℂ) (W : Set (Coeff 2 × Coeff 2))
    (hW : IsOpen W) (hrealW : Coeff.realPairLocus 2 ⊆ W)
    (hM : ∀ n, AnalyticOnNhd ℂ (M n) W)
    (hinv : ∀ n, ∀ z ∈ W, ∀ v ∈ W,
      z ∈ Coeff.realPairLocus 2 → v ∈ Coeff.realPairLocus 2 →
      normalizedCoordinateActions v = normalizedCoordinateActions z → M n v = M n z)
    (hbound : ∀ z ∈ Coeff.realPairLocus 2,
      ∃ T : Set (Coeff 2 × Coeff 2), IsOpen T ∧ z ∈ T ∧ T ⊆ W ∧
        ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ∀ n ∉ s,
          ‖((8*(n : ℝ)*Real.pi : ℝ) : ℂ)*M n v‖ ≤
            C*‖(normalizedCoordinateActions v).val (actionIndexEquiv.symm n)‖^2) :
    ∃ U : Set BaseActionSpace, ∃ R : ℕ+ → BaseActionSpace → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U ∧
      (∀ n, AnalyticOnNhd ℂ (R n) U) ∧
      (∀ n, ∀ z ∈ Coeff.realPairLocus 2, R n (normalizedCoordinateActions z) = M n z) ∧
      IsOpen (baseActionInclusion ⁻¹' U) ∧ positiveQuadrant ⊆ baseActionInclusion ⁻¹' U ∧
      AnalyticOnNhd ℂ (contourHamiltonian R) (baseActionInclusion ⁻¹' U) ∧
      ∀ a ∈ baseActionInclusion ⁻¹' U,
        Summable (fun n => ‖weightedContourTerm R n (baseActionInclusion a)‖) := by
  let c : ℕ+ → ℂ := fun n => ((8*(n : ℝ)*Real.pi : ℝ) : ℂ)
  have hc (n : ℕ+) : c n ≠ 0 := by dsimp [c]; exact_mod_cast (by positivity : 0 < 8*(n : ℝ)*Real.pi).ne'
  let f : ℕ+ → (Coeff 2 × Coeff 2) → ℂ := fun n z => c n*M n z
  have hf : ∀ n, AnalyticOnNhd ℂ (f n) W := fun n => analyticOnNhd_const.mul (hM n)
  have hfi : ∀ n, ∀ z ∈ W, ∀ v ∈ W,
      z ∈ Coeff.realPairLocus 2 → v ∈ Coeff.realPairLocus 2 →
      normalizedCoordinateActions v = normalizedCoordinateActions z → f n v = f n z := by
    intro n z hz v hv hzr hvr he
    dsimp only [f]
    rw [hinv n z hz v hv hzr hvr he]
  obtain ⟨U,G,hU,hcone,hG,hrec,htail⟩ :=
    WeightedCoeff.exists_global_scalar_action_family_with_raw_tail_bounds baseActionWeight
      actionIndexEquiv.symm f W hW hrealW hf hfi (by
        intro z hz
        obtain ⟨T,hT,hzT,hTW,s,C,hC,hb⟩ := hbound z hz
        refine ⟨T,hT,hzT,hTW,s,C,hC,?_⟩
        intro v hv n hn
        exact hb v hv n hn)
  let R : ℕ+ → BaseActionSpace → ℂ := fun n b => G n b/c n
  have hR : ∀ n, AnalyticOnNhd ℂ (R n) U := fun n => (hG n).div_const
  have hweight (n : ℕ+) (b : BaseActionSpace) : weightedContourTerm R n b = G n b := by
    change c n*(G n b/c n) = G n b
    exact mul_div_cancel₀ _ (hc n)
  have hrecover (n : ℕ+) (z : Coeff 2 × Coeff 2) (hz : z ∈ Coeff.realPairLocus 2) :
      R n (normalizedCoordinateActions z) = M n z := by
    change G n (normalizedCoordinateActions z)/c n = M n z
    rw [hrec n z hz]
    change (c n*M n z)/c n = M n z
    exact mul_div_cancel_left₀ _ (hc n)
  have hboundR : ∀ b ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ b ∈ T ∧ T ⊆ U ∧
      ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ∀ n ∉ s,
        ‖weightedContourTerm R n v‖ ≤ C*‖v.val (actionIndexEquiv.symm n)‖^2 := by
    intro b hb
    obtain ⟨T,hT,hbT,hTU,s,C,hC,hbnd⟩ := htail b hb
    refine ⟨T,hT,hbT,hTU,s,C,hC,?_⟩
    intro v hv n hn
    rw [hweight]
    exact hbnd v hv n hn
  have hsum := global_analytic_contour_sum_from_base_tail_bounds R U hU hcone hR hboundR
  exact ⟨U,R,hU,hcone,hR,hrecover,hsum⟩

end NLS.Articles.KdVConvexity
