import NLS.ZakharovShabat.SourceAngularIntegrand
import NLS.ZakharovShabat.SourceStandardRootComplexEndpointBound
import NLS.ZakharovShabat.SourceCriticalRootRatioTransverseBound

/-!
# Angular integrand bounds at complex periodic endpoints

After removing the selected standard root, the actual psi quotient
has an analytic numerator. Compactness bounds it on a small thickening
of the selected gap. Multiplication by the square root of the endpoint
distance controls the full angular integrand on either spectral sheet.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The regular part of the angular integrand after its selected
standard root is removed. This includes the literal factor `2i`. -/
def sourceAngularGapNumerator (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  sourcePsiCandidate n (z,(s n ψ : Coeff p)) /
    (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z)

/-- Exact selected-factor decomposition of the canonical-sheet
angular integrand, including the normalization constant. -/
theorem sourceAngularIntegrand_eq_gapNumerator_div_standardRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (z : ℂ) :
    sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ) =
      sourceAngularGapNumerator hp hp1 n m s ψ z / sourceStandardRoot hp hp1 ψ m z := by
  unfold sourceAngularIntegrand sourceAngularGapNumerator
  dsimp only
  rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem sourceAngularGapNumerator_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 m ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ m)) :
    AnalyticOnNhd ℂ (sourceAngularGapNumerator hp hp1 n m s ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ m) := by
  intro z hz
  have hnum : AnalyticAt ℂ (fun w => sourcePsiCandidate n (w,(s n ψ : Coeff p))) z :=
    (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,(s n ψ : Coeff p)) (mem_univ _)).comp
      (x := z) (f := fun w : ℂ => (w,(s n ψ : Coeff p)))
      (analyticAt_id.prod analyticAt_const)
  exact hnum.div (analyticAt_const.mul (hP z hz))
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m hz))

/-- A common positive bound at both complex endpoints, valid for
either square-root sign. The omitted-root domain hypotheses are the
actual spectral isolation and analyticity data, not an assumed bound. -/
theorem exists_sourceAngular_endpoint_weighted_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hD : IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ m))
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 m ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ m))
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ c ∈ ({l,r} : Set ℂ), ∀ z : ℂ,
        z ∈ sourceCanonicalRootDomain hp hp1 ψ → ‖c-z‖ ≤ ε →
        ∀ q : ℂ, q ^ 2 = sourceAngularRadicand hp (z,ψ) →
          ‖(sourcePsiCandidate n (z,(s n ψ : Coeff p)) / q) *
            ((Real.sqrt ((‖r-l‖/2)*‖c-z‖) : ℝ) : ℂ)‖ ≤ M := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let S := sourcePeriodicSegment hp hp1 ψ m
  let F := sourceAngularGapNumerator hp hp1 n m s ψ
  have hS : IsCompact S := by
    change IsCompact (segment ℝ l r)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨ε₀,hε₀,hthick⟩ := hS.exists_cthickening_subset_open hD hseg
  have hFcont : ContinuousOn F (cthickening ε₀ S) :=
    (sourceAngularGapNumerator_analyticOnNhd hp hp1 n m s ψ hP).continuousOn.mono hthick
  obtain ⟨C,hC⟩ := hS.cthickening.exists_bound_of_continuousOn hFcont
  let M := max C 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let d := ‖r-l‖ / 2
  have hd : 0 < d := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hgap.symm)) (by norm_num)
  refine ⟨min ε₀ d,M,lt_min hε₀ hd,hM,?_⟩
  intro c hc z hz hnear q hq
  have hcS : c ∈ S := by
    simp only [mem_insert_iff,mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hzK : z ∈ cthickening ε₀ S :=
    Metric.mem_cthickening_of_dist_le z c ε₀ S hcS (by
      rw [dist_eq_norm,norm_sub_rev]
      exact hnear.trans (min_le_left _ _))
  have hF : ‖F z‖ ≤ M := (hC z hzK).trans (by dsimp [M]; linarith [le_max_left C 0])
  have hroot : Real.sqrt (d*‖c-z‖) ≤ ‖sourceStandardRoot hp hp1 ψ m z‖ :=
    sourceStandardRoot_complexEndpoint_norm_lower_bound hp hp1 ψ m c z hc (hz m)
      (hnear.trans (min_le_right _ _))
  have hRne := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z (hz m)
  have hqnorm : ‖q‖ = ‖sourceCanonicalRoot hp hp1 ψ z‖ := by
    have hsq : q ^ 2 = sourceCanonicalRoot hp hp1 ψ z ^ 2 :=
      hq.trans (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z hz).symm
    rcases eq_or_eq_neg_of_sq_eq_sq q (sourceCanonicalRoot hp hp1 ψ z) hsq with h | h
    · rw [h]
    · rw [h,norm_neg]
  calc
    _ = ‖sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ) *
        ((Real.sqrt (d*‖c-z‖) : ℝ) : ℂ)‖ := by
      dsimp only [sourceAngularIntegrand,l,r,d]
      simp only [norm_mul,norm_div,hqnorm]
    _ = ‖(F z / sourceStandardRoot hp hp1 ψ m z) *
        ((Real.sqrt (d*‖c-z‖) : ℝ) : ℂ)‖ := by
      rw [sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s ψ z]
    _ ≤ M := norm_div_mul_real_le_of_weight_le_norm _ _ _ M
      (Real.sqrt_nonneg _) hM.le hF hroot hRne

end NLS.ZakharovShabat
