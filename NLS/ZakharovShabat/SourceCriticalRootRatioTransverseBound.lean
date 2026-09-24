import NLS.ZakharovShabat.SourceStandardRootTransverseBound

/-!
# Uniformly dominated transverse critical-root quotient

After multiplying by the cosine-path Jacobian, the selected root's
endpoint singularity is uniformly canceled. The remaining critical
numerator is bounded on a transverse neighborhood of the gap.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every point on a real-type periodic gap segment has zero imaginary
part. -/
theorem sourcePeriodicSegment_im_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment hp hp1 ψ n) : z.im = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hl : l.im = 0 := hends.1
  have hr : r.im = 0 := hends.2
  change z ∈ segment ℝ l r at hz
  obtain ⟨a,b,_,_,_,rfl⟩ := hz
  simp [hl, hr]

/-- A nonzero vertical displacement of the selected real gap avoids
the selected gap segment; avoidance of the other gaps suffices for
membership in the full canonical-root domain. -/
theorem sourceCanonicalRootGapPoint_vertical_mem_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (t y : ℝ) (hy : y ≠ 0)
    (hother : sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I ∈
      sourceCanonicalRootDomain hp hp1 ψ := by
  have hpoint : (sourceCanonicalRootGapPoint hp hp1 ψ n t).im = 0 := by
    rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
      hp hp1 ψ hreal n t]
    simp
  have hzim : (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I).im = y := by
    simp [hpoint]
  intro m
  by_cases hm : m = n
  · subst m
    intro hmem
    have hzero := sourcePeriodicSegment_im_eq_zero_of_realType
      hp hp1 ψ hreal n _ hmem
    exact hy (by linarith)
  · exact hother m hm

/-- A bound on the regular numerator and a matching lower bound on the
singular root give a uniform bound after multiplying by the real
Jacobian weight. -/
theorem norm_div_mul_real_le_of_weight_le_norm
    (F B : ℂ) (w M : ℝ) (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hF : ‖F‖ ≤ M) (hroot : w ≤ ‖B‖) (hB : B ≠ 0) :
    ‖(F / B) * (w : ℂ)‖ ≤ M := by
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hwB : w / ‖B‖ ≤ 1 := (div_le_one hBpos).2 hroot
  have hwBnonneg : 0 ≤ w / ‖B‖ := div_nonneg hw hBpos.le
  calc
    ‖(F / B) * (w : ℂ)‖ = ‖F‖ * (w / ‖B‖) := by
      rw [norm_mul, norm_div]
      simp [Real.norm_eq_abs, abs_of_nonneg hw]
      ring
    _ ≤ M * (w / ‖B‖) := mul_le_mul_of_nonneg_right hF hwBnonneg
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hwB hM
    _ = M := mul_one _

/-- The critical-root quotient, weighted by the cosine-path Jacobian,
is uniformly bounded on short nonzero vertical approaches to the
closed parameter interval of an open real periodic gap. -/
theorem exists_sourceCriticalRootRatio_transverse_weighted_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, ∀ y : ℝ, y ≠ 0 → |y| ≤ ε →
        let z := sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I
        ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
            sourceCanonicalRoot hp hp1 ψ z) *
          (((b-a)/2 * Real.sqrt (1-t^2) : ℝ) : ℂ)‖ ≤ M := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let S := standardRootGapSegment
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
  obtain ⟨ε,M,hε,hM,hKdom,hFbound⟩ :=
    exists_sourceCriticalRootGap_thickening_regularNumerator_bound
      hp hp1 ψ hreal n
  refine ⟨ε,M,hε,hM,?_⟩
  intro t ht y hy hyε
  let q := sourceCanonicalRootGapPoint hp hp1 ψ n t
  let z := q + (y:ℂ)*I
  let w : ℝ := (b-a)/2 * Real.sqrt (1-t^2)
  have hqS : q ∈ S := by
    exact ⟨t, ht, rfl⟩
  have hdist : dist z q = |y| := by
    calc
      dist z q = ‖(y:ℂ)*I‖ := by
        rw [dist_eq_norm]
        congr 1
        dsimp [z]
        ring
      _ = |y| := by simp
  have hzK : z ∈ cthickening ε S :=
    Metric.mem_cthickening_of_dist_le z q ε S hqS
      (by simpa [hdist] using hyε)
  have hzother : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n :=
    hKdom hzK
  have hzfull : z ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootGapPoint_vertical_mem_domain
      hp hp1 ψ hreal n t y hy hzother
  have hF : ‖sourceCriticalRootGapNumerator hp hp1 ψ n z‖ ≤ M :=
    hFbound z hzK
  have hw : 0 ≤ w := by
    dsimp [w]
    exact mul_nonneg (by dsimp [a,b] at *; linarith)
      (Real.sqrt_nonneg _)
  have hroot : w ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ :=
    sourceStandardRoot_transverse_norm_lower_bound
      hp hp1 ψ hreal n hopen t y ht hy
  have hB : sourceStandardRoot hp hp1 ψ n z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hzfull n)
  have hfactor :
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z =
        sourceCriticalRootGapNumerator hp hp1 ψ n z /
          sourceStandardRoot hp hp1 ψ n z := by
    rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension
      hp hp1 ψ n z hzfull]
    unfold sourceCriticalRootGapNumerator
    simp only [div_eq_mul_inv]
    ring
  dsimp only
  rw [hfactor]
  exact norm_div_mul_real_le_of_weight_le_norm _ _ w M hw hM.le
    hF hroot hB

end NLS.ZakharovShabat
