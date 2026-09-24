import NLS.ZakharovShabat.SourceActionHorizontalLimit
import NLS.ZakharovShabat.SourceActionGapSideIntegral

/-!
# Weighted cosine boundary values are gap-side path integrals

The selected-factor identity for the full canonical root converts
both weighted cosine boundary kernels to the upper and lower straight
gap-side kernels. The equality includes their endpoint integrals.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The upper and lower weighted cosine boundary integrals are the
corresponding straight gap-side path integrals. -/
theorem sourceAction_cosineBoundaryIntegral_eq_gapSidePathIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) (upper : Bool) :
    sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) upper =
      gapSidePathIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        (sourceActionGapNumerator hp hp1 ψ n q) (-1) 1 upper := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let F := sourceCriticalRootGapNumerator hp hp1 ψ n
  let G := sourceActionGapNumerator hp hp1 ψ n q
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgap := sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
    hp hp1 ψ hreal n hopen
  have hdom (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
        sourceStandardRootOmittedDomain hp hp1 ψ n :=
    sourceStandardRootGapSegment_subset_omittedDomain_of_realType
      hp hp1 ψ hreal n ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  have hpoint (θ : ℝ) (hθ : θ ∈ Ioo 0 Real.pi) :
      let t := Real.cos θ
      let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
      ((z-(q:ℂ)) *
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          (if upper then sourceCanonicalRootGapUpperValue hp hp1 ψ n t
            else sourceCanonicalRootGapLowerValue hp hp1 ψ n t))) *
        (δ*(Real.sin θ:ℂ)) =
      G (τ+δ*(t:ℂ)) *
        ((δ*(Real.sin θ:ℂ)) /
          ((if upper then -δ*I else δ*I) *
            (Real.sqrt (1-t^2):ℂ))) := by
    let t := Real.cos θ
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
    have ht : t ∈ Ioo (-1) 1 := cos_mem_gapInterior hθ
    have hfactor :
        deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          (if upper then sourceCanonicalRootGapUpperValue hp hp1 ψ n t
            else sourceCanonicalRootGapLowerValue hp hp1 ψ n t) =
        F z /
          ((if upper then -δ*I else δ*I) *
            (Real.sqrt (1-t^2):ℂ)) := by
      cases upper with
      | true =>
          have hf :=
            discriminant_derivative_div_canonicalRootGapUpperValue_eq_selectedFactor
              hp hp1 ψ n t hgap ht (hdom t ht)
          change deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
              sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
            F z / (-δ*I*(Real.sqrt (1-t^2):ℂ)) at hf
          simpa only [ite_true] using hf
      | false =>
          have hf :=
            discriminant_derivative_div_canonicalRootGapLowerValue_eq_selectedFactor
              hp hp1 ψ n t hgap ht (hdom t ht)
          change deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
              sourceCanonicalRootGapLowerValue hp hp1 ψ n t =
            F z / (δ*I*(Real.sqrt (1-t^2):ℂ)) at hf
          simpa only [Bool.false_eq_true, ite_false] using hf
    dsimp only [t,z]
    change ((z-(q:ℂ)) *
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          (if upper then sourceCanonicalRootGapUpperValue hp hp1 ψ n t
            else sourceCanonicalRootGapLowerValue hp hp1 ψ n t))) *
        (δ*(Real.sin θ:ℂ)) =
      ((z-(q:ℂ))*F z) *
        ((δ*(Real.sin θ:ℂ)) /
          ((if upper then -δ*I else δ*I) *
            (Real.sqrt (1-t^2):ℂ)))
    rw [hfactor]
    simp only [div_eq_mul_inv]
    ring
  have heq : sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) upper =
      gapSideBoundaryIntegral τ δ G 1 upper := by
    unfold sourceAction_cosineBoundaryIntegral gapSideBoundaryIntegral
    simp only [Real.arccos_one]
    apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro θ hθ
    exact hpoint θ hθ
  calc
    sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) upper =
        gapSideBoundaryIntegral τ δ G 1 upper := heq
    _ = gapSidePathIntegral τ δ G (-1) 1 upper :=
      (gapSidePathIntegral_eq_boundary τ δ G 1 hδ
        (by norm_num) (by norm_num) upper).symm

/-- The upper weighted cosine boundary integral is real and nonzero
on an open real-type gap. -/
theorem sourceAction_upper_cosineBoundaryIntegral_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    (sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true).im = 0 ∧
      sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true ≠ 0 := by
  rw [sourceAction_cosineBoundaryIntegral_eq_gapSidePathIntegral
    hp hp1 ψ hreal n hopen q true]
  exact sourceAction_upper_gapSidePathIntegral_sign
    hp hp1 ψ hreal n hopen q

/-- The two weighted boundary integrals have opposite signs because
the selected standard root changes sign across the cut. -/
theorem sourceAction_lower_cosineBoundaryIntegral_eq_neg_upper
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) false =
      -sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let F := sourceActionGapNumerator hp hp1 ψ n q
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  rw [sourceAction_cosineBoundaryIntegral_eq_gapSidePathIntegral
      hp hp1 ψ hreal n hopen q false,
    sourceAction_cosineBoundaryIntegral_eq_gapSidePathIntegral
      hp hp1 ψ hreal n hopen q true]
  rw [gapSidePathIntegral_eq_weighted τ δ F (-1) 1
      (by norm_num) (by norm_num) hδ false,
    gapSidePathIntegral_eq_weighted τ δ F (-1) 1
      (by norm_num) (by norm_num) hδ true]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  ring

end NLS.ZakharovShabat
