import NLS.ZakharovShabat.SourceAngularEtaCosineRepresentative
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue
import NLS.ZakharovShabat.SourceNormalizedActionFactorContinuity
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls

/-!
# Exact endpoint periods of the actual cosine primitives

The normalized psi circle is twice the upper gap-side integral. The
cosine substitution and the fundamental theorem of calculus identify
that half period with the angle primitive at zero. Real-form analytic
continuation gives the same Kronecker values on one complex source ball,
simultaneously for every numerator index. In particular, the diagonal
primitive at zero is minus i pi, and either eta sheet has value plus or
minus pi at the right endpoint.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- The primitive's full real angle interval is the reversed integral
of its actual regular cosine numerator. -/
theorem primitive_zero_angle_eq_neg_integral
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    sourceAngularCanonicalCosinePrimitive hp hp1 n m s (0,ψ) =
      -(∫ θ in (0 : ℝ)..Real.pi, sourceAngularGapNumerator hp hp1 n m s ψ
        (sourceCanonicalCosinePoint hp hp1 m ((θ : ℂ),ψ))) := by
  let H : ℂ → ℂ := fun θ => sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ)
  let g : ℂ → ℂ := fun θ => sourceAngularGapNumerator hp hp1 n m s ψ
    (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))
  have hangle (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) : (θ : ℂ) ∈ Ω := by
    apply D.angle_segment
    have ht : θ / Real.pi ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hθ.1 Real.pi_pos.le,(div_le_one Real.pi_pos).mpr hθ.2⟩
    convert lineMap_mem_segment ℝ (0 : ℂ) (Real.pi : ℂ) ht using 1
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul,mul_zero,zero_add,Complex.ofReal_div]
    field_simp
  have hH : ∀ θ ∈ Ω, HasDerivAt H (g θ) θ := D.primitive_derivative n ψ hψ
  have hcont : ContinuousOn (fun θ : ℝ => H (θ : ℂ)) (Icc 0 Real.pi) :=
    (show ContinuousOn H Ω from fun θ hθ => (hH θ hθ).continuousAt.continuousWithinAt).comp
      Complex.continuous_ofReal.continuousOn hangle
  have hg : ContinuousOn (fun θ : ℝ => g (θ : ℂ)) (Icc 0 Real.pi) := by
    have hga : AnalyticOnNhd ℂ g Ω := fun θ hθ =>
      (D.numerator_analytic n (θ,ψ) ⟨hθ,hψ⟩).comp
        (f := fun θ : ℂ => (θ,ψ)) (analyticAt_id.prod analyticAt_const)
    exact hga.continuousOn.comp Complex.continuous_ofReal.continuousOn hangle
  have hint : IntervalIntegrable (fun θ : ℝ => g (θ : ℂ)) volume 0 Real.pi :=
    hg.intervalIntegrable_of_Icc Real.pi_pos.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le hcont
    (fun θ hθ => (hH _ (hangle θ (Ioo_subset_Icc_self hθ))).comp_ofReal) hint
  have hnorm : H (Real.pi : ℂ) = 0 := sourceAngularCanonicalCosinePrimitive_pi hp hp1 n m s ψ
  change H 0 = -(∫ θ in (0 : ℝ)..Real.pi, g (θ : ℂ))
  simpa only [Complex.ofReal_zero,hnorm,zero_sub,neg_neg] using (congrArg Neg.neg hFTC).symm

/-- The actual psi normalization determines every full-gap cosine
period at a real source, including the previously missing diagonal. -/
theorem primitive_zero_angle_of_real
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    sourceAngularCanonicalCosinePrimitive hp hp1 n m s (0,ψ) =
      -I * (Real.pi : ℂ) * (if m = n then 1 else 0) := by
  classical
  let g := sourceAngularGapNumerator hp hp1 n m s ψ
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let δ := sourceStandardRootHalfGap hp hp1 ψ m
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let a : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  let H₀ := sourceAngularCanonicalCosinePrimitive hp hp1 n m s (0,ψ)
  let P := if m = n then (1 : ℂ) else 0
  have hfamily := (D.disc_family ψ hψ).contour_family
  have hgeom := hfamily.2 m
  have hcenter : ((c m).re : ℂ) = c m :=
    Complex.ext rfl (by simpa using (hfamily.1 m).symm)
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 m ψ hreal
    (by simpa only [sourcePeriodicGapDisplacement_apply] using D.gap_ne_zero ψ hψ)
  have hd : 0 < d := div_pos (sub_pos.mpr hopen) (by norm_num)
  have hg : AnalyticOnNhd ℂ g (closedBall (c m) (R m)) :=
    (sourceAngularGapNumerator_analyticOnNhd hp hp1 n m s ψ
      (D.endpoint_data ψ hψ).analytic_omitted).mono hgeom.2.2.1
  have hgap : standardRootGapSegment τ δ ⊆ ball (c m) (R m) := by
    rintro z ⟨t,ht,rfl⟩
    exact hgeom.2.1 (sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ m t ht.1 ht.2)
  obtain ⟨ρ,hρ,hnest⟩ := exists_sourceStandardRoot_innerMidpointDisc_of_realCenteredCircle
    hp hp1 ψ hreal m (c m).re (R m) (by simpa only [hcenter] using hgeom.2.1)
  change d < ρ at hρ
  change closedBall a ρ ⊆ ball ((c m).re : ℂ) (R m) at hnest
  rw [hcenter] at hnest
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball a ρ := by
    have h := sourcePeriodicSegment_subset_midpoint_ball hp hp1 ψ hreal m (ρ-d) (sub_pos.mpr hρ)
    change sourcePeriodicSegment hp hp1 ψ m ⊆ ball a (d+(ρ-d)) at h
    simpa only [show d+(ρ-d)=ρ by ring] using h
  have hcircle := weighted_sourceStandardRoot_midpointCircle_eq_boundary_of_local_disc
    hp hp1 ψ hreal m hopen g (ball (c m) (R m)) isOpen_ball hgap
      (hg.mono ball_subset_closedBall) ρ hρ hnest
  have houter : (∮ z in C(c m,R m), g z / sourceStandardRoot hp hp1 ψ m z) =
      -(2 * gapSideBoundaryIntegral τ δ g 1 true) := by
    rw [← hcircle]
    exact (circleIntegral_weighted_sourceStandardRoot_eq_of_local_nestedCircles
      hp hp1 ψ m g (closedBall (c m) (R m)) hg a (c m) ρ (R m)
        (hd.trans hρ) hgeom.1 hseg hgeom.2.1
        (hnest.trans ball_subset_closedBall) Subset.rfl).symm
  have hperiod := (D.disc_family ψ hψ).periods n m
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hraw : (∮ z in C(c m,R m), g z / sourceStandardRoot hp hp1 ψ m z) =
      (2 * Real.pi : ℂ) * P := by
    have hfun : (fun z => sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ : Coeff p),ψ))) =
        (fun z => g z / sourceStandardRoot hp hp1 ψ m z) := by
      funext z
      exact sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s ψ z
    unfold sourcePsiContour at hperiod
    rw [hfun] at hperiod
    simpa only [← mul_assoc,mul_inv_cancel₀ hπ,one_mul] using
      congrArg (fun z : ℂ => (2 * Real.pi : ℂ) * z) hperiod
  have hH₀ := D.primitive_zero_angle_eq_neg_integral ψ hψ n
  change H₀ = -(∫ θ in (0 : ℝ)..Real.pi, g (sourceCanonicalCosinePoint hp hp1 m ((θ : ℂ),ψ))) at hH₀
  have hpoint (θ : ℝ) : τ + δ * (Real.cos θ : ℂ) =
      sourceCanonicalCosinePoint hp hp1 m ((θ : ℂ),ψ) := by
    change τ + δ * (Real.cos θ : ℂ) = cosineGapPoint τ δ (θ : ℂ)
    rw [cosineGapPoint,Complex.ofReal_cos]
  have hi : (∫ θ in (0 : ℝ)..Real.pi, g (τ + δ * (Real.cos θ : ℂ))) =
      ∫ θ in (0 : ℝ)..Real.pi, g (sourceCanonicalCosinePoint hp hp1 m ((θ : ℂ),ψ)) := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact congrArg g (hpoint θ)
  have hB : gapSideBoundaryIntegral τ δ g 1 true = -I * H₀ := by
    rw [gapSideBoundaryIntegral_eq_primitive τ δ g 1
      (div_ne_zero (D.gap_ne_zero ψ hψ) (by norm_num)) true]
    simp only [gapSidePrimitive,ite_true,Real.arccos_one]
    rw [hi,hH₀]
    ring
  have heq : (2 * Real.pi : ℂ) * P = 2 * I * H₀ := by
    rw [← hraw,houter,hB]
    ring
  change H₀ = -I * (Real.pi : ℂ) * P
  have hInv : (-I / 2) * (2 * I) = 1 := by
    calc
      _ = -(I * I) := by ring
      _ = 1 := by rw [I_mul_I]; norm_num
  calc
    H₀ = ((-I / 2) * (2 * I)) * H₀ := by rw [hInv,one_mul]
    _ = (-I / 2) * ((2 * I) * H₀) := by ring
    _ = (-I / 2) * ((2 * Real.pi : ℂ) * P) := by rw [← heq]
    _ = -I * (Real.pi : ℂ) * P := by ring

/-- One complex source ball has the exact full-gap Kronecker periods
for all numerator indices, by analytic continuation from its real form. -/
theorem exists_local_primitive_zero_angle_periods
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∀ ψ ∈ U, ∀ n : ℤ, sourceAngularCanonicalCosinePrimitive hp hp1 n m s (0,ψ) =
        -I * (Real.pi : ℂ) * (if m = n then 1 else 0) := by
  classical
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp D.source_open φ hφ
  refine ⟨ball φ ρ,isOpen_ball,mem_ball_self hρ,hball,?_⟩
  intro ψ hψ n
  let f : CoeffPair p → ℂ := fun χ => sourceAngularCanonicalCosinePrimitive hp hp1 n m s (0,χ)
  have hf : DifferentiableOn ℂ f (ball φ ρ) := by
    intro χ hχ
    exact ((D.primitive_analytic n (0,χ) ⟨D.angle_segment (left_mem_segment ℝ _ _),hball hχ⟩).comp
      (f := fun χ : CoeffPair p => (0,χ)) (analyticAt_const.prod analyticAt_id)).differentiableAt.differentiableWithinAt
  have heq := eqOn_sourceRealCenteredBalls_of_real_agreement hp ⟨φ,hreal⟩ ⟨φ,hreal⟩ ρ ρ f
    (fun _ => -I * (Real.pi : ℂ) * (if m = n then 1 else 0)) hf (differentiableOn_const _) (by
      intro χ hχ
      exact D.primitive_zero_angle_of_real χ.val (hball hχ.1) χ.property n)
  exact heq ⟨hψ,hψ⟩

end SourceAngularCanonicalCosineChartData
end NLS.ZakharovShabat
