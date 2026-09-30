import NLS.ZakharovShabat.SourceAngularEndpointCommonDomain

/-!
# Angular integrals as genuine improper endpoint limits

The curve integrability proved for singular angular connectors means
that the integral of a shrinking initial parameter interval tends to
zero. Integrating from a positive parameter to the terminal parameter
therefore converges to the actual angular curve integral.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The singular start contributes no residual term when its initial
parameter interval is removed. The endpoint value is unrestricted. -/
theorem sourceAngular_initialIntegral_tendsto_zero
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (Q : ℂ × CoeffPair p → ℂ) (ψ : CoeffPair p) {a b : ℂ} (γ : Path a b)
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ) :
    Tendsto (fun u : ℝ => ∫ t in Ioc 0 u,
      curveIntegralFun (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ t)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hIoo := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hint
  exact tendsto_integral_Ioc_zero_of_integrableOn_Ioo (by norm_num) hIoo

/-- The actual angular path integral is the limit of its nonsingular
parameter truncations, so the curve integral realizes the improper integral. -/
theorem sourceAngularPathIntegral_eq_improper_limit
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (Q : ℂ × CoeffPair p → ℂ) (ψ : CoeffPair p) {a b : ℂ} (γ : Path a b)
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ) :
    Tendsto (fun u : ℝ => ∫ t in u..(1:ℝ),
      curveIntegralFun (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ t)
      (nhdsWithin 0 (Ioi 0)) (nhds (sourceAngularPathIntegral n s Q ψ γ)) := by
  let F := curveIntegralFun (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ
  have hIoo : IntegrableOn F (Ioo (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hint
  have hIcc : IntegrableOn F (Icc (0:ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioo).mpr hIoo
  have hcont : ContinuousOn (fun u : ℝ => ∫ t in u..(1:ℝ), F t) (Icc (0:ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left
      (a := (0:ℝ)) (b := 1) (by simpa only [uIcc_of_le zero_le_one] using hIcc)
    simpa only [uIcc_of_le zero_le_one] using h
  have hle : nhdsWithin (0:ℝ) (Ioi 0) ≤ nhdsWithin 0 (Icc 0 1) :=
    nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT (by norm_num : (0:ℝ) < 1))
  rw [sourceAngularPathIntegral,curveIntegral_def]
  exact (hcont.continuousWithinAt ⟨le_rfl,zero_le_one⟩).tendsto.mono_left hle

end NLS.ZakharovShabat
