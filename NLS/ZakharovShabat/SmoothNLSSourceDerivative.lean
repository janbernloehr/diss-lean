import NLS.ZakharovShabat.SmoothNLSData

/-! Uniform physical time differentiation gives the original Hilbert source tangent. -/
noncomputable section
open Set Complex Filter Topology NLS.Fourier
open scoped ContDiff ComplexConjugate ENNReal
namespace NLS.ZakharovShabat

/-- The existing even-frequency restriction as a bounded linear map. -/
def physicalNLSPeriodHalveCLM : Coeff 2 →L[ℂ] Coeff 2 :=
  LinearMap.mkContinuous
    { toFun := Coeff.periodHalve
      map_add' := by intro a b; ext n; rfl
      map_smul' := by intro c a; ext n; rfl }
    1 (by intro a; simpa using Coeff.norm_periodHalve_le a)

/-- Continuous extraction of the period-one physical Fourier coordinates. -/
def physicalNLSUnitFourierCLM : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] Coeff 2 :=
  physicalNLSPeriodHalveCLM.comp continuousFourierCLM

theorem physicalNLSUnitFourierCLM_apply (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) (n : ℤ) :
    physicalNLSUnitFourierCLM f n =
      periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))) n := by
  change continuousFourierCLM f (2*n) = _
  rw [continuousFourierCLM_apply,← periodTwoCoefficient_circle]
  exact periodTwoCoefficient_periodic_even _ hf
    ((f.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))).intervalIntegrable 0 1) n

/-- The actual real Fourier source map, bounded in the uniform physical norm. -/
def physicalNLSSourceCLM : C(AddCircle (2 : ℝ), ℂ) →L[ℝ] CoeffPair 2 :=
  let A := physicalNLSUnitFourierCLM.restrictScalars ℝ
  let R : Coeff 2 →L[ℝ] Coeff 2 := (starL ℝ : Coeff 2 ≃L[ℝ] Coeff 2).toContinuousLinearMap.comp
    ((Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
  ((CoeffPair.inlCLM (p := 2)).restrictScalars ℝ).comp A +
    ((CoeffPair.inrCLM (p := 2)).restrictScalars ℝ).comp (R.comp A)

theorem physicalNLSSourceCLM_fst (f : C(AddCircle (2 : ℝ), ℂ)) (n : ℤ) :
    (physicalNLSSourceCLM f).fst n = physicalNLSUnitFourierCLM f n := by
  simp [physicalNLSSourceCLM]

theorem physicalNLSSourceCLM_snd (f : C(AddCircle (2 : ℝ), ℂ)) (n : ℤ) :
    (physicalNLSSourceCLM f).snd n = conj (physicalNLSUnitFourierCLM f (-n)) := by
  simp [physicalNLSSourceCLM]

/-- The bounded source map is exactly the previously constructed smooth source. -/
theorem physicalNLSSourceCLM_eq_smoothSource (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    physicalNLSSourceCLM f = (smoothPeriodOneSourceAt 2 f hf hp).val := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext n
    change (physicalNLSSourceCLM f).fst n = (smoothPeriodOneSourceAt 2 f hf hp).val.fst n
    rw [physicalNLSSourceCLM_fst,physicalNLSUnitFourierCLM_apply f hp,smoothPeriodOneSourceAt_fst]
  · ext n
    change (physicalNLSSourceCLM f).snd n = (smoothPeriodOneSourceAt 2 f hf hp).val.snd n
    have hreal : (smoothPeriodOneSourceAt 2 f hf hp).val.snd n =
        conj ((smoothPeriodOneSourceAt 2 f hf hp).val.fst (-n)) :=
      (smoothPeriodOneSourceAt 2 f hf hp).property n
    rw [physicalNLSSourceCLM_snd,hreal,
      physicalNLSUnitFourierCLM_apply f hp,smoothPeriodOneSourceAt_fst]

/-- Every classical NLS solution has a differentiable original Hilbert source;
its derivative is obtained from the actual uniform physical time derivative. -/
theorem IsClassicalNLSTrajectory.hasDerivAt_hilbertSource
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u) (time : ℝ) :
    HasDerivAt (fun t => (smoothPeriodOneSourceAt 2 (u t)
      (hu.spatial_smooth t) (hu.periodic t)).val)
      (physicalNLSSourceCLM (deriv u time)) time := by
  have he (t : ℝ) := physicalNLSSourceCLM_eq_smoothSource (u t)
    (hu.spatial_smooth t) (hu.periodic t)
  simp_rw [← he]
  exact physicalNLSSourceCLM.hasFDerivAt.comp_hasDerivAt time (hu.time_differentiable time).hasDerivAt

end NLS.ZakharovShabat
