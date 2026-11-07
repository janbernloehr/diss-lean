import NLS.ZakharovShabat.SourcePsiIsospectralRoots
import NLS.ZakharovShabat.SourcePsiReflectionPeriods

/-! Infinitesimal isospectral invariance needs only analyticity and
agreement with the actual real normalized roots. Quadratic descent is
performed on the root variable itself, so its filled zero-energy value
has the same invariance without dividing by frequency. -/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem fderiv_actualPsiRoots_isospectral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : CoeffPair p → DeletedCoeff p n) (φ : realTypeSourceLocus p)
    (hs : AnalyticAt ℂ s φ.val)
    (hreal : ∀ χ : realTypeSourceLocus p, s χ.val = sourcePsiGapRoot hp hp1 n χ)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    (fderiv ℂ s φ.val) h = 0 := by
  obtain ⟨t,ht,hrealEvent,hstationary⟩ :=
    exists_sourcePsiGapRoot_isospectral_local_derivative hp hp1 n φ h hiso
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hs.eventually_analyticAt.and ht.eventually_analyticAt).and hrealEvent)
  have hsa : DifferentiableOn ℂ s (ball φ.val r) :=
    fun χ hχ => (hball hχ).1.1.differentiableAt.differentiableWithinAt
  have hta : DifferentiableOn ℂ t (ball φ.val r) :=
    fun χ hχ => (hball hχ).1.2.differentiableAt.differentiableWithinAt
  have heq := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ r r s t hsa hta
    (fun χ hχ => (hreal χ).trans ((hball hχ.1).2 χ.property).symm)
  have hnear : s =ᶠ[𝓝 φ.val] t := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with χ hχ
    exact heq ⟨hχ,hχ⟩
  rw [hnear.fderiv_eq]
  exact hstationary

theorem SourceTheorem12_1Data.fderiv_energyNumerator_isospectral_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (n : ℤ) (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) (E : ℂ) :
    (fderiv ℂ (fun ψ => sourcePsiEnergyNumerator s n (E,ψ)) φ.val) h = 0 := by
  let F : ℂ × DeletedCoeff p n → ℂ := oddSquareDescent (sourcePsiDeletedCandidate n)
  have hF : AnalyticOnNhd ℂ F (univ ×ˢ (univ : Set (DeletedCoeff p n))) :=
    analyticOnNhd_oddSquareDescent _ univ isOpen_univ
      ((analyticOnNhd_sourcePsiDeletedCandidate hp hp1 n).mono (subset_univ _))
  have hFE : DifferentiableAt ℂ (fun b : DeletedCoeff p n => F (E,b)) (s n φ.val) :=
    ((hF (E,s n φ.val) ⟨mem_univ _,mem_univ _⟩).comp
      (f := fun b : DeletedCoeff p n => (E,b)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hchain := (hFE.hasFDerivAt.comp φ.val
    (H.analytic n φ.val hφ).differentiableAt.hasFDerivAt).fderiv
  have hz := fderiv_actualPsiRoots_isospectral_eq_zero hp hp1 n (s n) φ
    (H.analytic n φ.val hφ) (H.real_agreement n) h hiso
  have heval := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hchain
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,hz,map_zero,
    F,sourcePsiEnergyNumerator,sourceSelectedPsiNumerator,oddSquareDescent,oddPartQuotient,
    jointDSlopeZero] using heval

end NLS.ZakharovShabat
