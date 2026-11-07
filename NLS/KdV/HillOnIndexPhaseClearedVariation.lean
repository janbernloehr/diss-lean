import NLS.KdV.HillOnIndexCorrectionIsospectral
import NLS.KdV.HillOnIndexPhysicalPhaseCharts
import NLS.KdV.HillPhysicalAbelianIsospectralVariation
import NLS.ComplexAnalysis.StationaryCosineTerminal

/-! The actual on-index cosine phase has the cleared original-energy
variation in every native isospectral direction. Its diagonal i term
cancels against the cosine-terminal variation. Only the selected gap
must be open; the physical terminal sheet may vanish. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_onIndex_phase_isospectral_cleared (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (hr : IsRealPeriodOneHminusOne q)
    (d ε α : PeriodOneHminusOne → ℂ) (hd : AnalyticAt ℂ d q) (hε : AnalyticAt ℂ ε q)
    (hne : d q ≠ 0)
    (hchart : ∀ᶠ a in 𝓝 q, a ∈ P.physicalDirichletSource ∧
      d a^2 = (canonicalPeriodicGap (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4 ∧
      cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ))
        (d a) (ε a) = P.physicalDirichletFrequency ((n:ℕ):ℤ) a ∧
      -I*d a*Complex.sin (ε a) = P.physicalDirichletRootCoefficient n a ∧
      α a = P.onIndexAbelianCosinePhase n a (d a) (ε a) ∧
      α a = ε a-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n a)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) :
    hillHminusDirichletSheet n q*((fderiv ℂ α q) h) =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*
        ((fderiv ℂ (hillHminusCanonicalDirichlet n) q) h) := by
  let μ := P.physicalDirichletFrequency ((n:ℕ):ℤ)
  let M : PeriodOneHminusOne → ℂ := fun a => sourceStandardRootMidpoint
    (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)
  let G : PeriodOneHminusOne → ℂ := fun a => (canonicalPeriodicGap (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2
  let K := P.abelianGapRootMultiplier n (μ q,q)
  have hM := (P.parent.parent.miuraBall.midpoint_analytic ((n:ℕ):ℤ) q
    (P.parent.subset (P.subset hq.1)).1).differentiableAt
  have hG := (P.parent.parent.miuraBall.dirac_gap_square_analytic ((n:ℕ):ℤ) q
    (P.parent.subset (P.subset hq.1)).1).differentiableAt
  have hMG := P.fderiv_symmetric_isospectral_eq_zero q hq.1 hr h hiso ((n:ℕ):ℤ)
  have hsq : (fun a => d a^2) =ᶠ[𝓝 q] (fun a => (1/4:ℂ)*G a) := by
    filter_upwards [hchart] with a ha
    have he := ha.2.1
    change d a^2 = G a/4 at he
    linear_combination he
  have hd0 := fderiv_square_root_stationary d G q h (1/4) hd.differentiableAt hG hne hMG.2 hsq
  have hcos : μ =ᶠ[𝓝 q] (fun a => M a+d a*Complex.cos (ε a)) :=
    hchart.mono (fun _ ha => ha.2.2.1.symm)
  have hbase := hchart.self_of_nhds
  have hsheet : hillHminusDirichletSheet n q = -I*d q*K*Complex.sin (ε q) := by
    calc
      _ = K*P.physicalDirichletRootCoefficient n q :=
        (P.physicalDirichletRootCoefficient_preserves_sheet n q hq).symm
      _ = K*(-I*d q*Complex.sin (ε q)) := congrArg (fun z : ℂ => K*z) hbase.2.2.2.1.symm
      _ = _ := by ring
  have heps := fderiv_cosine_terminal_cleared μ M d ε q h (hillHminusDirichletSheet n q) K
    hM hd.differentiableAt hε.differentiableAt hMG.1 hd0 hcos hsheet
  have hcor := P.fderiv_physicalOnIndexAbelianCorrection_isospectral_frequency_cleared n q hq hr h hiso
  have hαnear : α =ᶠ[𝓝 q] (fun a => ε a-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n a) :=
    hchart.mono (fun _ ha => ha.2.2.2.2.2)
  have hα := (hε.differentiableAt.hasFDerivAt.sub_const (Real.pi:ℂ)).fun_add
    (P.analytic_physicalOnIndexAbelianCorrection n q hq).differentiableAt.hasFDerivAt
  have hαeval := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hαnear.fderiv_eq
  rw [hα.fderiv] at hαeval
  simp only [add_apply] at hαeval
  have hall : hillHminusDirichletSheet n q*((fderiv ℂ α q) h) =
      K*P.abelianGapNumerator n n (μ q,q)*((fderiv ℂ μ q) h) := by
    linear_combination hillHminusDirichletSheet n q*hαeval+heps+hcor
  have hK : K ≠ 0 := P.abelianGapRootMultiplier_ne_zero n (μ q,q)
    ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩
  have hg : K*P.abelianGapNumerator n n (μ q,q) =
      2*μ q*hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q) := by
    change K*((2*μ q*hillHminusCanonicalPsi n
      ((μ q)^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q))/K) = _
    rw [mul_div_cancel₀ _ hK,P.physicalDirichletFrequency_energy n q hq.1]
  rw [hg] at hall
  rw [P.fderiv_physicalDirichletFrequency_energy n q hq.1 h]
  linear_combination hall

end NLS.KdV.HillProductEquationPatch
