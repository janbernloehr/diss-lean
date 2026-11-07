import NLS.KdV.HillOnIndexPhysicalCorrection
import NLS.ComplexAnalysis.ComplexCircleTerminal
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! At EVERY complex physical Dirichlet divisor with an open selected
gap, an analytic cosine terminal fixes BOTH frequency and ACTUAL root
coefficient. The resulting phase is analytic, including zero-sheet
Dirichlet endpoints; the physical sign is not inferred from a square. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_analytic_physical_onIndex_phase_chart (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hgap : (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4 ≠ 0) :
    ∃ δ ε α : PeriodOneHminusOne → ℂ, AnalyticAt ℂ δ q ∧ AnalyticAt ℂ ε q ∧ AnalyticAt ℂ α q ∧ δ q ≠ 0 ∧
      ∀ᶠ a in 𝓝 q, a ∈ P.physicalDirichletSource ∧
        δ a^2 = (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4 ∧
        cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)) (δ a) (ε a) =
          P.physicalDirichletFrequency ((n:ℕ):ℤ) a ∧
        -I*δ a*Complex.sin (ε a) = P.physicalDirichletRootCoefficient n a ∧
        α a = P.onIndexAbelianCosinePhase n a (δ a) (ε a) ∧
        α a = ε a-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n a := by
  let d : PeriodOneHminusOne → ℂ := fun a =>
    (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4
  let τ : PeriodOneHminusOne → ℂ := fun a => sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)
  let μ := P.physicalDirichletFrequency ((n:ℕ):ℤ)
  let r := P.physicalDirichletRootCoefficient n
  let w := Complex.sqrt (d q)
  have hw : w ≠ 0 := by intro he; apply hgap; change d q = 0; rw [← complex_sqrt_sq (d q)]; change w^2 = 0; rw [he]; norm_num
  have hd : AnalyticAt ℂ d q :=
    (P.parent.parent.miuraBall.dirac_gap_square_analytic ((n:ℕ):ℤ) q (P.parent.subset (P.subset hq.1)).1).div_const
  let δ := prescribedSquareRoot d w
  have hδsq (a : PeriodOneHminusOne) : δ a^2 = d a := prescribedSquareRoot_sq d w hw a
  have hδbase : δ q = w := prescribedSquareRoot_base d w hw q (complex_sqrt_sq (d q)).symm
  have hδne : δ q ≠ 0 := hδbase ▸ hw
  have hδ : AnalyticAt ℂ δ q := by
    have hslit := mem_prescribedSquareRootDomain d w hw q (complex_sqrt_sq (d q)).symm
    have hs : AnalyticAt ℂ Complex.sqrt (d q/w^2) :=
      Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hslit)
    exact analyticAt_const.mul (hs.comp (f := fun a => d a/w^2) hd.div_const)
  have hτ := P.analytic_abelianGapMidpoint n q hq.1
  have hμ := P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) q hq.1
  have hr := P.analytic_physicalDirichletRootCoefficient n q hq
  let σ : PeriodOneHminusOne → ℂ := fun a => I*r a/δ a
  have hσ : AnalyticAt ℂ σ q := (analyticAt_const.mul hr).div hδ hδne
  have hcircle : ∀ᶠ a in 𝓝 q, σ a^2+((μ a-τ a)/δ a)^2 = 1 := by
    filter_upwards [P.physicalDirichletSource_open.mem_nhds hq,hδ.continuousAt.eventually_ne hδne] with a ha hδa
    have hs : r a^2 = (μ a-τ a)^2-d a := P.physicalDirichletRootCoefficient_sq n a ha
    change (I*r a/δ a)^2+((μ a-τ a)/δ a)^2 = 1
    rw [div_pow,div_pow,← add_div]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hδa)).mpr
    rw [mul_pow,I_sq]
    linear_combination -hs-hδsq a
  obtain ⟨ε,hε,hterminal⟩ := exists_analytic_parametricCosine_terminal_from_circle τ δ μ σ q hτ hδ hμ hσ hδne hcircle
  let α : PeriodOneHminusOne → ℂ := fun a => ε a-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n a
  have hα : AnalyticAt ℂ α q := (hε.sub analyticAt_const).add (P.analytic_physicalOnIndexAbelianCorrection n q hq)
  refine ⟨δ,ε,α,hδ,hε,hα,hδne,?_⟩
  filter_upwards [P.physicalDirichletSource_open.mem_nhds hq,hterminal,hδ.continuousAt.eventually_ne hδne] with a ha he hδa
  have hroot : -I*δ a*Complex.sin (ε a) = r a := by
    rw [he.2]
    change -I*δ a*(I*r a/δ a) = r a
    field_simp [hδa]
    linear_combination -(r a)*I_sq
  refine ⟨ha,hδsq a,he.1,hroot,?_,rfl⟩
  unfold onIndexAbelianCosinePhase quadraticCosinePrimitive
  rw [he.1,hroot]
  rfl

end NLS.KdV.HillProductEquationPatch
