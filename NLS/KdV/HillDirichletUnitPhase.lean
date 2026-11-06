import NLS.KdV.HillSelectedDirichletAngle

/-! # The independent original Dirichlet terminal unit phase

Both trigonometric coordinates are fixed by the scalar Hill IVP and its
canonical sheet. This phase is locally complex analytic throughout its
own open-gap locus, including a Dirichlet point at either band edge.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def hillDirichletUnitPhase (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  -(hillDirichletGapCosine q.val q.property.1 q.property.2 n hn+
    hillDirichletGapSine q.val q.property.1 q.property.2 n hn*I)

theorem hillDirichletUnitPhase_eq_terminal (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (θ : ℝ)
    (hc : cos (θ : ℂ) = hillDirichletGapCosine q.val q.property.1 q.property.2 n hn)
    (hs : sin (θ : ℂ) = hillDirichletGapSine q.val q.property.1 q.property.2 n hn) :
    hillDirichletUnitPhase q n hn = -exp ((θ : ℂ)*I) := by
  rw [hillDirichletUnitPhase,exp_mul_I,hc,hs]

theorem norm_hillDirichletUnitPhase (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ‖hillDirichletUnitPhase q n hn‖ = 1 := by
  have he := hillSelectedDirichletAngle_spec q n hn hgap
  rw [hillDirichletUnitPhase_eq_terminal q n hn _ he.2.2.1 he.2.2.2,norm_neg,norm_exp]
  simp only [mul_re,ofReal_re,I_re,ofReal_im,I_im,mul_zero,zero_mul,sub_self,Real.exp_zero]

theorem hillDirichletUnitPhase_closed (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealGapHalfLength q.val q.property.1 q.property.2 n = 0) :
    hillDirichletUnitPhase q n hn = 0 := by
  simp only [hillDirichletUnitPhase,hillDirichletGapCosine,hillDirichletGapSine,hc,
    ofReal_zero,zero_mul,div_zero,zero_add,neg_zero]

theorem exists_hillDirichletUnitPhase_analytic_extension (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ A : Coeff 2 → ℂ, AnalyticAt ℂ A (SpectralWeight.one.toCoeff q.val) ∧
      A (SpectralWeight.one.toCoeff q.val) = hillDirichletUnitPhase q n hn ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        A (SpectralWeight.one.toCoeff p.val) = hillDirichletUnitPhase p n hn := by
  obtain ⟨ε,e,hε,_,_,hmatch⟩ := exists_hillDirichlet_analytic_sheeted_angle
    q.val q.property.1 q.property.2 n hn hgap
  let A : Coeff 2 → ℂ := fun p => -exp (ε p*I)
  have hA : AnalyticAt ℂ A (SpectralWeight.one.toCoeff q.val) := (hε.mul analyticAt_const).cexp.neg
  have hm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      A (SpectralWeight.one.toCoeff p.val) = hillDirichletUnitPhase p n hn := by
    filter_upwards [hmatch] with p hp
    have hc : cos (ε (SpectralWeight.one.toCoeff p.val)) =
        hillDirichletGapCosine p.val p.property.1 p.property.2 n hn := by
      apply (eq_div_iff (ofReal_ne_zero.mpr hp.1)).mpr
      have hx := hp.2.2.1
      dsimp only [cosineGapPoint] at hx
      linear_combination hx
    dsimp only [A,hillDirichletUnitPhase]
    rw [exp_mul_I,hc,hp.2.2.2]
  exact ⟨A,hA,Filter.EventuallyEq.eq_of_nhds hm,hm⟩

end NLS.KdV
