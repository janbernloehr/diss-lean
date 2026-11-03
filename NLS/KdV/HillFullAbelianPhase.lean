import NLS.KdV.HillAbelianCorrectionTails
import NLS.KdV.HillFiniteAbelianSupport
import NLS.SequenceSpaces.LocalSeriesContinuity

/-! # The full independent Abelian phase for every real L² Hill potential

The actual divisor corrections converge locally uniformly, including
through closed contributing gaps. Their sum is continuous everywhere;
the unit phase is continuous on its exact own open-gap locus.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat
namespace NLS.KdV

def hillFullRegularAbelianSum (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  ∑' k : ℕ,hillDirichletRegularAbelianTerm q n hn (k+1) (by omega)

theorem continuous_hillDirichletRegularAbelianTerm (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletRegularAbelianTerm q n hn k hk) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨β,hβ,hβ0,hmatch⟩ := exists_hillDirichletRegularAbelianTerm_analytic_extension q n hn k hk
  have hP : Continuous (fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  exact (hβ.continuousAt.comp (f := fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val)
    (x := q) hP.continuousAt).congr_of_eventuallyEq (Filter.EventuallyEq.symm hmatch)

theorem continuous_hillFullRegularAbelianSum (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillFullRegularAbelianSum q n hn) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact NLS.continuousAt_tsum_of_locally_small_nat_tails
    (fun p k => hillDirichletRegularAbelianTerm p n hn (k+1) (by omega)) q
    (fun p => summable_hillDirichletRegularAbelianTerm p n hn)
    (fun k => (continuous_hillDirichletRegularAbelianTerm n hn (k+1) (by omega)).continuousAt)
    (locally_small_hillDirichletRegularAbelianTerm_tails q n hn)

theorem hillFullRegularAbelianSum_im_eq_zero (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    (hillFullRegularAbelianSum q n hn).im = 0 := by
  rw [hillFullRegularAbelianSum,Complex.im_tsum (summable_hillDirichletRegularAbelianTerm q n hn)]
  simp only [hillDirichletRegularAbelianTerm_im_eq_zero,tsum_zero]

def hillFullAbelianPhase (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  hillDirichletUnitPhase q n hn*exp (I*hillFullRegularAbelianSum q n hn)

theorem norm_hillFullAbelianPhase (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ‖hillFullAbelianPhase q n hn‖ = 1 := by
  rw [hillFullAbelianPhase,norm_mul,norm_hillDirichletUnitPhase q n hn hgap,norm_exp]
  simp only [mul_re,I_re,I_im,zero_mul,one_mul,hillFullRegularAbelianSum_im_eq_zero,
    sub_zero,Real.exp_zero,one_mul]

theorem hillFullAbelianPhase_closed (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealGapHalfLength q.val q.property.1 q.property.2 n = 0) :
    hillFullAbelianPhase q n hn = 0 := by
  rw [hillFullAbelianPhase,hillDirichletUnitPhase_closed q n hn hc,zero_mul]

theorem norm_hillFullAbelianPhase_le_one (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ‖hillFullAbelianPhase q n hn‖ ≤ 1 := by
  by_cases hc : hillRealGapHalfLength q.val q.property.1 q.property.2 n = 0
  · rw [hillFullAbelianPhase_closed q n hn hc,norm_zero]
    norm_num
  · exact (norm_hillFullAbelianPhase q n hn hc).le

theorem continuousAt_hillFullAbelianPhase (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ContinuousAt (fun p : RealPeriodOneHillPotential => hillFullAbelianPhase p n hn) q := by
  obtain ⟨A,hA,hA0,hmatch⟩ := exists_hillDirichletUnitPhase_analytic_extension q n hn hgap
  have hP : Continuous (fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hu : ContinuousAt (fun p : RealPeriodOneHillPotential => hillDirichletUnitPhase p n hn) q :=
    (hA.continuousAt.comp (f := fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val)
      (x := q) hP.continuousAt).congr_of_eventuallyEq (Filter.EventuallyEq.symm hmatch)
  exact hu.mul (continuousAt_const.mul (continuous_hillFullRegularAbelianSum n hn).continuousAt).cexp

theorem continuousOn_hillFullAbelianPhase (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (fun p : RealPeriodOneHillPotential => hillFullAbelianPhase p n hn)
      {q | hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0} :=
  fun q hq => (continuousAt_hillFullAbelianPhase q n hn hq).continuousWithinAt

theorem hillFullAbelianPhase_eq_finite_of_closed_complement
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ)
    (hclosed : ∀ k, k ∉ F → hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) = 0) :
    hillFullAbelianPhase q n hn = hillFiniteAbelianPhase q n hn F := by
  rw [hillFullAbelianPhase,hillFiniteAbelianPhase,
    hillFiniteRegularAbelianSum_eq_tsum_of_closed_complement q n hn F hclosed,hillFullRegularAbelianSum]

/-- Natural finite partial phases converge to the literal full Abelian phase. -/
theorem tendsto_hillFiniteAbelianPhase (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun M : ℕ => hillFiniteAbelianPhase q n hn (Finset.range M)) atTop
      (𝓝 (hillFullAbelianPhase q n hn)) := by
  have hs := (summable_hillDirichletRegularAbelianTerm q n hn).hasSum.tendsto_sum_nat
  have he : Tendsto (fun M : ℕ => exp (I*hillFiniteRegularAbelianSum q n hn (Finset.range M))) atTop
      (𝓝 (exp (I*hillFullRegularAbelianSum q n hn))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul hs)
  exact tendsto_const_nhds.mul he

end NLS.KdV
