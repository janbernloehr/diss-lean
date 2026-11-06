import NLS.KdV.HillDirichletUnitPhase
import NLS.KdV.HillDirichletRegularTermAnalytic

/-! # Actual finite partial Abelian phases of the independent Hill divisor

Every finite partial sum has a unit phase on its own open-gap locus and
a local complex analytic extension even when any other gaps are closed.
These are literal Abelian integrals, not prescribed phase values. Passing
to the full infinite phase still requires convergence of the corrections.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat
namespace NLS.KdV

def hillFiniteRegularAbelianSum (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (F : Finset ℕ) : ℂ :=
  ∑ k ∈ F,hillDirichletRegularAbelianTerm q n hn (k+1) (by omega)

theorem hillFiniteRegularAbelianSum_im_eq_zero (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (F : Finset ℕ) : (hillFiniteRegularAbelianSum q n hn F).im = 0 := by
  simp only [hillFiniteRegularAbelianSum,Complex.im_sum,hillDirichletRegularAbelianTerm_im_eq_zero,Finset.sum_const_zero]

def hillFiniteAbelianPhase (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) : ℂ :=
  hillDirichletUnitPhase q n hn*exp (I*hillFiniteRegularAbelianSum q n hn F)

theorem norm_hillFiniteAbelianPhase (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) (F : Finset ℕ) :
    ‖hillFiniteAbelianPhase q n hn F‖ = 1 := by
  rw [hillFiniteAbelianPhase,norm_mul,norm_hillDirichletUnitPhase q n hn hgap,norm_exp]
  simp only [mul_re,I_re,I_im,zero_mul,one_mul,hillFiniteRegularAbelianSum_im_eq_zero,
    sub_zero,Real.exp_zero,one_mul]

theorem hillFiniteAbelianPhase_closed (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealGapHalfLength q.val q.property.1 q.property.2 n = 0) (F : Finset ℕ) :
    hillFiniteAbelianPhase q n hn F = 0 := by
  rw [hillFiniteAbelianPhase,hillDirichletUnitPhase_closed q n hn hc,zero_mul]

theorem exists_hillFiniteRegularAbelianSum_analytic_extension (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) :
    ∃ B : Coeff 2 → ℂ, AnalyticAt ℂ B (SpectralWeight.one.toCoeff q.val) ∧
      B (SpectralWeight.one.toCoeff q.val) = hillFiniteRegularAbelianSum q n hn F ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        B (SpectralWeight.one.toCoeff p.val) = hillFiniteRegularAbelianSum p n hn F := by
  classical
  choose β hβ _ hmatch using (fun k : ℕ =>
    exists_hillDirichletRegularAbelianTerm_analytic_extension q n hn (k+1) (by omega))
  let B : Coeff 2 → ℂ := fun p => ∑ k ∈ F,β k p
  have hB : AnalyticAt ℂ B (SpectralWeight.one.toCoeff q.val) :=
    F.analyticAt_fun_sum (fun k _ => hβ k)
  have hm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      B (SpectralWeight.one.toCoeff p.val) = hillFiniteRegularAbelianSum p n hn F := by
    filter_upwards [(F.eventually_all).mpr (fun k _ => hmatch k)] with p hp
    exact Finset.sum_congr rfl hp
  exact ⟨B,hB,Filter.EventuallyEq.eq_of_nhds hm,hm⟩

theorem exists_hillFiniteAbelianPhase_analytic_extension (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (F : Finset ℕ) :
    ∃ P : Coeff 2 → ℂ, AnalyticAt ℂ P (SpectralWeight.one.toCoeff q.val) ∧
      P (SpectralWeight.one.toCoeff q.val) = hillFiniteAbelianPhase q n hn F ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        P (SpectralWeight.one.toCoeff p.val) = hillFiniteAbelianPhase p n hn F := by
  obtain ⟨A,hA,_,hAm⟩ := exists_hillDirichletUnitPhase_analytic_extension q n hn hgap
  obtain ⟨B,hB,_,hBm⟩ := exists_hillFiniteRegularAbelianSum_analytic_extension q n hn F
  let P : Coeff 2 → ℂ := fun p => A p*exp (I*B p)
  have hP : AnalyticAt ℂ P (SpectralWeight.one.toCoeff q.val) := hA.mul (analyticAt_const.mul hB).cexp
  have hm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      P (SpectralWeight.one.toCoeff p.val) = hillFiniteAbelianPhase p n hn F := by
    filter_upwards [hAm,hBm] with p hp hq
    dsimp only [P,hillFiniteAbelianPhase]
    rw [hp,hq]
  exact ⟨P,hP,Filter.EventuallyEq.eq_of_nhds hm,hm⟩

end NLS.KdV
