import NLS.KdV.HillHminusOneFreeDirichletPairing

/-! # The exact Fourier linearization of every actual Dirichlet energy

At zero potential the full complex H^-1 derivative is
h_0-(h_n+h_-n)/2. Both signed Fourier coefficients and the mean are
retained. The mean-zero real restriction is consequently -Re(h_n).
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillHminusDirichlet_branch_fderiv_zero
    (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a 0) (n : ℕ+)
    (ha0 : a 0 = (freeHillValue (n : ℕ) : ℂ))
    (hroot : ∀ᶠ p in 𝓝 (0 : PeriodOneHminusOne), hillHminusDirichlet p (a p) = 0)
    (h : PeriodOneHminusOne) :
    fderiv ℂ a 0 h = h.val 0-(h.val (n : ℤ)+h.val (-(n : ℤ)))/2 := by
  have hr : IsRealPeriodOneHminusOne 0 := by intro k; simp
  have hz : hillHminusDirichlet 0 (a 0) = 0 := by
    rw [ha0]
    exact hillHminusDirichlet_free_nat_root (n : ℕ) n.property
  rw [hillHminusDirichlet_branch_fderiv 0 hr a ha hz hroot h,ha0,
    hillHminusWeakPotential_free_Dirichlet_square,hillHminusDirichletColumn_free_square_integral]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

theorem exists_hillHminusDirichletEnergy_free_analytic_extension_with_fderiv (n : ℕ+) :
    ∃ a : PeriodOneHminusOne → ℂ, AnalyticAt ℂ a 0 ∧ a 0 = (freeHillValue (n : ℕ) : ℂ) ∧
      (∀ᶠ p in 𝓝 (0 : PeriodOneHminusOne), hillHminusDirichlet p (a p) = 0) ∧
      (∀ᶠ p : PeriodOneRealHminusOne in 𝓝 (⟨0,by intro k; simp⟩ : PeriodOneRealHminusOne),
        a p.val = (hillHminusDirichletEnergy p.val p.property n : ℂ)) ∧
      ∀ h : PeriodOneHminusOne, fderiv ℂ a 0 h = h.val 0-(h.val (n : ℤ)+h.val (-(n : ℤ)))/2 := by
  obtain ⟨a,ha,ha0,hroot,hmatch⟩ := exists_hillHminusDirichletEnergy_analytic_extension
    (⟨0,by intro k; simp⟩ : PeriodOneRealHminusOne) n
  have ha0' : a 0 = (freeHillValue (n : ℕ) : ℂ) := by
    simpa only [hillHminusDirichletEnergy_zero_potential] using ha0
  exact ⟨a,ha,ha0',hroot,hmatch,fun h => hillHminusDirichlet_branch_fderiv_zero a ha n ha0' hroot h⟩

theorem hillHminusDirichlet_branch_fderiv_zero_real_mean_zero
    (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a 0) (n : ℕ+)
    (ha0 : a 0 = (freeHillValue (n : ℕ) : ℂ))
    (hroot : ∀ᶠ p in 𝓝 (0 : PeriodOneHminusOne), hillHminusDirichlet p (a p) = 0)
    (h : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne h) (hm : h.val 0 = 0) :
    fderiv ℂ a 0 h = -((h.val (n : ℤ)).re : ℂ) := by
  rw [hillHminusDirichlet_branch_fderiv_zero a ha n ha0 hroot h,hm,hr]
  have he : h.val (n : ℤ)+conj (h.val (n : ℤ)) = 2*((h.val (n : ℤ)).re : ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [he]
  ring

end NLS.KdV
