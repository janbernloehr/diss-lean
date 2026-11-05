import NLS.KdV.HillHminusOneDirichletSimplicity
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-! # Analytic original H^-1 Dirichlet root branches at every real potential

Every zero of the actual normalized entire characteristic extends as a
complex analytic root on an original H^-1 norm neighborhood. Nearby real
potentials give real energies. Neither a continuously chosen global label
nor a real shifted-Miura lift is assumed as input.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminusDirichlet_analytic_root_branch
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (energy : ℂ)
    (hz : hillHminusDirichlet q energy = 0) :
    ∃ a : PeriodOneHminusOne → ℂ, AnalyticAt ℂ a q ∧ a q = energy ∧
      ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (a p) = 0 := by
  let F : ℂ × PeriodOneHminusOne → ℂ := fun p => hillHminusDirichlet p.2 p.1
  have hF : AnalyticAt ℂ F (energy,q) :=
    analyticOnNhd_hillHminusDirichlet_joint (energy,q) (mem_univ _)
  let A := (fderiv ℂ F (energy,q)).comp (ContinuousLinearMap.inl ℂ ℂ PeriodOneHminusOne)
  let d := deriv (hillHminusDirichlet q) energy
  have hd : d ≠ 0 := hillHminusDirichlet_deriv_ne_zero_at_real_root q hr energy hz
  have he : (fderiv ℂ F (energy,q)) (1,0) = d :=
    (deriv_spectral_section_eq_fderiv F energy q hF.differentiableAt).symm
  have hA (w : ℂ) : A w = w*d := by
    change (fderiv ℂ F (energy,q)) (w,0) = w*d
    have hp : (w,(0 : PeriodOneHminusOne)) = w • (1,(0 : PeriodOneHminusOne)) := by simp
    rw [hp,map_smul,he,smul_eq_mul]
  have hbij : Function.Bijective A := by
    constructor
    · intro x y h
      rw [hA,hA] at h
      exact mul_right_cancel₀ hd h
    · intro y
      refine ⟨y/d,?_⟩
      rw [hA,div_mul_cancel₀ _ hd]
  exact exists_analytic_implicitBanachRoot F energy q hF hz hbij

theorem exists_hillHminusDirichlet_analytic_real_root_branch
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (energy : ℂ)
    (hz : hillHminusDirichlet q energy = 0) :
    ∃ a : PeriodOneHminusOne → ℂ, AnalyticAt ℂ a q ∧ a q = energy ∧
      ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (a p) = 0 ∧
        (IsRealPeriodOneHminusOne p → (a p).im = 0) := by
  obtain ⟨a,ha,haq,hroot⟩ := exists_hillHminusDirichlet_analytic_root_branch q hr energy hz
  refine ⟨a,ha,haq,?_⟩
  filter_upwards [hroot] with p hp
  exact ⟨hp,fun hpr => hillHminusDirichlet_zero_energy_im_zero p hpr (a p) hp⟩

end NLS.KdV
