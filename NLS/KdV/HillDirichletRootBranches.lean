import NLS.KdV.HillDirichletSimplicity
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem exists_hillL2Dirichlet_analytic_root_branch
    (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic q energy=0) :
    ∃ a : Coeff 2 → ℂ, AnalyticAt ℂ a q ∧ a q=energy ∧
      ∀ᶠ p in 𝓝 q, hillL2DirichletCharacteristic p (a p)=0 := by
  let F : ℂ × Coeff 2 → ℂ := fun p => hillL2DirichletCharacteristic p.2 p.1
  have hF : AnalyticAt ℂ F (energy,q) :=
    analyticOnNhd_hillL2DirichletCharacteristic_joint (energy,q) (mem_univ _)
  let A := (fderiv ℂ F (energy,q)).comp (ContinuousLinearMap.inl ℂ ℂ (Coeff 2))
  let d := deriv (hillL2DirichletCharacteristic q) energy
  have hd : d≠0 := hillL2DirichletCharacteristic_deriv_ne_zero q hq energy hz
  have he : (fderiv ℂ F (energy,q)) (1,0)=d :=
    (deriv_spectral_section_eq_fderiv F energy q hF.differentiableAt).symm
  have hA (w : ℂ) : A w=w*d := by
    change (fderiv ℂ F (energy,q)) (w,0)=w*d
    have hp : (w,(0 : Coeff 2))=w • (1,(0 : Coeff 2)) := by simp
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

theorem exists_hillL2Dirichlet_analytic_real_root_branch
    (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic q energy=0) :
    ∃ a : Coeff 2 → ℂ, AnalyticAt ℂ a q ∧ a q=energy ∧
      ∀ᶠ p in 𝓝 q, hillL2DirichletCharacteristic p (a p)=0 ∧
        (IsRealHillPotential p → (a p).im=0) := by
  obtain ⟨a,ha,hzero,he⟩ := exists_hillL2Dirichlet_analytic_root_branch q hq energy hz
  refine ⟨a,ha,hzero,?_⟩
  filter_upwards [he] with p hp
  exact ⟨hp,fun hr => hillL2DirichletCharacteristic_zero_real p hr (a p) hp⟩

theorem hillDirichlet_zero_mem_gap_of_between_neighbor_bands
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) (x : ℝ)
    (hx : x∈Ioo (hillRealLabels q hq hr (2*n-2)) (hillRealLabels q hq hr (2*n+1)))
    (hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x=0) :
    x∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) := by
  constructor
  · by_contra! hl
    apply hillL2DirichletCharacteristic_ne_zero_on_open_band q hq hr (n-1) x ?_ hz
    rw [show 2*(n-1)=2*n-2 by omega,show 2*n-2+1=2*n-1 by omega]
    exact ⟨hx.1,hl⟩
  · by_contra! hu
    exact hillL2DirichletCharacteristic_ne_zero_on_open_band q hq hr n x ⟨hu,hx.2⟩ hz

end NLS.KdV
