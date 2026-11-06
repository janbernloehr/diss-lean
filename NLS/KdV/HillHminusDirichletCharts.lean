import NLS.KdV.HillHminusSpectralDifferentials
import NLS.KdV.HillDirichletAnalyticLabels

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

/-- A simple actual Dirichlet zero has a genuine analytic H-minus-one source
chart, with the original derivative-one characteristic. -/
theorem exists_hillHminusDirichlet_analytic_root_branch
    (q : PeriodOneHminusOne) (energy : ℂ)
    (hz : hillHminusDirichlet q energy=0)
    (hd : deriv (hillHminusDirichlet q) energy≠0) :
    ∃ a : PeriodOneHminusOne → ℂ, AnalyticAt ℂ a q ∧ a q=energy ∧
      ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (a p)=0 := by
  let F : ℂ × PeriodOneHminusOne → ℂ := fun p => hillHminusDirichlet p.2 p.1
  have hF : AnalyticAt ℂ F (energy,q) :=
    analyticOnNhd_hillHminusDirichlet_joint (energy,q) (mem_univ _)
  let A := (fderiv ℂ F (energy,q)).comp (ContinuousLinearMap.inl ℂ ℂ PeriodOneHminusOne)
  let d := deriv (hillHminusDirichlet q) energy
  have he : (fderiv ℂ F (energy,q)) (1,0)=d :=
    (deriv_spectral_section_eq_fderiv F energy q hF.differentiableAt).symm
  have hA (w : ℂ) : A w=w*d := by
    change (fderiv ℂ F (energy,q)) (w,0)=w*d
    have hp : (w,(0 : PeriodOneHminusOne))=w • (1,(0 : PeriodOneHminusOne)) := by simp
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

/-- At every original real source, each actual labelled Dirichlet energy
extends analytically to a full H-minus-one neighborhood. The extension
agrees locally with the original physical label, including collapsed gaps. -/
theorem exists_hillDirichletEnergy_hminus_analytic_extension
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ a : PeriodOneHminusOne → ℂ, AnalyticAt ℂ a (hillOriginalHminusSource q.val) ∧
      a (hillOriginalHminusSource q.val)=
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ∧
      (∀ᶠ p in 𝓝 (hillOriginalHminusSource q.val), hillHminusDirichlet p (a p)=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        a (hillOriginalHminusSource p.val)=
          (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) := by
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  have he : hillHminusDirichlet (hillOriginalHminusSource q.val)=
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) :=
    funext (hillHminusDirichlet_original_source_agreement q.val q.property.1)
  have hz : hillHminusDirichlet (hillOriginalHminusSource q.val) E=0 := by
    rw [he]
    exact hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  have hd : deriv (hillHminusDirichlet (hillOriginalHminusSource q.val)) E≠0 := by
    rw [he]
    exact hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 E
      (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  obtain ⟨a,ha,hax,hroot⟩ := exists_hillHminusDirichlet_analytic_root_branch
    (hillOriginalHminusSource q.val) E hz hd
  refine ⟨a,ha,hax,hroot,?_⟩
  have hP : Continuous (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val) :=
    hillOriginalHminusSource.continuous.comp continuous_subtype_val
  have hz' : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff p.val)
        (a (hillOriginalHminusSource p.val))=0 := by
    filter_upwards [hP.continuousAt.tendsto.eventually hroot] with p hp
    rw [hillHminusDirichlet_original_source_agreement p.val p.property.1] at hp
    exact hp
  have hmatch := eventually_hillDirichletEnergy_eq_branch_family Subtype.val continuous_subtype_val
    (fun p => p.property.1) (fun p => p.property.2) n hn q
    (fun p => a (hillOriginalHminusSource p.val)) (ha.continuousAt.comp
      (f := fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      hP.continuousAt) hax hz'
  exact hmatch.mono (fun _ hp => hp.symm)

end NLS.KdV
