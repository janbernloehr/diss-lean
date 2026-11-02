import NLS.Articles.MKdVBelowL2.FourthHamiltonianPhaseFamily
import NLS.ZakharovShabat.SourceFiniteGapPhysicalFourthCoefficients
import NLS.ZakharovShabat.SourceActionPhaseFiniteGap
import NLS.ZakharovShabat.SourceMassActionDifferential

/-! # The actual fourth trajectory and its calibrated physical H₄ cotangent

At each finite-gap time the actual velocity is the original Poisson direction
of physical H₄ minus the exact mass and momentum corrections. The mass
cotangent is independently calibrated. The momentum-weighted finite action
cotangent is retained explicitly here; identifying it with physical H₂ is a
separate remaining step in the smooth renormalized PDE bridge.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Poisson
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- The fixed actual fourth lift has the calibrated physical H₄ derivative
and the exact two lower corrections at every real finite-gap time.
The momentum cotangent retains its original explicit signed action sum. -/
theorem exists_fourthFiniteGap_physical_cotangent_ODE
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
    let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
    let ψ := F.imageFlow D φ time
    ∃ a : NativeFourthSobolevSource, originalWeightedRealSource fourthSobolevSpectralWeight a = ψ ∧
      ∃ L4 LP : CoeffPair 2 →L[ℂ] ℂ,
        HasFDerivAt sourceComplexSobolevFourthHamiltonian
          (L4.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a.val ∧
        LP = ∑ n ∈ hf.toFinset, (2*(Real.pi:ℂ)*n) •
          fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val ∧
        HasDerivAt (fun r => (F.imageFlow D φ r).val)
          (sourceHamiltonianDirection le_rfl
            (L4-(6*sourceFourthSobolevMomentum a) • fderiv ℂ sourceHilbertMass ψ.val-
              (6*sourceFourthSobolevMass a) • LP)) time := by
  classical
  dsimp only
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let ψ := F.imageFlow D φ time
  have ht : (time,φ) ∈ F.imageDomain D := F.mem_imageDomain_of_le_two D le_rfl φ time
  have hfψ := F.imageFlow_finiteGap D φ hf time ht
  obtain ⟨a,ha⟩ := exists_nativeFourth_of_sourceFiniteGap ψ hfψ
  have hfa : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num) :=
    ha.symm ▸ hfψ
  let S := hf.toFinset
  have hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val = 0 :=
    F.imageFlow_action_differential_support D φ hf time ht
  have hSa : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0 := by
    simpa only [ha] using hS
  let L4 : CoeffPair 2 →L[ℂ] ℂ := ∑ n ∈ S, D.sobolevFourthFrequency a n •
    fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val
  let LP : CoeffPair 2 →L[ℂ] ℂ := ∑ n ∈ S, (2*(Real.pi:ℂ)*n) •
    fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val
  have hL4 : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L4.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a.val := by
    have he := D.sourceComplexSobolevFourthHamiltonian_fderiv_eq_finite_sum a S hSa
    rw [ha] at he
    exact he ▸ (analyticAt_sourceComplexSobolevFourthHamiltonian a.val).differentiableAt.hasFDerivAt
  let L : CoeffPair 2 →L[ℂ] ℂ := ∑ n ∈ S, (F.frequency ψ n:ℂ) •
    fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val
  have hfreq (n : ℤ) : (F.frequency ψ n:ℂ) = D.sobolevFourthFrequency a n-
      6*sourceFourthSobolevMomentum a-(12*Real.pi:ℂ)*n*sourceFourthSobolevMass a := by
    have he := fourthSourcePhaseFrequency_eq_physical_derivative a n
    rw [ha] at he
    exact he
  have hL : L = L4-(6*sourceFourthSobolevMomentum a) • fderiv ℂ sourceHilbertMass ψ.val-
      (6*sourceFourthSobolevMass a) • LP := by
    apply ContinuousLinearMap.ext
    intro h
    simp only [L,L4,LP,sum_apply,smul_apply,smul_eq_mul,sub_apply]
    rw [sourceHilbertMass_fderiv_eq_finite_sum ψ S hS h,Finset.mul_sum,Finset.mul_sum,
      ← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [hfreq]
    ring
  have hz : ∀ n ∉ S, (sourceComplexBirkhoffMap (by simp) (by norm_num)
      (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).roots φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap (by simp) (by norm_num)
        (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).roots φ.val).2 n = 0 := by
    intro n hn
    have hg : sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n = 0 := by
      rw [sourcePeriodicGapDisplacement_apply]
      by_contra h
      exact hn (hf.mem_toFinset.mpr h)
    obtain ⟨hx,hy⟩ := D.real_closed_gap_zero φ.val (D.real_subset φ.property) φ.property n hg
    simp only [sourceComplexBirkhoffMap,NLS.Birkhoff.rectangularToComplex_fst,
      NLS.Birkhoff.rectangularToComplex_snd,hx,hy,mul_zero,sub_zero,add_zero,and_self]
  have hd := F.hasDerivAt_imageFlow_finiteAction D le_rfl le_rfl φ S hz time
  rw [← F.frequency_imageFlow D φ time ht] at hd
  have he : sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl (F.frequency ψ) S ψ.val =
      sourceHamiltonianDirection le_rfl L := by
    simp only [sourceFiniteActionHamiltonianVector,sourceHamiltonianVector,L,map_sum,map_smul]
  rw [he,hL] at hd
  exact ⟨a,ha,L4,LP,hL4,rfl,hd⟩

end NLS.Articles.MKdVBelowL2
