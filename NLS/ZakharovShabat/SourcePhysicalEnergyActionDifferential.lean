import NLS.ZakharovShabat.SourceSobolevHamiltonianDifferential
import NLS.ZakharovShabat.SourceRenormalizedHamiltonianDifferential
import NLS.ZakharovShabat.SourceSobolevActionDifferential
import NLS.ZakharovShabat.SourceMassActionDifferential
import NLS.ZakharovShabat.SourceOrdinaryPhaseTrajectory

/-! # The full physical NLS energy differential in original actions

At every real finite-gap H¹ source, the actual physical energy has the
finite differential sum of original actions weighted by the ordinary NLS
frequencies. The proof combines the complex H¹ correction identity, the
FL⁴ renormalized Hamiltonian derivative, kinetic weights, and the physical
mass trace. All directions are arbitrary complex H¹ directions.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
namespace SourceAbelianMomentAtlas
variable {W P : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical correction derivative is the finite renormalized-frequency pairing on H¹. -/
theorem sobolevPhysicalCorrection_fderiv_eq_finite_sum
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (a : realTypeSobolevSourceLocus) (S : Finset ℤ)
    (hS : ∀ n ∉ S, sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (sobolevSourceInclusion a.val) n = 0) (h : ScalarDomain 2 × ScalarDomain 2) :
    fderiv ℂ sourceSobolevPhysicalCorrection a.val h =
      ∑ n ∈ S, C.renormalizedFrequency n (sobolevSourceInclusion a.val) *
        (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (sobolevSourceInclusion a.val)) (sobolevSourceInclusion h) := by
  obtain ⟨V,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (p := 4) (by simp) (by norm_num)
  obtain ⟨Y,Q,_,_,hQ,hrQ,u,hu,⟨B⟩⟩ :=
    exists_sourceAbelianMoment_squaredGapAtlas (p := 4) (by simp) (by norm_num)
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  let ψ : realTypeSourceSubmodule 4 := realSobolevSourceFL4 a
  have hclosed (n : ℤ) (hn : n ∉ S) :
      sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n = 0 := by
    rw [sourcePeriodicGapDisplacement_apply]
    change canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (CoeffPair.exponentInclusion (by norm_num : (2 : ℝ≥0∞) ≤ 4) φ.val)) _ n = 0
    rw [← canonicalPeriodicGap_source_exponent (by simp) (by simp) (by norm_num)
      (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 4) φ.val n]
    simpa only [sourcePeriodicGapDisplacement_apply] using hS n hn
  have hcot (n : ℤ) (hn : n ∉ S) :
      fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val = 0 :=
    sourceComplexAction_fderiv_eq_zero_of_closed_gap (by simp) (by norm_num) ψ.val ψ.property n (hclosed n hn)
  rw [A.sobolevPhysicalCorrection_fderiv a]
  change (fderiv ℂ A.renormalizedHamiltonian ψ.val) (sobolevSourceFL4 h) = _
  rw [A.renormalizedHamiltonian_fderiv_eq_finite_sum B hu hQ hrQ ψ S hcot]
  apply Finset.sum_congr rfl
  intro n _
  have hfreq := B.renormalizedFrequency_real_eq_of_coefficients C hu.toSourcePsiIsolatingComplexExtension
    hs ψ φ (fun _ => ⟨rfl,rfl⟩) n
  have hd := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (sobolevSourceInclusion h))
    (fderiv_sourceComplexAction_exponent (by simp) (by simp) (by norm_num) (by norm_num)
      (by norm_num : (2 : ℝ≥0∞) ≤ 4) n φ)
  exact congrArg₂ (fun x y : ℂ => x*y) hfreq hd.symm

/-- The full physical energy cotangent uses exactly the ordinary NLS frequencies. -/
theorem periodOneSobolevHamiltonian_fderiv_eq_finite_sum
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (a : realTypeSobolevSourceLocus) (S : Finset ℤ)
    (hS : ∀ n ∉ S, sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (sobolevSourceInclusion a.val) n = 0) (h : ScalarDomain 2 × ScalarDomain 2) :
    fderiv ℂ periodOneSobolevHamiltonian a.val h =
      ∑ n ∈ S, (C.ordinaryPhaseFrequency le_rfl ⟨sobolevSourceInclusion a.val,a.property⟩ n : ℂ) *
        (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (sobolevSourceInclusion a.val)) (sobolevSourceInclusion h) := by
  have hcot (n : ℤ) (hn : n ∉ S) :
      fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) (sobolevSourceInclusion a.val) = 0 :=
    sourceComplexAction_fderiv_eq_zero_of_closed_gap (by simp) (by norm_num) _ a.property n (hS n hn)
  have hE := (analyticAt_periodOneSobolevHamiltonian a.val).differentiableAt.hasFDerivAt
  have hM := (analyticAt_periodOneSobolevMass a.val).differentiableAt.hasFDerivAt
  have hK := (analyticAt_sourceSobolevWeightedActionSum a.val a.property).differentiableAt.hasFDerivAt
  have hder : HasFDerivAt sourceSobolevPhysicalCorrection
      (fderiv ℂ periodOneSobolevHamiltonian a.val -
        (4*periodOneSobolevMass a.val) • fderiv ℂ periodOneSobolevMass a.val -
          fderiv ℂ sourceSobolevWeightedActionSum a.val) a.val := by
    convert! ((hE.sub ((hM.pow 2).const_smul (2 : ℂ))).sub hK) using 1
    simp only [Nat.reduceSub,pow_one]
    module
  have hd := congrArg (fun L : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] ℂ => L h) hder.fderiv
  change fderiv ℂ sourceSobolevPhysicalCorrection a.val h =
    fderiv ℂ periodOneSobolevHamiltonian a.val h -
      (4*periodOneSobolevMass a.val) * fderiv ℂ periodOneSobolevMass a.val h -
        fderiv ℂ sourceSobolevWeightedActionSum a.val h at hd
  rw [C.sobolevPhysicalCorrection_fderiv_eq_finite_sum hs a S hS h,
    periodOneSobolevMass_fderiv_eq_finite_sum a.val a.property S hcot h,
    sourceSobolevWeightedActionSum_fderiv_eq_finite_sum a.val a.property S hcot h] at hd
  have hm : sourceOrdinaryComplexMass le_rfl (sobolevSourceInclusion a.val) = periodOneSobolevMass a.val := by
    have hi : CoeffPair.exponentInclusion le_rfl (sobolevSourceInclusion a.val) = sobolevSourceInclusion a.val := by
      apply (CoeffPair.toMax 2).injective
      apply Prod.ext <;> ext n <;> rfl
    rw [sourceOrdinaryComplexMass,hi]
    exact (periodOneSobolevMass_eq_sourceHilbertMass a.val).symm
  simp only [C.ordinaryPhaseFrequency_complex hs,hm,add_mul,Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  linear_combination -hd

/-- Every real finite-gap H¹ source has a finite ordinary-action cotangent
whose restriction is the full physical energy derivative. -/
theorem exists_periodOneSobolevHamiltonian_finiteGap_differential
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (a : realTypeSobolevSourceLocus) (hf : a ∈ sourceSobolevFiniteGapLocus) :
    ∃ S : Finset ℤ, fderiv ℂ periodOneSobolevHamiltonian a.val =
      (∑ n ∈ S, (C.ordinaryPhaseFrequency le_rfl ⟨sobolevSourceInclusion a.val,a.property⟩ n : ℂ) •
        fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (sobolevSourceInclusion a.val)).comp sobolevSourceInclusion := by
  classical
  have hS (n : ℤ) (hn : n ∉ hf.toFinset) :
      sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n = 0 := by
    rw [sourcePeriodicGapDisplacement_apply]
    by_contra h
    exact hn (hf.mem_toFinset.mpr h)
  refine ⟨hf.toFinset,?_⟩
  apply ContinuousLinearMap.ext
  intro h
  rw [C.periodOneSobolevHamiltonian_fderiv_eq_finite_sum hs a hf.toFinset hS h]
  simp

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
