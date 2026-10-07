import NLS.ZakharovShabat.SourceFiniteGapWeightedLift
import NLS.ZakharovShabat.SourceSobolevNormalizedCoordinates
import NLS.ZakharovShabat.SourceSobolevPhysicalCorrection
import NLS.ZakharovShabat.SourceFiniteGapHamiltonianODE

/-! # H¹ time differentiability of the actual finite-gap trajectory

The analytic weighted lift identifies the canonical H¹ representatives
along any differentiable real source curve with a fixed closed-gap tail.
Action conservation supplies that common tail for the constructed
Hamiltonian-oriented finite-gap flow.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Original Hilbert differentiability upgrades to H¹ differentiability
for finite-gap curves with a common local closed-gap tail. -/
theorem differentiableAt_sourceFiniteGapSobolevPair
    (γ : ℝ → realTypeSourceSubmodule 2)
    (hf : ∀ t, γ t ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ)
    (hγ : DifferentiableAt ℝ (fun t => (γ t).val) time) (K : ℕ)
    (hgap : ∀ᶠ t in 𝓝 time, ∀ n : ℤ, K ≤ n.natAbs →
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (γ t).val)
        (periodOnePotential_mem (γ t).val) n = 0) :
    DifferentiableAt ℝ (fun t => sourceFiniteGapSobolevPair (by simp) (by norm_num) (γ t) (hf t)) time := by
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) (γ time) (hf time)
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let φ := sobolevNormalizedCoordinates a
  have hdecode : normalizedWeightedSource w φ = (γ time).val :=
    (normalizedWeightedSource_sobolevNormalizedCoordinates a).trans
      (sobolevSourceInclusion_sourceFiniteGapSobolevPair (γ time) (hf time))
  have hreal : IsRealType (CoeffPair.toMax 2 φ) :=
    (sobolevNormalizedCoordinates_realType_iff a).mpr (by
      rw [sobolevSourceInclusion_sourceFiniteGapSobolevPair]
      exact (γ time).property)
  have hfφ : (⟨normalizedWeightedSource w φ,normalizedWeightedSource_realType w φ hreal⟩ : realTypeSourceLocus 2)
      ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
    change {n : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (normalizedWeightedSource w φ)) (periodOnePotential_mem _) n ≠ 0}.Finite
    have hh : {n : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (γ time).val) (periodOnePotential_mem _) n ≠ 0}.Finite := hf time
    simpa only [hdecode] using hh
  obtain ⟨ξ,hξ,_,hξdecode⟩ := exists_differentiableAt_sourceFiniteGap_weightedLift
    (by simp) (by norm_num) w φ hreal hfφ K (fun t => (γ t).val) time hγ hdecode.symm
    (Filter.Eventually.of_forall (fun t => (γ t).property)) hgap
  have hd : DifferentiableAt ℝ (fun t => sobolevNormalizedCoordinates.symm (ξ t)) time :=
    (sobolevNormalizedCoordinates.symm.toContinuousLinearMap.restrictScalars ℝ).differentiableAt.comp time hξ
  apply hd.congr_of_eventuallyEq
  filter_upwards [hξdecode] with t ht
  apply sobolevNormalizedCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply normalizedWeightedSource_injective w
  exact ((normalizedWeightedSource_sobolevNormalizedCoordinates _).trans
    (sobolevSourceInclusion_sourceFiniteGapSobolevPair (γ t) (hf t))).trans ht.symm

namespace SourceAbelianMomentAtlas
variable {W V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- An initially collapsed indexed gap stays collapsed for all real time. -/
theorem hamiltonianOrdinarySourceFlow_closed_gap
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (time : ℝ) (n : ℤ)
    (hgap : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (A.hamiltonianOrdinarySourceFlow D le_rfl φ time).val)
      (periodOnePotential_mem _) n = 0 := by
  let ψ := A.hamiltonianOrdinarySourceFlow D le_rfl φ time
  have hg : sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n = 0 := by
    simpa only [sourcePeriodicGapDisplacement_apply] using hgap
  have ha := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp) (by norm_num) φ.val φ.property n).2.2.mpr hg
  have he := A.hamiltonianOrdinarySourceFlow_action D le_rfl φ time n
  rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n ψ.val ψ.property,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property,ha] at he
  have hgψ : sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n = 0 :=
    (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) ψ.val ψ.property n).2.2.mp he
  rw [sourcePeriodicGapDisplacement_apply] at hgψ
  exact hgψ

/-- One initial spectral cutoff remains a closed-gap tail for the entire trajectory. -/
theorem exists_hamiltonianOrdinarySourceFlow_closed_gap_tail
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ K : ℕ, ∀ time : ℝ, ∀ n : ℤ, K ≤ n.natAbs →
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (A.hamiltonianOrdinarySourceFlow D le_rfl φ time).val)
        (periodOnePotential_mem _) n = 0 := by
  classical
  let S := hf.toFinset
  refine ⟨S.sup Int.natAbs+1,?_⟩
  intro time n hn
  apply A.hamiltonianOrdinarySourceFlow_closed_gap D φ time n
  by_contra hne
  have hmem : n ∈ S := hf.mem_toFinset.mpr hne
  have hle := Finset.le_sup (f := Int.natAbs) hmem
  omega

/-- The canonical physical H¹ representatives of the actual finite-gap
Hamiltonian-oriented spectral flow are differentiable at every real time. -/
theorem differentiable_hamiltonianOrdinarySourceFlow_sobolev
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Differentiable ℝ (fun time => sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)) := by
  obtain ⟨K,hK⟩ := A.exists_hamiltonianOrdinarySourceFlow_closed_gap_tail D φ hf
  intro time
  apply differentiableAt_sourceFiniteGapSobolevPair _ _ time _ K
    (Filter.Eventually.of_forall (hK ·))
  exact (realTypeSourceSubmodule (2 : ℝ≥0∞)).subtypeL.differentiableAt.comp time
    (A.differentiable_hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)

/-- At each spatial point, both physical components of the actual
finite-gap trajectory are differentiable in real time. -/
theorem differentiable_hamiltonianOrdinarySourceFlow_physical
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (x : ℝ) :
    Differentiable ℝ (fun time => (sourceFiniteGapPhysicalPair (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).1 x) ∧
    Differentiable ℝ (fun time => (sourceFiniteGapPhysicalPair (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).2 x) := by
  let E := (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).comp NLS.Fourier.periodOneSobolevSynthesis
  have hd := A.differentiable_hamiltonianOrdinarySourceFlow_sobolev D φ hf
  constructor
  · have h := ((E.comp (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).differentiable.comp hd
    have he : (fun time => E (sourceFiniteGapSobolevPair (by simp) (by norm_num)
        (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
        (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).1) =
        (fun time => (sourceFiniteGapPhysicalPair (by simp) (by norm_num)
          (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
          (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).1 x) := by
      funext time
      exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num)
        _ (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).1 x
    change Differentiable ℝ (fun time => E (sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).1) at h
    rwa [he] at h
  · have h := ((E.comp (ContinuousLinearMap.snd ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).differentiable.comp hd
    have he : (fun time => E (sourceFiniteGapSobolevPair (by simp) (by norm_num)
        (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
        (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).2) =
        (fun time => (sourceFiniteGapPhysicalPair (by simp) (by norm_num)
          (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
          (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).2 x) := by
      funext time
      exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num)
        _ (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).2 x
    change Differentiable ℝ (fun time => E (sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).2) at h
    rwa [he] at h

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
