import NLS.ZakharovShabat.SourceFiniteGapSobolevTime
import NLS.ZakharovShabat.SourceFiniteGapRenormalizedHamiltonianODE

/-! # Sobolev time regularity for the renormalized finite-gap flow -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace SourceAbelianMomentAtlas
variable {W V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- An initially collapsed indexed gap stays collapsed for all real time. -/
theorem hamiltonianRenormalizedSourceFlow_closed_gap
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (time : ℝ) (n : ℤ)
    (hgap : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time).val)
      (periodOnePotential_mem _) n = 0 := by
  let ψ := A.hamiltonianRenormalizedSourceFlow D le_rfl φ time
  have hg : sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n = 0 := by
    simpa only [sourcePeriodicGapDisplacement_apply] using hgap
  have ha := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp) (by norm_num) φ.val φ.property n).2.2.mpr hg
  have he := A.hamiltonianRenormalizedSourceFlow_action D le_rfl φ time n
  rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n ψ.val ψ.property,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property,ha] at he
  have hgψ : sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n = 0 :=
    (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) ψ.val ψ.property n).2.2.mp he
  rw [sourcePeriodicGapDisplacement_apply] at hgψ
  exact hgψ

/-- One initial spectral cutoff remains a closed-gap tail for the entire trajectory. -/
theorem exists_hamiltonianRenormalizedSourceFlow_closed_gap_tail
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ K : ℕ, ∀ time : ℝ, ∀ n : ℤ, K ≤ n.natAbs →
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time).val)
        (periodOnePotential_mem _) n = 0 := by
  classical
  let S := hf.toFinset
  refine ⟨S.sup Int.natAbs+1,?_⟩
  intro time n hn
  apply A.hamiltonianRenormalizedSourceFlow_closed_gap D φ time n
  by_contra hne
  have hmem : n ∈ S := hf.mem_toFinset.mpr hne
  have hle := Finset.le_sup (f := Int.natAbs) hmem
  omega

/-- The canonical physical H¹ representatives of the actual finite-gap
Hamiltonian-oriented spectral flow are differentiable at every real time. -/
theorem differentiable_hamiltonianRenormalizedSourceFlow_sobolev
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Differentiable ℝ (fun time => sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
      (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)) := by
  obtain ⟨K,hK⟩ := A.exists_hamiltonianRenormalizedSourceFlow_closed_gap_tail D φ hf
  intro time
  apply differentiableAt_sourceFiniteGapSobolevPair _ _ time _ K
    (Filter.Eventually.of_forall (hK ·))
  exact (realTypeSourceSubmodule (2 : ℝ≥0∞)).subtypeL.differentiableAt.comp time
    (A.differentiable_hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)

/-- At each spatial point, both physical components of the actual
finite-gap trajectory are differentiable in real time. -/
theorem differentiable_hamiltonianRenormalizedSourceFlow_physical
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (x : ℝ) :
    Differentiable ℝ (fun time => (sourceFiniteGapPhysicalPair (by simp) (by norm_num)
      (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
      (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).1 x) ∧
    Differentiable ℝ (fun time => (sourceFiniteGapPhysicalPair (by simp) (by norm_num)
      (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
      (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).2 x) := by
  let E := (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).comp NLS.Fourier.periodOneSobolevSynthesis
  have hd := A.differentiable_hamiltonianRenormalizedSourceFlow_sobolev D φ hf
  constructor
  · have h := ((E.comp (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).differentiable.comp hd
    have he : (fun time => E (sourceFiniteGapSobolevPair (by simp) (by norm_num)
        (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
        (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).1) =
        (fun time => (sourceFiniteGapPhysicalPair (by simp) (by norm_num)
          (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
          (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).1 x) := by
      funext time
      exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num)
        _ (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).1 x
    change Differentiable ℝ (fun time => E (sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
      (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).1) at h
    rwa [he] at h
  · have h := ((E.comp (ContinuousLinearMap.snd ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).differentiable.comp hd
    have he : (fun time => E (sourceFiniteGapSobolevPair (by simp) (by norm_num)
        (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
        (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).2) =
        (fun time => (sourceFiniteGapPhysicalPair (by simp) (by norm_num)
          (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
          (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).2 x) := by
      funext time
      exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num)
        _ (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).2 x
    change Differentiable ℝ (fun time => E (sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
      (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).2) at h
    rwa [he] at h

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
