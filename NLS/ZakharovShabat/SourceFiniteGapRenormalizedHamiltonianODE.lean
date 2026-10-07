import NLS.ZakharovShabat.SourceFiniteActionHamiltonian
import NLS.ZakharovShabat.SourceHamiltonianRenormalizedFlow

/-! # The renormalized action Hamiltonian ODE for finite-gap trajectories

Injectivity of the actual complex Birkhoff differential identifies the
full source derivative with a finite sum of original action Hamiltonian
fields. Frequency invariance makes the equation autonomous. This uses the
Hamiltonian time orientation; SourceRenormalizedMassCorrection identifies
this sum with the physical NLS field and its exact mass correction.
-/
noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- An initial finite coordinate cutoff contains the active coordinates for all time. -/
theorem complex_support_hamiltonianRenormalizedSourceFlow
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n = 0) (τ : ℝ) :
    ∀ n ∉ S,
      (sourceComplexBirkhoffMap hp hp1 t (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ).val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 t (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ).val).2 n = 0 := by
  intro n hn
  rw [A.complex_map_hamiltonianRenormalizedSourceFlow]
  simp only [Birkhoff.hamiltonianPhaseFlow_fst,Birkhoff.hamiltonianPhaseFlow_snd,
    (hz n hn).1,(hz n hn).2,mul_zero,and_self]

/-- Finite-gap sources remain finite-gap under the Hamiltonian-oriented renormalized flow. -/
theorem hamiltonianRenormalizedSourceFlow_finiteGap
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (τ : ℝ) :
    A.hamiltonianRenormalizedSourceFlow D hp2 φ τ ∈ sourceFiniteGapLocus hp hp1 := by
  let ψ := A.hamiltonianRenormalizedSourceFlow D hp2 φ τ
  apply hf.subset
  intro n hn
  by_contra hnot
  have hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0 := by
    simpa only [sourcePeriodicGapDisplacement_apply,Set.mem_ofPred_eq,not_not] using hnot
  have ha := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).2.2.mpr hg
  have he := A.hamiltonianRenormalizedSourceFlow_action D hp2 φ τ n
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ.val ψ.property,
    sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property,ha] at he
  have hgψ := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ.val ψ.property n).2.2.mp he
  exact hn (by simpa only [sourcePeriodicGapDisplacement_apply] using hgψ)

/-- The full source derivative is a finite sum of original action fields with initial frequencies. -/
theorem hasDerivAt_hamiltonianRenormalizedSourceFlow_finiteAction
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n = 0) (τ : ℝ) :
    HasDerivAt (fun σ => (A.hamiltonianRenormalizedSourceFlow D hp2 φ σ).val)
      (sourceFiniteActionHamiltonianVector hp hp1 h2p (A.phaseFrequency φ) S
        (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ).val) τ := by
  let γ := fun σ => A.hamiltonianRenormalizedSourceFlow D hp2 φ σ
  let z := sourceComplexBirkhoffMap hp hp1 t φ.val
  let freq := A.phaseFrequency φ
  let v := (D.realJacobianEquivAll (γ τ)).symm
    (Birkhoff.decodeReal (Birkhoff.finiteHamiltonianPhaseVelocity freq S
      (Birkhoff.hamiltonianPhaseFlow freq τ z)))
  have ht : HasDerivAt γ v τ := A.hasDerivAt_hamiltonianRenormalizedSourceFlow_of_support D hp2 φ S hz τ
  have hi := (realTypeSourceSubmodule p).subtypeL.hasFDerivAt.comp_hasDerivAt τ ht
  change HasDerivAt (fun σ => (γ σ).val) v.val τ at hi
  have hc := ((D.complex_map_analytic (γ τ).val (D.real_subset (γ τ).property)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ hi
  change HasDerivAt (fun σ => sourceComplexBirkhoffMap hp hp1 t (γ σ).val)
    ((fderiv ℂ (sourceComplexBirkhoffMap hp hp1 t) (γ τ).val) v.val) τ at hc
  have hc' : HasDerivAt (fun σ => Birkhoff.hamiltonianPhaseFlow freq σ z)
      ((fderiv ℂ (sourceComplexBirkhoffMap hp hp1 t) (γ τ).val) v.val) τ := by
    simpa only [Function.comp_def,γ,A.complex_map_hamiltonianRenormalizedSourceFlow] using! hc
  have hv := hc'.unique (Birkhoff.hasDerivAt_hamiltonianPhaseFlow_of_support freq S z hz τ)
  have he : v.val = sourceFiniteActionHamiltonianVector hp hp1 h2p freq S (γ τ).val := by
    apply D.complex_jacobian_injective (γ τ)
    rw [hv,D.complex_jacobian_finiteActionHamiltonian h2p]
    rw [show sourceComplexBirkhoffMap hp hp1 t (γ τ).val =
      Birkhoff.hamiltonianPhaseFlow freq τ z from A.complex_map_hamiltonianRenormalizedSourceFlow D hp2 φ τ]
  simpa only [he] using! hi

/-- The same ODE uses the frequencies of the current source, so it is autonomous. -/
theorem hasDerivAt_hamiltonianRenormalizedSourceFlow_autonomous
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n = 0) (τ : ℝ) :
    HasDerivAt (fun σ => (A.hamiltonianRenormalizedSourceFlow D hp2 φ σ).val)
      (sourceFiniteActionHamiltonianVector hp hp1 h2p
        (A.phaseFrequency (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ)) S
        (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ).val) τ := by
  have hf : A.phaseFrequency (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ) =
      A.phaseFrequency φ := A.phaseFrequency_renormalizedSourceFlow hs D hp2 φ (-τ)
  rw [hf]
  exact A.hasDerivAt_hamiltonianRenormalizedSourceFlow_finiteAction D hp2 h2p φ S hz τ

/-- Every Hilbert finite-gap source follows a genuine finite action-Hamiltonian ODE for all time. -/
theorem exists_finiteAction_renormalizedSource_ODE
    {W₂ P₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {V₂ B₂ X₂ : Set (CoeffPair 2)} {t₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ S : Finset ℤ, ∀ τ : ℝ,
      HasDerivAt (fun σ => (A.hamiltonianRenormalizedSourceFlow D le_rfl φ σ).val)
        (sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl
          (A.phaseFrequency (A.hamiltonianRenormalizedSourceFlow D le_rfl φ τ)) S
          (A.hamiltonianRenormalizedSourceFlow D le_rfl φ τ).val) τ := by
  obtain ⟨S,hS⟩ := D.exists_complex_support_finiteGap φ hf
  exact ⟨S,fun τ => A.hasDerivAt_hamiltonianRenormalizedSourceFlow_autonomous hs D le_rfl le_rfl φ S hS τ⟩

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
