import NLS.ZakharovShabat.SourceSobolevPhaseFlow
import NLS.ZakharovShabat.SourceSection22Original

/-! # Sobolev almost periodicity of original global NLS solutions

The actual weighted norms and original coefficients are retained throughout.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W Wa : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
namespace SourceAbelianMomentAtlas

/-- The weighted lift with ordinary frequencies is the same original physical flow. -/
theorem originalWeightedRealSource_ordinarySobolevPhase
    (A : SourceAbelianMomentAtlas hp hp1 Wa s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) (t : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ)
      (D.weightedSourcePhaseFlow hp2 σ hσ
        (A.ordinaryPhaseFrequency hp2 (originalWeightedRealSource _ a)) a t) =
    A.hamiltonianOrdinarySourceFlow D hp2 (originalWeightedRealSource _ a) t :=
  D.originalWeightedRealSource_weightedSourcePhaseFlow hp2 σ hσ _ a t

/-- Renormalized frequencies likewise give the original Hamiltonian-oriented flow. -/
theorem originalWeightedRealSource_renormalizedSobolevPhase
    (A : SourceAbelianMomentAtlas hp hp1 Wa s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) (t : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ)
      (D.weightedSourcePhaseFlow hp2 σ hσ
        (A.phaseFrequency (originalWeightedRealSource _ a)) a t) =
    A.hamiltonianRenormalizedSourceFlow D hp2 (originalWeightedRealSource _ a) t :=
  D.originalWeightedRealSource_weightedSourcePhaseFlow hp2 σ hσ _ a t

end SourceAbelianMomentAtlas

/-- Both original global solutions retain all prescribed nonnegative real Sobolev
regularity and are Bohr almost periodic in that actual stronger norm. -/
theorem exists_original_sobolev_almostPeriodic_solutions
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) :
    ∃ γ γstar : ℝ → weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ),
      γ 0 = a ∧ γstar 0 = a ∧ Dynamics.BohrAlmostPeriodic γ ∧ Dynamics.BohrAlmostPeriodic γstar ∧
      IsOrdinaryNLSSolutionOn univ (originalWeightedRealSource _ a)
        (fun t => originalWeightedRealSource _ (γ t)) ∧
      IsRenormalizedNLSSolutionOn univ (originalWeightedRealSource _ a)
        (fun t => originalWeightedRealSource _ (γstar t)) := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  let w := sourceSobolevSpectralWeight σ hσ
  let φ := originalWeightedRealSource w a
  let γ := D.complex.weightedSourcePhaseFlow hp2 σ hσ (A.ordinaryPhaseFrequency hp2 φ) a
  let γstar := D.complex.weightedSourcePhaseFlow hp2 σ hσ (A.phaseFrequency φ) a
  have he : (fun t => originalWeightedRealSource w (γ t)) =
      A.hamiltonianOrdinarySourceFlow D.complex hp2 φ := by
    funext t
    exact A.originalWeightedRealSource_ordinarySobolevPhase D.complex hp2 σ hσ a t
  have hestar : (fun t => originalWeightedRealSource w (γstar t)) =
      A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ := by
    funext t
    exact A.originalWeightedRealSource_renormalizedSobolevPhase D.complex hp2 σ hσ a t
  refine ⟨γ,γstar,D.complex.weightedSourcePhaseFlow_zero hp2 σ hσ _ a,
    D.complex.weightedSourcePhaseFlow_zero hp2 σ hσ _ a,
    D.complex.bohrAlmostPeriodic_weightedSourcePhaseFlow hp2 σ hσ _ a,
    D.complex.bohrAlmostPeriodic_weightedSourcePhaseFlow hp2 σ hσ _ a,?_,?_⟩
  · rw [he]
    exact (Q.global_physical_solutions hp2 φ).2
  · rw [hestar]
    exact (Q.global_physical_solutions hp2 φ).1

/-- Every original global ordinary solution with Sobolev initial data has the same
almost-periodic stronger representative, by original solution uniqueness. -/
theorem exists_sobolev_almostPeriodic_lift_of_isOrdinaryNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (γ : ℝ → realTypeSourceSubmodule p)
    (hγ : IsOrdinaryNLSSolutionOn univ (originalWeightedRealSource _ a) γ) :
    ∃ Γ : ℝ → weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ),
      Γ 0 = a ∧ Dynamics.BohrAlmostPeriodic Γ ∧
        ∀ t, originalWeightedRealSource _ (Γ t) = γ t := by
  obtain ⟨Γ,_,h0,_,hrec,_,hsol,_⟩ :=
    exists_original_sobolev_almostPeriodic_solutions hp hp1 hp2 σ hσ a
  exact ⟨Γ,h0,hrec,fun t => hsol.eqOn_inter hγ hp hp1 ⟨mem_univ t,mem_univ t⟩⟩

/-- The same stronger representative is retained for every original renormalized solution. -/
theorem exists_sobolev_almostPeriodic_lift_of_isRenormalizedNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (γ : ℝ → realTypeSourceSubmodule p)
    (hγ : IsRenormalizedNLSSolutionOn univ (originalWeightedRealSource _ a) γ) :
    ∃ Γ : ℝ → weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ),
      Γ 0 = a ∧ Dynamics.BohrAlmostPeriodic Γ ∧
        ∀ t, originalWeightedRealSource _ (Γ t) = γ t := by
  obtain ⟨_,Γ,_,h0,_,hrec,_,hsol⟩ :=
    exists_original_sobolev_almostPeriodic_solutions hp hp1 hp2 σ hσ a
  exact ⟨Γ,h0,hrec,fun t => hsol.eqOn_inter hγ hp hp1 ⟨mem_univ t,mem_univ t⟩⟩

end NLS.ZakharovShabat
