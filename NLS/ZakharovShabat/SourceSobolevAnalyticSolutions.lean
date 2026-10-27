import NLS.ZakharovShabat.SourceSobolevNLSAnalytic

/-! # Constructed global NLS solutions with analytic Sobolev dependence -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both original global solution maps are analytic in the full compact-time
Sobolev norm at every nonnegative real regularity. Solutions retain the exact
raw Fourier coefficients and the original all-smooth-approximation meaning.
Uniqueness is inherited in that solution class, including stronger lifts. -/
theorem exists_original_sobolev_analytic_solutions
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ Φ Φstar : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) →
      ℝ → weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ),
      (∀ a, Φ a 0 = a ∧ Φstar a 0 = a ∧
        Dynamics.BohrAlmostPeriodic (Φ a) ∧ Dynamics.BohrAlmostPeriodic (Φstar a) ∧
        IsOrdinaryNLSSolutionOn univ (originalWeightedRealSource _ a)
          (fun τ => originalWeightedRealSource _ (Φ a τ)) ∧
        IsRenormalizedNLSSolutionOn univ (originalWeightedRealSource _ a)
          (fun τ => originalWeightedRealSource _ (Φstar a τ))) ∧
      (∀ T : ℝ, ∃ S Sstar : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) →
        C(Icc (-T) T, weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)),
        AnalyticOnNhd ℝ S univ ∧ AnalyticOnNhd ℝ Sstar univ ∧
        ∀ a τ, S a τ = Φ a τ.val ∧ Sstar a τ = Φstar a τ.val) ∧
      (∀ a γ, IsOrdinaryNLSSolutionOn univ (originalWeightedRealSource _ a)
        (fun τ => originalWeightedRealSource _ (γ τ)) → γ = Φ a) ∧
      (∀ a γ, IsRenormalizedNLSSolutionOn univ (originalWeightedRealSource _ a)
        (fun τ => originalWeightedRealSource _ (γ τ)) → γ = Φstar a) := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  let w := sourceSobolevSpectralWeight σ hσ
  let Φ := fun a : weightedRealSourceSubmodule (p := p) w =>
    D.complex.weightedSourcePhaseFlow hp2 σ hσ (A.ordinaryPhaseFrequency hp2 (originalWeightedRealSource w a)) a
  let Φstar := fun a : weightedRealSourceSubmodule (p := p) w =>
    D.complex.weightedSourcePhaseFlow hp2 σ hσ (A.phaseFrequency (originalWeightedRealSource w a)) a
  have hΦ (a : weightedRealSourceSubmodule (p := p) w) (τ : ℝ) :
      originalWeightedRealSource w (Φ a τ) = A.hamiltonianOrdinarySourceFlow D.complex hp2
        (originalWeightedRealSource w a) τ :=
    A.originalWeightedRealSource_ordinarySobolevPhase D.complex hp2 σ hσ a τ
  have hΦstar (a : weightedRealSourceSubmodule (p := p) w) (τ : ℝ) :
      originalWeightedRealSource w (Φstar a τ) = A.hamiltonianRenormalizedSourceFlow D.complex hp2
        (originalWeightedRealSource w a) τ :=
    A.originalWeightedRealSource_renormalizedSobolevPhase D.complex hp2 σ hσ a τ
  have hinj : Function.Injective (originalWeightedRealSource (p := p) w) := by
    intro a b h
    apply Subtype.ext
    exact originalWeightedSourceCLM_injective w (congrArg Subtype.val h)
  have hsol (a : weightedRealSourceSubmodule (p := p) w) :
      IsOrdinaryNLSSolutionOn univ (originalWeightedRealSource w a)
        (fun τ => originalWeightedRealSource w (Φ a τ)) ∧
      IsRenormalizedNLSSolutionOn univ (originalWeightedRealSource w a)
        (fun τ => originalWeightedRealSource w (Φstar a τ)) := by
    simp_rw [hΦ,hΦstar]
    exact (Q.global_physical_solutions hp2 (originalWeightedRealSource w a)).symm
  refine ⟨Φ,Φstar,?_,?_,?_,?_⟩
  · intro a
    exact ⟨D.complex.weightedSourcePhaseFlow_zero hp2 σ hσ _ a,
      D.complex.weightedSourcePhaseFlow_zero hp2 σ hσ _ a,
      D.complex.bohrAlmostPeriodic_weightedSourcePhaseFlow hp2 σ hσ _ a,
      D.complex.bohrAlmostPeriodic_weightedSourcePhaseFlow hp2 σ hσ _ a,hsol a⟩
  · intro T
    obtain ⟨S,Sstar,hS,hSstar,he⟩ := A.exists_analytic_sobolevHamiltonianTrajectories
      Q.roots D.roots_open D.roots_real_subset D.complex hp2 σ hσ
      (⟨Subtype.val,continuous_subtype_val⟩ : C(Icc (-T) T,ℝ))
    refine ⟨S,Sstar,hS,hSstar,fun a τ => ⟨hinj ?_,hinj ?_⟩⟩
    · exact (he a τ).1.trans (hΦ a τ.val).symm
    · exact (he a τ).2.trans (hΦstar a τ.val).symm
  · intro a γ hγ
    funext τ
    exact hinj (hγ.eqOn_inter (hsol a).1 hp hp1 ⟨mem_univ τ,mem_univ τ⟩)
  · intro a γ hγ
    funext τ
    exact hinj (hγ.eqOn_inter (hsol a).2 hp hp1 ⟨mem_univ τ,mem_univ τ⟩)

end NLS.ZakharovShabat
