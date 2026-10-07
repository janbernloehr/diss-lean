import NLS.ZakharovShabat.SourceRenormalizedSourceTrajectoryAnalytic

/-! # Constructed global analytic source trajectories

The actual spectral atlas and Birkhoff family supply a global continuous
group whose trajectory map is real analytic in the uniform source norm on
every compact time interval, for 1 < p ≤ 2. Classical-solution agreement
and the ordinary NLS mass shift remain separate parts of Section 22.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Global renormalized spectral dynamics with analytic compact-time source dependence,
constructed from the original spectral objects and preserving the original actions. -/
theorem exists_analytic_renormalizedSourceTrajectories
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W P : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ hs : SourcePsiSquaredGapComplexExtension hp hp1 P s,
    ∃ hP : IsOpen P, ∃ hr : realTypeSourceLocus p ⊆ P,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
      (∀ T : ℝ, AnalyticOnNhd ℝ (A.renormalizedSourceTrajectoryOn hs hP hr D hp2 T) univ) ∧
      Continuous (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedSourceFlow D hp2 x.2 x.1) ∧
      (∀ φ, A.renormalizedSourceFlow D hp2 φ 0 = φ) ∧
      (∀ φ τ σ, A.renormalizedSourceFlow D hp2 (A.renormalizedSourceFlow D hp2 φ σ) τ =
        A.renormalizedSourceFlow D hp2 φ (τ+σ)) ∧
      ∀ φ τ n, sourceComplexAction hp hp1 n (A.renormalizedSourceFlow D hp2 φ τ).val =
        sourceComplexAction hp hp1 n φ.val := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W,P,s,A,hs,hP,hr,W₀,B,X,t,D,
    A.analytic_renormalizedSourceTrajectoryOn hs hP hr D hp2,
    A.continuous_renormalizedSourceFlow hs hP hr D hp2,
    A.renormalizedSourceFlow_zero D hp2,
    A.renormalizedSourceFlow_add hs.toSourcePsiIsolatingComplexExtension D hp2,
    A.renormalizedSourceFlow_action D hp2⟩

end NLS.ZakharovShabat
