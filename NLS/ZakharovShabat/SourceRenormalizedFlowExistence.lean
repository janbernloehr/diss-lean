import NLS.ZakharovShabat.SourceRenormalizedFlowTrajectories

/-! # Constructed global continuous renormalized flows

The moment atlas, normalized psi family, and actual Birkhoff map are
constructed. The resulting coordinate trajectories exist at every finite
exponent above one. In the globally invertible range p ≤ 2, they give a
continuous group on the original real source space, preserving its actual
spectral actions, with negative time as inverse.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the continuous coordinate trajectories and, for p ≤ 2, the global
source flow with its actual coordinates, actions, group law, and homeomorphisms. -/
theorem exists_continuous_renormalizedFlow (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
      Continuous (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedPhaseTrajectory t x.2 x.1) ∧
      (∀ φ : realTypeSourceSubmodule p, ∀ τ : ℝ,
        Birkhoff.IsConjugatePair (A.renormalizedPhaseTrajectory t φ τ) ∧
        ∀ n : ℤ, (A.renormalizedPhaseTrajectory t φ τ).1 n*(A.renormalizedPhaseTrajectory t φ τ).2 n =
          sourceComplexAction hp hp1 n φ.val) ∧
      ∀ hp2 : p ≤ 2,
        Continuous (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedSourceFlow D hp2 x.2 x.1) ∧
        (∀ φ, A.renormalizedSourceFlow D hp2 φ 0 = φ) ∧
        (∀ φ τ σ, A.renormalizedSourceFlow D hp2 (A.renormalizedSourceFlow D hp2 φ σ) τ =
          A.renormalizedSourceFlow D hp2 φ (τ+σ)) ∧
        (∀ φ τ, sourceComplexBirkhoffMap hp hp1 t (A.renormalizedSourceFlow D hp2 φ τ).val =
          A.renormalizedPhaseTrajectory t φ τ) ∧
        (∀ φ τ n, sourceComplexAction hp hp1 n (A.renormalizedSourceFlow D hp2 φ τ).val =
          sourceComplexAction hp hp1 n φ.val) ∧
        ∀ τ : ℝ, ∃ e : realTypeSourceSubmodule p ≃ₜ realTypeSourceSubmodule p,
          (∀ φ, e φ = A.renormalizedSourceFlow D hp2 φ τ) ∧
          ∀ φ, e.symm φ = A.renormalizedSourceFlow D hp2 φ (-τ) := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,A.continuous_renormalizedPhaseTrajectory hs hP hr D,?_,?_⟩
  · intro φ τ
    exact ⟨A.renormalizedPhaseTrajectory_real D φ τ,A.renormalizedPhaseTrajectory_action D φ τ⟩
  · intro hp2
    refine ⟨A.continuous_renormalizedSourceFlow hs hP hr D hp2,
      A.renormalizedSourceFlow_zero D hp2,
      A.renormalizedSourceFlow_add hs.toSourcePsiIsolatingComplexExtension D hp2,
      A.complex_map_renormalizedSourceFlow D hp2,A.renormalizedSourceFlow_action D hp2,?_⟩
    intro τ
    exact ⟨A.renormalizedSourceHomeomorph hs hP hr D hp2 τ,fun _ => rfl,fun _ => rfl⟩

end NLS.ZakharovShabat
