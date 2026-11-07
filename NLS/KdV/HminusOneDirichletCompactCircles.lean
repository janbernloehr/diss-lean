import NLS.KdV.HminusOneDirichletSourceCircles
import NLS.FunctionalAnalysis.CompactThreshold

/-! One source-circle cutoff on each fixed compact native potential set. -/
noncomputable section
open Set Metric
namespace NLS.KdV

/-- Compactness makes the actual Dirichlet source contours, original-index
isolation and algebraic simplicity uniform on the entire compact set. -/
theorem exists_uniform_hillHminusDirichlet_sourceCircles_on_compact
    (K : Set PeriodOneHminusOne) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ a ∈ K, ∀ n : ℕ+, N < (n:ℕ) →
      sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet (periodOneOriginal a) ∧
      hillHminusDirichletComplexLabels a n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ∧
      (∀ z ∈ closedBall (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
        z ∈ singularDirichletSpectrum (periodOneOriginal a) ↔ z = hillHminusDirichletComplexLabels a n) ∧
      singularDirichletAlgebraicMultiplicity (periodOneOriginal a)
        (hillHminusDirichletComplexLabels a n) = 1 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let P : K → ℕ → Prop := fun a M => ∀ n : ℕ+, (n:ℕ) = M →
    sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet (periodOneOriginal a.val) ∧
    hillHminusDirichletComplexLabels a.val n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ∧
    (∀ z ∈ closedBall (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
      z ∈ singularDirichletSpectrum (periodOneOriginal a.val) ↔ z = hillHminusDirichletComplexLabels a.val n) ∧
    singularDirichletAlgebraicMultiplicity (periodOneOriginal a.val)
      (hillHminusDirichletComplexLabels a.val n) = 1
  have hlocal (a : K) : ∃ N : ℕ, ∃ U : Set K, IsOpen U ∧ a ∈ U ∧
      ∀ b ∈ U, ∀ M : ℕ, N ≤ M → P b M := by
    obtain ⟨N,V,_,hV,ha,_,hb⟩ := exists_uniform_hillHminusDirichlet_sourceCircles a.val
    refine ⟨N+1,Subtype.val ⁻¹' V,hV.preimage continuous_subtype_val,ha,?_⟩
    intro b hbV M hM n hn
    exact hb b.val hbV n (by omega)
  obtain ⟨N,hN⟩ := NLS.exists_uniform_nat_threshold_on_compact P hlocal
  refine ⟨max N 1,by omega,?_⟩
  intro a ha n hn
  exact hN ⟨a,ha⟩ (n:ℕ) (by omega) n rfl

end NLS.KdV
