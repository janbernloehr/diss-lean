import NLS.ZakharovShabat.SourceBirkhoffOriginalJacobian
import NLS.SequenceSpaces.PairOutputCutoff

/-!
# Actual finite-rank approximations of the normalized Jacobian

At every real finite-gap source the cutoffs converge in operator norm.
The tail estimate retains the bounded Fourier inverse factor.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
/-- Finite output cutoffs of A minus identity, using the exact inverse Fourier map. -/
def sourceBirkhoffNormalizedJacobianCutoff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p) (S : Finset ℤ) :
    CoeffPair p →L[ℂ] CoeffPair p :=
  Coeff.pairOutputCutoff (sourceBirkhoffJacobianRemainder hp hp1 s ψ)
    sourceBirkhoffFourierInverse S

/-- The cutoff is the literal finite gradient-basis sum, with the negative y term. -/
theorem sourceBirkhoffNormalizedJacobianCutoff_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ h : CoeffPair p) (S : Finset ℤ) :
    sourceBirkhoffNormalizedJacobianCutoff hp hp1 s ψ S h =
      ∑ n ∈ S, ((sourceBirkhoffJacobianRemainder hp hp1 s ψ h).1 n • sourceBirkhoffFreeXGradient p (-n) -
        (sourceBirkhoffJacobianRemainder hp hp1 s ψ h).2 n • sourceBirkhoffFreeYGradient p (-n)) := by
  rw [sourceBirkhoffNormalizedJacobianCutoff,Coeff.pairOutputCutoff_apply]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [neg_neg] using sourceBirkhoffFourierInverse_single (-n)
    ((sourceBirkhoffJacobianRemainder hp hp1 s ψ h).1 n)
    ((sourceBirkhoffJacobianRemainder hp hp1 s ψ h).2 n)

theorem sourceBirkhoffNormalizedJacobianCutoff_error_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p)
    (b₁ b₂ : Coeff p)
    (hrow : ∀ (n : ℤ) (h : CoeffPair p),
      ‖(sourceBirkhoffJacobianRemainder hp hp1 s ψ h).1 n‖ ≤ ‖b₁ n‖*‖h‖ ∧
      ‖(sourceBirkhoffJacobianRemainder hp hp1 s ψ h).2 n‖ ≤ ‖b₂ n‖*‖h‖)
    (S : Finset ℤ) :
    ‖sourceBirkhoffNormalizedJacobianCutoff hp hp1 s ψ S -
      (sourceBirkhoffNormalizedJacobian hp hp1 s ψ - ContinuousLinearMap.id ℂ (CoeffPair p))‖ ≤
      ‖sourceBirkhoffFourierInverse (p := p)‖ *
        max ‖Coeff.truncate S b₁-b₁‖ ‖Coeff.truncate S b₂-b₂‖ := by
  rw [sourceBirkhoffNormalizedJacobian_sub_id]
  exact Coeff.norm_pairOutputCutoff_sub_le _ _ b₁ b₂ hrow S

theorem sourceBirkhoffNormalizedJacobianCutoff_finiteDimensional (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p) (S : Finset ℤ) :
    FiniteDimensional ℂ (LinearMap.range (sourceBirkhoffNormalizedJacobianCutoff hp hp1 s ψ S).toLinearMap) :=
  Coeff.finiteDimensional_range_pairOutputCutoff _ _ S

namespace SourceSection15OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
theorem normalizedCutoff_tendsto (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Tendsto (sourceBirkhoffNormalizedJacobianCutoff hp hp1 s φ.val) atTop
      (𝓝 (sourceBirkhoffNormalizedJacobian hp hp1 s φ.val - ContinuousLinearMap.id ℂ (CoeffPair p))) := by
  let T := sourceBirkhoffJacobianRemainder hp hp1 s φ.val
  let T₁ := (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp T
  let T₂ := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp T
  obtain ⟨h₁, h₂⟩ := D.complex.tendsto_truncate_jacobianRemainder_finiteGap φ hfinite
  let combine : ((CoeffPair p →L[ℂ] Coeff p) × (CoeffPair p →L[ℂ] Coeff p)) ≃ₗᵢ[ℂ]
      (CoeffPair p →L[ℂ] (Coeff p × Coeff p)) := ContinuousLinearMap.prodₗᵢ ℂ
  have ht := (combine.continuous.tendsto (T₁,T₂)).comp (h₁.prodMk_nhds h₂)
  have hc := ((ContinuousLinearMap.compL ℂ (CoeffPair p) (Coeff p × Coeff p) (CoeffPair p))
    sourceBirkhoffFourierInverse).continuous.tendsto (T₁.prod T₂) |>.comp ht
  have he : T₁.prod T₂ = T := by ext h <;> rfl
  change Tendsto (sourceBirkhoffNormalizedJacobianCutoff hp hp1 s φ.val) atTop
    (𝓝 (sourceBirkhoffFourierInverse.comp (T₁.prod T₂))) at hc
  rw [he] at hc
  rwa [sourceBirkhoffNormalizedJacobian_sub_id]

theorem normalizedCutoff_symmetric_tendsto (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Tendsto (fun N : ℕ => sourceBirkhoffNormalizedJacobianCutoff hp hp1 s φ.val (Finset.Icc (-(N:ℤ)) N)) atTop
      (𝓝 (sourceBirkhoffNormalizedJacobian hp hp1 s φ.val - ContinuousLinearMap.id ℂ (CoeffPair p))) :=
  (normalizedCutoff_tendsto D φ hfinite).comp Finset.tendsto_Icc_neg

end SourceSection15OriginalData

end NLS.ZakharovShabat
