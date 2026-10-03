import NLS.ZakharovShabat.SourceBirkhoffLemma16_2
import NLS.ZakharovShabat.SourceBirkhoffFourierEquivalence
import NLS.ZakharovShabat.SourceFiniteGapDensity
import NLS.SequenceSpaces.CompactRowMajorant

/-! # Compactness of the actual Birkhoff Jacobian remainder

Lemma 16.2 supplies summable row bounds at finite-gap sources. Finite
output truncations prove compactness there. Density in the original
source norm and continuity of the actual Jacobian extend compactness
to every real source at every finite exponent strictly above one.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Jacobian minus its explicitly normalized free Fourier map. -/
def sourceBirkhoffJacobianRemainder (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (φ : CoeffPair p) :
    CoeffPair p →L[ℂ] (Coeff p × Coeff p) :=
  sourceBirkhoffJacobian hp hp1 s φ-sourceBirkhoffFourier

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual finite-gap Jacobian remainder has summable bounds on both output rows. -/
theorem exists_jacobianRemainder_rowMajorants_finiteGap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ b₁ b₂ : Coeff p, ∀ (n : ℤ) (h : CoeffPair p),
      ‖(sourceBirkhoffJacobianRemainder hp hp1 s φ.val h).1 n‖ ≤ ‖b₁ n‖*‖h‖ ∧
      ‖(sourceBirkhoffJacobianRemainder hp hp1 s φ.val h).2 n‖ ≤ ‖b₂ n‖*‖h‖ := by
  let L₁ (n : ℤ) := fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val-sourceBirkhoffFreeXCotangent hp hp1 n
  let L₂ (n : ℤ) := fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val-sourceBirkhoffFreeYCotangent hp hp1 n
  have hL := D.angular.memlp_birkhoffXY_fderiv_sub_free_finiteGap W D.source_open D.source_subset
    φ (D.real_subset φ.property) hfinite
  let b₁ : Coeff p := ⟨fun n => (‖L₁ n‖ : ℂ),hL.1.norm.mono (by intro n; simp [L₁])⟩
  let b₂ : Coeff p := ⟨fun n => (‖L₂ n‖ : ℂ),hL.2.norm.mono (by intro n; simp [L₂])⟩
  refine ⟨b₁,b₂,fun n h => ?_⟩
  have hcoord := D.jacobian_coordinates φ.val (D.real_subset φ.property) h n
  constructor
  · change ‖(sourceBirkhoffJacobian hp hp1 s φ.val h).1 n-(sourceBirkhoffFourier h).1 n‖ ≤
      ‖(‖L₁ n‖ : ℂ)‖*‖h‖
    rw [hcoord.1,sourceBirkhoffFourier_fst,← (sourceBirkhoffFreeCotangents_apply hp hp1 n h).1]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact (L₁ n).le_opNorm h
  · change ‖(sourceBirkhoffJacobian hp hp1 s φ.val h).2 n-(sourceBirkhoffFourier h).2 n‖ ≤
      ‖(‖L₂ n‖ : ℂ)‖*‖h‖
    rw [hcoord.2,sourceBirkhoffFourier_snd,← (sourceBirkhoffFreeCotangents_apply hp hp1 n h).2]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact (L₂ n).le_opNorm h

/-- Finite output truncations of both actual remainder components converge in operator norm. -/
theorem tendsto_truncate_jacobianRemainder_finiteGap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    let T := sourceBirkhoffJacobianRemainder hp hp1 s φ.val
    let T₁ := (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp T
    let T₂ := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp T
    Tendsto (fun S : Finset ℤ => (Coeff.truncateCLM S).comp T₁) atTop (𝓝 T₁) ∧
      Tendsto (fun S : Finset ℤ => (Coeff.truncateCLM S).comp T₂) atTop (𝓝 T₂) := by
  obtain ⟨b₁,b₂,hb⟩ := D.exists_jacobianRemainder_rowMajorants_finiteGap φ hfinite
  exact ⟨Coeff.tendsto_truncate_operator_of_rowMajorant hp _ b₁ (fun n h => (hb n h).1),
    Coeff.tendsto_truncate_operator_of_rowMajorant hp _ b₂ (fun n h => (hb n h).2)⟩

/-- Lemma 16.2 makes the actual finite-gap Jacobian a compact perturbation of Fourier. -/
theorem isCompactOperator_jacobianRemainder_finiteGap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    IsCompactOperator (sourceBirkhoffJacobianRemainder hp hp1 s φ.val) := by
  obtain ⟨b₁,b₂,hb⟩ := D.exists_jacobianRemainder_rowMajorants_finiteGap φ hfinite
  let T := sourceBirkhoffJacobianRemainder hp hp1 s φ.val
  let T₁ := (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp T
  let T₂ := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp T
  have h₁ : IsCompactOperator T₁ := Coeff.isCompactOperator_of_rowMajorant hp T₁ b₁ (fun n h => (hb n h).1)
  have h₂ : IsCompactOperator T₂ := Coeff.isCompactOperator_of_rowMajorant hp T₂ b₂ (fun n h => (hb n h).2)
  have hsum := (h₁.clm_comp (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p))).add
    (h₂.clm_comp (ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p)))
  have heq : (fun h => T h) =
      (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p) ∘ T₁+
        ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p) ∘ T₂) := by
    funext h
    apply Prod.ext <;> simp [T₁,T₂]
  rw [← heq] at hsum
  exact hsum

/-- The remainder varies continuously on the entire real source space. -/
theorem continuous_jacobianRemainder_real
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    Continuous (fun φ : realTypeSourceSubmodule p => sourceBirkhoffJacobianRemainder hp hp1 s φ.val) := by
  apply continuous_iff_continuousAt.mpr
  intro φ
  exact ((D.jacobian_analytic φ.val (D.real_subset φ.property)).continuousAt.sub continuousAt_const).comp
    continuous_subtype_val.continuousAt

/-- The actual Jacobian is a compact perturbation of Fourier at every real
source, by finite-gap density and closedness of compact operators. -/
theorem isCompactOperator_jacobianRemainder_real
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    IsCompactOperator (sourceBirkhoffJacobianRemainder hp hp1 s φ.val) := by
  have hclosed : IsClosed {ψ : realTypeSourceSubmodule p |
      IsCompactOperator (sourceBirkhoffJacobianRemainder hp hp1 s ψ.val)} :=
    isClosed_setOfPred_isCompactOperator.preimage D.continuous_jacobianRemainder_real
  have hsub : sourceFiniteGapLocus hp hp1 ⊆ {ψ : realTypeSourceSubmodule p |
      IsCompactOperator (sourceBirkhoffJacobianRemainder hp hp1 s ψ.val)} :=
    fun ψ hψ => D.isCompactOperator_jacobianRemainder_finiteGap ψ hψ
  exact closure_minimal hsub hclosed ((dense_sourceFiniteGapLocus hp hp1) φ)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
