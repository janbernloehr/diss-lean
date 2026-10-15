import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.SequenceSpaces.Compact
import NLS.SequenceSpaces.LinearSpectralWeight

/-! # Compact decoding of weighted sources

The exact multiplier 1/w(2n) vanishes at infinity for every M₁ weight.
This gives relative compactness of weighted bounded sets in the original
source topology, including the physical H¹ embedding used in (5.14).
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The reciprocal symbol at the original doubled Fourier frequencies. -/
def normalizedWeightedSourceInverseSymbol (w : SpectralWeight) : Coeff ⊤ :=
  ⟨fun n => (w (2*n) : ℂ)⁻¹, memℓp_infty ⟨1,by
    rintro _ ⟨n,rfl⟩
    change ‖(w (2*n):ℂ)⁻¹‖ ≤ 1
    rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le]
    exact inv_le_one_of_one_le₀ (w.one_le _)⟩⟩

/-- M₁ weights give uniformly vanishing reciprocal tails. -/
theorem normalizedWeightedSourceInverseSymbol_tail (w : SpectralWeight) (hw : w.HasLinearFactor) :
    ∀ ε > (0:ℝ), ∃ s : Finset ℤ, ∀ n ∉ s, ‖normalizedWeightedSourceInverseSymbol w n‖ ≤ ε := by
  intro ε hε
  have ht := tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Complex.isClosedEmbedding_intCast
  have he := ht.eventually_ge_atTop ε⁻¹
  have hf := Filter.eventually_cofinite.mp he
  refine ⟨hf.toFinset,fun n hn => ?_⟩
  have hn' : ε⁻¹ ≤ ‖(n:ℂ)‖ := by
    simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,not_not,Function.comp_apply] using hn
  have hw' := SpectralWeight.bracket_le_of_hasLinearFactor hw (2*n)
  have hbound : ε⁻¹ ≤ w (2*n) := by
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hw'
    rw [Complex.norm_intCast] at hn'
    linarith [abs_nonneg (n:ℝ)]
  change ‖(w (2*n):ℂ)⁻¹‖ ≤ ε
  rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le]
  simpa using inv_anti₀ (inv_pos.mpr hε) hbound

/-- Decoding an M₁ weighted source is compact in the unweighted source norm. -/
theorem isCompactOperator_normalizedWeightedSource (w : SpectralWeight) (hw : w.HasLinearFactor) :
    IsCompactOperator (normalizedWeightedSourceCLM (p := p) w) := by
  let M := Coeff.multiplierCLM (p := p) (normalizedWeightedSourceInverseSymbol w)
  have hM : IsCompactOperator M := Coeff.isCompactOperator_multiplierCLM _ (normalizedWeightedSourceInverseSymbol_tail w hw)
  have h₁ := (hM.comp_clm (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))).clm_comp
    (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p))
  have h₂ := (hM.comp_clm (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))).clm_comp
    (ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p))
  have hprod : IsCompactOperator (M.prodMap M) := by
    have he : (M.prodMap M : (Coeff p × Coeff p) → (Coeff p × Coeff p)) =
        (fun a => (M a.1,0))+(fun a => (0,M a.2)) := by
      funext a
      change (M a.1,M a.2) = (M a.1+0,0+M a.2)
      simp
    rw [he]
    exact h₁.add h₂
  have he : normalizedWeightedSourceCLM (p := p) w =
      (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
        ((M.prodMap M).comp (CoeffPair.toMax p).toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro a
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext n <;>
      simp [M,normalizedWeightedSourceInverseSymbol,div_eq_mul_inv,mul_comm]
  rw [he]
  exact (hprod.comp_clm (CoeffPair.toMax p).toContinuousLinearMap).clm_comp
    (CoeffPair.toMax p).symm.toContinuousLinearMap


end NLS.ZakharovShabat
