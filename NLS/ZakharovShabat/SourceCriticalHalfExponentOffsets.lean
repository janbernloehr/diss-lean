import NLS.SequenceSpaces.QuasiHolderProduct
import NLS.SequenceSpaces.QuasiExponentEmbedding
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform
import NLS.ZakharovShabat.SourceSquaredGapNorm

/-! # Critical offsets in the half-exponent sequence space

Both the critical-midpoint offset and its gap-normalized form belong to
`ell^(p/2)`, including the range below exponent one. These are actual
coefficient products, so collapsed gaps require no choice of a quotient.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The offset after removing one gap factor: `gamma_n*q_n`. -/
def sourceCriticalGapLinearOffset (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff (ENNReal.ofReal (p.toReal/2)) := by
  let : p.HolderTriple p (ENNReal.ofReal (p.toReal/2)) := by
    rw [Coeff.halfExponent_eq_div hp]
    exact Coeff.holderTriple_half p
  exact Coeff.quasiHolderProduct (sourcePeriodicGapDisplacement hp hp1 ψ)
    (sourceCriticalGapQuotient hp hp1 ψ)

@[simp] theorem sourceCriticalGapLinearOffset_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceCriticalGapLinearOffset hp hp1 ψ n =
      sourcePeriodicGapDisplacement hp hp1 ψ n*sourceCriticalGapQuotient hp hp1 ψ n := rfl

theorem norm_sourceCriticalGapLinearOffset_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) :
    ‖sourceCriticalGapLinearOffset hp hp1 ψ‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ‖*‖sourceCriticalGapQuotient hp hp1 ψ‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  let : p.HolderTriple p (ENNReal.ofReal (p.toReal/2)) := by
    rw [Coeff.halfExponent_eq_div hp]
    exact Coeff.holderTriple_half p
  exact Coeff.norm_quasiHolderProduct_le hp0 hp0 _ _

/-- The actual critical-midpoint offset represented at the half exponent. -/
def sourceCriticalHalfGapOffset (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff (ENNReal.ofReal (p.toReal/2)) :=
  Coeff.multiplier (Coeff.exponentInclusion le_top (sourceCriticalGapQuotient hp hp1 ψ))
    (sourcePeriodicSquaredGapCoeff hp hp1 ψ)

@[simp] theorem sourceCriticalHalfGapOffset_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceCriticalHalfGapOffset hp hp1 ψ n =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*sourceCriticalGapQuotient hp hp1 ψ n := by
  simp only [sourceCriticalHalfGapOffset,Coeff.multiplier_apply,Coeff.exponentInclusion_apply,
    sourcePeriodicSquaredGapCoeff_apply,mul_comm]

theorem norm_sourceCriticalHalfGapOffset_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) :
    ‖sourceCriticalHalfGapOffset hp hp1 ψ‖ ≤
      ‖sourceCriticalGapQuotient hp hp1 ψ‖*‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2 := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hr : ENNReal.ofReal (p.toReal/2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  apply (Coeff.norm_multiplier_le_quasi hr _ _).trans
  exact mul_le_mul (Coeff.norm_exponentInclusion_le le_top _)
    (norm_sourcePeriodicSquaredGapCoeff_le_sq hp hp1 ψ)
    (lp.norm_nonneg' _) (norm_nonneg _)

/-- A common source neighborhood supplies uniformly bounded half-exponent
sequences for both offsets and their exact critical-point identities. -/
theorem exists_local_uniform_sourceCriticalHalfOffsets
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V,
      ‖sourceCriticalHalfGapOffset hp hp1 ψ‖ ≤ M ∧
      ‖sourceCriticalGapLinearOffset hp hp1 ψ‖ ≤ M ∧
      ∀ n : ℤ,
        canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
          canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
            sourceCriticalHalfGapOffset hp hp1 ψ n ∧
        sourceCriticalHalfGapOffset hp hp1 ψ n =
          sourcePeriodicGapDisplacement hp hp1 ψ n*sourceCriticalGapLinearOffset hp hp1 ψ n := by
  obtain ⟨Vq,hVq,hφq,K,hK,hq⟩ := exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  obtain ⟨_,_,Vd,hVd,hφd,D,hD,hd⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  refine ⟨Vq ∩ Vd,hVq.inter hVd,⟨hφq,hφd⟩,max (K*D^2) (D*K),by positivity,?_⟩
  intro ψ hψ
  refine ⟨?_,?_,?_⟩
  · apply (norm_sourceCriticalHalfGapOffset_le hp hp1 ψ).trans
    exact (mul_le_mul (hq ψ hψ.1).1 (pow_le_pow_left₀ (norm_nonneg _) (hd ψ hψ.2).1 2)
      (sq_nonneg _) hK).trans (le_max_left _ _)
  · apply (norm_sourceCriticalGapLinearOffset_le hp hp1 ψ).trans
    exact (mul_le_mul (hd ψ hψ.2).1 (hq ψ hψ.1).1 (norm_nonneg _) hD).trans (le_max_right _ _)
  · intro n
    constructor
    · simpa only [sourceCriticalHalfGapOffset_apply] using (hq ψ hψ.1).2 n
    · simp only [sourceCriticalHalfGapOffset_apply,sourceCriticalGapLinearOffset_apply]
      ring

end NLS.ZakharovShabat
