import NLS.ZakharovShabat.SourcePsiLemma12_12
import NLS.ZakharovShabat.SourceSquaredGapNorm
import NLS.SequenceSpaces.QuasiExponentEmbedding

/-! # Refined exponents for the actual filled psi displacement

The actual numerator displacement is the squared gap times the offset
sequence of Lemma 12.12. Multiplication by a bounded sequence and
contractive exponent inclusion give every finite exponent at least p/2,
including when the squared-gap space is below exponent one.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual filled numerator displacement has a half-exponent bound.
Only the bounded multiplier uses the offset's lp norm. -/
theorem exists_filledPsi_offset_coeff_of_squared_offsets
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (a : DeletedCoeff p n)
    (α : Coeff p) (hαn : α n = 0)
    (hα : ∀ k, k ≠ n → displacedRoots (a : Coeff p) k =
      sourceStandardRootMidpoint hp hp1 ψ k+(sourcePeriodicGapDisplacement hp hp1 ψ k)^2*α k)
    (r : ℝ≥0∞) (hr : r ≠ ⊤) (hrpos : 0 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) :
    ∃ β : Coeff r,
      (∀ k, displacedRoots (sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n)) k-
        sourceStandardRootMidpoint hp hp1 ψ k = β k) ∧
      ‖β‖ ≤ ‖α‖*‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ := by
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (div_pos (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp) (by norm_num))
  let m : Coeff ⊤ := Coeff.exponentInclusion le_top α
  let b := Coeff.multiplier m (sourcePeriodicSquaredGapCoeff hp hp1 ψ)
  let β : Coeff r := ⟨fun k => b k,(lp.memℓp b).of_exponent_ge hpr⟩
  refine ⟨β,?_,?_⟩
  · intro k
    change _ = m k*sourcePeriodicSquaredGapCoeff hp hp1 ψ k
    simp only [m,Coeff.exponentInclusion_apply,sourcePeriodicSquaredGapCoeff_apply]
    by_cases hkn : k = n
    · subst k
      simp only [displacedRoots_sourcePsiFillDeletedRoot_same,sub_self,hαn,zero_mul]
    · rw [displacedRoots_sourcePsiFillDeletedRoot_other n k hkn,hα k hkn]
      ring
  · calc
      ‖β‖ ≤ ‖b‖ := Coeff.norm_quasiExponentInclusion_le hhalf hrpos hr hpr b
      _ ≤ ‖m‖*‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ := Coeff.norm_multiplier_le_quasi hhalf.ne' m _
      _ ≤ ‖α‖*‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ :=
        mul_le_mul_of_nonneg_right (Coeff.norm_exponentInclusion_le le_top α) (lp.norm_nonneg' _)

/-- One source neighborhood and one norm bound work before the deleted
index and before every finite exponent above one and at least p/2. -/
theorem SourcePsiSquaredGapComplexExtension.locally_uniform_refined_filled_offsets
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s) (φ : CoeffPair p) (hφ : φ ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ V ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∀ r : ℝ≥0∞,
        r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ β : Coeff r,
          (∀ k, displacedRoots (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)) k-
            sourceStandardRootMidpoint hp hp1 ψ k = β k) ∧ ‖β‖ ≤ B := by
  obtain ⟨T,hT,hφT,hTV,C,hC,hroot⟩ := hs.locally_uniform_squared_gap_offsets φ hφ
  obtain ⟨G,hG,hφG,R,_,hgap⟩ := exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
  refine ⟨T ∩ G,hT.inter hG,⟨hφT,hφG⟩,fun _ h => hTV h.1,C*R^2,mul_nonneg hC.le (sq_nonneg _),?_⟩
  intro ψ hψ n r hr hr1 hpr
  obtain ⟨α,hαn,hα,hαnorm⟩ := hroot ψ hψ.1 n
  obtain ⟨β,hβ,hβnorm⟩ := exists_filledPsi_offset_coeff_of_squared_offsets hp hp1 ψ n (s n ψ)
    α hαn hα r hr (zero_lt_one.trans hr1) hpr
  exact ⟨β,hβ,hβnorm.trans (mul_le_mul hαnorm (hgap ψ hψ.2) (lp.norm_nonneg' _) hC.le)⟩

end NLS.ZakharovShabat
