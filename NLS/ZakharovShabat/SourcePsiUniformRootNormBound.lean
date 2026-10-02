import NLS.ZakharovShabat.SourcePsiUniformRetainedRootBounds

/-! # Uniform norms of the actual deleted root vectors

The squared-gap offset factorization bounds the full deleted `ℓᵖ`
norm, uniformly in the omitted index. This supplies bounded root
inputs for the diagonal quotient estimates used in Section 15.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem exists_local_uniform_deletedRoot_norm_bound
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ A : ℝ, 0 < A ∧ ∀ ψ ∈ V, ∀ n : ℤ, ‖s n ψ‖ ≤ A := by
  obtain ⟨Va,hVa,hφa,hVaW,L,hL,hoffset⟩ := hs.locally_uniform_squared_gap_offsets φ hφ
  obtain ⟨_,_,Vm,hVm,hφm,D,hD,hmid⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  refine ⟨(Va ∩ Vm) ∩ Vg,(hVa.inter hVm).inter hVg,⟨⟨hφa,hφm⟩,hφg⟩,
    (fun ψ hψ => hVaW hψ.1.1),D+G^2*L+1,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨α,_,hfactor,hα⟩ := hoffset ψ hψ.1.1 n
  let t := sourcePeriodicMidpointDisplacement hp hp1 ψ
  let E : Coeff p := Coeff.magnitude t + ((G^2 : ℝ) : ℂ) • Coeff.magnitude α
  have hE m : ‖E m‖ = ‖t m‖+G^2*‖α m‖ := by
    simp only [E,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,
      Coeff.magnitude_apply,smul_eq_mul,← Complex.ofReal_mul,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ ‖t m‖+G^2*‖α m‖)]
  have hnorm : ‖s n ψ‖ ≤ ‖E‖ := by
    change ‖(s n ψ : Coeff p)‖ ≤ ‖E‖
    apply lp.norm_mono (zero_lt_one.trans hp1).ne'
    intro m
    change ‖(s n ψ : Coeff p) m‖ ≤ ‖E m‖
    by_cases hmn : m = n
    · subst m
      rw [show (s n ψ : Coeff p) n = 0 from (s n ψ).property,norm_zero]
      exact norm_nonneg _
    · have hm : (s n ψ : Coeff p) m = t m+(sourcePeriodicGapDisplacement hp hp1 ψ m)^2*α m := by
        have hf := hfactor m hmn
        simp only [displacedRoots] at hf
        simp only [t,sourcePeriodicMidpointDisplacement_apply]
        linear_combination hf
      have hgm : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ G :=
        (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ m).trans (hgap ψ hψ.2).1
      rw [hm,hE]
      exact (norm_add_le _ _).trans (by
        rw [norm_mul,norm_pow]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ m)) hgm 2) (norm_nonneg (α m))))
  have hEnorm : ‖E‖ ≤ D+G^2*L := by
    calc
      ‖E‖ ≤ ‖Coeff.magnitude t‖+‖((G^2 : ℝ) : ℂ) • Coeff.magnitude α‖ := norm_add_le _ _
      _ = ‖t‖+G^2*‖α‖ := by
        rw [norm_smul,Coeff.norm_magnitude,Coeff.norm_magnitude,Complex.norm_real,
          Real.norm_of_nonneg (sq_nonneg G)]
      _ ≤ D+G^2*L := add_le_add (hmid ψ hψ.1.2).1
        (mul_le_mul_of_nonneg_left hα (sq_nonneg G))
  exact (hnorm.trans hEnorm).trans (by linarith)

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
