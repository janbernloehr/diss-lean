import NLS.ZakharovShabat.SourceSquaredGapNorm
import NLS.ZakharovShabat.DeletedPeriodicFree

/-!
# Full original sequence bounds for Lemma 10.2

The actual squared gap lies in the literal half-exponent coefficient space,
including below exponent one. Its quasi-norm and every truncated tail
quasi-norm equal the square of the corresponding unsquared-gap norm.
One original source neighborhood controls both midpoint and squared-gap
sequences, including their entire central blocks.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual squared-gap sequence at the literal exponent p/2. -/
def sourcePeriodicSquaredGapSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) : Coeff (p/2) :=
  ⟨fun n => (canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)^2,
    memℓp_sourcePeriodicSquaredGap hp hp1 φ⟩

/-- Every signed coordinate is the square of the actual gap. -/
@[simp] theorem sourcePeriodicSquaredGapSequence_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    sourcePeriodicSquaredGapSequence hp hp1 φ n = (sourcePeriodicGapDisplacement hp hp1 φ n)^2 := by
  simp only [sourcePeriodicSquaredGapSequence,sourcePeriodicGapDisplacement_apply]

/-- Squaring a sequence and halving its exponent squares its quasi-norm. -/
theorem lp_norm_eq_sq_of_apply_eq_sq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (g : Coeff p) (h : Coeff (p/2)) (hh : ∀ n : ℤ, h n = (g n)^2) : ‖h‖ = ‖g‖^2 := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hq : (p/2).toReal = p.toReal/2 := by simp [ENNReal.toReal_div]
  have hqr : 0 < (p/2).toReal := by rw [hq]; positivity
  apply (Real.rpow_left_inj (lp.norm_nonneg' h) (sq_nonneg _) hqr.ne').mp
  calc
    ‖h‖^(p/2).toReal = ∑' n : ℤ, ‖h n‖^(p/2).toReal := lp.norm_rpow_eq_tsum hqr h
    _ = ∑' n : ℤ, ‖g n‖^p.toReal := by
      apply tsum_congr
      intro n
      rw [hh n,hq,norm_sq_rpow_half]
    _ = ‖g‖^p.toReal := (lp.norm_rpow_eq_tsum hpr g).symm
    _ = (‖g‖^2)^(p/2).toReal := by
      rw [hq,← Real.rpow_natCast ‖g‖ 2,← Real.rpow_mul (norm_nonneg g)]
      congr 1
      ring

/-- The full squared-gap quasi-norm is exactly the squared gap norm. -/
theorem norm_sourcePeriodicSquaredGapSequence (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ‖sourcePeriodicSquaredGapSequence hp hp1 φ‖ = ‖sourcePeriodicGapDisplacement hp hp1 φ‖^2 :=
  lp_norm_eq_sq_of_apply_eq_sq hp hp1 _ _ (sourcePeriodicSquaredGapSequence_apply hp hp1 φ)

/-- The same exact identity holds after removing any finite set of indices. -/
theorem norm_sourcePeriodicSquaredGapSequence_tail (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (s : Finset ℤ) :
    ‖sourcePeriodicSquaredGapSequence hp hp1 φ-Coeff.truncate s (sourcePeriodicSquaredGapSequence hp hp1 φ)‖ =
      ‖sourcePeriodicGapDisplacement hp hp1 φ-Coeff.truncate s (sourcePeriodicGapDisplacement hp hp1 φ)‖^2 := by
  apply lp_norm_eq_sq_of_apply_eq_sq hp hp1
  intro n
  by_cases hn : n ∈ s <;>
    simp only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,hn,ite_true,ite_false,
      sub_self,sub_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sourcePeriodicSquaredGapSequence_apply]

/-- The entire squared-gap sequence vanishes at the free source. -/
@[simp] theorem sourcePeriodicSquaredGapSequence_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourcePeriodicSquaredGapSequence hp hp1 (0 : CoeffPair p) = 0 := by
  ext n
  simp only [sourcePeriodicSquaredGapSequence_apply,sourcePeriodicGapDisplacement_apply,map_zero,
    canonicalPeriodicGap_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),lp.coeFn_zero,Pi.zero_apply]

/-- One neighborhood and cutoff bound both full sequences and all sufficiently distant tails. -/
theorem exists_uniform_sourceLemma10_2_sequences (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {η : ℝ} (hη : 0 < η) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∃ N : ℕ, 2 ≤ N ∧ ∃ R : ℝ, 0 ≤ R ∧
      ∀ ψ ∈ U, ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R ∧
        ‖sourcePeriodicSquaredGapSequence hp hp1 ψ‖ ≤ R^2 ∧
        ∀ M : ℕ, N ≤ M →
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ-
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (sourcePeriodicMidpointDisplacement hp hp1 ψ)‖ ≤ η ∧
          ‖sourcePeriodicSquaredGapSequence hp hp1 ψ-
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (sourcePeriodicSquaredGapSequence hp hp1 ψ)‖ ≤ η^2 := by
  obtain ⟨Nm,hNm,Um,hUm,hφm,Rm,hRm,hm⟩ := exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ hη
  obtain ⟨Ng,hNg,Ug,hUg,hφg,Rg,hRg,hg⟩ := exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ hη
  refine ⟨Um ∩ Ug,hUm.inter hUg,⟨hφm,hφg⟩,max Nm Ng,hNm.trans (le_max_left _ _),
    max Rm Rg,hRm.trans (le_max_left _ _),?_⟩
  intro ψ hψ
  obtain ⟨hmb,hmt⟩ := hm ψ hψ.1
  obtain ⟨hgb,hgt⟩ := hg ψ hψ.2
  refine ⟨hmb.trans (le_max_left _ _),?_,?_⟩
  · rw [norm_sourcePeriodicSquaredGapSequence]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgb.trans (le_max_right _ _)) 2
  · intro M hM
    refine ⟨hmt M ((le_max_left _ _).trans hM),?_⟩
    rw [norm_sourcePeriodicSquaredGapSequence_tail]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgt M ((le_max_right _ _).trans hM)) 2

end NLS.ZakharovShabat
