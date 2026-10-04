import NLS.ZakharovShabat.SourceMidpointProductSharedMajorant
import NLS.ZakharovShabat.SourcePsiRefinedQuotientTail
import NLS.SequenceSpaces.QuasiHolderProduct

/-! # A shared quotient-error sequence for all actual psi rows

The squared gaps are the fixed weights in the shared midpoint-product
estimate. The gap correction is a reciprocal-square sequence independent
of the deleted index. Their sum therefore bounds every actual filled
quotient at once, with one source neighborhood preceding the exponent.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One refined sequence controls the quotient tails simultaneously for
all deleted indices. In particular, its diagonal entries have the same
sequence bound; the majorant is chosen before the deleted index. -/
theorem SourcePsiSquaredGapComplexExtension.exists_local_shared_quotient_tail_majorant
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ T : Set (CoeffPair p),
      IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧ ∃ K : ℕ, N < K ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∃ B : Coeff r, ‖B‖ ≤ M ∧
            ∀ n k : ℤ, K ≤ k.natAbs → ∀ z ∈ sourceIsolatingDisc hp hp1 φ.val N ε k,
              ‖sourceSingleRootQuotientJointProduct hp hp1 k
                (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖B k‖ := by
  obtain ⟨Ta,hTa,hφa,haV,A,hA,hoffset⟩ := hs.locally_uniform_squared_gap_offsets φ.val hφ
  obtain ⟨Tb,hTb,hφb,_,L,hL,hbeta⟩ := hs.locally_uniform_refined_filled_offsets φ.val hφ
  obtain ⟨N,ε,hε,_,Tg,hTg,_,hφg,C,_,H,hC,_,_,K,hNK,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data hp hp1 φ.val φ.property
  refine ⟨N,ε,hε,(Ta ∩ Tb) ∩ Tg,(hTa.inter hTb).inter hTg,⟨⟨hφa,hφb⟩,hφg⟩,
    fun _ h => haV h.1.1,K,hNK,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  have hC0 : 0 ≤ C := by linarith
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (div_pos (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp) (by norm_num))
  have hpp : ENNReal.ofReal (p.toReal/2) ≤ p := by
    calc
      ENNReal.ofReal (p.toReal/2) ≤ ENNReal.ofReal p.toReal :=
        ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
      _ = p := ENNReal.ofReal_toReal hp
  let κ := ‖Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖
  have hκ : 0 ≤ κ := lp.norm_nonneg' _
  let Q := Real.exp (C*L*κ)*C^2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hhalfReal : (1/2:ℝ) < p.toReal/2 := by
    have h := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
    simp only [ENNReal.toReal_one] at h
    linarith
  let J := ‖squaredReciprocalKernel (min 1 (p.toReal/2)) (lt_min (by norm_num) hhalfReal)‖
  let M := sourceSharedMidpointMajorantBound hp hr1 C A (H^2)+Q*(H^2*J)
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro ψ hψ
  obtain ⟨_,hgap,hsep,hsmall,hdom⟩ := hdata ψ hψ.2
  let g : Coeff r := ⟨fun j => sourcePeriodicSquaredGapCoeff hp hp1 ψ j,
    (lp.memℓp (sourcePeriodicSquaredGapCoeff hp hp1 ψ)).of_exponent_ge hpr⟩
  have hg : ‖g‖ ≤ H^2 :=
    (Coeff.norm_quasiExponentInclusion_le hhalf (zero_lt_one.trans hr1) hr hpr _).trans hgap
  obtain ⟨Bm,hBm,hmid⟩ := exists_sourceMidpointProduct_sharedMajorant hp hp1 hr hr1
    φ.val ψ N ε C A (H^2) hC hA.le (sq_nonneg _) hsep g hg
  obtain ⟨S,hS,hSnorm⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  let Sr : Coeff r := ⟨fun k => S k,(lp.memℓp S).of_exponent_ge hpr⟩
  have hSr : ‖Sr‖ ≤ H^2*J :=
    (Coeff.norm_quasiExponentInclusion_le hhalf (zero_lt_one.trans hr1) hr hpr S).trans
      (hSnorm.trans (mul_le_mul_of_nonneg_right hgap (lp.norm_nonneg' _)))
  let B := Coeff.magnitude Bm+(Q:ℂ) • Coeff.magnitude Sr
  have hBpoint (k : ℤ) : ‖B k‖ = ‖Bm k‖+Q*‖S k‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      Coeff.magnitude_apply,← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  refine ⟨B,?_,?_⟩
  · apply le_trans _ (le_max_right 0 M)
    calc
      ‖B‖ ≤ ‖Coeff.magnitude Bm‖+‖(Q:ℂ) • Coeff.magnitude Sr‖ := norm_add_le _ _
      _ = ‖Bm‖+Q*‖Sr‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hQ]; simp
      _ ≤ M := add_le_add hBm (mul_le_mul_of_nonneg_left hSr hQ)
  intro n k hk z hz
  obtain ⟨α,hαn,hα,hαnorm⟩ := hoffset ψ hψ.1.1 n
  obtain ⟨β,hβ,hβnorm⟩ := hbeta ψ hψ.1.2 n p hp hp1 hpp
  let a := sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)
  have hβfactor (j : ℤ) : β j = g j*α j := by
    rw [← hβ j]
    by_cases hj : j = n
    · subst j
      simp only [displacedRoots_sourcePsiFillDeletedRoot_same,sub_self,hαn,mul_zero]
    · rw [displacedRoots_sourcePsiFillDeletedRoot_other n j hj,hα j hj]
      simp only [g,sourcePeriodicSquaredGapCoeff_apply]
      ring
  have hmidpoint := hmid α hαnorm β hβfactor k z hz
  have hcorr := norm_sourceSingleRootQuotientJointProduct_sub_midpoint_le_of_small_row hp hp1 hp
    φ.val ψ a β hβ N ε C hC hsep k z hz (hdom a k hk z hz) (hsmall k hk)
  have hexp : Real.exp (C*‖β‖*κ)*C^2 ≤ Q := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβnorm hC0) hκ]
  have hSk : ‖S k‖ = ∑' j, sourceSquaredGapReciprocalTerm hp hp1 ψ k j := by
    rw [(hS k).2,Complex.norm_real,Real.norm_of_nonneg]
    exact tsum_nonneg (fun j => by unfold sourceSquaredGapReciprocalTerm; split_ifs <;> positivity)
  have hcorr' : ‖sourceSingleRootQuotientJointProduct hp hp1 k (z,(a,ψ))-
      (sourceMidpointProductRow hp hp1 ψ β k z+1)‖ ≤ Q*‖S k‖ := by
    rw [hSk]
    exact hcorr.trans (mul_le_mul_of_nonneg_right hexp (by rw [← hSk]; exact norm_nonneg _))
  rw [hBpoint]
  calc
    _ = ‖(sourceSingleRootQuotientJointProduct hp hp1 k (z,(a,ψ))-
        (sourceMidpointProductRow hp hp1 ψ β k z+1))+sourceMidpointProductRow hp hp1 ψ β k z‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (by simpa only [add_comm] using add_le_add hcorr' hmidpoint)

end NLS.ZakharovShabat
