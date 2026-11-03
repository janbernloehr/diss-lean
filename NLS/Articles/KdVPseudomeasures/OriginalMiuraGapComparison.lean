import NLS.Articles.KdVPseudomeasures.OriginalHillLabels
import NLS.KdV.HminusOneMiuraHighPairs
import NLS.SequenceSpaces.BoundedScalarProducts

/-!
# Exact original physical Hill/Dirac high-gap comparison

The entire original real H-minus-one domain is retained. The high index is
the same on both sides, and the actual algebraic multiplicities include
collapsed gaps. The energy translation cancels in the gap identity.
-/
noncomputable section
open Set Complex Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- Every sufficiently high ORIGINAL physical Hill gap is the product of
the actual Dirac gap and the sum of its endpoints at the same index. -/
theorem exists_originalCanonicalGapValues_miura_factorization
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      originalCanonicalGapValues q n =
        (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)*
          (hillMiuraDiracRight u.val n+hillMiuraDiracLeft u.val n) ∧
      Real.pi*(n:ℝ) ≤ (hillMiuraDiracLeft u.val n).re+(hillMiuraDiracRight u.val n).re := by
  obtain ⟨N,hN,hlabels⟩ := exists_hillHminusLabels_squared_miuraDirac
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) u c himage
  refine ⟨N,hN,fun n hn => ?_⟩
  obtain ⟨hl,hr,hsum⟩ := hlabels n hn
  change originalHillLabels q (2*n-1) = _ at hl
  change originalHillLabels q (2*n) = _ at hr
  refine ⟨?_,hsum⟩
  have hn0 : (n:ℤ) ≠ 0 := by have := hN.trans hn; omega
  have hreal := hillMiuraDiracPair_real u n
  have ha : (((hillMiuraDiracLeft u.val n).re : ℝ) : ℂ) = hillMiuraDiracLeft u.val n := by
    apply Complex.ext <;> simp [hreal.1]
  have hb : (((hillMiuraDiracRight u.val n).re : ℝ) : ℂ) = hillMiuraDiracRight u.val n := by
    apply Complex.ext <;> simp [hreal.2]
  rw [originalCanonicalGapValues,if_neg hn0,show (n:ℤ).natAbs = n by simp,hl,hr]
  push_cast
  rw [ha,hb]
  ring

/-- One cutoff precedes every real Sobolev weight. The original Hill gaps
control the actual positive-index Dirac gaps with exactly one extra order.
No endpoint membership of the potential is assumed. -/
theorem exists_originalCanonicalGapValues_miura_weighted_bound
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ s : ℝ,
      ‖(Weight.sobolev (s+1) (n:ℤ):ℂ)*
        (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)‖ ≤
        (2/Real.pi)*‖(Weight.sobolev s (n:ℤ):ℂ)*originalCanonicalGapValues q n‖ := by
  obtain ⟨N,hN,hgap⟩ := exists_originalCanonicalGapValues_miura_factorization q u c himage
  refine ⟨N,hN,fun n hn s => ?_⟩
  obtain ⟨he,hsum⟩ := hgap n hn
  let d := hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n
  have hsumNorm : Real.pi*(n:ℝ) ≤ ‖hillMiuraDiracRight u.val n+hillMiuraDiracLeft u.val n‖ := by
    have hh := Complex.re_le_norm (hillMiuraDiracRight u.val n+hillMiuraDiracLeft u.val n)
    simp only [add_re] at hh
    linarith
  have hbase : Real.pi*(n:ℝ)*‖d‖ ≤ ‖originalCanonicalGapValues q n‖ := by
    rw [he,norm_mul]
    simpa only [d,mul_comm] using mul_le_mul_of_nonneg_right hsumNorm (norm_nonneg d)
  have hgain : (1+(n:ℝ))*‖d‖ ≤ (2/Real.pi)*‖originalCanonicalGapValues q n‖ := by
    apply (mul_le_mul_iff_of_pos_left Real.pi_pos).mp
    have hc : Real.pi*((2/Real.pi)*‖originalCanonicalGapValues q n‖) =
        2*‖originalCanonicalGapValues q n‖ := by field_simp
    rw [hc]
    have hnr : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hh := mul_nonneg (sub_nonneg.mpr hnr) (norm_nonneg d)
    have hh' := mul_nonneg Real.pi_pos.le hh
    nlinarith
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev (s+1)).positive _),abs_of_pos ((Weight.sobolev s).positive _),
    Weight.sobolev_add,Weight.sobolev_apply (s := 1)]
  simp only [Real.rpow_one,Int.cast_natCast,abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]
  have hw := mul_le_mul_of_nonneg_left hgain ((Weight.sobolev s).positive (n:ℤ)).le
  simpa only [d,mul_assoc,mul_left_comm,mul_comm] using hw

/-- The norm identity holds on both signed tails at the unsigned physical
Hill index. No unproved symmetry of the Dirac labels is used. -/
theorem exists_originalCanonicalGapValues_miura_signed_norm
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ k : ℤ, N ≤ k.natAbs →
      ‖originalCanonicalGapValues q k‖ =
        ‖hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k‖*
          ‖hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k‖ ∧
      Real.pi*(k.natAbs:ℝ) ≤ ‖hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k‖ := by
  obtain ⟨M,r,hlabels⟩ := hillHminusLabels_spec (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q)
  obtain ⟨K,hK,hlocal⟩ := exists_miuraDirac_signed_square_localization u c r hlabels.radius_pos
  refine ⟨max M K,hK.trans (le_max_right _ _),fun k hk => ?_⟩
  have hkM : M ≤ k.natAbs := (le_max_left _ _).trans hk
  have hkK : K ≤ k.natAbs := (le_max_right _ _).trans hk
  obtain ⟨p,hl,hr⟩ := hlabels.high_pair k.natAbs hkM
  change originalHillLabels q (2*k.natAbs-1) = _ at hl
  change originalHillLabels q (2*k.natAbs) = _ at hr
  obtain ⟨hleftNe,hsum,hleft,hright⟩ := hlocal k hkK
  have hsumNe : hillMiuraDiracLeft u.val k+hillMiuraDiracRight u.val k ≠ 0 := by
    intro he
    have hz : hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k = 0 := by simpa only [add_comm] using he
    rw [hz,norm_zero] at hsum
    have hp : 0 < Real.pi*(k.natAbs:ℝ) := mul_pos Real.pi_pos (by have := hK.trans hkK; positivity)
    linarith
  have he := hillHminus_pair_gap_norm_eq_miuraDirac (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) u c himage k
    ⟨k.natAbs,by have := hlabels.cutoff_ge_two; omega⟩ r p hleftNe hsumNe
    (ball_subset_closedBall hleft) (ball_subset_closedBall hright)
  refine ⟨?_,hsum⟩
  have hk0 : k ≠ 0 := by intro hz; subst k; have := hK.trans hkK; simp at this
  rw [originalCanonicalGapValues,if_neg hk0,hl,hr]
  exact he

/-- The one-order weighted gap gain holds on BOTH tails, with one cutoff
chosen before the Sobolev order or the summability exponent. -/
theorem exists_originalCanonicalGapValues_miura_signed_weighted_bound
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ k : ℤ, N ≤ k.natAbs → ∀ s : ℝ,
      ‖(Weight.sobolev (s+1) k:ℂ)*(hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k)‖ ≤
        (2/Real.pi)*‖(Weight.sobolev s k:ℂ)*originalCanonicalGapValues q k‖ := by
  obtain ⟨N,hN,hgap⟩ := exists_originalCanonicalGapValues_miura_signed_norm q u c himage
  refine ⟨N,hN,fun k hk s => ?_⟩
  obtain ⟨he,hsum⟩ := hgap k hk
  let d := hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k
  have hbase : Real.pi*(k.natAbs:ℝ)*‖d‖ ≤ ‖originalCanonicalGapValues q k‖ := by
    rw [he]
    simpa only [d,mul_comm] using mul_le_mul_of_nonneg_right hsum (norm_nonneg d)
  have hgain : (1+(k.natAbs:ℝ))*‖d‖ ≤ (2/Real.pi)*‖originalCanonicalGapValues q k‖ := by
    apply (mul_le_mul_iff_of_pos_left Real.pi_pos).mp
    have hc : Real.pi*((2/Real.pi)*‖originalCanonicalGapValues q k‖) =
        2*‖originalCanonicalGapValues q k‖ := by field_simp
    rw [hc]
    have hkr : (1:ℝ) ≤ k.natAbs := by exact_mod_cast (show 1 ≤ k.natAbs by omega)
    have hh := mul_nonneg (sub_nonneg.mpr hkr) (norm_nonneg d)
    have hh' := mul_nonneg Real.pi_pos.le hh
    nlinarith
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev (s+1)).positive _),abs_of_pos ((Weight.sobolev s).positive _),
    Weight.sobolev_add,Weight.sobolev_apply (s := 1)]
  simp only [Real.rpow_one,Nat.cast_natAbs,Int.cast_abs] at hgain ⊢
  have hw := mul_le_mul_of_nonneg_left hgain ((Weight.sobolev s).positive k).le
  simpa only [d,mul_assoc,mul_left_comm,mul_comm] using hw

/-- Original physical Hill gap regularity supplies one additional order
on the entire actual Dirac gap sequence, at every Banach exponent including
infinity. The finite central part is handled by finite modification. -/
theorem memlp_miuraDiracGap_of_original_gap
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c s : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hgap : Memℓp (fun k : ℤ => (Weight.sobolev s k:ℂ)*originalCanonicalGapValues q k) p) :
    Memℓp (fun k : ℤ => (Weight.sobolev (s+1) k:ℂ)*
      (hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k)) p := by
  obtain ⟨N,_,hbound⟩ := exists_originalCanonicalGapValues_miura_signed_weighted_bound q u c himage
  let D := fun k : ℤ => (Weight.sobolev (s+1) k:ℂ)*
    (hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k)
  have hC : 0 < 2/Real.pi := div_pos (by norm_num) Real.pi_pos
  have hm : Memℓp (fun k : ℤ => if N ≤ k.natAbs then D k else 0) p := by
    apply (hgap.const_mul ((2/Real.pi:ℝ):ℂ)).mono'
    intro k
    by_cases hk : N ≤ k.natAbs
    · rw [if_pos hk]
      have hc : ‖((2/Real.pi:ℝ):ℂ)*((Weight.sobolev s k:ℂ)*originalCanonicalGapValues q k)‖ =
          (2/Real.pi)*‖(Weight.sobolev s k:ℂ)*originalCanonicalGapValues q k‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
      exact (hbound k hk s).trans_eq hc.symm
    · rw [if_neg hk,norm_zero]
      exact norm_nonneg _
  apply NLS.memlp_vector_of_eq_outside_finset hm (Finset.Icc (-(N:ℤ)) N)
  intro k hk
  have hlarge : N ≤ k.natAbs := by
    simp only [Finset.mem_Icc,not_and_or] at hk
    omega
  simp only [if_pos hlarge,D]

end NLS.Articles.KdVPseudomeasures
