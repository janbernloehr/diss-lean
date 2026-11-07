import NLS.KdV.HillNativeRealSignedMap
import NLS.KdV.HillDirichletSpectralLocalFlow
import NLS.KdV.HillHminusOneCanonicalQuotients
import NLS.SequenceSpaces.RealMeanZeroHalfFourierEquiv

/-! Actual high gaps are bounded by the inverse free half-Fourier transform
of the SAME actual native output. The cutoff depends on the source; no
global properness estimate or control of varying sources is asserted. -/
noncomputable section
open Set Complex
namespace NLS.KdV

/-- The exact8*pi*n normalization gives a quadratic high-gap lower action
bound whenever the filled normalized ratio differs from1 by at most1/2. -/
theorem hillHminus_gapSquare_norm_le_action (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalRatioDomain) (n : ℕ+)
    (hR : ‖hillHminusCanonicalActionRatio n q-1‖ ≤ (1/2:ℝ)) :
    ‖hillHminusCanonicalGapSquare n q‖ ≤
      16*Real.pi*(n:ℕ)*‖hillHminusCanonicalAction n q‖ := by
  have he := norm_hillHminusCanonicalAction_error_le n q hq (1/2) hR
  have ht := norm_sub_le ((8*((Real.pi:ℂ)*(n:ℕ)))*hillHminusCanonicalAction n q)
    ((8*((Real.pi:ℂ)*(n:ℕ)))*hillHminusCanonicalAction n q-hillHminusCanonicalGapSquare n q)
  rw [sub_sub_cancel] at ht
  have hn : ‖(8*((Real.pi:ℂ)*(n:ℕ)))*hillHminusCanonicalAction n q‖=
      8*Real.pi*(n:ℕ)*‖hillHminusCanonicalAction n q‖ := by
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_natCast]
    ring
  rw [hn] at ht
  linarith

/-- At every actual physical source, BOTH signed tails of the actual
canonical gaps are dominated by the SAME inverse-free-Fourier output.
Every finite low/central cluster is retained for later finite-modification arguments. -/
theorem exists_hillReal_native_inverse_gap_tail (q : HillRealMeanZeroSource) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ k : ℤ, N ≤ k.natAbs →
      ‖((hillHminusLabels (hillRealMeanZeroInclusion q) q.property (2*k.natAbs)-
          hillHminusLabels (hillRealMeanZeroInclusion q) q.property (2*k.natAbs-1):ℝ):ℂ)‖ ≤
        3*‖((WeightedCoeff.realMeanZeroHalfFourierEquiv 2).symm
          (hillRealSignedMap q)).val.val.val k‖ := by
  let Q := hillRealMeanZeroInclusion q
  have hQ : Q ∈ hillHminusCanonicalRatioDomain := real_mem_hillHminusCanonicalRatioDomain Q q.property
  obtain ⟨N,U,hN,_,hqU,_,hhigh⟩ := exists_hillHminusCanonicalActionRatio_uniform_high Q hQ (1/2) (by norm_num)
  let a := (WeightedCoeff.realMeanZeroHalfFourierEquiv 2).symm (hillRealSignedMap q)
  have hp (n : ℕ+) (hn : N ≤ (n:ℕ)) :
      ‖((hillHminusLabels Q q.property (2*(n:ℕ))-
          hillHminusLabels Q q.property (2*(n:ℕ)-1):ℝ):ℂ)‖ ≤ 3*‖a.val.val.val (n:ℤ)‖ := by
    let g : ℂ := ((hillHminusLabels Q q.property (2*(n:ℕ))-
      hillHminusLabels Q q.property (2*(n:ℕ)-1):ℝ):ℂ)
    let z := hillRealSignedMap q
    have hs : ‖g‖^2 ≤ 16*Real.pi*(n:ℕ)*‖hillHminusCanonicalAction n Q‖ := by
      have h := hillHminus_gapSquare_norm_le_action Q hQ n (hhigh n hn Q hqU)
      rw [hillHminusCanonicalGapSquare_eq_real Q q.property n,norm_pow] at h
      simpa only [g,Complex.ofReal_sub] using h
    have hI : ‖hillHminusCanonicalAction n Q‖=‖z.val.val.val (n:ℤ)‖^2 := by
      have he := hillHminusNativeComplexMap_action_identity Q
        (real_mem_hillHminusActionAngleNativeDomain Q q.property) n
      have hc (k : ℤ) : z.val.val.val k=(hillHminusNativeComplexMap Q).val k := by
        rw [hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]
        rfl
      rw [← hc,← hc,z.property] at he
      rw [← he,norm_mul,Complex.norm_conj,pow_two]
    have ha : ‖a.val.val.val (n:ℤ)‖^2=(2*Real.pi*(n:ℕ))*‖z.val.val.val (n:ℤ)‖^2 := by
      dsimp only [a]
      rw [WeightedCoeff.realMeanZeroHalfFourierEquiv_symm_apply,
        WeightedCoeff.halfFourierInverseSymbol,norm_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_pow,
        mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
      rw [Int.cast_natCast,abs_of_nonneg (by positivity),max_eq_right (by exact_mod_cast (show 1 ≤ (n:ℕ) by omega))]
    rw [hI] at hs
    change ‖g‖ ≤ 3*‖a.val.val.val (n:ℤ)‖
    nlinarith [sq_nonneg ‖a.val.val.val (n:ℤ)‖,norm_nonneg g,norm_nonneg (a.val.val.val (n:ℤ))]
  refine ⟨N,hN,fun k hk => ?_⟩
  let n : ℕ+ := ⟨k.natAbs,by omega⟩
  have h := hp n hk
  change ‖((hillHminusLabels Q q.property (2*(n:ℕ))-
      hillHminusLabels Q q.property (2*(n:ℕ)-1):ℝ):ℂ)‖ ≤ 3*‖a.val.val.val k‖
  by_cases hkp : 0 ≤ k
  · have hn : (n:ℤ)=k := by
      change (k.natAbs:ℤ)=k
      rw [Int.natCast_natAbs,abs_of_nonneg hkp]
    rw [hn] at h
    exact h
  · have hn : -(n:ℤ)=k := by
      change -(k.natAbs:ℤ)=k
      rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hkp),neg_neg]
    have he : ‖a.val.val.val (n:ℤ)‖=‖a.val.val.val k‖ := by
      rw [← hn,a.property,Complex.norm_conj]
    rw [he] at h
    exact h

end NLS.KdV
