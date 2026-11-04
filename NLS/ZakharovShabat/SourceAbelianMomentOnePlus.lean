import NLS.ZakharovShabat.SourceAbelianMomentCriticalBound
import NLS.ZakharovShabat.SourcePsiCriticalProductOnePlus
import NLS.ZakharovShabat.SourceAbelianMomentCubicCoefficients
import NLS.SequenceSpaces.ReciprocalBootstrapStep

/-! # The sharper off-diagonal second-moment rows

Critical cancellation replaces the midpoint coefficient by the actual
psi-critical root difference. Proposition 4.1 and the absolute reciprocal
rows then give every finite exponent above one. The existing finite-head
cubic coefficient bound retains the same scalar coefficients at all gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W W₀ V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {A : SourceAbelianMomentAtlas hp hp1 W s}

/-- Article Lemma 5.3's sharper off-diagonal coefficient bound near a real source.
The common source neighborhood precedes the exponent, and every row is actual. -/
theorem SourceAbelianMomentErrorDomain.exists_local_offDiagonal_onePlus_coefficients
    (D : SourceAbelianMomentErrorDomain A) (H : SourceLemma12_11Data hp hp1 W₀ V s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s) (hp2 : 2 < p)
    (φ : realTypeSourceSubmodule p) (hφV : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ D.domain ∩ V ∧
      ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
        ∀ ψ ∈ T, ∀ n : ℤ, ∃ a : Coeff q,
          (∀ k, a k = sourceSecondMomentCubicCoefficient A n ψ k) ∧ a n = 0 ∧ ‖a‖ ≤ M ∧
          ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ =
            (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k := by
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  obtain ⟨Ta,hTa,hφa,_,harows⟩ := H.exists_local_critical_gapNormalized_onePlus hp2 φ₀ hφV
  obtain ⟨Te,hTe,hφe,_,Ke,herows⟩ := H.exists_local_critical_product_onePlus_majorants hp2 φ₀ hφV
  obtain ⟨Tz,hTz,hφz,_,Kz,hzrows⟩ := H.exists_local_critical_filled_quotient_small_tail φ₀ hφV 1 (by norm_num)
  obtain ⟨Tb,hTb,hφb,B,hB,hb⟩ := exists_local_uniform_sourceCriticalPoint_gap_distance_bound hp hp1 φ.val φ.property
  obtain ⟨Ts,hTs,hφs,Ks,hsep⟩ := exists_local_sourceCritical_tail_lattice_separation hp hp1 φ₀
  obtain ⟨Tl,hTl,hφl,_,hlrows⟩ := A.exists_local_refined_square_gap_majorants φ
  obtain ⟨To,hTo,hφo,hToD,horows⟩ := D.exists_local_offDiagonal_secondMoment_coefficients hs φ hφV
  obtain ⟨_,_,Tg,hTg,hφg,G,hG,hg⟩ := exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ.val (by norm_num : (0:ℝ)<1)
  obtain ⟨Wc,_,_,hcauchy⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hCφ⟩ := hcauchy φ
  have hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hCφ]
    exact mem_ball_self C.discs.sourceRadius_pos
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp]
    exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
  obtain ⟨Sl,hSl,hls⟩ := hlrows p hp hp1 hhalf
  obtain ⟨Mo,hMo,hos⟩ := horows p hp hp1 hhalf
  have hpc1 : 1 < p.conjExponent := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hpc : p.conjExponent ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hpc1.le⟩
  obtain ⟨Ap,hAp,hars⟩ := harows p.conjExponent hpc hpc1
  let L := Sl+1/4
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let K := max Ke (max Kz Ks)
  let T := (((Ta ∩ Te) ∩ (Tz ∩ Tb)) ∩ ((Ts ∩ Tl) ∩ (To ∩ Tg))) ∩
    ball C.discs.source.val C.discs.sourceRadius
  refine ⟨T,(((hTa.inter hTe).inter (hTz.inter hTb)).inter
    ((hTs.inter hTl).inter (hTo.inter hTg))).inter isOpen_ball,
    ⟨⟨⟨⟨hφa,hφe⟩,hφz,hφb⟩,⟨hφs,hφl⟩,hφo,hφg⟩,hφC⟩,
    fun _ h => hToD h.1.2.2.1,?_⟩
  intro q hq hq1
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  obtain ⟨Aq,hAq,haq⟩ := harows q hq hq1
  obtain ⟨Eq,hEq,heq⟩ := herows q hq hq1
  let J := ‖NLS.Fourier.hilbertKernelCoeffs hpc1‖
  have hJ : 0 ≤ J := norm_nonneg _
  let R := 4*L*(2*Aq+B*Eq+((Ap+B)*2/Real.pi)*(G*J))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  refine ⟨(Finset.Icc (-(K:ℤ)) K).card*Mo+R,by positivity,?_⟩
  intro ψ hψ n
  rcases hψ with ⟨⟨⟨⟨hψa,hψe⟩,hψz,hψb⟩,⟨hψs,hψl⟩,hψo,hψg⟩,hψC⟩
  obtain ⟨α,hα,hαn,hαval,hαroots⟩ := haq ψ hψa n
  obtain ⟨αp,hαp,_,hαpval,_⟩ := hars ψ hψa n
  obtain ⟨E,hE,herror⟩ := heq ψ hψe n
  obtain ⟨e,hen,hSquare⟩ := hls ψ hψl
  obtain ⟨a₀,ha₀,han₀,hn₀,hformula₀⟩ := hos ψ hψo n
  let F₁ := Coeff.quasiHolderProduct (r := 1) (sourcePeriodicGapDisplacement hp hp1 ψ)
    (Coeff.shift n (NLS.Fourier.hilbertKernelCoeffs hpc1))
  let F : Coeff q := Coeff.exponentInclusion hq1.le F₁
  have hFnorm : ‖F‖ ≤ G*J := by
    apply (Coeff.norm_exponentInclusion_le hq1.le F₁).trans
    have hp0 := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
    have hpc0 := ENNReal.toReal_pos (zero_lt_one.trans hpc1).ne' hpc
    have hn := Coeff.norm_quasiHolderProduct_le (r := 1) hp0 hpc0 (sourcePeriodicGapDisplacement hp hp1 ψ)
      (Coeff.shift n (NLS.Fourier.hilbertKernelCoeffs hpc1))
    rw [Coeff.norm_shift] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right (hg ψ hψg).1 hJ)
  have hF (k : ℤ) : ‖F k‖ = ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖NLS.Fourier.hilbertKernel (n-k)‖ := by
    simp only [F,Coeff.exponentInclusion_apply,F₁,Coeff.quasiHolderProduct_apply,Coeff.shift_apply,
      NLS.Fourier.hilbertKernelCoeffs,norm_mul]
    congr 1
    rw [← neg_sub n k,NLS.Fourier.hilbertKernel_neg,norm_neg]
  let β := ((4*L:ℝ):ℂ) • (((2:ℝ):ℂ) • Coeff.magnitude α+(B:ℂ) • Coeff.magnitude E+
    (((Ap+B)*2/Real.pi:ℝ):ℂ) • Coeff.magnitude F)
  have hβ (k : ℤ) : ‖β k‖ = 4*L*(2*‖α k‖+B*‖E k‖+((Ap+B)*2/Real.pi)*‖F k‖) := by
    simp only [β,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,
      ← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hβnorm : ‖β‖ ≤ R := by
    have hsum : ‖((2:ℝ):ℂ) • Coeff.magnitude α+(B:ℂ) • Coeff.magnitude E+
        (((Ap+B)*2/Real.pi:ℝ):ℂ) • Coeff.magnitude F‖ ≤
        2*Aq+B*Eq+((Ap+B)*2/Real.pi)*(G*J) := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · apply (norm_add_le _ _).trans
        apply add_le_add
        · simpa only [norm_smul,Complex.norm_real,Real.norm_ofNat,Coeff.norm_magnitude] using mul_le_mul_of_nonneg_left hα (by norm_num : (0:ℝ)≤2)
        · simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hB.le,Coeff.norm_magnitude] using mul_le_mul_of_nonneg_left hE hB.le
      · simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ (Ap+B)*2/Real.pi),Coeff.norm_magnitude] using
          mul_le_mul_of_nonneg_left hFnorm (by positivity : 0 ≤ (Ap+B)*2/Real.pi)
    calc
      ‖β‖ = 4*L*‖((2:ℝ):ℂ) • Coeff.magnitude α+(B:ℂ) • Coeff.magnitude E+
          (((Ap+B)*2/Real.pi:ℝ):ℂ) • Coeff.magnitude F‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
      _ ≤ R := mul_le_mul_of_nonneg_left hsum (by positivity)
  have htail (k : ℤ) (hk : K ≤ k.natAbs) : ‖a₀ k‖ ≤ ‖β k‖ := by
    by_cases hkn : k=n
    · subst k
      rw [han₀,norm_zero]
      exact norm_nonneg _
    by_cases hγ : sourcePeriodicGapDisplacement hp hp1 ψ k = 0
    · rw [ha₀ k]
      simp only [sourceSecondMomentCubicCoefficient,if_neg hkn,hγ,zero_pow (by decide : (3:ℕ)≠0),div_zero,norm_zero]
      exact norm_nonneg _
    have hkz : Kz ≤ k.natAbs := by dsimp only [K] at hk; omega
    have hks : Ks ≤ k.natAbs := by dsimp only [K] at hk; omega
    have hke : Ke ≤ k.natAbs := by dsimp only [K] at hk; omega
    have hαpk : ‖α k‖ ≤ Ap := by
      rw [hαval k,← hαpval k]
      exact (lp.norm_apply_le_norm (zero_lt_one.trans hpc1).ne' αp k).trans hαp
    have hS (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
        ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*L := by
      have ht := norm_sub_le_norm_sub_add_norm_sub
        (sourceFullAbelianSquare hp hp1 W k (z,ψ)) (-sourceAngularSelectedPolynomial hp hp1 ψ k z) 0
      simp only [sub_zero,sub_neg_eq_add,norm_neg] at ht
      have hek := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' e k).trans hen
      have hpoly := norm_sourceAngularSelectedPolynomial_le_gap_sq hp hp1 ψ k z hz
      have hbnd := hSquare k z hz
      dsimp only [L]
      nlinarith [mul_le_mul_of_nonneg_left hek (sq_nonneg ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖)]
    have hZ (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
        ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z‖ ≤ 2 := by
      have hh := (hzrows ψ hψz n k hkz).2 z (ball_subset_closedBall ((hzrows ψ hψz n k hkz).1 hz))
      have ht := norm_sub_le_norm_sub_add_norm_sub (sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z) 1 0
      simp only [sub_zero,norm_one] at ht
      linarith
    have hden (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
        (Real.pi/2)*|((n-k:ℤ):ℝ)| ≤ ‖sourceCriticalRoot hp hp1 ψ n-z‖ :=
      hsep ψ hψs k hks n (Ne.symm hkn) z (ball_subset_closedBall ((hzrows ψ hψz n k hkz).1 hz))
    have hm := D.critical_cubic_index_bound C ψ (hToD hψo).1 hψC n k hkn (α k) (hαroots k hkn)
      L 2 B Ap ‖E k‖ hL hB.le hαpk hS hZ
      (fun z hz => by simpa only [sourceCriticalRoot,mul_comm] using hb ψ hψb k z hz)
      (herror k hke) hden
    have hm' : ‖((n-k:ℤ):ℂ)*A.moment n k 2 ψ‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*‖β k‖ := by
      simpa only [hβ,hF] using hm
    rw [ha₀ k]
    simp only [sourceSecondMomentCubicCoefficient,if_neg hkn,norm_div,norm_pow]
    exact (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hγ) 3)).mpr (by simpa only [mul_comm] using hm')
  obtain ⟨a,ha,hn⟩ := Coeff.exists_coeff_of_tail_majorant a₀ β K htail
  refine ⟨a,fun k => (ha k).trans (ha₀ k),by rw [ha n,han₀],hn.trans (add_le_add
    (mul_le_mul_of_nonneg_left hn₀ (Nat.cast_nonneg _)) hβnorm),?_⟩
  intro k hkn
  simpa only [ha k] using hformula₀ k hkn

end NLS.ZakharovShabat
