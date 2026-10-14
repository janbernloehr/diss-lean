import NLS.ZakharovShabat.SourceReverseCubicPotential

/-!
# The positive-component factor fails even after restoring the powers

Near the fixed constant potential (1,0), an arbitrarily small second mode
creates a negative remainder whose square is quadratic in its amplitude.
The printed positive-component budget is quartic after a positive cutoff
removes the background. Thus the norm-factor issue is independent of the
missing powers. The refutation is local and uniform in the frequency cutoff.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The printed negative-remainder budget at p=2, retaining the positive inner component. -/
def sourcePositiveComponentHilbertBudget (C : ℝ) (φ : CoeffPair 2) (N K : ℕ) : ℝ :=
  C * (‖φ.snd‖^4/(N : ℝ) + ‖sourceFourierTail K φ‖^4) * ‖φ.fst‖^2

/-- After removing the constant background, this budget is at most quartic. -/
theorem sourcePositiveComponentBudget_reverse_le (C : ℝ) (hC : 0 ≤ C) (n : ℤ)
    (t : ℝ) (ht : 0 ≤ t) (N K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K) :
    sourcePositiveComponentHilbertBudget C (sourceReverseCubicPotential n 1 t) N K ≤ 2*C*t^4 := by
  let φ := sourceReverseCubicPotential (p := 2) n 1 t
  have hc := sourceReverseCubicPotential_component_norms (p := 2) n 1 t
  have htail2 := sourceReverseCubicPotential_tail_norm_sq_le n t K hK
  simp only [Complex.norm_real,Real.norm_of_nonneg ht] at hc htail2
  have htail : ‖sourceFourierTail K φ‖ ≤ t := by nlinarith [norm_nonneg (sourceFourierTail K φ)]
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold sourcePositiveComponentHilbertBudget
  rw [hc.1,hc.2]
  simp only [norm_one,one_pow,mul_one]
  calc
    _ ≤ C * (t^4/(N : ℝ)+t^4) := by gcongr
    _ ≤ C * (t^4+t^4) := by
      gcongr
      exact div_le_self (by positivity) hNR
    _ = 2*C*t^4 := by ring

/-- A quadratic coefficient cannot be bounded by this quartic budget near the background. -/
private theorem exists_component_amplitude (C r d : ℝ) (hC : 0 ≤ C) (hr : 0 < r) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ t < r ∧ 2*C*t^4 < t^2/d^4 := by
  have hden : 0 < 2*C*d^4+1 := by positivity
  obtain ⟨t,ht,hsmall⟩ := exists_between (show (0 : ℝ) < min 1 (min r (1/(2*C*d^4+1))) by positivity)
  have ht1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have htr : t < r := lt_of_lt_of_le hsmall ((min_le_right 1 _).trans (min_le_left _ _))
  have htd : t < 1/(2*C*d^4+1) := lt_of_lt_of_le hsmall ((min_le_right 1 _).trans (min_le_right _ _))
  have ht2 : t^2 ≤ t := by nlinarith
  have hdt := (lt_div_iff₀ hden).mp htd
  have hprod : 2*C*d^4*t^2 < 1 := by nlinarith [mul_le_mul_of_nonneg_left ht2 (show 0 ≤ 2*C*d^4 by positivity)]
  have hmul := mul_lt_mul_of_pos_right hprod (sq_pos_of_pos ht)
  refine ⟨t,ht,htr,?_⟩
  apply (lt_div_iff₀ (pow_pos hd 4)).mpr
  nlinarith

/-- Every neighborhood of the same constant background contains a distant squared remainder exceeding the component budget. -/
theorem exists_sourceRemainder_exceeding_component_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (CoeffPair 2)) (ho : IsOpen U) (hbase : sourceConstantPotential 1 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U,
      ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one (unitWeightedPairEquiv φ) n
        ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1 ∧
      (∀ k : ℤ, n ≤ k.natAbs → SourceCoefficientStripBounds (by norm_num) SpectralWeight.one φ k) ∧
      (∀ K : ℕ, 1 ≤ K → sourcePositiveComponentHilbertBudget C φ n K <
        (sourceResonantBMinusSup (by norm_num) SpectralWeight.one φ n)^2) := by
  let base := sourceConstantPotential (p := 2) 1 0
  obtain ⟨Nc,_,Vc,hco,_,hcb,_,hc⟩ := sourceLemma6_6_uniform (p := 2) (by norm_num) base
  obtain ⟨Ns,_,Vs,hso,_,hsb,_,hs⟩ := sourceLemma6_8_unweighted (p := 2) (by norm_num) (by norm_num) base
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (ho.inter (hco.inter hso)) base ⟨hbase,hcb,hsb⟩
  let n := max M (max Nc (max Ns 2))
  have hnM : M ≤ n := by omega
  have hnC : Nc ≤ n := by omega
  have hnS : Ns ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn : (0 : ℤ) < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨t,ht,htr,htsmall⟩ := exists_component_amplitude C r (2*Real.pi*(n : ℝ)) hC hr (by positivity)
  let φ := sourceReverseCubicPotential (p := 2) n 1 t
  have hnorm : ‖φ-base‖^2 = t^2 := by
    simpa [φ,base,Complex.norm_real,Real.norm_of_nonneg ht.le] using sourceReverseCubicPotential_distance_sq n t
  have hφnorm : ‖φ-base‖ < r := (show ‖φ-base‖ ≤ t by nlinarith [norm_nonneg (φ-base)]).trans_lt htr
  have hφ : φ ∈ U ∩ (Vc ∩ Vs) := hball (by simpa only [Metric.mem_ball,dist_eq_norm] using hφnorm)
  obtain ⟨hsmall,_⟩ := hc φ hφ.2.1 n (by simpa using hnC) ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)
  have hb (k : ℤ) (hk : n ≤ k.natAbs) := (hs φ hφ.2.2).1 k (hnS.trans hk)
  refine ⟨n,hnM,hn2,φ,hφ.1,hsmall,hb,?_⟩
  intro K hK
  have hv := ((hb n (by simp)).2.2.2.2.2.2 _ (center_mem_resonantStrip n)).2.1
  simp only [SpectralWeight.one_apply,one_mul] at hv
  have hvsq : ‖sourceResonantBMinusFunction (by norm_num) φ n ((Real.pi : ℂ)*(n : ℤ)) - φ.fst (-(2*(n : ℤ)))‖^2 ≤
      (sourceResonantBMinusSup (by norm_num) SpectralWeight.one φ n)^2 := by gcongr
  have hexact := sourceReverseCubicPotential_remainder_norm_sq (p := 2) (by norm_num) n hn t ht.le hsmall
  have hvalue : t^2/(2*Real.pi*(n : ℝ))^4 ≤ (sourceResonantBMinusSup (by norm_num) SpectralWeight.one φ n)^2 := by
    simpa only [Int.cast_natCast] using hexact.symm.le.trans hvsq
  exact (sourcePositiveComponentBudget_reverse_le C hC n t ht.le n K (by omega) hK).trans_lt (htsmall.trans_le hvalue)

/-- The negative remainder tail with its correct square restored. -/
def sourceSquaredNegativeRemainderTail (N : ℕ) (φ : CoeffPair 2) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then (sourceResonantBMinusSup (by norm_num) SpectralWeight.one φ n)^2 else 0

/-- Restoring the powers does not repair the positive-component budget, even locally near (1,0). -/
theorem not_sourceLemma6_8_positive_component_sum (κ : ℕ → ℕ) (hκ : ∀ N : ℕ, 2 ≤ N → 1 ≤ κ N) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ sourceConstantPotential 1 0 ∈ U ∧
      ∀ φ ∈ U, ∀ N : ℕ, M ≤ N → 2 ≤ N →
        Summable (sourceSquaredNegativeRemainderTail N φ) ∧
          (∑' n : ℤ, sourceSquaredNegativeRemainderTail N φ n) ≤ sourcePositiveComponentHilbertBudget C φ N (κ N) := by
  rintro ⟨C,hC,M,U,ho,hbase,hbound⟩
  obtain ⟨n,hnM,hn2,φ,hφ,_,_,hbad⟩ := exists_sourceRemainder_exceeding_component_budget C hC U ho hbase M
  obtain ⟨hs,hbudget⟩ := hbound φ hφ n hnM hn2
  have hterm := hs.le_tsum (n : ℤ) (fun k _ => by unfold sourceSquaredNegativeRemainderTail; split_ifs <;> positivity)
  have hle : (sourceResonantBMinusSup (by norm_num) SpectralWeight.one φ n)^2 ≤
      ∑' k : ℤ, sourceSquaredNegativeRemainderTail n φ k := by
    simpa only [sourceSquaredNegativeRemainderTail,Int.natAbs_natCast,le_refl,ite_true] using hterm
  exact (not_le_of_gt (hbad (κ n) (hκ n hn2))) (hle.trans hbudget)

end NLS.ZakharovShabat
