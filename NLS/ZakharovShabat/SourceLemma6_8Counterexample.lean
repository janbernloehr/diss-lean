import NLS.ZakharovShabat.SourceCubicResonantPotential

/-!
# The omitted powers in the printed Lemma 6.8(ii)

At p=2 a two-mode original potential has a cubic positive remainder, whereas
the printed budget is sextic near zero. Every neighborhood of zero and every
common cutoff admit a counterexample. This does not assert failure beyond
every individual cutoff for one fixed finite-support potential.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The literal positive-remainder p=2 budget, with an explicit Fourier-tail cutoff. -/
def sourcePrintedHilbertRemainderBudget (C : ℝ) (φ : CoeffPair 2) (N K : ℕ) : ℝ :=
  C * (‖φ.snd‖^4/(N : ℝ) + ‖sourceFourierTail K φ‖^4) * ‖φ.snd‖^2

/-- Even replacing the inner positive-component norm by the full pair does not repair the missing powers. -/
def sourceUnpoweredHilbertRemainderBudget (C : ℝ) (φ : CoeffPair 2) (N K : ℕ) : ℝ :=
  C * (‖φ‖^4/(N : ℝ) + ‖sourceFourierTail K φ‖^4) * ‖φ.snd‖^2

/-- The literal budget is at most the one with the enlarged inner norm. -/
theorem sourcePrintedRemainderBudget_le_unpowered (C : ℝ) (hC : 0 ≤ C) (φ : CoeffPair 2) (N K : ℕ) :
    sourcePrintedHilbertRemainderBudget C φ N K ≤ sourceUnpoweredHilbertRemainderBudget C φ N K := by
  unfold sourcePrintedHilbertRemainderBudget sourceUnpoweredHilbertRemainderBudget
  gcongr
  exact WithLp.norm_snd_le _ φ

/-- A Fourier tail cannot enlarge the original Hilbert pair norm. -/
private theorem sourceTail_norm_le (φ : CoeffPair 2) (K : ℕ) : ‖sourceFourierTail K φ‖ ≤ ‖φ‖ := by
  simpa only [weightedPairFourierTail_unitWeightedPairEquiv,LinearIsometryEquiv.norm_map] using
    norm_weightedPairFourierTail_le (p := 2) (by norm_num) SpectralWeight.one.toWeight K (unitWeightedPairEquiv φ)

/-- Uniform sextic upper bound, independent of the tail rounding convention. -/
theorem sourceUnpoweredRemainderBudget_cubic_le (C : ℝ) (hC : 0 ≤ C) (n : ℤ)
    (t : ℝ) (ht : 0 ≤ t) (N K : ℕ) (hN : 1 ≤ N) :
    sourceUnpoweredHilbertRemainderBudget C (sourceCubicPotential n t t) N K ≤ 16*C*t^6 := by
  let φ := sourceCubicPotential (p := 2) n t t
  have hnorm : ‖φ‖^2 = 2*t^2 := by
    simpa [φ,Complex.norm_real,Real.norm_of_nonneg ht,two_mul] using sourceCubicPotential_norm_sq n t t
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ C * (‖φ‖^4/(N : ℝ)+‖φ‖^4) * ‖φ‖^2 := by
      unfold sourceUnpoweredHilbertRemainderBudget
      gcongr
      · exact sourceTail_norm_le φ K
      · exact WithLp.norm_snd_le _ φ
    _ ≤ C * (‖φ‖^4+‖φ‖^4) * ‖φ‖^2 := by
      gcongr
      exact div_le_self (by positivity) hNR
    _ = 2*C*(‖φ‖^2)^3 := by ring
    _ = 16*C*t^6 := by rw [hnorm]; ring

/-- Choose an amplitude that makes the cubic coefficient exceed any sextic budget. -/
private theorem exists_cubic_amplitude (C r d : ℝ) (hC : 0 ≤ C) (hr : 0 < r) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 2*t < r ∧ 16*C*t^6 < t^3/d^2 := by
  have hden : 0 < 16*C*d^2+1 := by positivity
  obtain ⟨t,ht,hsmall⟩ := exists_between (show (0 : ℝ) < min 1 (min (r/2) (1/(16*C*d^2+1))) by positivity)
  have ht1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have htr : t < r/2 := lt_of_lt_of_le hsmall ((min_le_right 1 _).trans (min_le_left _ _))
  have htd : t < 1/(16*C*d^2+1) := lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_right _ _))
  have ht2 : t^2 ≤ 1 := by nlinarith
  have ht3 : t^3 ≤ t := by nlinarith [mul_le_mul_of_nonneg_right ht2 ht.le]
  have hdt := (lt_div_iff₀ hden).mp htd
  have hprod : 16*C*d^2*t^3 < 1 := by nlinarith [mul_le_mul_of_nonneg_left ht3 (show 0 ≤ 16*C*d^2 by positivity)]
  have hmul := mul_lt_mul_of_pos_right hprod (pow_pos ht 3)
  refine ⟨t,ht,ht1,by linarith,?_⟩
  apply (lt_div_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith

/-- Every source neighborhood of zero contains a distant coefficient exceeding even the enlarged budget. -/
theorem exists_sourceRemainder_exceeding_unpowered_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (CoeffPair 2)) (ho : IsOpen U) (h0 : 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U,
      ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one (unitWeightedPairEquiv φ) n
        ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1 ∧
      (∀ k : ℤ, n ≤ k.natAbs → SourceCoefficientStripBounds (by norm_num) SpectralWeight.one φ k) ∧
      (∀ K : ℕ, sourceUnpoweredHilbertRemainderBudget C φ n K <
        sourceResonantBPlusSup (by norm_num) SpectralWeight.one φ n) := by
  obtain ⟨Nc,_,Vc,hco,_,_,hc0,hc⟩ := sourceLemma6_6_uniform (p := 2) (by norm_num) 0
  obtain ⟨Ns,_,Vs,hso,_,_,hs0,hs⟩ := sourceLemma6_8_unweighted (p := 2) (by norm_num) (by norm_num) 0
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (ho.inter (hco.inter hso)) 0 ⟨h0,hc0,hs0⟩
  let n := max M (max Nc (max Ns 2))
  have hnM : M ≤ n := by omega
  have hnC : Nc ≤ n := by omega
  have hnS : Ns ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn : (0 : ℤ) < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨t,ht,_,htr,htsmall⟩ := exists_cubic_amplitude C r (2*Real.pi*(n : ℝ)) hC hr (by positivity)
  let φ := sourceCubicPotential (p := 2) n t t
  have hnorm : ‖φ‖^2 = 2*t^2 := by
    simpa [φ,Complex.norm_real,Real.norm_of_nonneg ht.le,two_mul] using sourceCubicPotential_norm_sq n t t
  have hφnorm : ‖φ‖ < r := (show ‖φ‖ ≤ 2*t by nlinarith [norm_nonneg φ]).trans_lt htr
  have hφ : φ ∈ U ∩ (Vc ∩ Vs) := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hφnorm)
  obtain ⟨hsmall,_⟩ := hc φ hφ.2.1 n (by simpa using hnC) ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)
  have hb (k : ℤ) (hk : n ≤ k.natAbs) := (hs φ hφ.2.2).1 k (hnS.trans hk)
  refine ⟨n,hnM,hn2,φ,hφ.1,hsmall,hb,?_⟩
  intro K
  have hv := ((hb n (by simp)).2.2.2.2.2.2 _ (center_mem_resonantStrip n)).2.2
  simp only [SpectralWeight.one_apply,one_mul] at hv
  have hexact := sourceCubicPotential_remainder_norm (p := 2) (by norm_num) n hn t ht.le hsmall
  have hvalue : t^3/(2*Real.pi*(n : ℝ))^2 ≤ sourceResonantBPlusSup (by norm_num) SpectralWeight.one φ n := by
    simpa only [Int.cast_natCast] using hexact.symm.le.trans hv
  exact (sourceUnpoweredRemainderBudget_cubic_le C hC n t ht.le n K (by omega)).trans_lt (htsmall.trans_le hvalue)

/-- The unpowered full signed remainder tail used by the literal printed display. -/
def sourceUnpoweredRemainderTail (N : ℕ) (φ : CoeffPair 2) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then sourceResonantBPlusSup (by norm_num) SpectralWeight.one φ n else 0

/-- Enlarging the inner norm cannot repair the missing powers, for any tail-cutoff convention. -/
theorem not_sourceLemma6_8_unpowered_sum (κ : ℕ → ℕ) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ 0 ∈ U ∧
      ∀ φ ∈ U, ∀ N : ℕ, M ≤ N → 2 ≤ N →
        Summable (sourceUnpoweredRemainderTail N φ) ∧
          (∑' n : ℤ, sourceUnpoweredRemainderTail N φ n) ≤ sourceUnpoweredHilbertRemainderBudget C φ N (κ N) := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  obtain ⟨n,hnM,hn2,φ,hφ,_,hb,hbad⟩ := exists_sourceRemainder_exceeding_unpowered_budget C hC U ho h0 M
  obtain ⟨hs,hbudget⟩ := hbound φ hφ n hnM hn2
  have hnonneg (k : ℤ) : 0 ≤ sourceUnpoweredRemainderTail n φ k := by
    unfold sourceUnpoweredRemainderTail
    split_ifs with hk
    · exact (hb k hk).2.2.2.2.2.1
    · rfl
  have hterm := hs.le_tsum (n : ℤ) (fun k _ => hnonneg k)
  have hle : sourceResonantBPlusSup (by norm_num) SpectralWeight.one φ n ≤
      ∑' k : ℤ, sourceUnpoweredRemainderTail n φ k := by
    simpa only [sourceUnpoweredRemainderTail,Int.natAbs_natCast,le_refl,ite_true] using hterm
  exact (not_le_of_gt (hbad (κ n))) (hle.trans hbudget)

/-- The literal positive-remainder display fails locally at zero, already at p=2 and unit weight. -/
theorem not_sourceLemma6_8_printed_sum (κ : ℕ → ℕ) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ 0 ∈ U ∧
      ∀ φ ∈ U, ∀ N : ℕ, M ≤ N → 2 ≤ N →
        Summable (sourceUnpoweredRemainderTail N φ) ∧
          (∑' n : ℤ, sourceUnpoweredRemainderTail N φ n) ≤ sourcePrintedHilbertRemainderBudget C φ N (κ N) := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  apply not_sourceLemma6_8_unpowered_sum κ
  refine ⟨C,hC,M,U,ho,h0,?_⟩
  intro φ hφ N hNM hN2
  obtain ⟨hs,hb⟩ := hbound φ hφ N hNM hN2
  exact ⟨hs,hb.trans (sourcePrintedRemainderBudget_le_unpowered C hC φ N (κ N))⟩

end NLS.ZakharovShabat
