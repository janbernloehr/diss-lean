import NLS.ZakharovShabat.SourceLemma6_8UniformSeries
import NLS.ZakharovShabat.SourceLemma6_8
import NLS.ZakharovShabat.DiagonalProofPowerSums

/-! # The literal diagonal proof in Lemma 6.8

The original coefficient has the signed, absolutely convergent Fourier sum.
Holder uses the actual even vector and its unweighted component bound.
Genuine full-strip suprema and summable outer moments retain those norms.
The exact near/far proof yields an explicit exponent-only constant, first
with distinguished components and then with the printed pair/half-cutoff budget.
The series includes p=1; the power-tail estimates require 1<p<infinity.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact signed original diagonal series, with the resonant denominator omitted. -/
theorem sourceResonantA_signed_series (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceResonantAFunction hp φ n z =
      ∑' m : ℤ, if m = n then 0 else
        (φ.snd (n+m) / (z-(Real.pi:ℂ)*m)) * (sourceResonantEvenVector hp φ n z hz h 1).fst (-m) := by
  rw [(sourceResonantFunctions_eq hp φ n z hz h).1]
  unfold sourceResonantA
  rw [weightedResonantA_eq_tsum,← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply,sub_neg_eq_add,neg_neg,unitWeightedPairEquiv_snd,
    sourceResonantEvenVector,sourceWeightedPeriodTwoInput_fst]
  by_cases hm : m = n
  · simp [hm,complementarySymbol]
  · simp [hm,complementarySymbol,div_eq_mul_inv,mul_assoc]

/-- Absolute convergence accompanies the literal signed diagonal series. -/
theorem summable_sourceResonantA_signed_series (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    Summable (fun m : ℤ => if m = n then (0:ℂ) else
      (φ.snd (n+m) / (z-(Real.pi:ℂ)*m)) * (sourceResonantEvenVector hp φ n z hz h 1).fst (-m)) := by
  have hs := (Equiv.neg ℤ).summable_iff.mpr
    (summable_weightedResonantA_terms hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h)
  apply hs.congr
  intro m
  simp only [Function.comp_def,Equiv.neg_apply,sub_neg_eq_add,neg_neg,unitWeightedPairEquiv_snd,
    sourceResonantEvenVector,sourceWeightedPeriodTwoInput_fst]
  by_cases hm : m = n
  · simp [hm,complementarySymbol]
  · simp [hm,complementarySymbol,div_eq_mul_inv,mul_assoc]

/-- Physical-coordinate form of the same original series, before frequency reflection. -/
theorem sourceResonantA_physical_series (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceResonantAFunction hp φ n z =
      ∑' k : ℤ, φ.snd (n-k) * complementarySymbol n z (-k) *
        (sourceResonantEvenVector hp φ n z hz h 1).fst k := by
  rw [(sourceResonantFunctions_eq hp φ n z hz h).1]
  simpa only [sourceResonantA,sourceResonantEvenVector,sourceWeightedPeriodTwoInput_fst,
    unitWeightedPairEquiv_snd] using weightedResonantA_eq_tsum hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The literal conjugate reciprocal moment controls the original diagonal before bounding u_n. -/
theorem sourceResonantA_signed_holder (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    ‖sourceResonantAFunction hp φ n z‖ ≤ ‖(sourceResonantEvenVector hp φ n z hz h 1).fst‖ *
      (∑' m : ℤ, (‖φ.snd (n+m)‖ / |((m-n : ℤ) : ℝ)|)^p.conjExponent.toReal)^(1/p.conjExponent.toReal) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  rw [sourceResonantA_physical_series hp φ n z hz h]
  have hb := norm_tsum_complementaryRow_le (q := p.conjExponent) hq φ.snd
    (sourceResonantEvenVector hp φ n z hz h 1).fst n z hz
  rw [norm_complementaryRowEnvelope_eq hq
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne] at hb
  exact hb

/-- The original even vector has the smaller unweighted distinguished-component bound. -/
theorem norm_sourceResonantEvenVector_one_le (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ ≤ 1/2) :
    ‖sourceResonantEvenVector hp φ n z hz h 1‖ ≤ 2 * ‖φ.fst‖ := by
  have he (f : WeightedCoeffPair SpectralWeight.one.toWeight p) :
      sourceWeightedPeriodTwoInput SpectralWeight.one f = unitWeightedPairEquiv.symm f := by
    apply unitWeightedPairEquiv.injective
    rw [unitWeightedPairEquiv_sourceWeightedInput, LinearIsometryEquiv.apply_symm_apply]
    apply weightedPair_ext <;> intro k <;> simp
  rw [sourceResonantEvenVector,he,LinearIsometryEquiv.norm_map]
  simpa only [SpectralWeight.shiftedPairNorm_one hp, (sourceUnitWeighted_component_norms φ).1] using
    shiftedPairNorm_evenVector_one_le hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h hh

/-- The original diagonal Holder bound retains the unweighted opposite component norm. -/
theorem sourceResonantA_signed_holder_half (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ ≤ 1/2) :
    ‖sourceResonantAFunction hp φ n z‖ ≤ (2 * ‖φ.fst‖) *
      (∑' m : ℤ, (‖φ.snd (n+m)‖ / |((m-n : ℤ) : ℝ)|)^p.conjExponent.toReal)^(1/p.conjExponent.toReal) := by
  exact (sourceResonantA_signed_holder hp hp1 φ n z hz h).trans
    (mul_le_mul_of_nonneg_right
      ((WithLp.norm_fst_le _ _).trans (norm_sourceResonantEvenVector_one_le hp φ n z hz h hh))
      (Real.rpow_nonneg (tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)) _))

omit [Fact (1 ≤ p)] in
/-- Raising the Holder estimate gives the precise p/q power of the inner sum. -/
theorem diagonalHolder_power_le {A B M q : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (h : A ≤ (2*B)*M^(1/q)) :
    A^p.toReal ≤ (2:ℝ)^p.toReal * B^p.toReal * M^(p.toReal/q) := by
  have hpow := Real.rpow_le_rpow hA h (ENNReal.toReal_nonneg : 0 ≤ p.toReal)
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hM _),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hB,← Real.rpow_mul hM] at hpow
  simpa only [show (1/q)*p.toReal = p.toReal/q by ring] using hpow

/-- The pointwise p-power Holder inequality for the literal original diagonal. -/
theorem sourceResonantA_signed_holder_power (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ ≤ 1/2) :
    ‖sourceResonantAFunction hp φ n z‖^p.toReal ≤ (2:ℝ)^p.toReal * ‖φ.fst‖^p.toReal *
      (∑' m : ℤ, (‖φ.snd (n+m)‖ / |((m-n : ℤ) : ℝ)|)^p.conjExponent.toReal)^(p.toReal/p.conjExponent.toReal) :=
  diagonalHolder_power_le (norm_nonneg _) (norm_nonneg _)
    (tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _))
    (sourceResonantA_signed_holder_half hp hp1 φ n z hz h hh)

/-- One neighborhood gives the literal Holder bound for genuine suprema on full strips. -/
theorem exists_uniform_sourceDiagonalHolder (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        let η := sourceWeightedPeriodTwoInput w ψ
        let M := ∑' m : ℤ, (‖η.snd (n+m)‖ / |((m-n : ℤ) : ℝ)|)^p.conjExponent.toReal
        BddAbove ((fun z : ℂ => ‖sourceResonantAFunction hp η n z‖) '' resonantStrip n) ∧
        0 ≤ sourceResonantDiagonalSup hp η n ∧
        sourceResonantDiagonalSup hp η n ≤ (2*‖η.fst‖)*M^(1/p.conjExponent.toReal) ∧
        (sourceResonantDiagonalSup hp η n)^p.toReal ≤
          (2:ℝ)^p.toReal*‖η.fst‖^p.toReal*M^(p.toReal/p.conjExponent.toReal) := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,h₁⟩ := exists_uniform_resonantDiagonalBound hp w φ
  obtain ⟨N₂,hN₂,U₂,ho₂,hc₂,hφ₂,h0₂,h₂⟩ := exists_uniform_sourceResonantFunctions_weightedInput hp w φ
  refine ⟨max N₁ N₂,by omega,U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro ψ hψ n hn
  dsimp only
  let η := sourceWeightedPeriodTwoInput w ψ
  let M := ∑' m : ℤ, (‖η.snd (n+m)‖ / |((m-n : ℤ) : ℝ)|)^p.conjExponent.toReal
  let B := (2*‖η.fst‖)*M^(1/p.conjExponent.toReal)
  have hf : η.fst = w.toCoeff ψ.fst := by ext k; simp [η]
  have hpoint (z : ℂ) (hz : z ∈ resonantStrip n) : ‖sourceResonantAFunction hp η n z‖ ≤ B := by
    rw [(h₂ ψ hψ.2 n (by omega) z hz).1]
    obtain ⟨_,_,hb⟩ := h₁ ψ hψ.1 n (by omega) z hz
    rw [resonantDiagonalBound_eq hp hp1] at hb
    simpa only [B,M,hf,η,sourceWeightedPeriodTwoInput_snd,
      SpectralWeight.norm_toCoeff_eq_norm_forgetWeight] using hb
  have hbounded : BddAbove ((fun z : ℂ => ‖sourceResonantAFunction hp η n z‖) '' resonantStrip n) := by
    refine ⟨B,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact hpoint z hz
  have hnon : 0 ≤ sourceResonantDiagonalSup hp η n :=
    (norm_nonneg _).trans (le_csSup hbounded ⟨_,center_mem_resonantStrip n,rfl⟩)
  have hsup : sourceResonantDiagonalSup hp η n ≤ B := by
    have hne : ((fun z : ℂ => ‖sourceResonantAFunction hp η n z‖) '' resonantStrip n).Nonempty :=
      ⟨_,(Real.pi : ℂ)*n,center_mem_resonantStrip n,rfl⟩
    apply csSup_le hne
    rintro _ ⟨z,hz,rfl⟩
    exact hpoint z hz
  exact ⟨hbounded,hnon,hsup,diagonalHolder_power_le hnon (norm_nonneg _)
    (tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)) hsup⟩

/-- The displayed sum after Holder is a comparison of convergent full signed tails. -/
theorem exists_uniform_sourceDiagonalHolder_sum (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        let η := sourceWeightedPeriodTwoInput w ψ
        Summable (sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp η)) ∧
        Summable (diagonalMomentPowerTail p N η.snd) ∧
        (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp η) n) ≤
          (2:ℝ)^p.toReal*‖η.fst‖^p.toReal*(∑' n : ℤ, diagonalMomentPowerTail p N η.snd n) := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_sourceDiagonalHolder hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hN
  let η := sourceWeightedPeriodTwoInput w ψ
  let C := (2:ℝ)^p.toReal*‖η.fst‖^p.toReal
  have hm := summable_diagonalMomentPowerTail hp hp1 η.snd N
  have hnon (n : ℤ) : 0 ≤ sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp η) n := by
    unfold sourceCoefficientPowerTail
    split_ifs with hn
    · exact Real.rpow_nonneg (hb ψ hψ n (hN.trans hn)).2.1 _
    · exact le_rfl
  have hdom (n : ℤ) : sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp η) n ≤
      C*diagonalMomentPowerTail p N η.snd n := by
    by_cases hn : N ≤ n.natAbs
    · simpa only [sourceCoefficientPowerTail,diagonalMomentPowerTail,if_pos hn,C] using
        (hb ψ hψ n (hN.trans hn)).2.2.2
    · simp only [sourceCoefficientPowerTail,diagonalMomentPowerTail,if_neg hn,mul_zero,le_refl]
  have hs := Summable.of_nonneg_of_le hnon hdom (hm.mul_left C)
  refine ⟨hs,hm,?_⟩
  simpa only [tsum_mul_left] using hs.tsum_le_tsum hdom (hm.mul_left C)

/-- One explicit exponent-only constant obtained by the literal diagonal proof. -/
def diagonalProofConstant (p : ℝ≥0∞) : ℝ :=
  (2:ℝ)^p.toReal * (2:ℝ)^(p.toReal-1) * diagonalRegionConstant p

omit [Fact (1 ≤ p)] in
theorem diagonalProofConstant_pos (hp : p ≠ ⊤) (hp1 : 1 < p) : 0 < diagonalProofConstant p := by
  have hc := diagonalRegionConstant_pos hp hp1
  unfold diagonalProofConstant
  positivity

/-- The original diagonal tail follows from the literal Holder and regional sums. -/
theorem exists_uniform_sourceDiagonalProofBound (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        let η := sourceWeightedPeriodTwoInput w ψ
        Summable (sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp η)) ∧
        (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp η) n) ≤
          diagonalProofConstant p * ‖η.fst‖^p.toReal *
            (‖η.snd‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖Coeff.fourierTail N η.snd‖^p.toReal) := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_sourceDiagonalHolder_sum hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hN
  have he := hb ψ hψ N hN
  refine ⟨he.1,he.2.2.trans ?_⟩
  calc
    _ ≤ ((2:ℝ)^p.toReal*‖(sourceWeightedPeriodTwoInput w ψ).fst‖^p.toReal)*
        ((2:ℝ)^(p.toReal-1)*diagonalRegionConstant p *
          (‖(sourceWeightedPeriodTwoInput w ψ).snd‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) +
            ‖Coeff.fourierTail N (sourceWeightedPeriodTwoInput w ψ).snd‖^p.toReal)) :=
      mul_le_mul_of_nonneg_left (diagonalMomentPowerTail_sum_le hp hp1 _ N (by omega)) (by positivity)
    _ = _ := by unfold diagonalProofConstant; ring

/-- Replacing distinguished components and a full cutoff by the printed pair/half-cutoff budget is monotone. -/
theorem diagonalProof_component_budget_le_pair (hp : p ≠ ⊤) (hp1 : 1 < p) (η : CoeffPair p) (N : ℕ) :
    diagonalProofConstant p * ‖η.fst‖^p.toReal *
      (‖η.snd‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖Coeff.fourierTail N η.snd‖^p.toReal) ≤
    diagonalProofConstant p * ‖η‖^p.toReal *
      (‖η‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail (N/2) η‖^p.toReal) := by
  have hc := (diagonalProofConstant_pos hp hp1).le
  have hf := WithLp.norm_fst_le _ η
  have hs := WithLp.norm_snd_le _ η
  have ht : ‖Coeff.fourierTail N η.snd‖ ≤ ‖sourceFourierTail (N/2) η‖ := by
    exact (Coeff.norm_fourierTail_antitone (zero_lt_one.trans hp1).ne' η.snd (by omega)).trans
      (WithLp.norm_snd_le _ (sourceFourierTail (N/2) η))
  gcongr

/-- Lemma 6.8(i), obtained directly through the displayed diagonal proof with original norms. -/
theorem sourceLemma6_8_diagonal_proof (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        let η := sourceWeightedPeriodTwoInput w ψ
        Summable (sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp η)) ∧
        (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp η) n) ≤
          diagonalProofConstant p * ‖η‖^p.toReal *
            (‖η‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail (N/2) η‖^p.toReal) := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_sourceDiagonalProofBound hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hN
  exact ⟨(hb ψ hψ N hN).1,(hb ψ hψ N hN).2.trans
    (diagonalProof_component_budget_le_pair hp hp1 _ N)⟩

end NLS.ZakharovShabat
