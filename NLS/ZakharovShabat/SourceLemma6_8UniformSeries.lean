import NLS.ZakharovShabat.ResonantSeriesApproximation
import NLS.ZakharovShabat.SourceResonantAnalytic

/-! # The uniform scalar series in the proof of Lemma 6.8

The finite sums use the actual original operator powers and physical Fourier
coefficients. They converge uniformly on the full closed strips, locally
uniformly in the weighted potential, with one truncation length for all distant
signed indices. All assertions include p=1. The quantitative power-tail bounds
of the lemma retain their separate scope 1<p<infinity and recorded corrections.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Forgetting a weight commutes with every actual complementary potential power. -/
theorem forgetPairWeight_potentialInverse_pow (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (r : ℕ) :
    w.forgetPairWeight ((weightedPotentialInverse hp w φ n z hz ^ r) f) =
      (weightedPotentialInverse hp SpectralWeight.one (w.forgetPairWeight φ) n z hz ^ r)
        (w.forgetPairWeight f) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ',pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,
      forgetPairWeight_potentialInverse,ih]

/-- The finite scalar series retains its values after forgetting a spectral weight. -/
theorem weightedResonantParityPartialSumFunction_forget (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (r m : ℕ) (i j : Fin 2)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    weightedResonantParityPartialSumFunction hp SpectralWeight.one (w.forgetPairWeight φ) n r m i j z =
      weightedResonantParityPartialSumFunction hp w φ n r m i j z := by
  simp only [weightedResonantParityPartialSumFunction_eq hp _ _ n r m i j z hz,
    weightedResonantParityPartialSum,← forgetPairWeight_resonantSource hp w φ n j,
    ← pow_mul,← forgetPairWeight_potentialInverse_pow]
  apply Finset.sum_congr rfl
  intro k _
  fin_cases i <;> simp [resonantCoordinates]

/-- An original-source scalar parity term, with a total analytic extension in lambda. -/
def sourceResonantParityTermFunction (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (r k : ℕ) (i j : Fin 2) (z : ℂ) : ℂ :=
  weightedResonantParityTermFunction hp SpectralWeight.one (unitWeightedPairEquiv φ) n r k i j z

/-- The finite original scalar series, extended in lambda without a strip proof argument. -/
def sourceResonantParityPartialSumFunction (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (r m : ℕ) (i j : Fin 2) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m, sourceResonantParityTermFunction hp φ n r k i j z

/-- Each extended term is exactly the original operator-power coefficient on the closed strip. -/
theorem sourceResonantParityTermFunction_eq (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (r k : ℕ) (i j : Fin 2) (z : ℂ) (hz : z ∈ resonantStrip n) :
    sourceResonantParityTermFunction hp φ n r k i j z =
      let a := (sourcePotentialInverse hp φ n z hz ^ r)
        (((sourcePotentialInverse hp φ n z hz ^ 2)^k) (sourceResonantPotentialVector hp φ n j))
      if i = 0 then a.fst (-n) else a.snd n := by
  simp only [sourceResonantParityTermFunction,weightedResonantParityTermFunction,
    weightedPotentialExtension_eq hp _ _ n z hz,sourceResonantPotentialVector,
    ← pow_mul,sourcePotentialInverse_pow_unitInput]
  fin_cases i <;> simp [resonantCoordinates]

/-- The finite sum is the literal finite scalar source series, retaining both physical signs. -/
theorem sourceResonantParityPartialSumFunction_eq (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (r m : ℕ) (i j : Fin 2) (z : ℂ) (hz : z ∈ resonantStrip n) :
    sourceResonantParityPartialSumFunction hp φ n r m i j z =
      ∑ k ∈ Finset.range m,
        let a := (sourcePotentialInverse hp φ n z hz ^ r)
          (((sourcePotentialInverse hp φ n z hz ^ 2)^k) (sourceResonantPotentialVector hp φ n j))
        if i = 0 then a.fst (-n) else a.snd n := by
  simp only [sourceResonantParityPartialSumFunction,sourceResonantParityTermFunction_eq hp φ n r _ i j z hz]

/-- The original and weighted scalar partial sums agree on every full closed strip. -/
theorem sourceResonantParityPartialSumFunction_weightedInput (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (r m : ℕ) (i j : Fin 2)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    sourceResonantParityPartialSumFunction hp (sourceWeightedPeriodTwoInput w φ) n r m i j z =
      weightedResonantParityPartialSumFunction hp w φ n r m i j z := by
  change weightedResonantParityPartialSumFunction hp SpectralWeight.one
    (unitWeightedPairEquiv (sourceWeightedPeriodTwoInput w φ)) n r m i j z = _
  rw [unitWeightedPairEquiv_sourceWeightedInput]
  exact weightedResonantParityPartialSumFunction_forget hp w φ n r m i j z hz

/-- Every original-source scalar term is jointly analytic near the full closed strip. -/
theorem analyticAt_sourceResonantParityTermFunction (hp : p ≠ ⊤)
    (n : ℤ) (r k : ℕ) (i j : Fin 2) (s : CoeffPair p × ℂ) (hs : s.2 ∈ resonantStrip n) :
    AnalyticAt ℂ (fun t : CoeffPair p × ℂ => sourceResonantParityTermFunction hp t.1 n r k i j t.2) s := by
  have hmap : AnalyticAt ℂ (fun t : CoeffPair p × ℂ => (unitWeightedPairEquiv t.1,t.2)) s :=
    (((unitWeightedPairEquiv (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt s.1).comp analyticAt_fst).prod analyticAt_snd
  exact (analyticAt_weightedResonantParityTermFunction hp SpectralWeight.one n r k i j
    (unitWeightedPairEquiv s.1,s.2) hs).comp (f := fun t : CoeffPair p × ℂ => (unitWeightedPairEquiv t.1,t.2)) hmap

/-- A common local rate for all three original scalar series, uniform also in the signed strip index. -/
theorem exists_uniform_sourceResonantParitySeries_rate (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ m : ℕ, ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        let η := sourceWeightedPeriodTwoInput w ψ
        ‖sourceResonantAFunction hp η n z - sourceResonantParityPartialSumFunction hp η n 1 m 1 1 z‖ ≤
          (2*Coeff.complementaryConstant p hp*(‖φ‖+1)^2)*(1/2:ℝ)^m ∧
        w (2*n) * ‖(sourceResonantBPlusFunction hp η n z - η.snd (2*n)) -
          sourceResonantParityPartialSumFunction hp η n 2 m 1 0 z‖ ≤ (‖φ‖+1)*(1/2:ℝ)^m ∧
        w (2*n) * ‖(sourceResonantBMinusFunction hp η n z - η.fst (-(2*n))) -
          sourceResonantParityPartialSumFunction hp η n 2 m 0 1 z‖ ≤ (‖φ‖+1)*(1/2:ℝ)^m := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,h₁⟩ := exists_uniform_resonantParitySeries_rate hp w φ
  obtain ⟨N₂,hN₂,U₂,ho₂,hc₂,hφ₂,h0₂,h₂⟩ := exists_uniform_sourceResonantFunctions_weightedInput hp w φ
  refine ⟨max N₁ N₂,by omega,U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro m ψ hψ n hn z hz
  have he := h₂ ψ hψ.2 n (by omega) z hz
  simpa only [he.1,he.2.1,he.2.2,sourceResonantParityPartialSumFunction_weightedInput hp w ψ n _ _ _ _ z hz,
    sourceWeightedPeriodTwoInput_fst,sourceWeightedPeriodTwoInput_snd] using h₁ m ψ hψ.1 n (by omega) z hz

/-- One truncation length controls all three source series throughout all distant closed strips. -/
theorem exists_uniform_sourceResonantParitySeries (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
          let η := sourceWeightedPeriodTwoInput w ψ
          ‖sourceResonantAFunction hp η n z - sourceResonantParityPartialSumFunction hp η n 1 m 1 1 z‖ < ε ∧
          w (2*n) * ‖(sourceResonantBPlusFunction hp η n z - η.snd (2*n)) -
            sourceResonantParityPartialSumFunction hp η n 2 m 1 0 z‖ < ε ∧
          w (2*n) * ‖(sourceResonantBMinusFunction hp η n z - η.fst (-(2*n))) -
            sourceResonantParityPartialSumFunction hp η n 2 m 0 1 z‖ < ε := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_sourceResonantParitySeries_rate hp w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ε hε
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  have ha : Filter.Tendsto (fun m : ℕ => (2*Coeff.complementaryConstant p hp*(‖φ‖+1)^2)*(1/2:ℝ)^m)
      Filter.atTop (nhds 0) := by simpa using ht.const_mul (2*Coeff.complementaryConstant p hp*(‖φ‖+1)^2)
  have hb' : Filter.Tendsto (fun m : ℕ => (‖φ‖+1)*(1/2:ℝ)^m) Filter.atTop (nhds 0) := by
    simpa using ht.const_mul (‖φ‖+1)
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp ((ha.eventually_lt_const hε).and (hb'.eventually_lt_const hε))
  refine ⟨M,?_⟩
  intro m hm ψ hψ n hn z hz
  have he := hb m ψ hψ n hn z hz
  exact ⟨he.1.trans_lt (hM m hm).1,he.2.1.trans_lt (hM m hm).2,he.2.2.trans_lt (hM m hm).2⟩

/-- The three displayed source scalar series converge uniformly on whole closed strips,
locally uniformly in the weighted potential. -/
theorem sourceLemma6_8_uniform_series (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        TendstoUniformlyOn
          (fun m (t : WeightedCoeffPair w.toWeight p × ℂ) =>
            sourceResonantParityPartialSumFunction hp (sourceWeightedPeriodTwoInput w t.1) n 1 m 1 1 t.2)
          (fun t => sourceResonantAFunction hp (sourceWeightedPeriodTwoInput w t.1) n t.2)
          Filter.atTop (U ×ˢ resonantStrip n) ∧
        TendstoUniformlyOn
          (fun m (t : WeightedCoeffPair w.toWeight p × ℂ) =>
            sourceResonantParityPartialSumFunction hp (sourceWeightedPeriodTwoInput w t.1) n 2 m 1 0 t.2)
          (fun t => sourceResonantBPlusFunction hp (sourceWeightedPeriodTwoInput w t.1) n t.2 - t.1.snd.val (2*n))
          Filter.atTop (U ×ˢ resonantStrip n) ∧
        TendstoUniformlyOn
          (fun m (t : WeightedCoeffPair w.toWeight p × ℂ) =>
            sourceResonantParityPartialSumFunction hp (sourceWeightedPeriodTwoInput w t.1) n 2 m 0 1 t.2)
          (fun t => sourceResonantBMinusFunction hp (sourceWeightedPeriodTwoInput w t.1) n t.2 - t.1.fst.val (-(2*n)))
          Filter.atTop (U ×ˢ resonantStrip n) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_sourceResonantParitySeries hp w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro n hn
  refine ⟨Metric.tendstoUniformlyOn_iff.mpr ?_,Metric.tendstoUniformlyOn_iff.mpr ?_,Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  all_goals
    intro ε hε
    obtain ⟨M,hM⟩ := hb ε hε
    apply Filter.eventually_atTop.mpr
    refine ⟨M,?_⟩
    intro m hm t ht
    have he := hM m hm t.1 ht.1 n hn t.2 ht.2
    simp only [sourceWeightedPeriodTwoInput_fst,sourceWeightedPeriodTwoInput_snd] at he
    simp only [dist_eq_norm]
  · exact he.1
  · exact (le_mul_of_one_le_left (norm_nonneg _) (w.one_le (2*n))).trans_lt he.2.1
  · exact (le_mul_of_one_le_left (norm_nonneg _) (w.one_le (2*n))).trans_lt he.2.2

end NLS.ZakharovShabat
