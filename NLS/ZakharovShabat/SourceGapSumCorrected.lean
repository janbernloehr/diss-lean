import NLS.ZakharovShabat.SourceGapCoefficientMajorant

/-! # The final Section 6 gap sum with a corrected constant

The full signed canonical gap tail is controlled by the literal grouped
leading and remainder sums with factor `2^(3*p.toReal-2)`. Both sums converge.
One open convex neighborhood and cutoff work for every larger cutoff, and
Lemma 6.8 yields the corrected budget in the original weighted pair norm.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Summability and the actual counted pair give the corrected full signed coefficient-sum inequality. -/
theorem sourceCanonicalGapSum_le_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p)
    (N : ℕ) (ξ η : ℤ → ℂ)
    (hr : ∀ n : ℤ, N ≤ n.natAbs → SourceResonantRootPair hp φ n (ξ n) (η n))
    (hc : ∀ n : ℤ, N ≤ n.natAbs → SourceCoefficientStripBounds hp w φ n)
    (hg : ∀ n : ℤ, N ≤ n.natAbs → ‖sourcePeriodTwoCanonicalGap hp hp1 φ n‖ = ‖ξ n-η n‖)
    (hl : Summable (sourceGapLeadingPowerTail w φ N)) (he : Summable (sourceGapRemainderPowerTail hp w φ N)) :
    Summable (sourceCanonicalWeightedGapPowerTail hp hp1 w φ N) ∧
      (∑' n : ℤ, sourceCanonicalWeightedGapPowerTail hp hp1 w φ N n) ≤ rootGapSummationConstant p *
        ((∑' n : ℤ, sourceGapLeadingPowerTail w φ N n)+(∑' n : ℤ, sourceGapRemainderPowerTail hp w φ N n)) := by
  have hn (n : ℤ) : 0 ≤ sourceCanonicalWeightedGapPowerTail hp hp1 w φ N n := by
    have hw := (w.positive (2*n)).le
    unfold sourceCanonicalWeightedGapPowerTail
    split_ifs <;> positivity
  have hpoint (n : ℤ) : sourceCanonicalWeightedGapPowerTail hp hp1 w φ N n ≤ rootGapSummationConstant p *
      (sourceGapLeadingPowerTail w φ N n+sourceGapRemainderPowerTail hp w φ N n) := by
    unfold sourceCanonicalWeightedGapPowerTail sourceGapLeadingPowerTail sourceGapRemainderPowerTail
    split_ifs with hn
    · rw [hg n hn]
      have h := sourceResonantRootPair_gap_le_four_terms hp w φ n (ξ n) (η n) (hr n hn) (hc n hn)
      simpa only [Real.mul_rpow (w.positive _).le (norm_nonneg _),mul_add,add_assoc] using h
    · simp
  have hsum := (hl.add he).mul_left (rootGapSummationConstant p)
  have hactual := hsum.of_nonneg_of_le hn hpoint
  refine ⟨hactual,?_⟩
  have h := hactual.tsum_le_tsum hpoint hsum
  rwa [tsum_mul_left,hl.tsum_add he] at h

/-- Lemma 6.8 bounds both convergent original coefficient sums by the corrected weighted budget. -/
theorem sourceGapCoefficientSums_le_budget (hp : p ≠ ⊤) (w : SpectralWeight)
    (ψ : WeightedCoeffPair w.toWeight p) (N : ℕ) (htails : SourceCoefficientTailEstimates hp w ψ N) :
    let f := sourceWeightedPeriodTwoInput w ψ
    Summable (sourceGapLeadingPowerTail w f N) ∧ Summable (sourceGapRemainderPowerTail hp w f N) ∧
      rootGapSummationConstant p *
        ((∑' n : ℤ, sourceGapLeadingPowerTail w f N n)+(∑' n : ℤ, sourceGapRemainderPowerTail hp w f N n)) ≤ rootGapBudget w ψ N := by
  dsimp only
  obtain ⟨_,⟨hsm,hm⟩,⟨hsp,hp'⟩⟩ := htails
  obtain ⟨hsl,hl⟩ := resonantLeadingPower_tail_summable_and_le hp w ψ N (N/2) (by omega)
  rw [← sourceGapLeadingPowerTail_weightedInput] at hsl hl
  have hse : Summable (sourceGapRemainderPowerTail hp w (sourceWeightedPeriodTwoInput w ψ) N) := by
    rw [sourceGapRemainderPowerTail_eq]
    exact hsm.add hsp
  refine ⟨hsl,hse,?_⟩
  rw [sourceGapRemainderPowerTail_eq]
  simp only [Pi.add_apply]
  rw [hsm.tsum_add hsp]
  have he := add_le_add hm hp'
  have heq : sourceOffDiagonalTailBudget w ψ ‖ψ.fst‖ N+sourceOffDiagonalTailBudget w ψ ‖ψ.snd‖ N =
      offDiagonalSummationConstant p*‖ψ‖^p.toReal *
        (‖ψ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1))+
          ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^(2*p.toReal)) := by
    unfold sourceOffDiagonalTailBudget
    rw [norm_withLp_prod_rpow hp ψ]
    ring
  rw [heq] at he
  exact mul_le_mul_of_nonneg_left (add_le_add hl he) (rootGapSummationConstant_nonneg p)

/-- One original neighborhood carries counted roots with the canonical gap norm. -/
theorem exists_uniform_sourceCanonicalGapPair (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ, ∀ n : ℤ, N ≤ n.natAbs →
        SourceResonantRootPair hp ψ n (ξ n) (η n) ∧
        ‖sourcePeriodTwoCanonicalGap hp hp1 ψ n‖ = ‖ξ n-η n‖ := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := sourceLemma6_9_proof_canonical hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hr⟩ := hr ψ hψ
  exact ⟨ξ,η,fun n hn => ⟨(hr n hn).2.1,(hr n hn).2.2.2⟩⟩

/-- Pull an open convex neighborhood and all its cutoff data back through a continuous linear map. -/
theorem sourceUniformLinearPullback {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    (T : E →L[ℂ] F) (φ : E) (P : ℕ → F → Prop)
    (h : ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set F, IsOpen U ∧ Convex ℝ U ∧ T φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, P N ψ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set E, IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, P N (T ψ) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := h
  exact ⟨N,hN,T ⁻¹' U,ho.preimage T.continuous,hc.linear_preimage (T.restrictScalars ℝ).toLinearMap,
    hφ,by simpa using h0,fun ψ hψ => hr (T ψ) hψ⟩

/-- Weighted inputs retain the original period-two counted pair on a common neighborhood. -/
theorem exists_uniform_sourceWeightedCanonicalGapPair (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ, ∀ n : ℤ, N ≤ n.natAbs →
          SourceResonantRootPair hp (sourceWeightedPeriodTwoInput w ψ) n (ξ n) (η n) ∧
          ‖sourcePeriodTwoCanonicalGap hp hp1 (sourceWeightedPeriodTwoInput w ψ) n‖ = ‖ξ n-η n‖ := by
  exact sourceUniformLinearPullback (sourceWeightedPeriodTwoInput w) φ _
    (exists_uniform_sourceCanonicalGapPair hp hp1 (sourceWeightedPeriodTwoInput w φ))

/-- The same neighborhood supplies original coefficient control, convergent tails and the canonical gap pair. -/
theorem exists_uniform_sourceGapCoefficientData (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp w (sourceWeightedPeriodTwoInput w ψ) n) ∧
        (∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates hp w ψ N) ∧
        ∃ ξ η : ℤ → ℂ, ∀ n : ℤ, N₀ ≤ n.natAbs →
          SourceResonantRootPair hp (sourceWeightedPeriodTwoInput w ψ) n (ξ n) (η n) ∧
          ‖sourcePeriodTwoCanonicalGap hp hp1 (sourceWeightedPeriodTwoInput w ψ) n‖ = ‖ξ n-η n‖ := by
  obtain ⟨Nc,hNc,U,hoU,hcU,hφU,h0U,hstrip,htails⟩ := sourceLemma6_8_quantitative hp hp1 w φ
  obtain ⟨Nr,_,V,hoV,hcV,hφV,h0V,hroots⟩ := exists_uniform_sourceWeightedCanonicalGapPair hp hp1 w φ
  refine ⟨max Nc Nr,hNc.trans (le_max_left _ _),U ∩ V,hoU.inter hoV,
    hcU.inter hcV,⟨hφU,hφV⟩,⟨h0U,h0V⟩,?_⟩
  intro ψ hψ
  refine ⟨fun n hn => hstrip ψ hψ.1 n ((le_max_left _ _).trans hn),
    fun N hN => htails ψ hψ.1 N ((le_max_left _ _).trans hN),?_⟩
  obtain ⟨ξ,η,hr⟩ := hroots ψ hψ.2
  refine ⟨ξ,η,?_⟩
  intro n hn
  exact hr n ((le_max_right _ _).trans hn)

/-- The corrected final p.44 coefficient-sum estimate and its Lemma 6.8 budget hold for every larger cutoff on one neighborhood. -/
theorem sourceProposition6_3_coefficient_sum_corrected (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        let f := sourceWeightedPeriodTwoInput w ψ
        Summable (sourceGapLeadingPowerTail w f N) ∧ Summable (sourceGapRemainderPowerTail hp w f N) ∧
        Summable (sourceCanonicalWeightedGapPowerTail hp hp1 w f N) ∧
        (∑' n : ℤ, sourceCanonicalWeightedGapPowerTail hp hp1 w f N n) ≤ rootGapSummationConstant p *
          ((∑' n : ℤ, sourceGapLeadingPowerTail w f N n)+(∑' n : ℤ, sourceGapRemainderPowerTail hp w f N n)) ∧
        rootGapSummationConstant p *
          ((∑' n : ℤ, sourceGapLeadingPowerTail w f N n)+(∑' n : ℤ, sourceGapRemainderPowerTail hp w f N n)) ≤ rootGapBudget w ψ N := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hdata⟩ := exists_uniform_sourceGapCoefficientData hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hN
  dsimp only
  obtain ⟨hstrip,htails,ξ,η,hr⟩ := hdata ψ hψ
  obtain ⟨hsl,hse,hbudget⟩ := sourceGapCoefficientSums_le_budget hp w ψ N (htails N hN)
  have hc := sourceCanonicalGapSum_le_coefficients hp hp1 w (sourceWeightedPeriodTwoInput w ψ) N ξ η
    (fun n hn => (hr n (hN.trans hn)).1)
    (fun n hn => hstrip n (hN.trans hn))
    (fun n hn => (hr n (hN.trans hn)).2) hsl hse
  exact ⟨hsl,hse,hc.1,hc.2,hbudget⟩

/-- The corrected reciprocal-constant inequality also holds on an original unweighted source neighborhood. -/
theorem sourceProposition6_3_coefficient_sum_unweighted (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (sourceGapLeadingPowerTail SpectralWeight.one ψ N) ∧ Summable (sourceGapRemainderPowerTail hp SpectralWeight.one ψ N) ∧
        Summable (sourceCanonicalWeightedGapPowerTail hp hp1 SpectralWeight.one ψ N) ∧
        (∑' n : ℤ, sourceCanonicalWeightedGapPowerTail hp hp1 SpectralWeight.one ψ N n)/rootGapSummationConstant p ≤
          (∑' n : ℤ, sourceGapLeadingPowerTail SpectralWeight.one ψ N n)+(∑' n : ℤ, sourceGapRemainderPowerTail hp SpectralWeight.one ψ N n) := by
  have h := sourceProposition6_3_coefficient_sum_corrected hp hp1 SpectralWeight.one (unitWeightedPairEquiv φ)
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hbound⟩ := sourceUnitWeightedUniformPullback unitWeightedPairEquiv φ _ h
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hN
  have hd := hbound ψ hψ N hN
  simp only [sourceWeightedInput_unitWeightedPairEquiv] at hd
  refine ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩
  exact (div_le_iff₀ (rootGapSummationConstant_pos p)).mpr (by simpa only [mul_comm] using hd.2.2.2.1)

end NLS.ZakharovShabat
