import NLS.ZakharovShabat.ResonantRealGapCenter
import NLS.ZakharovShabat.SourceClosedGapCenter
import NLS.ZakharovShabat.SourcePeriodicGapTails

/-! # Uniform gap bounds for the actual source diagonal centers

The canonical counted periodic endpoints supply the real roots, including
collapsed gaps. One neighborhood and cutoff control both actual center
coefficients at every real source in that neighborhood.
-/

noncomputable section

namespace NLS.ZakharovShabat
open Set Complex
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
set_option maxHeartbeats 500000

/-- A uniform factor-two gap bound at every sufficiently distant actual center.
No estimate or spectral labeling is supplied as an external premise. -/
theorem exists_uniform_sourceResonantCenter_gap_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ₀ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ₀ ∈ U ∧
      ∀ φ ∈ U, IsRealType (CoeffPair.toMax p φ) → ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ) n
        ‖weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ) n ζ‖ ≤
          2 * ‖sourcePeriodicGapDisplacement hp hp1 φ n‖ ∧
        ‖weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ) n ζ‖ ≤
          2 * ‖sourcePeriodicGapDisplacement hp hp1 φ n‖ := by
  let w := SpectralWeight.one
  let ψ₀ := sourceWeightedPeriodOne φ₀
  obtain ⟨N₁,hN₁,U₁,ho₁,_,hφ₁,_,h₁⟩ := exists_uniform_resonantDeterminant_control hp hp1 w ψ₀
  obtain ⟨N₂,_,U₂,ho₂,_,hφ₂,_,h₂⟩ := exists_uniform_weightedDeterminant_spectral_iff hp w ψ₀
  obtain ⟨N₃,_,U₃,ho₃,_,hφ₃,_,h₃⟩ := exists_uniform_resonantRoots hp hp1 w ψ₀
  obtain ⟨N₄,_,U₄,ho₄,_,hφ₄,_,h₄⟩ := exists_uniform_canonicalPeriodicEndpoints hp hp1 w ψ₀
  refine ⟨max N₁ (max N₂ (max N₃ (N₄+1))),by omega,
    sourceWeightedPeriodOne ⁻¹' (U₁ ∩ U₂ ∩ U₃ ∩ U₄),
    (((ho₁.inter ho₂).inter ho₃).inter ho₄).preimage sourceWeightedPeriodOne.continuous,
    ⟨⟨⟨hφ₁,hφ₂⟩,hφ₃⟩,hφ₄⟩,?_⟩
  intro φ hφ hreal n hn
  rcases hφ with ⟨⟨⟨hφ₁,hφ₂⟩,hφ₃⟩,hφ₄⟩
  let ψ := sourceWeightedPeriodOne φ
  have hlabel : PeriodicEndpointLabeling hp (periodOnePotential φ) N₄
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ))
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)) := by
    have hh : ∀ hψ : weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne φ) ∈ pairParitySubspace 0,
        PeriodicEndpointLabeling hp (weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne φ)) N₄
          (canonicalPeriodicLeft hp hp1 _ hψ) (canonicalPeriodicRight hp hp1 _ hψ) :=
      fun hψ => h₄ ψ hφ₄ hψ N₄ le_rfl
    rw [weightedBaseToPair_sourceWeightedPeriodOne] at hh
    exact hh (periodOnePotential_mem φ)
  let x := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let y := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  have hpair := hlabel.distant n (by omega)
  have hx : x ∈ refinedResonantDisk n := hpair.left_mem
  have hy : y ∈ refinedResonantDisk n := hpair.right_mem
  have hxs := refinedResonantDisk_subset_strip n hx
  have hys := refinedResonantDisk_subset_strip n hy
  have hspectrum (z : ℂ) (hz : z ∈ resonantStrip n) :
      resonantDeterminantExtension hp w ψ n z = 0 ↔ z = x ∨ z = y := by
    rw [← h₂ ψ hφ₂ n (by omega) z hz]
    change z ∈ periodicSpectrum hp (weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne φ)) ↔ _
    rw [weightedBaseToPair_sourceWeightedPeriodOne,hpair.spectrum_iff z hz]
  have hx0 := (hspectrum x hxs).mpr (Or.inl rfl)
  have hy0 := (hspectrum y hys).mpr (Or.inr rfl)
  have hdom (z : ℂ) (hz : z ∈ resonantStrip n) : (ψ,z) ∈ weightedCorrectionDomain hp w n :=
    (h₁ n (by omega)).1 ⟨hφ₁,hz⟩
  have hbound (z : ℂ) (hz : z ∈ resonantStrip n) := (h₁ n (by omega)).2 ψ hφ₁ z hz
  have hsmall (z : ℂ) (hz : z ∈ resonantStrip n) :
      ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1 := (hbound z hz).1.trans_lt (by norm_num)
  have ha : AnalyticOnNhd ℂ (weightedResonantAExtension hp w ψ n) (resonantStrip n) :=
    fun z hz => (analyticAt_weightedResonantAExtension hp w n (ψ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hb : AnalyticOnNhd ℂ (weightedResonantBPlusExtension hp w ψ n) (resonantStrip n) :=
    fun z hz => (analyticAt_weightedResonantBPlusExtension hp w n (ψ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hd : AnalyticOnNhd ℂ (weightedResonantBMinusExtension hp w ψ n) (resonantStrip n) :=
    fun z hz => (analyticAt_weightedResonantBMinusExtension hp w n (ψ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hdouble (he : x = y) : deriv (resonantDeterminantExtension hp w ψ n) x = 0 := by
    obtain ⟨r₁,hr₁,r₂,hr₂,hr₁0,hr₂0,_,horder,_,_,_⟩ := h₃ ψ hφ₃ n (by omega)
    have hr₁x : r₁ = x := by
      have h := (hspectrum r₁ (refinedResonantDisk_subset_strip n hr₁)).mp hr₁0
      simpa only [← he,or_self] using h
    have hr₂x : r₂ = x := by
      have h := (hspectrum r₂ (refinedResonantDisk_subset_strip n hr₂)).mp hr₂0
      simpa only [← he,or_self] using h
    have htwo : analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) x = 2 := by
      rw [horder x hxs,hr₁x,hr₂x]
      simp
    by_contra hne
    have hsimple := (analyticAt_resonantDeterminantExtension_spectral hp w ψ n x (hdom x hxs)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hx0 hne
    have hone : analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) x = 1 := by
      simp [analyticOrderNatAt,hsimple]
    omega
  have hrealdata (z : ℂ) (hz : z ∈ resonantStrip n) (hzim : z.im = 0) :
      (weightedResonantAExtension hp w ψ n z).im = 0 ∧
        ‖weightedResonantBPlusExtension hp w ψ n z‖ = ‖weightedResonantBMinusExtension hp w ψ n z‖ := by
    have hconj : (starRingEnd ℂ) z = z := by
      apply Complex.ext <;> simp [hzim]
    have hA := weightedResonantA_conj hp w 1 (by simp) ψ
      (sourceWeightedPeriodOne_hasRealitySign φ hreal) n z hz (hsmall z hz)
      (hsmall _ (conj_mem_resonantStrip hz))
    have hB := weightedResonantBMinus_conj hp w 1 (by simp) ψ
      (sourceWeightedPeriodOne_hasRealitySign φ hreal) n z hz (hsmall z hz)
      (hsmall _ (conj_mem_resonantStrip hz))
    simp only [one_mul,hconj] at hA hB
    constructor
    · rw [weightedResonantAExtension_eq hp w ψ n z hz (hsmall z hz)]
      have hi := congrArg Complex.im hA
      simp only [Complex.conj_im] at hi
      linarith
    · rw [weightedResonantBMinusExtension_eq hp w ψ n z hz (hsmall z hz),
        weightedResonantBPlusExtension_eq hp w ψ n z hz (hsmall z hz),hB,Complex.norm_conj]
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hreal) n
  have hrx := hrealdata x hxs him.1
  have hry := hrealdata y hys him.2
  have hcenter := weightedResonantDiagonalCenter_spec hp w ψ n ha (fun z hz => (hbound z hz).2.1)
  have h := norm_resonant_offDiagonal_center_le_gap n _ _ _ ha hb hd
    (fun z hz => ⟨(hbound z hz).2.1,(hbound z hz).2.2.2,(hbound z hz).2.2.1⟩)
    x y (weightedResonantDiagonalCenter hp w ψ n) hx hy hcenter.1 hcenter.2.2.1
    him.1 him.2 hrx.1 hry.1 hrx.2 hry.2 hx0 hy0 hdouble
  have hgap : ‖x-y‖ = ‖sourcePeriodicGapDisplacement hp hp1 φ n‖ := by
    rw [sourcePeriodicGapDisplacement_apply]
    change ‖x-y‖ = ‖y-x‖
    exact norm_sub_rev x y
  simpa only [hgap] using h
end NLS.ZakharovShabat
