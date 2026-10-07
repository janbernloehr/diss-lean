import NLS.ZakharovShabat.ResonantDoubleRootClosing
import NLS.ZakharovShabat.SourceFiniteGap
import NLS.ZakharovShabat.SourceAdaptedClosingMapReality
import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints

/-! # Real closed gaps force the actual center closing equations

A distant collapsed canonical gap is a double zero of the actual
resonant determinant. The source reality identity and Cauchy bounds
force both off-diagonal coefficients to vanish there. Uniqueness of
the diagonal equation identifies that endpoint with the named center.
-/

noncomputable section
set_option maxHeartbeats 400000
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One open source neighborhood and one cutoff suffice for every real closed gap. -/
theorem exists_uniform_sourceClosedGap_center_equations
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ₀ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ₀ ∈ U ∧
      ∀ φ ∈ U, IsRealType (CoeffPair.toMax p φ) → ∀ n : ℤ, N ≤ n.natAbs →
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0 →
      let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ) n
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = ζ ∧
      weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ) n ζ = 0 ∧
      weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ) n ζ = 0 := by
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
  intro φ hφ hreal n hn hgap
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
  let z := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  have hend : canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = z :=
    sub_eq_zero.mp hgap
  have hpair := hlabel.distant n (by omega)
  have hz : z ∈ refinedResonantDisk n := hpair.left_mem
  have hzs := refinedResonantDisk_subset_strip n hz
  have hspectrum (x : ℂ) (hx : x ∈ resonantStrip n) :
      resonantDeterminantExtension hp w ψ n x = 0 ↔ x = z := by
    rw [← h₂ ψ hφ₂ n (by omega) x hx]
    change x ∈ periodicSpectrum hp (weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne φ)) ↔ _
    rw [weightedBaseToPair_sourceWeightedPeriodOne,hpair.spectrum_iff x hx,hend]
    simp only [z, or_self]
  have hz0 := (hspectrum z hzs).mpr rfl
  obtain ⟨x,hx,y,hy,hx0,hy0,_,horder,_,_,_⟩ := h₃ ψ hφ₃ n (by omega)
  have hxz := (hspectrum x (refinedResonantDisk_subset_strip n hx)).mp hx0
  have hyz := (hspectrum y (refinedResonantDisk_subset_strip n hy)).mp hy0
  have htwo : analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z = 2 := by
    rw [horder z hzs,hxz,hyz]
    simp
  have hdom (x : ℂ) (hx : x ∈ resonantStrip n) : (ψ,x) ∈ weightedCorrectionDomain hp w n :=
    (h₁ n (by omega)).1 ⟨hφ₁,hx⟩
  have hbound (x : ℂ) (hx : x ∈ resonantStrip n) := (h₁ n (by omega)).2 ψ hφ₁ x hx
  have hsmall (x : ℂ) (hx : x ∈ resonantStrip n) :
      ‖weightedPotentialSquareInShift hp w ψ n x hx‖ < 1 := (hbound x hx).1.trans_lt (by norm_num)
  have ha : AnalyticOnNhd ℂ (weightedResonantAExtension hp w ψ n) (resonantStrip n) :=
    fun x hx => (analyticAt_weightedResonantAExtension hp w n (ψ,x) (hdom x hx)).comp
      (analyticAt_const.prod analyticAt_id)
  have hb : AnalyticOnNhd ℂ (weightedResonantBPlusExtension hp w ψ n) (resonantStrip n) :=
    fun x hx => (analyticAt_weightedResonantBPlusExtension hp w n (ψ,x) (hdom x hx)).comp
      (analyticAt_const.prod analyticAt_id)
  have hd : AnalyticOnNhd ℂ (weightedResonantBMinusExtension hp w ψ n) (resonantStrip n) :=
    fun x hx => (analyticAt_weightedResonantBMinusExtension hp w n (ψ,x) (hdom x hx)).comp
      (analyticAt_const.prod analyticAt_id)
  have hderiv : deriv (resonantDeterminantExtension hp w ψ n) z = 0 := by
    by_contra hne
    have hsimple := (analyticAt_resonantDeterminantExtension_spectral hp w ψ n z (hdom z hzs)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz0 hne
    have hone : analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z = 1 := by
      simp [analyticOrderNatAt,hsimple]
    omega
  have hzim : z.im = 0 := (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hreal) n).1
  have hconj : (starRingEnd ℂ) z = z := by
    apply Complex.ext <;> simp [hzim]
  have hbconj : weightedResonantBMinusExtension hp w ψ n z =
      (starRingEnd ℂ) (weightedResonantBPlusExtension hp w ψ n z) := by
    have h := weightedResonantBMinus_conj hp w 1 (by simp) ψ
      (sourceWeightedPeriodOne_hasRealitySign φ hreal) n z hzs (hsmall z hzs)
      (hsmall _ (conj_mem_resonantStrip hzs))
    simp only [one_mul,hconj] at h
    rw [weightedResonantBMinusExtension_eq hp w ψ n z hzs (hsmall z hzs),
      weightedResonantBPlusExtension_eq hp w ψ n z hzs (hsmall z hzs)]
    exact h
  have hnorm : ‖weightedResonantBPlusExtension hp w ψ n z‖ =
      ‖weightedResonantBMinusExtension hp w ψ n z‖ := by rw [hbconj,Complex.norm_conj]
  have hclose := resonant_double_zero_closing_on_refined_disk n _ _ _ ha hb hd
    (fun x hx => ⟨(hbound x hx).2.1,(hbound x hx).2.2.2,(hbound x hx).2.2.1⟩)
    z hz hnorm hz0 hderiv
  have hcenter := weightedResonantDiagonalCenter_spec hp w ψ n ha (fun x hx => (hbound x hx).2.1)
  have hzcenter := hcenter.2.2.2 z hzs hclose.1
  exact ⟨hzcenter,
    (congrArg (weightedResonantBPlusExtension hp w ψ n) hzcenter.symm).trans hclose.2.1,
    (congrArg (weightedResonantBMinusExtension hp w ψ n) hzcenter.symm).trans hclose.2.2⟩

/-- The converse of the distant center closing criterion for real sources. -/
theorem exists_sourceClosedGap_center_equations
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0 →
      let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ) n
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = ζ ∧
      weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ) n ζ = 0 ∧
      weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ) n ζ = 0 := by
  obtain ⟨N,hN,U,_,hφ,h⟩ := exists_uniform_sourceClosedGap_center_equations hp hp1 φ
  exact ⟨N,hN,h φ hφ hreal⟩

end NLS.ZakharovShabat
