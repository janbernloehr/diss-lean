import NLS.ZakharovShabat.FullCutoffRootMajorants
import NLS.ZakharovShabat.PeriodicRootSequence

/-! # Sharper corrected Section 6 cutoff estimates

The original source norms and spectral data are retained. The additive leading-tail
term is not removed; the refuted printed estimates are not asserted.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The same counted root sequences satisfy corrected bounds at the full Fourier cutoff. -/
theorem exists_uniform_resonantRoots_with_displacement_sum_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs →
            ξ n ∈ refinedResonantDisk n ∧ η n ∈ refinedResonantDisk n ∧
            resonantDeterminantExtension hp w ψ n (ξ n) = 0 ∧
            resonantDeterminantExtension hp w ψ n (η n) = 0 ∧
            (∀ z ∈ resonantStrip n, resonantDeterminantExtension hp w ψ n z = 0 ↔ z = ξ n ∨ z = η n) ∧
            (∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z =
              ({ξ n,η n} : Multiset ℂ).count z) ∧
            ‖ξ n-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧ ‖η n-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧
            ‖ξ n-η n‖^2 ≤ 6*resonantBProductSup hp w ψ n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ rootDisplacementBudget_fullCutoff w ψ N := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,hroots⟩ := exists_uniform_resonantRoots hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,hmajorant⟩ := exists_uniform_resonantDisplacementMajorant_fullCutoff hp hp1 w φ
  let N₀ := max N₁ N₂
  refine ⟨N₀,hN₁.trans (le_max_left _ _),U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro ψ hψ
  have he : ∀ n : ℤ, ∃ x y : ℂ, N₀ ≤ n.natAbs →
      x ∈ refinedResonantDisk n ∧ y ∈ refinedResonantDisk n ∧
      resonantDeterminantExtension hp w ψ n x = 0 ∧ resonantDeterminantExtension hp w ψ n y = 0 ∧
      (∀ z ∈ resonantStrip n, resonantDeterminantExtension hp w ψ n z = 0 ↔ z = x ∨ z = y) ∧
      (∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z = ({x,y} : Multiset ℂ).count z) ∧
      ‖x-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧ ‖y-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧
      ‖x-y‖^2 ≤ 6*resonantBProductSup hp w ψ n := by
    intro n
    by_cases hn : N₀ ≤ n.natAbs
    · obtain ⟨x,hx,y,hy,hdata⟩ := hroots ψ hψ.1 n ((le_max_left _ _).trans hn)
      exact ⟨x,y,fun _ => ⟨hx,hy,hdata⟩⟩
    · exact ⟨(Real.pi : ℂ)*n,(Real.pi : ℂ)*n,fun h => (hn h).elim⟩
  choose ξ η hdata using he
  refine ⟨ξ,η,hdata,?_⟩
  intro N hN
  have hmaj := hmajorant ψ hψ.2 N ((le_max_right _ _).trans hN)
  have hbound (n : ℤ) (hn : N ≤ n.natAbs) :
      ‖ξ n-(Real.pi : ℂ)*n‖^p.toReal + ‖η n-(Real.pi : ℂ)*n‖^p.toReal ≤ resonantDisplacementMajorant hp w ψ n := by
    have hr := hdata n (hN.trans hn)
    exact (hmaj.2.2 n hn).2 (ξ n) (refinedResonantDisk_subset_strip n hr.1)
      (η n) (refinedResonantDisk_subset_strip n hr.2.1) hr.2.2.1 hr.2.2.2.1
  obtain ⟨hs,hb⟩ := rootDisplacementPowerTail_summable_and_le p N ξ η
    (resonantDisplacementMajorant hp w ψ) hmaj.1 hbound
  exact ⟨hs,hb.trans hmaj.2.1⟩

/-- The same counted root sequences satisfy corrected bounds at the full Fourier cutoff. -/
theorem exists_uniform_resonantRoots_with_power_sums_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs →
            ξ n ∈ refinedResonantDisk n ∧ η n ∈ refinedResonantDisk n ∧
            resonantDeterminantExtension hp w ψ n (ξ n) = 0 ∧
            resonantDeterminantExtension hp w ψ n (η n) = 0 ∧
            (∀ z ∈ resonantStrip n, resonantDeterminantExtension hp w ψ n z = 0 ↔ z = ξ n ∨ z = η n) ∧
            (∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z =
              ({ξ n,η n} : Multiset ℂ).count z) ∧
            ‖ξ n-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧ ‖η n-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧
            ‖ξ n-η n‖^2 ≤ 6*resonantBProductSup hp w ψ n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ rootDisplacementBudget_fullCutoff w ψ N ∧
            Summable (rootGapPowerTail p w N ξ η) ∧
            (∑' n : ℤ, rootGapPowerTail p w N ξ η n) ≤ rootGapBudget_fullCutoff w ψ N := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,hroots⟩ := exists_uniform_resonantRoots_with_displacement_sum_fullCutoff hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,hmajorant⟩ := exists_uniform_resonantGapMajorant_fullCutoff hp hp1 w φ
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,
    ⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hdata,hdisp⟩ := hroots ψ hψ.1
  refine ⟨ξ,η,(fun n hn => hdata n (by omega)),?_⟩
  intro N hN
  have hmaj := hmajorant ψ hψ.2 N (by omega)
  have hbound (n : ℤ) (hn : N ≤ n.natAbs) :
      (w (2*n)*‖ξ n-η n‖)^p.toReal ≤ resonantGapMajorant hp w ψ n := by
    have hr := hdata n (by omega)
    exact hmaj.2.2 n hn (ξ n) (refinedResonantDisk_subset_strip n hr.1)
      (η n) (refinedResonantDisk_subset_strip n hr.2.1) hr.2.2.1 hr.2.2.2.1
  obtain ⟨hs,hb⟩ := rootGapPowerTail_summable_and_le p w N ξ η
    (resonantGapMajorant hp w ψ) hmaj.1 hbound
  exact ⟨(hdisp N (by omega)).1,(hdisp N (by omega)).2,hs,hb.trans hmaj.2.1⟩

/-- The same counted root sequences satisfy corrected bounds at the full Fourier cutoff. -/
theorem exists_uniform_periodicRoots_with_power_sums_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n)) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ rootDisplacementBudget_fullCutoff w ψ N ∧
            Summable (rootGapPowerTail p w N ξ η) ∧
            (∑' n : ℤ, rootGapPowerTail p w N ξ η n) ≤ rootGapBudget_fullCutoff w ψ N := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,hroots⟩ := exists_uniform_resonantRoots_with_power_sums_fullCutoff hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,hspec⟩ := exists_uniform_weightedDeterminant_spectral_iff hp w φ
  obtain ⟨N₃,U₃,ho₃,hc₃,hφ₃,h0₃,hcount⟩ := exists_uniform_disk_multiplicity_two hp (weightedBaseToPair w φ)
    (r := Real.pi/4) (by positivity) le_rfl
  let V := (weightedBaseToPair (p := p) w) ⁻¹' U₃
  have hoV : IsOpen V := ho₃.preimage (weightedBaseToPair w).continuous
  have hcV : Convex ℝ V := hc₃.linear_preimage ((weightedBaseToPair (p := p) w).restrictScalars ℝ).toLinearMap
  refine ⟨max N₁ (max N₂ N₃),hN₁.trans (le_max_left _ _),(U₁ ∩ U₂) ∩ V,
    (ho₁.inter ho₂).inter hoV,(hc₁.inter hc₂).inter hcV,⟨⟨hφ₁,hφ₂⟩,hφ₃⟩,
    ⟨⟨h0₁,h0₂⟩,by simpa [V] using h0₃⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hr,htail⟩ := hroots ψ hψ.1.1
  refine ⟨ξ,η,?_,fun N hN => htail N (by omega)⟩
  intro n hn
  have hpair := hr n (by omega)
  have hs (z : ℂ) (hz : z ∈ resonantStrip n) :
      z ∈ periodicSpectrum hp (weightedBaseToPair w ψ) ↔ z = ξ n ∨ z = η n :=
    (hspec ψ hψ.1.2 n (by omega) z hz).trans (hpair.2.2.2.2.1 z hz)
  have hcounts := hcount (weightedBaseToPair w ψ) hψ.2 n (by omega)
  have hset := enclosedPeriodicSpectrum_eq_rootPair hp _ n (ξ n) (η n) hpair.1 hpair.2.1 hs
  have htrace := contourMidpoint_squaredGap_eq_pair hp (weightedBaseToPair w ψ) _ _ (by positivity)
    hcounts.1 hcounts.2.1 (ξ n) (η n) hset
  exact {
    left_mem := hpair.1
    right_mem := hpair.2.1
    spectrum_iff := hs
    multiplicity_eq_count := periodicAlgebraicMultiplicity_eq_rootPair_count hp _ n (ξ n) (η n)
      hpair.1 hpair.2.1 hs hcounts.2.2
    analyticOrder_eq_multiplicity := analyticOrderNatAt_eq_periodicAlgebraicMultiplicity_of_pair hp w ψ n
      (ξ n) (η n) hpair.1 hpair.2.1 hs hcounts.2.2 hpair.2.2.2.2.2.1
    midpoint_eq := htrace.1
    squaredGap_eq := htrace.2.1
    left_bound := hpair.2.2.2.2.2.2.1
    right_bound := hpair.2.2.2.2.2.2.2.1
    gap_le := hpair.2.2.2.2.2.2.2.2 }

end NLS.ZakharovShabat
