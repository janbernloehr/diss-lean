import NLS.ZakharovShabat.ParityCutoffOrders

/-!
# Original multiplicities of the entire parity products

Spectral isolation and Rouché stability pass the exact eventual cutoff orders
to the entire limits, retaining finite orders at every point of the plane.
These orders are the dimensions of the original parity root spaces.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Positive parity multiplicity implies membership in the full original spectrum. -/
theorem mem_periodicSpectrum_of_parityMultiplicity_pos (hp : p ≠ ⊤) (φ : PairSpace p)
    (r : ℤ) (z : ℂ) (hz : 0 < parityAlgebraicMultiplicity hp φ r z) :
    z ∈ periodicSpectrum hp φ := by
  by_contra hn
  rw [parityAlgebraicMultiplicity_eq_zero_of_not_mem hp φ r z hn] at hz
  omega

/-- Every zero of any even cutoff belongs to the original even spectrum. -/
theorem CompletePeriodicParityPairs.evenCutoff_zero_multiplicity_pos {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (M : ℕ) (z : ℂ)
    (hz : evenSpectralPairCutoff ξ η z M = 0) :
    0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 0 z := by
  have hf : (∏ n ∈ Finset.Icc (-(M : ℤ)) M, spectralPairFactor ξ η z (2*n)) = 0 := neg_eq_zero.mp hz
  obtain ⟨n, _, hn⟩ := Finset.prod_eq_zero_iff.mp hf
  apply (h.affine_root_iff 0 (Or.inl rfl) z).mp
  exact ⟨n, by simpa only [add_zero] using (spectralPairFactor_eq_zero_iff ξ η z (2*n)).mp hn⟩

/-- Every zero of any odd cutoff belongs to the original odd spectrum. -/
theorem CompletePeriodicParityPairs.oddCutoff_zero_multiplicity_pos {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (M : ℕ) (z : ℂ)
    (hz : oddSpectralPairCutoff ξ η z M = 0) :
    0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 1 z := by
  have hf : (∏ n ∈ Finset.Icc (-(M : ℤ)) M, spectralPairFactor ξ η z (2*n+1)) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (by norm_num)
  obtain ⟨n, _, hn⟩ := Finset.prod_eq_zero_iff.mp hf
  exact (h.affine_root_iff 1 (Or.inr rfl) z).mp
    ⟨n, (spectralPairFactor_eq_zero_iff ξ η z (2*n+1)).mp hn⟩

private theorem parity_limit_order (hp : p ≠ ⊤) (φ : PairSpace p)
    (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hF : ∀ M, AnalyticOnNhd ℂ (F M) Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hconv : TendstoLocallyUniformlyOn F g atTop Set.univ)
    (hFz : ∀ M a, F M a = 0 → a ∈ periodicSpectrum hp φ)
    (hgz : ∀ a, g a = 0 → a ∈ periodicSpectrum hp φ)
    (z : ℂ) (m : ℕ) (horder : ∀ᶠ M : ℕ in atTop, analyticOrderAt (F M) z = (m : ℕ∞)) :
    analyticOrderAt g z = (m : ℕ∞) := by
  obtain ⟨r,hr,hiso⟩ := exists_periodicSpectrum_isolating_closedBall hp φ z
  have hgiso : ∀ a ∈ closedBall z r, g a = 0 → a = z :=
    fun a ha ha0 => hiso a ha (hgz a ha0)
  have hstab := NLS.ComplexAnalysis.eventually_analyticOrderNatAt_eq_of_isolated F g z r hr
    (fun M => (hF M).mono (Set.subset_univ _)) (hg.mono (Set.subset_univ _))
    (fun M a ha ha0 => hiso a ha (hFz M a ha0)) hgiso
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z r)).mp
      (hconv.mono (Set.subset_univ _)))
  obtain ⟨M,hM,hm⟩ := (hstab.and horder).exists
  have hn : analyticOrderNatAt (F M) z = m := by
    simpa only [analyticOrderNatAt, ENat.toNat_natCast] using congrArg ENat.toNat hm
  have hfin := NLS.ComplexAnalysis.analyticOrderAt_ne_top_of_isolated g z r hr
    (hg.mono (Set.subset_univ _)) hgiso
  rw [← Nat.cast_analyticOrderNatAt hfin, hM.symm.trans hn]

/-- The entire even product has exactly the original even root-space multiplicity everywhere. -/
theorem CompletePeriodicParityPairs.evenProduct_order {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) :
    analyticOrderAt (evenSpectralPairProduct ξ η) z =
      (parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 0 z : ℕ∞) := by
  apply parity_limit_order hp (weightedBaseToPair w φ) (fun M t => evenSpectralPairCutoff ξ η t M)
    (evenSpectralPairProduct ξ η) (fun M => (analyticOnNhd_paritySpectralCutoffs ξ η M).1)
    (analyticOnNhd_evenSpectralPairProduct hp ξ η h.left_displacement h.right_displacement)
    (tendstoLocallyUniformlyOn_evenSpectralPairProduct hp ξ η h.left_displacement h.right_displacement)
    (fun M a ha => mem_periodicSpectrum_of_parityMultiplicity_pos hp _ 0 a
      (h.evenCutoff_zero_multiplicity_pos M a ha))
    (fun a ha => mem_periodicSpectrum_of_parityMultiplicity_pos hp _ 0 a
      ((h.evenProduct_eq_zero_iff a).mp ha))
  exact (h.eventually_cutoff_orders z).mono (fun _ hM => hM.1)

/-- The entire odd product has exactly the original odd root-space multiplicity everywhere. -/
theorem CompletePeriodicParityPairs.oddProduct_order {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) :
    analyticOrderAt (oddSpectralPairProduct ξ η) z =
      (parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 1 z : ℕ∞) := by
  apply parity_limit_order hp (weightedBaseToPair w φ) (fun M t => oddSpectralPairCutoff ξ η t M)
    (oddSpectralPairProduct ξ η) (fun M => (analyticOnNhd_paritySpectralCutoffs ξ η M).2)
    (analyticOnNhd_oddSpectralPairProduct hp ξ η h.left_displacement h.right_displacement)
    (tendstoLocallyUniformlyOn_oddSpectralPairProduct hp ξ η h.left_displacement h.right_displacement)
    (fun M a ha => mem_periodicSpectrum_of_parityMultiplicity_pos hp _ 1 a
      (h.oddCutoff_zero_multiplicity_pos M a ha))
    (fun a ha => mem_periodicSpectrum_of_parityMultiplicity_pos hp _ 1 a
      ((h.oddProduct_eq_zero_iff a).mp ha))
  exact (h.eventually_cutoff_orders z).mono (fun _ hM => hM.2)

/-- Multiplying the parity products recovers the full spectral multiplicity at every point. -/
theorem CompletePeriodicParityPairs.parityProduct_mul_order {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) :
    analyticOrderAt (evenSpectralPairProduct ξ η * oddSpectralPairProduct ξ η) z =
      (periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z : ℕ∞) := by
  rw [analyticOrderAt_mul
    ((analyticOnNhd_evenSpectralPairProduct hp ξ η h.left_displacement h.right_displacement) z (Set.mem_univ z))
    ((analyticOnNhd_oddSpectralPairProduct hp ξ η h.left_displacement h.right_displacement) z (Set.mem_univ z)),
    h.evenProduct_order z, h.oddProduct_order z,
    periodicAlgebraicMultiplicity_eq_parity_sum hp _ h.even_potential z, Nat.cast_add]

end NLS.ZakharovShabat
