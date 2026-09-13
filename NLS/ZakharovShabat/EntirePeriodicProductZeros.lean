import NLS.ZakharovShabat.EntirePeriodicProducts
import NLS.ComplexAnalysis.LimitNonvanishing

/-!
# Exact zeros of the entire periodic product

Every polynomial cutoff has no zeros outside the actual periodic spectrum.
Boundary reciprocal bounds preserve this property at the filled free lattice
points. Conversely each original spectral value makes all sufficiently large
cutoffs vanish. Thus the entire product has exactly the actual spectral zero set.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal finite cutoffs have no zeros outside the original spectrum. -/
theorem periodicSpectralPolynomialCutoff_ne_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (M : ℕ) (z : ℂ) (hz : z ∉ periodicSpectrum hp (weightedBaseToPair w φ)) :
    periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M z ≠ 0 := by
  have hc : centralPeriodicPolynomial hp (weightedBaseToPair w φ) N z ≠ 0 := by
    intro h
    exact hz ((mem_centralPeriodicSpectrum hp _ N z).mp
      ((centralPeriodicPolynomial_eq_zero_iff hp _ N z).mp h)).1
  unfold periodicSpectralPolynomialCutoff
  apply mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) hc) (centralSpectralNormalization_ne_zero N))
  apply Finset.prod_ne_zero_iff.mpr
  intro n hn
  have hn' : N < n.natAbs := by
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
    omega
  have hpair := hr n hn'
  have hl := (hpair.spectrum_iff (ξ n) (refinedResonantDisk_subset_strip n hpair.left_mem)).mpr (Or.inl rfl)
  have hr' := (hpair.spectrum_iff (η n) (refinedResonantDisk_subset_strip n hpair.right_mem)).mpr (Or.inr rfl)
  rw [spectralPairFactor_eq_div]
  apply div_ne_zero _ (spectralPairDenominator_ne_zero n)
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (fun he => hz (he ▸ hl))
  · exact sub_ne_zero.mpr (fun he => hz (he ▸ hr'))

/-- Each original spectral value is a zero of every sufficiently large literal cutoff. -/
theorem eventually_periodicSpectralPolynomialCutoff_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (z : ℂ) (hz : z ∈ periodicSpectrum hp (weightedBaseToPair w φ)) :
    ∀ᶠ M : ℕ in atTop, periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M z = 0 := by
  rcases (hc.mem_spectrum_iff_central_or_disk z).mp hz with hz | ⟨n,hn,_⟩
  · apply Filter.Eventually.of_forall
    intro M
    have hzero := (centralPeriodicPolynomial_eq_zero_iff hp _ N z).mpr hz
    simp only [periodicSpectralPolynomialCutoff, hzero, mul_zero, zero_div, zero_mul]
  · have hmem := hn.2
    rw [(hr n hn.1).enclosed_eq] at hmem
    have hroot : ξ n = z ∨ η n = z := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm] using hmem
    filter_upwards [eventually_ge_atTop n.natAbs] with M hM
    unfold periodicSpectralPolynomialCutoff
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (show n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \
      Finset.Icc (-(N : ℤ)) (N : ℤ) from by
        simp only [Finset.mem_sdiff, Finset.mem_Icc]
        constructor
        · constructor <;> omega
        · omega)
    rcases hroot with hroot | hroot <;> simp [spectralPairFactor, hroot]

/-- Filling the lattice adds no extra zeros, by reciprocal maximum-modulus bounds on resolvent discs. -/
theorem entirePeriodicProduct_ne_zero_of_not_mem (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (z : ℂ) (hz : z ∉ periodicSpectrum hp (weightedBaseToPair w φ)) :
    entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η z ≠ 0 := by
  obtain ⟨R,hR,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isClosed_periodicSpectrum hp (weightedBaseToPair w φ)).isOpen_compl.mem_nhds hz)
  obtain ⟨r,hr0,hrR,hs⟩ := NLS.ComplexAnalysis.exists_small_sphere_subset_compl_countable
    freeLattice countable_freeLattice z R hR
  have hout (a : ℂ) (ha : a ∈ closedBall z r) : a ∉ periodicSpectrum hp (weightedBaseToPair w φ) :=
    hball (closedBall_subset_closedBall hrR.le ha)
  have hconv := tendstoLocallyUniformlyOn_entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η hξ hη
  have han := analyticOnNhd_entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η hξ hη
  apply NLS.ComplexAnalysis.limit_ne_zero_of_nonzero_on_closedBall _ _ z r hr0
    (fun M => differentiableOn_univ.mp (analyticOnNhd_periodicSpectralPolynomialCutoff hp _ N ξ η M).differentiableOn)
    (fun M a ha => periodicSpectralPolynomialCutoff_ne_zero hp w φ N ξ η hr M a (hout a ha))
    (han.continuousOn.mono (Set.subset_univ _))
  · intro a ha hzero
    rw [entirePeriodicProduct_eq_offLattice hp _ N ξ η hξ hη a (hs ha)] at hzero
    exact hout a (sphere_subset_closedBall ha)
      ((periodicSpectralProductOffLattice_eq_zero_iff hp w φ N ξ η hξ hη hc hr ⟨a,hs ha⟩).mp hzero)
  · exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z r)).mp
      (hconv.mono (Set.subset_univ _))
  · exact hconv.tendsto_at (Set.mem_univ z)

/-- The entire product has exactly the original periodic spectrum as its zeros, including free lattice points. -/
theorem entirePeriodicProduct_eq_zero_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) (z : ℂ) :
    entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η z = 0 ↔
      z ∈ periodicSpectrum hp (weightedBaseToPair w φ) := by
  constructor
  · intro hzero
    by_contra hz
    exact entirePeriodicProduct_ne_zero_of_not_mem hp w φ N ξ η hξ hη hc hr z hz hzero
  · intro hz
    have he := eventually_periodicSpectralPolynomialCutoff_eq_zero hp w φ N ξ η hc hr z hz
    exact tendsto_nhds_unique
      ((tendstoLocallyUniformlyOn_entirePeriodicProduct hp _ N ξ η hξ hη).tendsto_at (Set.mem_univ z))
      (tendsto_const_nhds.congr' (Filter.Eventually.mono he (fun _ h => h.symm)))

end NLS.ZakharovShabat
