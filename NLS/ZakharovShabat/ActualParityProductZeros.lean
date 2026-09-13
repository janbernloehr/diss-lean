import NLS.ZakharovShabat.ParityProductsOffLattice
import NLS.ZakharovShabat.EntirePeriodicProductOrders

/-!
# Exact whole-plane zeros of the actual parity products

Finite cutoffs vanish at precisely their selected roots. Original spectral
isolation and reciprocal maximum-modulus bounds prevent new zeros when the
free lattice is filled. Every actual parity eigenvalue is eventually a cutoff
zero, hence a zero of the locally uniform entire limit.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A paired factor has exactly its two indicated roots, regardless of collisions. -/
theorem spectralPairFactor_eq_zero_iff (ξ η : ℤ → ℂ) (z : ℂ) (n : ℤ) :
    spectralPairFactor ξ η z n = 0 ↔ ξ n = z ∨ η n = z := by
  rw [spectralPairFactor_eq_div]
  simp [div_eq_zero_iff, spectralPairDenominator_ne_zero, mul_eq_zero, sub_eq_zero]

/-- An affine-indexed root is eventually present in every symmetric cutoff. -/
theorem eventually_parityPairFactors_eq_zero (ξ η : ℤ → ℂ) (r : ℤ) (z : ℂ)
    (hz : ∃ n : ℤ, ξ (2*n+r) = z ∨ η (2*n+r) = z) :
    ∀ᶠ M : ℕ in atTop, (∏ n ∈ Finset.Icc (-(M : ℤ)) M, spectralPairFactor ξ η z (2*n+r)) = 0 := by
  obtain ⟨n, hn⟩ := hz
  filter_upwards [eventually_ge_atTop n.natAbs] with M hM
  apply Finset.prod_eq_zero (i := n)
  · simp only [Finset.mem_Icc]
    constructor <;> omega
  · exact (spectralPairFactor_eq_zero_iff ξ η z (2*n+r)).mpr hn

private theorem parity_limit_ne_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (hr : r = 0 ∨ r = 1)
    (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (hF : ∀ M, Differentiable ℂ (F M)) (hg : Continuous g)
    (hconv : TendstoLocallyUniformlyOn F g atTop Set.univ)
    (hcut : ∀ M a, ¬ 0 < parityAlgebraicMultiplicity hp φ r a → F M a ≠ 0)
    (haway : ∀ a, a ∉ freeLattice → (g a = 0 ↔ 0 < parityAlgebraicMultiplicity hp φ r a))
    (z : ℂ) (hz : ¬ 0 < parityAlgebraicMultiplicity hp φ r z) : g z ≠ 0 := by
  obtain ⟨R,hR,hiso⟩ := exists_periodicSpectrum_isolating_closedBall hp φ z
  obtain ⟨ρ,hρ,hρR,hs⟩ := NLS.ComplexAnalysis.exists_small_sphere_subset_compl_countable
    freeLattice countable_freeLattice z R hR
  have hout (a : ℂ) (ha : a ∈ closedBall z ρ) : ¬ 0 < parityAlgebraicMultiplicity hp φ r a := by
    intro hm
    have hf : 0 < periodicAlgebraicMultiplicity hp φ a := by
      rw [periodicAlgebraicMultiplicity_eq_parity_sum hp φ hφ a]
      rcases hr with rfl | rfl <;> omega
    have he := hiso a (closedBall_subset_closedBall hρR.le ha)
      ((periodicAlgebraicMultiplicity_pos_iff hp φ a).mp hf)
    exact hz (he ▸ hm)
  apply NLS.ComplexAnalysis.limit_ne_zero_of_nonzero_on_closedBall F g z ρ hρ hF
    (fun M a ha => hcut M a (hout a ha)) hg.continuousOn
    (fun a ha he => hout a (sphere_subset_closedBall ha) ((haway a (hs ha)).mp he))
  · exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z ρ)).mp
      (hconv.mono (Set.subset_univ _))
  · exact hconv.tendsto_at (Set.mem_univ z)

/-- The completed even product has exactly the original even-sector eigenvalues on the whole plane. -/
theorem CompletePeriodicParityPairs.evenProduct_eq_zero_iff {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) :
    evenSpectralPairProduct ξ η z = 0 ↔ 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 0 z := by
  have hconv := tendstoLocallyUniformlyOn_evenSpectralPairProduct hp ξ η h.left_displacement h.right_displacement
  constructor
  · intro he
    by_contra hz
    apply parity_limit_ne_zero hp _ h.even_potential 0 (Or.inl rfl)
      (fun M z => evenSpectralPairCutoff ξ η z M) (evenSpectralPairProduct ξ η)
      (fun M => differentiableOn_univ.mp (analyticOnNhd_paritySpectralCutoffs ξ η M).1.differentiableOn)
      (continuousOn_univ.mp (analyticOnNhd_evenSpectralPairProduct hp ξ η h.left_displacement h.right_displacement).continuousOn)
      hconv ?_ (fun a ha => (h.products_zero_offLattice a ha).1) z hz he
    intro M a ha hzero
    have hf : (∏ n ∈ Finset.Icc (-(M : ℤ)) M, spectralPairFactor ξ η a (2*n)) = 0 := neg_eq_zero.mp hzero
    obtain ⟨n, _, hn⟩ := Finset.prod_eq_zero_iff.mp hf
    apply ha
    apply (h.affine_root_iff 0 (Or.inl rfl) a).mp
    exact ⟨n, by simpa only [add_zero] using (spectralPairFactor_eq_zero_iff ξ η a (2*n)).mp hn⟩
  · intro hz
    have he := eventually_parityPairFactors_eq_zero ξ η 0 z ((h.affine_root_iff 0 (Or.inl rfl) z).mpr hz)
    have he' : ∀ᶠ M : ℕ in atTop, evenSpectralPairCutoff ξ η z M = 0 := by
      filter_upwards [he] with M hM
      simpa only [evenSpectralPairCutoff, add_zero, neg_eq_zero] using hM
    exact tendsto_nhds_unique (hconv.tendsto_at (Set.mem_univ z))
      (tendsto_const_nhds.congr' (he'.mono (fun _ he => he.symm)))

/-- The completed odd product has exactly the original odd-sector eigenvalues on the whole plane. -/
theorem CompletePeriodicParityPairs.oddProduct_eq_zero_iff {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) :
    oddSpectralPairProduct ξ η z = 0 ↔ 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 1 z := by
  have hconv := tendstoLocallyUniformlyOn_oddSpectralPairProduct hp ξ η h.left_displacement h.right_displacement
  constructor
  · intro he
    by_contra hz
    apply parity_limit_ne_zero hp _ h.even_potential 1 (Or.inr rfl)
      (fun M z => oddSpectralPairCutoff ξ η z M) (oddSpectralPairProduct ξ η)
      (fun M => differentiableOn_univ.mp (analyticOnNhd_paritySpectralCutoffs ξ η M).2.differentiableOn)
      (continuousOn_univ.mp (analyticOnNhd_oddSpectralPairProduct hp ξ η h.left_displacement h.right_displacement).continuousOn)
      hconv ?_ (fun a ha => (h.products_zero_offLattice a ha).2) z hz he
    intro M a ha hzero
    have hf : (∏ n ∈ Finset.Icc (-(M : ℤ)) M, spectralPairFactor ξ η a (2*n+1)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    obtain ⟨n, _, hn⟩ := Finset.prod_eq_zero_iff.mp hf
    exact ha ((h.affine_root_iff 1 (Or.inr rfl) a).mp
      ⟨n, (spectralPairFactor_eq_zero_iff ξ η a (2*n+1)).mp hn⟩)
  · intro hz
    have he := eventually_parityPairFactors_eq_zero ξ η 1 z ((h.affine_root_iff 1 (Or.inr rfl) z).mpr hz)
    have he' : ∀ᶠ M : ℕ in atTop, oddSpectralPairCutoff ξ η z M = 0 := by
      filter_upwards [he] with M hM
      simp only [oddSpectralPairCutoff, hM, mul_zero]
    exact tendsto_nhds_unique (hconv.tendsto_at (Set.mem_univ z))
      (tendsto_const_nhds.congr' (he'.mono (fun _ he => he.symm)))

end NLS.ZakharovShabat
