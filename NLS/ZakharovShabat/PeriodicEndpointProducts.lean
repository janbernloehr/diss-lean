import NLS.ZakharovShabat.CanonicalPeriodicEndpoints
import NLS.ZakharovShabat.CanonicalPeriodicProduct
import NLS.ZakharovShabat.EntireSpectralPairProducts

/-!
# Full products of canonical periodic endpoints

The full central multiset suffices to identify every large literal cutoff
with the intrinsic periodic polynomial. No choice of central parity groups
is needed. Hence every complete endpoint labeling has the canonical product.
-/

noncomputable section
open Filter Topology Set
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full central root multiset gives its original characteristic polynomial. -/
theorem prod_centralPeriodicRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (z : ℂ) :
    ((centralPeriodicRoots hp φ N).map (fun ζ => ζ-z)).prod = centralPeriodicPolynomial hp φ N z := by
  rw [Finset.prod_multiset_map_count]
  have hs : (centralPeriodicRoots hp φ N).toFinset = centralPeriodicSpectrum hp φ N := by
    ext ζ
    simp only [Multiset.mem_toFinset,mem_centralPeriodicRoots]
  rw [hs]
  apply Finset.prod_congr rfl
  intro ζ hζ
  rw [count_centralPeriodicRoots,if_pos hζ]

/-- Every full central pairing reproduces the intrinsic polynomial, including multiplicities. -/
theorem CentralPeriodicLabeling.prod_eq {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CentralPeriodicLabeling hp φ N ξ η) (z : ℂ) :
    (∏ n ∈ Finset.Icc (-(N : ℤ)) N, (ξ n-z)*(η n-z)) = centralPeriodicPolynomial hp φ N z := by
  have hm := prod_centralPeriodicRoots hp φ N z
  rw [← h.roots] at hm
  have he (s : Finset ℤ) : ((∑ n ∈ s, ({ξ n,η n} : Multiset ℂ)).map (fun ζ => ζ-z)).prod =
      ∏ n ∈ s, (ξ n-z)*(η n-z) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
      have hpair : (({ξ n,η n} : Multiset ℂ).map (fun ζ => ζ-z)).prod = (ξ n-z)*(η n-z) := by simp
      rw [Finset.sum_insert hn,Multiset.map_add,Multiset.prod_add,hpair,ih,Finset.prod_insert hn]
  rwa [he] at hm

/-- Every sufficiently large endpoint cutoff is the normalized intrinsic central polynomial. -/
theorem PeriodicEndpointLabeling.fullCutoff_eq_normalizedCentral {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η)
    (K : ℕ) (hK : N ≤ K) (z : ℂ) :
    spectralPairPartialProduct ξ η z K = normalizedCentralPeriodicPolynomial hp φ K z := by
  simp only [spectralPairPartialProduct,spectralPairFactor_eq_div,Finset.prod_div_distrib,
    (h.central_at_larger_cutoff K hK).prod_eq z,normalizedCentralPeriodicPolynomial,
    centralSpectralNormalization]
  ring

/-- The full entire product is intrinsic for every complete endpoint labeling. -/
theorem PeriodicEndpointLabeling.fullProduct_eq_canonical {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η) :
    entireSpectralPairProduct ξ η = canonicalPeriodicProduct hp φ := by
  funext z
  have ht := (tendstoLocallyUniformlyOn_entireSpectralPairProduct hp ξ η
    h.left_displacement h.right_displacement).tendsto_at (mem_univ z)
  have he : ∀ᶠ K : ℕ in atTop, spectralPairPartialProduct ξ η z K =
      normalizedCentralPeriodicPolynomial hp φ K z := by
    filter_upwards [eventually_ge_atTop N] with K hK
    exact h.fullCutoff_eq_normalizedCentral K hK z
  exact ((ht.congr' he).limUnder_eq).symm

/-- The canonical endpoint product has the canonical full normalization. -/
theorem canonicalPeriodicEndpoints_product (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) :
    entireSpectralPairProduct (canonicalPeriodicLeft hp hp1 φ heven)
      (canonicalPeriodicRight hp hp1 φ heven) = canonicalPeriodicProduct hp φ :=
  (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.fullProduct_eq_canonical

end NLS.ZakharovShabat
