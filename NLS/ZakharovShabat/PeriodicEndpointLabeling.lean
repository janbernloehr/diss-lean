import NLS.ZakharovShabat.CentralPeriodicOrdering
import NLS.ZakharovShabat.CompletePeriodicParityPairs

/-!
# Complete periodic endpoint labels without central parity choices

A complete labeling records the full central multiset and two actual
endpoints in every distant disc, with exact multiplicities and lp
displacements. This representation permits ordering all central roots
before identifying the ordered endpoints' parity.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The two endpoints in a distant disc, with original spectral membership and multiplicity. -/
structure PeriodicEndpointPair (hp : p ≠ ⊤) (φ : PairSpace p) (n : ℤ) (x y : ℂ) : Prop where
  left_mem : x ∈ refinedResonantDisk n
  right_mem : y ∈ refinedResonantDisk n
  spectrum_iff : ∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp φ ↔ z = x ∨ z = y
  multiplicity_eq_count : ∀ z ∈ resonantStrip n,
    periodicAlgebraicMultiplicity hp φ z = ({x,y} : Multiset ℂ).count z

/-- Weighted resonant pairs supply the intrinsic endpoint data. -/
theorem PeriodicResonantPair.toEndpoints {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {x y : ℂ} (h : PeriodicResonantPair hp w φ n x y) :
    PeriodicEndpointPair hp (weightedBaseToPair w φ) n x y :=
  ⟨h.left_mem,h.right_mem,h.spectrum_iff,h.multiplicity_eq_count⟩

/-- Exchanging the two slots preserves every spectral and multiplicity assertion. -/
theorem PeriodicEndpointPair.swap {hp : p ≠ ⊤} {φ : PairSpace p} {n : ℤ} {x y : ℂ}
    (h : PeriodicEndpointPair hp φ n x y) : PeriodicEndpointPair hp φ n y x := by
  refine ⟨h.right_mem,h.left_mem,fun z hz => (h.spectrum_iff z hz).trans or_comm,?_⟩
  intro z hz
  rw [h.multiplicity_eq_count z hz, Multiset.pair_comm]

/-- A complete pair sequence with original central and distant multiplicities. -/
structure PeriodicEndpointLabeling (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (ξ η : ℤ → ℂ) : Prop where
  counting : PeriodicCountingData hp φ N
  central : CentralPeriodicLabeling hp φ N ξ η
  distant : ∀ n : ℤ, N < n.natAbs → PeriodicEndpointPair hp φ n (ξ n) (η n)
  left_displacement : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p
  right_displacement : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p

/-- A completed parity sequence supplies complete intrinsic endpoint labels. -/
theorem CompletePeriodicParityPairs.toEndpoints {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) :
    PeriodicEndpointLabeling hp (weightedBaseToPair w φ) N ξ η :=
  ⟨h.counting,h.central.toPeriodic h.even_potential,fun n hn => (h.distant n hn).toEndpoints,
    h.left_displacement,h.right_displacement⟩

/-- A complete endpoint labeling enumerates all and only original periodic eigenvalues. -/
theorem PeriodicEndpointLabeling.exhaustive {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (z : ℂ) :
    z ∈ periodicSpectrum hp φ ↔ ∃ n : ℤ, ξ n = z ∨ η n = z := by
  constructor
  · intro hz
    rcases (h.counting.mem_spectrum_iff_central_or_disk z).mp hz with hc | hd
    · obtain ⟨n,_,hn⟩ := (h.central.root_iff z).mpr hc
      exact ⟨n,hn⟩
    · obtain ⟨n,⟨hn,hzn⟩,_⟩ := hd
      have hb := ((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hzn).2
      exact ⟨n,by simpa only [eq_comm] using ((h.distant n hn).spectrum_iff z
        (refinedResonantDisk_subset_strip n hb)).mp hz⟩
  · rintro ⟨n,hn⟩
    by_cases hfar : N < n.natAbs
    · have hs := h.distant n hfar
      rcases hn with rfl | rfl
      · exact (hs.spectrum_iff _ (refinedResonantDisk_subset_strip n hs.left_mem)).mpr (Or.inl rfl)
      · exact (hs.spectrum_iff _ (refinedResonantDisk_subset_strip n hs.right_mem)).mpr (Or.inr rfl)
    · exact ((mem_centralPeriodicSpectrum hp φ N z).mp ((h.central.root_iff z).mp ⟨n,by omega,hn⟩)).1

/-- Replacing the central enumeration preserves complete endpoint labeling and lp displacement. -/
theorem PeriodicEndpointLabeling.relabel_central {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (α β : ℤ → ℂ)
    (hc : CentralPeriodicLabeling hp φ N α β) :
    PeriodicEndpointLabeling hp φ N (spliceCentralRoots N α ξ) (spliceCentralRoots N β η) := by
  refine ⟨h.counting,⟨?_⟩,?_,memℓp_spliceCentralRoots N α ξ h.left_displacement,
    memℓp_spliceCentralRoots N β η h.right_displacement⟩
  · rw [← hc.roots]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : ¬N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [spliceCentralRoots, if_neg hn']
  · intro n hn
    simpa only [spliceCentralRoots, if_pos hn] using h.distant n hn

end NLS.ZakharovShabat
