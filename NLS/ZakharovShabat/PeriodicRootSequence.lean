import NLS.ZakharovShabat.SpectralRootPair
import NLS.ZakharovShabat.RootGapSequence

/-!
# The original periodic eigenvalue pair with corrected power sums

The weighted scalar root sequences are now identified with the original
periodic spectrum and its algebraic multiplicities. Their midpoint and
squared gap agree with the intrinsic contour invariants. All identifications
and both quantitative tails hold on the same potential neighborhood.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A pair of actual periodic eigenvalues, with repetition recording multiplicity. -/
structure PeriodicResonantPair (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (x y : ℂ) : Prop where
  left_mem : x ∈ refinedResonantDisk n
  right_mem : y ∈ refinedResonantDisk n
  spectrum_iff : ∀ z ∈ resonantStrip n,
    z ∈ periodicSpectrum hp (weightedBaseToPair w φ) ↔ z = x ∨ z = y
  multiplicity_eq_count : ∀ z ∈ resonantStrip n,
    periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z = ({x,y} : Multiset ℂ).count z
  analyticOrder_eq_multiplicity : ∀ z ∈ resonantStrip n,
    analyticOrderNatAt (resonantDeterminantExtension hp w φ n) z =
      periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z
  midpoint_eq : periodicMidpoint hp (weightedBaseToPair w φ) n = (x+y)/2
  squaredGap_eq : periodicSquaredGap hp (weightedBaseToPair w φ) n = (x-y)^2
  left_bound : ‖x-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32
  right_bound : ‖y-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32
  gap_le : ‖x-y‖^2 ≤ 6*resonantBProductSup hp w φ n

/-- The unordered finite spectral set of a counted pair is exactly its two values. -/
theorem PeriodicResonantPair.enclosed_eq {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {x y : ℂ} (h : PeriodicResonantPair hp w φ n x y) :
    enclosedPeriodicSpectrum hp (weightedBaseToPair w φ) ((Real.pi : ℂ)*n) (Real.pi/4) = {x,y} :=
  enclosedPeriodicSpectrum_eq_rootPair hp _ n x y h.left_mem h.right_mem h.spectrum_iff

/-- Any two counted pairs differ only by exchanging their entries, including at double roots. -/
theorem PeriodicResonantPair.eq_or_swap {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {x y a b : ℂ}
    (h : PeriodicResonantPair hp w φ n x y) (k : PeriodicResonantPair hp w φ n a b) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have he := congrArg (fun s : Finset ℂ => (s : Set ℂ)) (h.enclosed_eq.symm.trans k.enclosed_eq)
  exact Set.pair_eq_pair_iff.mp (by simpa only [Finset.coe_insert, Finset.coe_singleton] using he)

/-- Arbitrary modewise choices of counted eigenvalue labels give identical displacement and gap tails. -/
theorem periodicRoot_powerTails_eq {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} (N : ℕ) (ξ η α β : ℤ → ℂ)
    (h : ∀ n : ℤ, N ≤ n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (k : ∀ n : ℤ, N ≤ n.natAbs → PeriodicResonantPair hp w φ n (α n) (β n)) :
    rootDisplacementPowerTail p N ξ η = rootDisplacementPowerTail p N α β ∧
      rootGapPowerTail p w N ξ η = rootGapPowerTail p w N α β := by
  have he (n : ℤ) :
      rootDisplacementPowerTail p N ξ η n = rootDisplacementPowerTail p N α β n ∧
      rootGapPowerTail p w N ξ η n = rootGapPowerTail p w N α β n := by
    by_cases hn : N ≤ n.natAbs
    · rcases (h n hn).eq_or_swap (k n hn) with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · simp only [rootDisplacementPowerTail, rootGapPowerTail, hx, hy, and_self]
      · simp only [rootDisplacementPowerTail, rootGapPowerTail, hx, hy, norm_sub_rev, add_comm, and_self]
    · simp only [rootDisplacementPowerTail, rootGapPowerTail, if_neg hn, and_self]
  exact ⟨funext (fun n => (he n).1),funext (fun n => (he n).2)⟩

/-- Corrected periodic displacement and weighted gap estimates with the original spectral multiplicities. -/
theorem exists_uniform_periodicRoots_with_power_sums (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n)) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ rootDisplacementBudget w ψ N ∧
            Summable (rootGapPowerTail p w N ξ η) ∧
            (∑' n : ℤ, rootGapPowerTail p w N ξ η n) ≤ rootGapBudget w ψ N := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,hroots⟩ := exists_uniform_resonantRoots_with_power_sums hp hp1 w φ
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
