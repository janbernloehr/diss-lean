import NLS.ZakharovShabat.SourceResonantDeterminant

/-!
# Lemma 6.9 in the original period-two source space

The actual determinant has two roots counted with multiplicity on every
distant strip. They exhaust the original spectrum there and satisfy the
factor-six gap estimate. One original neighborhood and cutoff also work
for the corrected displacement budget, with its additive leading tail.
-/

noncomputable section
open scoped ENNReal
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two original determinant roots; repetition records the full analytic multiplicity. -/
structure SourceResonantRootPair (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (x y : ℂ) : Prop where
  left_mem : x ∈ refinedResonantDisk n
  right_mem : y ∈ refinedResonantDisk n
  zeros_iff : ∀ z ∈ resonantStrip n,
    sourceResonantDeterminantFunction hp φ n z = 0 ↔ z = x ∨ z = y
  order_eq_count : ∀ z ∈ resonantStrip n,
    analyticOrderNatAt (sourceResonantDeterminantFunction hp φ n) z = ({x,y} : Multiset ℂ).count z
  spectrum_iff : ∀ z ∈ resonantStrip n, z ∉ sourceResolventSet hp φ ↔ z = x ∨ z = y
  multiplicity_eq_count : ∀ z ∈ resonantStrip n,
    periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) z = ({x,y} : Multiset ℂ).count z
  left_bound : ‖x-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32
  right_bound : ‖y-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32
  gap_le : ‖x-y‖^2 ≤ 6*sourceResonantBProductSup hp φ n

/-- The existing counted spectral pair is a counted pair of the actual source determinant. -/
theorem SourceResonantRootPair.of_periodic {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ} {x y : ℂ}
    (h : PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv φ) n x y)
    (hc : SourceResonantStripControl hp φ n) : SourceResonantRootPair hp φ n x y := by
  have hs (z : ℂ) (hz : z ∈ resonantStrip n) : z ∉ sourceResolventSet hp φ ↔ z = x ∨ z = y :=
    (sourcePeriodTwoSpectrum_iff hp φ z).trans (h.spectrum_iff z hz)
  exact {
    left_mem := h.left_mem
    right_mem := h.right_mem
    zeros_iff := fun z hz => (sourceResonantDeterminantFunction_spectrum_iff hp φ n z hz
      ((hc.small z hz).trans_lt (by norm_num))).symm.trans (hs z hz)
    order_eq_count := fun z hz => (h.analyticOrder_eq_multiplicity z hz).trans (h.multiplicity_eq_count z hz)
    spectrum_iff := hs
    multiplicity_eq_count := fun z hz => by
      simpa only [weightedBaseToPair_unitWeightedPairEquiv] using h.multiplicity_eq_count z hz
    left_bound := h.left_bound
    right_bound := h.right_bound
    gap_le := by simpa only [sourceResonantBProductSup_unit] using h.gap_le }

theorem SourceResonantRootPair.left_zero {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ} {x y : ℂ}
    (h : SourceResonantRootPair hp φ n x y) : sourceResonantDeterminantFunction hp φ n x = 0 :=
  (h.zeros_iff x (refinedResonantDisk_subset_strip n h.left_mem)).mpr (Or.inl rfl)

theorem SourceResonantRootPair.right_zero {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ} {x y : ℂ}
    (h : SourceResonantRootPair hp φ n x y) : sourceResonantDeterminantFunction hp φ n y = 0 :=
  (h.zeros_iff y (refinedResonantDisk_subset_strip n h.right_mem)).mpr (Or.inr rfl)

/-- The entire unbounded strip has exactly two zeros counted with repetition. -/
theorem SourceResonantRootPair.zero_count {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ} {x y : ℂ}
    (h : SourceResonantRootPair hp φ n x y) :
    analyticZeroCount (sourceResonantDeterminantFunction hp φ n) (resonantStrip n) = 2 := by
  classical
  have hx := refinedResonantDisk_subset_strip n h.left_mem
  have hy := refinedResonantDisk_subset_strip n h.right_mem
  have hmem (z : ℂ) (hz : z ∈ ({x,y} : Finset ℂ)) : z ∈ resonantStrip n := by
    rcases (by simpa using hz : z = x ∨ z = y) with rfl | rfl
    · exact hx
    · exact hy
  rw [analyticZeroCount_eq_sum {x,y} (fun z hz => hmem z hz) (by
    intro z hz
    simpa using (h.zeros_iff z hz.1).mp hz.2)]
  calc
    _ = ∑ z ∈ ({x,y} : Finset ℂ), ({x,y} : Multiset ℂ).count z :=
      Finset.sum_congr rfl (fun z hz => h.order_eq_count z (hmem z hz))
    _ = 2 := by
      by_cases he : x = y
      · subst y; simp
      · simp [he, Ne.symm he]

/-- Counted labels are unique up to exchange, also at a double root. -/
theorem SourceResonantRootPair.eq_or_swap {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ} {x y a b : ℂ}
    (h : SourceResonantRootPair hp φ n x y) (k : SourceResonantRootPair hp φ n a b) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  apply Set.pair_eq_pair_iff.mp
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact (k.zeros_iff _ (refinedResonantDisk_subset_strip n h.left_mem)).mp h.left_zero
    · exact (k.zeros_iff _ (refinedResonantDisk_subset_strip n h.right_mem)).mp h.right_zero
  · rintro (rfl | rfl)
    · exact (h.zeros_iff _ (refinedResonantDisk_subset_strip n k.left_mem)).mp k.left_zero
    · exact (h.zeros_iff _ (refinedResonantDisk_subset_strip n k.right_mem)).mp k.right_zero

/-- The complete signed displacement tail is independent of all modewise label choices. -/
theorem sourceResonantRoot_displacementTail_eq {hp : p ≠ ⊤} {φ : CoeffPair p}
    (N : ℕ) (ξ η α β : ℤ → ℂ)
    (h : ∀ n : ℤ, N ≤ n.natAbs → SourceResonantRootPair hp φ n (ξ n) (η n))
    (k : ∀ n : ℤ, N ≤ n.natAbs → SourceResonantRootPair hp φ n (α n) (β n)) :
    rootDisplacementPowerTail p N ξ η = rootDisplacementPowerTail p N α β := by
  funext n
  by_cases hn : N ≤ n.natAbs
  · rcases (h n hn).eq_or_swap (k n hn) with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · simp only [rootDisplacementPowerTail,hx,hy]
    · simp only [rootDisplacementPowerTail,hx,hy,add_comm]
  · simp only [rootDisplacementPowerTail,if_neg hn]

/-- Lemma 6.9 with actual source determinants, multiplicities, gap bounds, and the corrected power sum. -/
theorem sourceLemma6_9 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ n : ℤ, N₀ ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun s : CoeffPair p × ℂ => sourceResonantDeterminantFunction hp s.1 n s.2)
          (U ×ˢ resonantStrip n) ∧ ∀ ψ ∈ U, SourceResonantStripControl hp ψ n) ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceResonantRootPair hp ψ n (ξ n) (η n)) ∧
        ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
          (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ N := by
  obtain ⟨Nc,hNc,V,hoV,hcV,hφV,h0V,hcontrol⟩ := exists_uniform_sourceResonantDeterminant_control hp hp1 φ
  obtain ⟨Nr,_,W,hoW,hcW,hφW,h0W,hroots⟩ := exists_uniform_sourcePeriodTwoDisplacement hp hp1 φ
  refine ⟨max Nc Nr,hNc.trans (le_max_left _ _),V ∩ W,hoV.inter hoW,hcV.inter hcW,
    ⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_,?_⟩
  · intro n hn
    refine ⟨?_,fun ψ hψ => (hcontrol n (by omega)).2 ψ hψ.1⟩
    intro s hs
    exact (hcontrol n (by omega)).1 s ⟨hs.1.1,hs.2⟩
  · intro ψ hψ
    obtain ⟨ξ,η,hr,_,ht⟩ := hroots ψ hψ.2
    exact ⟨ξ,η,fun n hn => SourceResonantRootPair.of_periodic (hr n (by omega)) ((hcontrol n (by omega)).2 ψ hψ.1),
      fun N hN => ht N (by omega)⟩

end NLS.ZakharovShabat
