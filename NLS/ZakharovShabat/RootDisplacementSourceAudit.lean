import NLS.ZakharovShabat.SingleResonantPotential
import NLS.ZakharovShabat.ResonantDeterminantBounds

/-!
# Audit of the root-displacement display in Lemma 6.9

The printed page-43 bound has an extra overall factor `‖φ‖^p`. At `p=2`,
small potentials with one mode at each signed resonant frequency have roots
at `nπ ± t` and squared pair norm `2t²`. Thus their displacement energy is
quadratic in `t`, whereas the printed right-hand side is quartic near zero.
The counterexample below works beyond any cutoff in any open neighborhood
of zero, on the actual small-square domain of the reduced determinant.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The literal right-hand side of the printed Lemma 6.9 displacement bound at `p=2`. -/
def printedHilbertRootBudget (C : ℝ) (φ : WeightedCoeffPair SpectralWeight.one.toWeight 2) (N : ℕ) : ℝ :=
  C * (‖φ‖^2 / (N : ℝ) + ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) φ‖^2) *
    (1+‖φ‖^2) * ‖φ‖^2

/-- The printed Hilbert budget is quartic for a small resonant mode pair. -/
theorem printedHilbertRootBudget_single_le {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    printedHilbertRootBudget C (singleResonantPotential SpectralWeight.one n t t) N ≤ 24*C*t^4 := by
  let φ := singleResonantPotential (p := 2) SpectralWeight.one n (t : ℂ) (t : ℂ)
  have hnorm : ‖φ‖^2 = 2*t^2 := by
    simpa [φ, Complex.norm_real, Real.norm_of_nonneg ht, two_mul] using norm_singleResonantPotential_sq n (t : ℂ) (t : ℂ)
  have htail := norm_weightedPairFourierTail_le (p := 2) (by norm_num) SpectralWeight.one.toWeight (N/2) φ
  have htail2 : ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) φ‖^2 ≤ 2*t^2 := by
    nlinarith [norm_nonneg φ, norm_nonneg (weightedPairFourierTail SpectralWeight.one.toWeight (N/2) φ)]
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfirst : ‖φ‖^2 / (N : ℝ) + ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) φ‖^2 ≤ 4*t^2 := by
    have hd := div_le_self (sq_nonneg ‖φ‖) hn
    nlinarith
  have hsecond : 1+‖φ‖^2 ≤ 3 := by nlinarith
  change C * (‖φ‖^2 / (N : ℝ) + ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) φ‖^2) *
    (1+‖φ‖^2) * ‖φ‖^2 ≤ _
  calc
    _ ≤ C * (4*t^2) * 3 * (2*t^2) := by
      gcongr
      exact hnorm.le
    _ = _ := by ring

/-- Arbitrarily small amplitudes make the printed quartic budget smaller than a single root displacement. -/
theorem exists_small_amplitude_for_printed_budget {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ 2*t < r ∧ t < Real.pi/4 ∧ 24*C*t^2 < 1 := by
  obtain ⟨ε,hε,hεsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1) (24*C)
  let t := min ε (min 1 (min (r/4) (Real.pi/8)))
  have ht : 0 < t := by dsimp [t]; positivity
  have htε : t ≤ ε := min_le_left _ _
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have htr : t ≤ r/4 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have htπ : t ≤ Real.pi/8 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨t,ht,ht1,by linarith,by linarith [Real.pi_pos],?_⟩
  have hsq : t^2 ≤ ε := (by nlinarith : t^2 ≤ t).trans htε
  exact (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 24*C)).trans_lt hεsmall

/-- No fixed printed constant and cutoff work on any open neighborhood of zero, even for one actual root. -/
theorem exists_resonantRoot_exceeding_printed_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2)) (ho : IsOpen U) (h0 : 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U, ∃ z ∈ refinedResonantDisk (n : ℤ),
      ∃ hz : z ∈ resonantStrip (n : ℤ),
        ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one φ (n : ℤ) z hz‖ < 1 ∧
        resonantDeterminantExtension (by norm_num) SpectralWeight.one φ (n : ℤ) z = 0 ∧
        printedHilbertRootBudget C φ n < ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
  obtain ⟨N,_,V,hVo,_,_,hV0,_,hsmall⟩ := exists_uniform_complementarySquare_half
    (p := 2) (by norm_num) SpectralWeight.one 0
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (ho.inter hVo) 0 ⟨h0,hV0⟩
  obtain ⟨t,ht,ht1,htr,htπ,htsmall⟩ := exists_small_amplitude_for_printed_budget hC hr
  let n := max M (max N 2)
  let φ := singleResonantPotential (p := 2) SpectralWeight.one (n : ℤ) (t : ℂ) (t : ℂ)
  let z : ℂ := (Real.pi : ℂ)*(n : ℤ) + t
  have hnM : M ≤ n := le_max_left _ _
  have hnN : N ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hn2 : 2 ≤ n := (le_max_right _ _).trans (le_max_right _ _)
  have hnorm : ‖φ‖^2 = 2*t^2 := by
    simpa [φ, Complex.norm_real, Real.norm_of_nonneg ht.le, two_mul] using
      norm_singleResonantPotential_sq (n : ℤ) (t : ℂ) (t : ℂ)
  have hφnorm : ‖φ‖ < r := by nlinarith [norm_nonneg φ]
  have hφmem : φ ∈ U ∩ V := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hφnorm)
  have hdist : ‖z-(Real.pi : ℂ)*(n : ℤ)‖ = t := by
    simp [z, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hzDisk : z ∈ refinedResonantDisk (n : ℤ) := by
    change dist z ((Real.pi : ℂ)*(n : ℤ)) < Real.pi/4
    simpa only [dist_eq_norm, hdist] using htπ
  have hzStrip := refinedResonantDisk_subset_strip (n : ℤ) hzDisk
  have hcontract := ((hsmall φ hφmem.2 (n : ℤ) (by simpa using hnN) z hzStrip).1).trans_lt (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨n,hnM,hn2,φ,hφmem.1,z,hzDisk,hzStrip,hcontract,?_,?_⟩
  · rw [resonantDeterminant_singleResonantPotential (by norm_num) SpectralWeight.one
      (n : ℤ) (t : ℂ) (t : ℂ) z hzStrip hcontract]
    dsimp [z]
    ring
  · rw [hdist]
    have hb := printedHilbertRootBudget_single_le hC ht.le ht1 (n : ℤ) n (by omega)
    apply hb.trans_lt
    nlinarith [sq_pos_of_pos ht]

/-- Even the single-root consequence of the printed estimate cannot hold locally uniformly at zero. -/
theorem not_exists_locally_uniform_printedRootBudget :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ,
      ∃ U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2), IsOpen U ∧ 0 ∈ U ∧
        ∀ φ ∈ U, ∀ n : ℕ, M ≤ n → 2 ≤ n → ∀ z ∈ refinedResonantDisk (n : ℤ),
          ∀ hz : z ∈ resonantStrip (n : ℤ),
            ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one φ (n : ℤ) z hz‖ < 1 →
            resonantDeterminantExtension (by norm_num) SpectralWeight.one φ (n : ℤ) z = 0 →
            ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 ≤ printedHilbertRootBudget C φ n := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  obtain ⟨n,hnM,hn2,φ,hφ,z,hz,hzs,hsmall,hzero,hbad⟩ :=
    exists_resonantRoot_exceeding_printed_budget C hC U ho h0 M
  exact (not_le_of_gt hbad) (hbound φ hφ n hnM hn2 z hz hzs hsmall hzero)

end NLS.ZakharovShabat
