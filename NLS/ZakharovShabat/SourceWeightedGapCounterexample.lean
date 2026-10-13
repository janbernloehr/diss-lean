import NLS.ZakharovShabat.SourceWeightedGapAsymptotics
import NLS.ZakharovShabat.RootDisplacementSourceAudit

/-!
# Proposition 6.3's printed budget fails locally at zero

Unit weight already gives a counterexample in the exact original weighted
norm: two small resonant modes have actual roots nπ±t and squared gap 4t².
The printed p=2 budget is quartic. No locally uniform cutoff repairs it.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The printed p=2 weighted gap budget with ceiling at the half-cutoff. -/
def sourcePrintedHilbertGapBudget (C : ℝ) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight 2) (N : ℕ) : ℝ :=
  C * (‖φ‖^2/(N : ℝ)+‖weightedPairFourierTail w.toWeight ((N+1)/2) φ‖^2) *
    (1+‖φ‖^2)*‖φ‖^2

/-- Rounding the half-cutoff upward only makes the printed budget smaller. -/
theorem sourcePrintedHilbertGapBudget_one_le (C : ℝ) (hC : 0 ≤ C)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight 2) (N : ℕ) :
    sourcePrintedHilbertGapBudget C SpectralWeight.one φ N ≤ printedHilbertRootBudget C φ N := by
  have ht := norm_weightedPairFourierTail_antitone (p := 2) (by norm_num)
    SpectralWeight.one.toWeight φ (show N/2 ≤ (N+1)/2 by omega)
  unfold sourcePrintedHilbertGapBudget printedHilbertRootBudget
  gcongr

private theorem gap_sq_of_two_values (x y a b : ℂ) (hne : a ≠ b)
    (ha : a = x ∨ a = y) (hb : b = x ∨ b = y) : (x-y)^2 = (a-b)^2 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hne (ha.trans hb.symm))
  · rw [← ha,← hb]
  · rw [← ha,← hb]; ring
  · exact False.elim (hne (ha.trans hb.symm))

/-- Every neighborhood of zero contains an actual distant gap exceeding the printed budget. -/
theorem exists_periodicGap_exceeding_printed_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2)) (ho : IsOpen U) (h0 : 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U,
      printedHilbertRootBudget C φ n <
        ‖periodicSquaredGap (by norm_num) (weightedBaseToPair SpectralWeight.one φ) n‖ := by
  obtain ⟨Nr,_,Vr,hro,_,_,hr0,hr⟩ := exists_uniform_periodicRoots_with_power_sums
    (p := 2) (by norm_num) (by norm_num) SpectralWeight.one 0
  obtain ⟨Ns,_,Vs,hso,_,_,hs0,hs⟩ := exists_uniform_weightedDeterminant_spectral_iff
    (p := 2) (by norm_num) SpectralWeight.one 0
  obtain ⟨Nc,_,Vc,hco,_,_,hc0,_,hc⟩ := exists_uniform_complementarySquare_half
    (p := 2) (by norm_num) SpectralWeight.one 0
  obtain ⟨r,hR,hball⟩ := Metric.isOpen_iff.mp
    (ho.inter ((hro.inter hso).inter hco)) 0 ⟨h0,⟨⟨hr0,hs0⟩,hc0⟩⟩
  obtain ⟨t,ht,ht1,htr,htπ,htsmall⟩ := exists_small_amplitude_for_printed_budget hC hR
  let n := max M (max Nr (max Ns (max Nc 2)))
  have hnM : M ≤ n := le_max_left _ _
  have hnR : Nr ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hnS : Ns ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hnC : Nc ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hn2 : 2 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  let φ := singleResonantPotential (p := 2) SpectralWeight.one (n : ℤ) (t : ℂ) (t : ℂ)
  have hnorm : ‖φ‖^2 = 2*t^2 := by
    simpa [φ,Complex.norm_real,Real.norm_of_nonneg ht.le,two_mul] using
      norm_singleResonantPotential_sq (n : ℤ) (t : ℂ) (t : ℂ)
  have hφnorm : ‖φ‖ < r := by nlinarith [norm_nonneg φ]
  have hφ : φ ∈ U ∩ ((Vr ∩ Vs) ∩ Vc) := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hφnorm)
  let a : ℂ := (Real.pi : ℂ)*(n : ℤ)+t
  let b : ℂ := (Real.pi : ℂ)*(n : ℤ)-t
  have haD : a ∈ refinedResonantDisk (n : ℤ) := by
    change dist a ((Real.pi : ℂ)*(n : ℤ)) < Real.pi/4
    rw [dist_eq_norm]
    simpa [a,Complex.norm_real,Real.norm_of_nonneg ht.le] using htπ
  have hbD : b ∈ refinedResonantDisk (n : ℤ) := by
    change dist b ((Real.pi : ℂ)*(n : ℤ)) < Real.pi/4
    rw [dist_eq_norm]
    simpa [b,sub_sub,Complex.norm_real,Real.norm_of_nonneg ht.le] using htπ
  have haS := refinedResonantDisk_subset_strip (n : ℤ) haD
  have hbS := refinedResonantDisk_subset_strip (n : ℤ) hbD
  have hz (z : ℂ) (hz : z ∈ resonantStrip (n : ℤ)) :
      resonantDeterminantExtension (by norm_num) SpectralWeight.one φ n z =
        (z-(Real.pi : ℂ)*(n : ℤ))^2-(t : ℂ)*(t : ℂ) :=
    resonantDeterminant_singleResonantPotential (by norm_num) SpectralWeight.one (n : ℤ) t t z hz
      (((hc φ hφ.2.2 (n : ℤ) (by simpa using hnC) z hz).1).trans_lt (by norm_num))
  have haZ : resonantDeterminantExtension (by norm_num) SpectralWeight.one φ n a = 0 := by rw [hz a haS]; dsimp [a]; ring
  have hbZ : resonantDeterminantExtension (by norm_num) SpectralWeight.one φ n b = 0 := by rw [hz b hbS]; dsimp [b]; ring
  have haSpec := (hs φ hφ.2.1.2 (n : ℤ) (by simpa using hnS) a haS).mpr haZ
  have hbSpec := (hs φ hφ.2.1.2 (n : ℤ) (by simpa using hnS) b hbS).mpr hbZ
  obtain ⟨ξ,η,hpair,_⟩ := hr φ hφ.2.1.1
  have pair := hpair (n : ℤ) (by simpa using hnR)
  have hab : a ≠ b := by
    intro he
    have heR := congrArg Complex.re he
    simp [a,b] at heR
    linarith
  have hgap : periodicSquaredGap (by norm_num) (weightedBaseToPair SpectralWeight.one φ) n = (2*(t : ℂ))^2 := by
    rw [pair.squaredGap_eq,gap_sq_of_two_values (ξ n) (η n) a b hab
      ((pair.spectrum_iff a haS).mp haSpec) ((pair.spectrum_iff b hbS).mp hbSpec)]
    dsimp [a,b]
    ring
  have hgapNorm : ‖periodicSquaredGap (by norm_num) (weightedBaseToPair SpectralWeight.one φ) n‖ = 4*t^2 := by
    rw [hgap,norm_pow,norm_mul]
    simp [Complex.norm_real,Real.norm_of_nonneg ht.le]
    ring
  refine ⟨n,hnM,hn2,φ,hφ.1,?_⟩
  rw [hgapNorm]
  have hbudget := printedHilbertRootBudget_single_le hC ht.le ht1 (n : ℤ) n (by omega)
  apply hbudget.trans_lt
  nlinarith [sq_pos_of_pos ht]

/-- The same actual-gap witness exceeds the ceiling-cutoff printed budget. -/
theorem exists_periodicGap_exceeding_printed_ceiling_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2)) (ho : IsOpen U) (h0 : 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U,
      sourcePrintedHilbertGapBudget C SpectralWeight.one φ n <
        ‖periodicSquaredGap (by norm_num) (weightedBaseToPair SpectralWeight.one φ) n‖ := by
  obtain ⟨n,hn,hn2,φ,hφ,hb⟩ := exists_periodicGap_exceeding_printed_budget C hC U ho h0 M
  exact ⟨n,hn,hn2,φ,hφ,(sourcePrintedHilbertGapBudget_one_le C hC φ n).trans_lt hb⟩

/-- The printed locally uniform weighted gap estimate fails already for unit weight at p=2. -/
theorem not_sourceProposition6_3_printed_gap_sum :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ,
      ∃ U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2), IsOpen U ∧ 0 ∈ U ∧
        ∀ φ ∈ U, ∀ N : ℕ, M ≤ N → 2 ≤ N →
          Summable (periodicGapPowerTail (by norm_num) SpectralWeight.one φ N) ∧
          (∑' n : ℤ, periodicGapPowerTail (by norm_num) SpectralWeight.one φ N n) ≤
            sourcePrintedHilbertGapBudget C SpectralWeight.one φ N := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  obtain ⟨n,hn,hn2,φ,hφ,hbad⟩ := exists_periodicGap_exceeding_printed_ceiling_budget C hC U ho h0 M
  obtain ⟨hs,hb⟩ := hbound φ hφ n hn hn2
  have hterm := hs.le_tsum (n : ℤ) (fun k _ => by
    unfold periodicGapPowerTail
    simp only [SpectralWeight.one_apply,Real.one_rpow,one_mul]
    split_ifs <;> positivity)
  have hle : ‖periodicSquaredGap (by norm_num) (weightedBaseToPair SpectralWeight.one φ) n‖ ≤
      ∑' k : ℤ, periodicGapPowerTail (by norm_num) SpectralWeight.one φ n k := by
    simpa [periodicGapPowerTail] using hterm
  exact (not_le_of_gt hbad) (hle.trans hb)

/-- No choice of actual counted root pairs can satisfy the printed weighted gap sum locally at zero. -/
theorem not_sourceProposition6_3_printed_pair_sum :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ,
      ∃ U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2), IsOpen U ∧ 0 ∈ U ∧
        ∀ φ ∈ U, ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, M ≤ n.natAbs → 2 ≤ n.natAbs →
            PeriodicResonantPair (by norm_num) SpectralWeight.one φ n (ξ n) (η n)) ∧
          ∀ N : ℕ, M ≤ N → 2 ≤ N →
            Summable (rootGapPowerTail 2 SpectralWeight.one N ξ η) ∧
            (∑' n : ℤ, rootGapPowerTail 2 SpectralWeight.one N ξ η n) ≤
              sourcePrintedHilbertGapBudget C SpectralWeight.one φ N := by
  rintro ⟨C,hC,M,U,ho,h0,hr⟩
  apply not_sourceProposition6_3_printed_gap_sum
  refine ⟨C,hC,M,U,ho,h0,?_⟩
  intro φ hφ N hN hN2
  obtain ⟨ξ,η,hpair,ht⟩ := hr φ hφ
  rw [periodicGapPowerTail_eq_rootGapPowerTail (by norm_num) SpectralWeight.one φ N ξ η
    (fun n hn => (hpair n (hN.trans hn) (hN2.trans hn)).squaredGap_eq)]
  exact ht N hN hN2

end NLS.ZakharovShabat
