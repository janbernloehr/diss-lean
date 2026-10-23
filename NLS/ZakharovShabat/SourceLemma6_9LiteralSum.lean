import NLS.ZakharovShabat.SourcePositiveDisplacementTail
import NLS.ZakharovShabat.SourceLemma6_9

/-! # The repeated positive-root term printed in Lemma 6.9

Page 43 repeats the first label twice in the positive-index sum. The actual
resonant witness has roots nπ±t, so either chosen label violates the printed
budget. This treats that literal display without assuming a label order.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every labeling of the actual two-point resonant spectrum has a violating first root. -/
theorem exists_periodicFirstRoot_exceeding_printed_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2))
    (ho : IsOpen U) (h0 : 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U, ∀ x y : ℂ,
      (∀ z ∈ resonantStrip (n : ℤ),
        z ∈ periodicSpectrum (by norm_num) (weightedBaseToPair SpectralWeight.one φ) ↔
          z = x ∨ z = y) →
      printedHilbertRootBudget C φ n < ‖x-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
  obtain ⟨Ns,_,Vs,hso,_,_,hs0,hs⟩ := exists_uniform_weightedDeterminant_spectral_iff
    (p := 2) (by norm_num) SpectralWeight.one 0
  obtain ⟨Nc,_,Vc,hco,_,_,hc0,_,hc⟩ := exists_uniform_complementarySquare_half
    (p := 2) (by norm_num) SpectralWeight.one 0
  obtain ⟨r,hR,hball⟩ := Metric.isOpen_iff.mp
    (ho.inter (hso.inter hco)) 0 ⟨h0,⟨hs0,hc0⟩⟩
  obtain ⟨t,ht,ht1,htr,htπ,htsmall⟩ := exists_small_amplitude_for_printed_budget hC hR
  let n := max M (max Ns (max Nc 2))
  have hnM : M ≤ n := le_max_left _ _
  have hnS : Ns ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hnC : Nc ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hn2 : 2 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let φ := singleResonantPotential (p := 2) SpectralWeight.one (n : ℤ) (t : ℂ) (t : ℂ)
  have hnorm : ‖φ‖^2 = 2*t^2 := by
    simpa [φ,Complex.norm_real,Real.norm_of_nonneg ht.le,two_mul] using
      norm_singleResonantPotential_sq (n : ℤ) (t : ℂ) (t : ℂ)
  have hφnorm : ‖φ‖ < r := by nlinarith [norm_nonneg φ]
  have hφ : φ ∈ U ∩ (Vs ∩ Vc) := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hφnorm)
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
  have haSpec := (hs φ hφ.2.1 (n : ℤ) (by simpa using hnS) a haS).mpr haZ
  have hbSpec := (hs φ hφ.2.1 (n : ℤ) (by simpa using hnS) b hbS).mpr hbZ
  have hab : a ≠ b := by
    intro he
    have heR := congrArg Complex.re he
    simp [a,b] at heR
    linarith
  refine ⟨n,hnM,hn2,φ,hφ.1,?_⟩
  intro x y hpair
  have hx : x = a ∨ x = b := by
    rcases (hpair a haS).mp haSpec with ha | ha <;>
      rcases (hpair b hbS).mp hbSpec with hb | hb
    · exact False.elim (hab (ha.trans hb.symm))
    · exact Or.inl ha.symm
    · exact Or.inr hb.symm
    · exact False.elim (hab (ha.trans hb.symm))
  have hxnorm : ‖x-(Real.pi : ℂ)*(n : ℤ)‖^2 = t^2 := by
    rcases hx with rfl | rfl
    · simp [a,Complex.norm_real,Real.norm_of_nonneg ht.le]
    · simp [b,Complex.norm_real,Real.norm_of_nonneg ht.le]
  rw [hxnorm]
  apply (printedHilbertRootBudget_single_le hC ht.le ht1 (n : ℤ) n (by omega)).trans_lt
  nlinarith [mul_lt_mul_of_pos_right htsmall (sq_pos_of_pos ht)]

private theorem exists_sourceFirstRootTransport
    (e : CoeffPair 2 ≃ₗᵢ[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight 2)
    (U : Set (CoeffPair 2)) (ho : IsOpen U) (h0 : 0 ∈ U)
    (P : WeightedCoeffPair SpectralWeight.one.toWeight 2 → Prop)
    (h : ∀ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2),
      IsOpen V → 0 ∈ V → ∃ ψ ∈ V, P ψ) : ∃ φ ∈ U, P (e φ) := by
  obtain ⟨ψ,hψ,hP⟩ := h (e.symm ⁻¹' U) (ho.preimage e.symm.continuous)
    (by simpa only [Set.mem_preimage,map_zero] using h0)
  exact ⟨e.symm ψ,hψ,by simpa only [LinearIsometryEquiv.apply_symm_apply] using hP⟩

/-- The first root of every actual original determinant pair violates the budget somewhere. -/
theorem exists_sourceFirstRoot_exceeding_printed_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (CoeffPair 2)) (ho : IsOpen U) (h0 : 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U, ∀ x y : ℂ,
      SourceResonantRootPair (by norm_num) φ n x y →
        sourcePrintedHilbertDisplacementBudget C φ n < ‖x-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
  have hw : ∀ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2), IsOpen V → 0 ∈ V →
      ∃ ψ ∈ V, ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∀ x y : ℂ,
        (∀ z ∈ resonantStrip (n : ℤ),
          z ∈ periodicSpectrum (by norm_num) (weightedBaseToPair SpectralWeight.one ψ) ↔
            z = x ∨ z = y) →
        printedHilbertRootBudget C ψ n < ‖x-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
    intro V hVo hV0
    obtain ⟨n,hn,hn2,ψ,hψ,hbad⟩ := exists_periodicFirstRoot_exceeding_printed_budget C hC V hVo hV0 M
    exact ⟨ψ,hψ,n,hn,hn2,hbad⟩
  obtain ⟨φ,hφ,n,hn,hn2,hbad⟩ := exists_sourceFirstRootTransport unitWeightedPairEquiv U ho h0 _ hw
  refine ⟨n,hn,hn2,φ,hφ,?_⟩
  intro x y hpair
  apply (sourcePrintedHilbertDisplacementBudget_le C hC φ n).trans_lt
  apply hbad x y
  intro z hz
  exact (sourcePeriodTwoSpectrum_iff (by norm_num) φ z).symm.trans (hpair.spectrum_iff z hz)

/-- Literal page-43 formula: n≥N, with the first root's displacement repeated twice. -/
theorem not_sourceLemma6_9_printed_duplicated_positive_sum :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ 0 ∈ U ∧
      ∀ φ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℕ, M ≤ n → 2 ≤ n →
          SourceResonantRootPair (by norm_num) φ n (ξ n) (η n)) ∧
        ∀ N : ℕ, M ≤ N → 2 ≤ N → Summable (sourcePositiveDisplacementPowerTail 2 N ξ ξ) ∧
          (∑' n : ℤ, sourcePositiveDisplacementPowerTail 2 N ξ ξ n) ≤
            sourcePrintedHilbertDisplacementBudget C φ N := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  obtain ⟨n,hn,hn2,φ,hφ,hbad⟩ := exists_sourceFirstRoot_exceeding_printed_budget C hC U ho h0 M
  obtain ⟨ξ,η,hpair,ht⟩ := hbound φ hφ
  have hb := sourcePeriodTwoRoot_sq_le_positive_pair_tail n n le_rfl ξ ξ (ξ n)
    (Or.inl rfl) (ht n hn hn2).1
  exact (not_le_of_gt (hbad (ξ n) (η n) (hpair n hn hn2))) (hb.trans (ht n hn hn2).2)

end NLS.ZakharovShabat
