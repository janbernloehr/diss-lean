import NLS.ZakharovShabat.SourceBoundaryHeightCounterexample

/-! # Necessary exponent dependence of a boundary height coefficient

The finite triangular family rules out every fixed replacement for the
printed constant eight. At integer exponent P, a universal bound of the
form (1+C*norm)^P with C nonnegative requires C at least P/96.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The triangular family defeats any coefficient smaller than P/96. -/
theorem triangular_height_gt_coefficient {P : ℕ} [Fact (1 ≤ (P : ℝ≥0∞))]
    (hP : 0 < P) {C : ℝ} (hC : 0 ≤ C) (hPC : 96*C < (P : ℝ)) :
    (1+C*‖CoeffPair.ofFinsupp (p := (P : ℝ≥0∞))
      (triangularNormalizedCoefficients P,0)‖)^((P : ℝ≥0∞).toReal) <
      |(((2 : ℂ)^P)*I).im| := by
  have hPr : 0 < (P : ℝ) := by exact_mod_cast hP
  have hn := norm_triangularNormalizedCoefficients_source_le hP
  have hcn : C*‖CoeffPair.ofFinsupp (p := (P : ℝ≥0∞))
      (triangularNormalizedCoefficients P,0)‖ < 1 := by
    apply (mul_le_mul_of_nonneg_left hn hC).trans_lt
    rw [← mul_div_assoc,div_lt_one hPr]
    linarith
  rw [ENNReal.toReal_natCast,Real.rpow_natCast,abs_im_triangular_height]
  exact pow_lt_pow_left₀ (by linarith) (by positivity) hP.ne'

/-- Any universal source-norm boundary height coefficient must grow at least linearly
along the integer exponents. This uses the actual source Dirichlet spectrum. -/
theorem sourceBoundaryHeightCoefficient_necessary {P : ℕ} [Fact (1 ≤ (P : ℝ≥0∞))]
    (hp1 : 1 < (P : ℝ≥0∞)) {C : ℝ} (hC : 0 ≤ C)
    (hheight : ∀ φ : CoeffPair (P : ℝ≥0∞), ∀ z ∈ BoundaryCondition.spectrum .dirichlet
      (ENNReal.natCast_ne_top P)
      (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hp1 φ).val
      (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hp1 φ).property,
      |z.im| ≤ (1+C*‖φ‖)^((P : ℝ≥0∞).toReal)) : (P : ℝ) ≤ 96*C := by
  by_contra h
  have hP : 0 < P := by exact_mod_cast (zero_lt_one.trans hp1)
  have hroot := mem_sourceDirichletSpectrum_triangularNormalized hp1
  exact (not_le_of_gt (triangular_height_gt_coefficient hP hC (lt_of_not_ge h)))
    (hheight _ _ hroot)

/-- No nonnegative constant can give the proposed shape of global height for all
integer exponents, even when only Dirichlet eigenvalues are considered. -/
theorem not_exists_uniform_sourceBoundaryHeightCoefficient :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, ∀ hP : 1 < (P : ℝ≥0∞),
      let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨hP.le⟩
      ∀ φ : CoeffPair (P : ℝ≥0∞), ∀ z ∈ BoundaryCondition.spectrum .dirichlet
        (ENNReal.natCast_ne_top P)
        (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hP φ).val
        (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hP φ).property,
        |z.im| ≤ (1+C*‖φ‖)^((P : ℝ≥0∞).toReal) := by
  rintro ⟨C,hC,h⟩
  obtain ⟨P,hPC⟩ := exists_nat_gt (max (96*C) 1)
  have hP1 : 1 < P := by exact_mod_cast ((le_max_right (96*C) 1).trans_lt hPC)
  have hp1 : 1 < (P : ℝ≥0∞) := by exact_mod_cast hP1
  let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨hp1.le⟩
  exact (not_le_of_gt ((le_max_left (96*C) 1).trans_lt hPC))
    (sourceBoundaryHeightCoefficient_necessary hp1 hC (h P hp1))

/-- Even allowing an arbitrary central cutoff and all high disks does not remove
the necessary linear growth of the boundary height coefficient. -/
theorem sourceBoundaryCountingHeightCoefficient_necessary {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hp1 : 1 < (P : ℝ≥0∞)) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ φ : CoeffPair (P : ℝ≥0∞), ∃ N : ℕ,
      BoundaryCondition.spectrum .dirichlet (ENNReal.natCast_ne_top P)
        (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hp1 φ).val
        (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hp1 φ).property ⊆
      heightSpectralBox N ((1+C*‖φ‖)^((P : ℝ≥0∞).toReal)) ∪
        highSpectralDisks N (Real.pi/4)) : (P : ℝ) ≤ 96*C := by
  by_contra h
  have hP : 0 < P := by exact_mod_cast (zero_lt_one.trans hp1)
  obtain ⟨N,hN⟩ := hcount (CoeffPair.ofFinsupp (triangularNormalizedCoefficients P,0))
  rcases hN (mem_sourceDirichletSpectrum_triangularNormalized hp1) with hbox | hdisks
  · exact (not_le_of_gt (triangular_height_gt_coefficient hP hC (lt_of_not_ge h))) hbox.2
  · exact triangular_height_not_mem_highSpectralDisks hP N hdisks

/-- No fixed nonnegative replacement for eight repairs Theorem 1.4's exhaustion
assertion for all finite exponents. Integer exponents already suffice. -/
theorem not_exists_uniform_sourceBoundaryCountingHeightCoefficient :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, ∀ hP : 1 < (P : ℝ≥0∞),
      let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨hP.le⟩
      ∀ φ : CoeffPair (P : ℝ≥0∞), ∃ N : ℕ,
        BoundaryCondition.spectrum .dirichlet (ENNReal.natCast_ne_top P)
          (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hP φ).val
          (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hP φ).property ⊆
        heightSpectralBox N ((1+C*‖φ‖)^((P : ℝ≥0∞).toReal)) ∪
          highSpectralDisks N (Real.pi/4) := by
  rintro ⟨C,hC,h⟩
  obtain ⟨P,hPC⟩ := exists_nat_gt (max (96*C) 1)
  have hP1 : 1 < P := by exact_mod_cast ((le_max_right (96*C) 1).trans_lt hPC)
  have hp1 : 1 < (P : ℝ≥0∞) := by exact_mod_cast hP1
  let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨hp1.le⟩
  exact (not_le_of_gt ((le_max_left (96*C) 1).trans_lt hPC))
    (sourceBoundaryCountingHeightCoefficient_necessary hp1 hC (h P hp1))

end NLS.ZakharovShabat
