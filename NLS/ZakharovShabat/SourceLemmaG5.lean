import NLS.ZakharovShabat.ClassicalHermitianGradientFourier

/-! # Corrected G.5 for the full gradient on exact periodic H¹ source balls

The reference is the actual free gradient, with the upper minus component
and lower plus component identified in SourceLemmaG5ReferenceAudit.
The outer exponent is finite; the printed infinity endpoint is false.
-/
noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Full gradient Fourier norms have one summable majorant on each exact source-norm ball. -/
theorem sourceG5_gradient_uniform_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖classicalHermitianGradientFourierCoefficients
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (ν n)‖ ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_fourier_uniform_memlp p hp q hq
    (2*max M 0) (by positivity) B hB N₀ ν hν
  refine ⟨(fun n => 8*‖b n‖),hb.norm.const_mul 8,fun n => by positivity,?_⟩
  intro a ha n
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*max M 0 :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by nlinarith [le_max_left M 0])
  exact (norm_hermitianGradientObservationAssembly_le _ (b n)
    (fun v hv L hL P hP => h _ ha' v hv L hL P hP n)).trans
    (mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num))

/-- Full shifted-reference gradient summability under eventual inverse-index displacement. -/
theorem sourceG5_shifted_gradient_uniform_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖classicalHermitianGradientFourierCoefficients
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)‖ ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_shifted_fourier_uniform_memlp p hp q hq
    (2*max M 0) (by positivity) B hB N₀ ν hν
  refine ⟨(fun n => 8*‖b n‖),hb.norm.const_mul 8,fun n => by positivity,?_⟩
  intro a ha n
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*max M 0 :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by nlinarith [le_max_left M 0])
  apply (norm_hermitianGradientObservationAssembly_le _ (b n) ?_).trans
    (mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num))
  intro v hv L hL P hP
  simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using h _ ha' v hv L hL P hP n

/-- The first assertion of G.5, with corrected free-reference superscripts and finite p. -/
theorem sourceLemmaG5_corrected
    (p : ℝ) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal (p/(p-1)))]
    (M : ℝ) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖classicalHermitianGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
            (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)))
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (ν n)‖ ≤ b n :=
  sourceG5_gradient_uniform_majorant p (by linarith) _
    (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)) M (Real.pi/4) (by positivity) N₀ ν hν

/-- The second assertion of corrected G.5, with the exact lattice free gradient. -/
theorem sourceLemmaG5_shifted_corrected
    (p : ℝ) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal (p/(p-1)))]
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖classicalHermitianGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
            (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)))
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)‖ ≤ b n :=
  sourceG5_shifted_gradient_uniform_majorant p (by linarith) _
    (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)) M B hB N₀ ν hν

/-- The actual full-gradient Fourier sequences form an outer ℓp sequence. -/
theorem sourceG5_gradient_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => classicalHermitianGradientFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (ν n)) (ENNReal.ofReal p) := by
  obtain ⟨b,hb,_,h⟩ := sourceG5_gradient_uniform_majorant p hp q hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  exact hb.mono (fun n => h a le_rfl n)

/-- Their full operator Fourier norms are therefore also an ℓp sequence. -/
theorem sourceG5_gradient_norms_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => ‖classicalHermitianGradientFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (ν n)‖) (ENNReal.ofReal p) :=
  (sourceG5_gradient_memlp p hp q hq B hB N₀ ν hν a).norm

/-- The actual full-gradient Fourier sequences form an outer ℓp sequence. -/
theorem sourceG5_shifted_gradient_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => classicalHermitianGradientFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)) (ENNReal.ofReal p) := by
  obtain ⟨b,hb,_,h⟩ := sourceG5_shifted_gradient_uniform_majorant p hp q hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  exact hb.mono (fun n => h a le_rfl n)

/-- Their full operator Fourier norms are therefore also an ℓp sequence. -/
theorem sourceG5_shifted_gradient_norms_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => ‖classicalHermitianGradientFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)‖) (ENNReal.ofReal p) :=
  (sourceG5_shifted_gradient_memlp p hp q hq B hB N₀ ν hν a).norm

end NLS.ZakharovShabat
