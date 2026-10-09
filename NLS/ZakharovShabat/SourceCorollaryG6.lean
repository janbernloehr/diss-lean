import NLS.ZakharovShabat.ClassicalHermitianCharacteristicGradients
import NLS.ZakharovShabat.SourceCorollaryG6ReferenceAudit
import NLS.SequenceSpaces.PairNorm
import NLS.SequenceSpaces.Reflection

/-! # G.6 on exact periodic H¹ source balls

The discriminant assertion holds unchanged. The anti-discriminant uses
wave subscripts -2*n, correcting the extra pi in the printed reference.
Both complete vector Fourier norms are uniformly summable on source balls.
-/
noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One nonnegative summable majorant controls both components over the exact source-norm ball. -/
theorem sourceG6_discriminant_uniform_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖classicalHermitianDiscriminantGradientCoefficients
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)‖ ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalDiscriminantGradient_fourier_uniform_memlp p hp q hq
    (2*max M 0) (by positivity) B hB N₀ ν hν
  refine ⟨(fun n => 2*‖b n‖),hb.norm.const_mul 2,fun n => by positivity,?_⟩
  intro a ha n
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*max M 0 :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by nlinarith [le_max_left M 0])
  apply (norm_hermitianCharacteristicGradientAssembly_le _ (b n) ?_).trans
    (mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num))
  intro P hP
  exact h _ ha' P hP n

/-- The actual vector-valued Fourier sequences themselves form an outer ℓp sequence. -/
theorem sourceG6_discriminant_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => classicalHermitianDiscriminantGradientCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)) (ENNReal.ofReal p) := by
  obtain ⟨b,hb,_,h⟩ := sourceG6_discriminant_uniform_majorant p hp q hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  exact hb.mono (fun n => h a le_rfl n)

/-- The full Hermitian vector Fourier norms are an outer ℓp sequence. -/
theorem sourceG6_discriminant_norms_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => ‖classicalHermitianDiscriminantGradientCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)‖) (ENNReal.ofReal p) :=
  (sourceG6_discriminant_memlp p hp q hq B hB N₀ ν hν a).norm

/-- One nonnegative summable majorant controls both components over the exact source-norm ball. -/
theorem sourceG6_antiDiscriminant_uniform_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖classicalHermitianAntiDiscriminantGradientCoefficients
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)‖ ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalAntiDiscriminantGradient_fourier_uniform_memlp p hp q hq
    (2*max M 0) (by positivity) B hB N₀ ν hν
  refine ⟨(fun n => 2*‖b n‖),hb.norm.const_mul 2,fun n => by positivity,?_⟩
  intro a ha n
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*max M 0 :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by nlinarith [le_max_left M 0])
  apply (norm_hermitianCharacteristicGradientAssembly_le _ (b n) ?_).trans
    (mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num))
  intro P hP
  simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using h _ ha' P hP n

/-- The actual vector-valued Fourier sequences themselves form an outer ℓp sequence. -/
theorem sourceG6_antiDiscriminant_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => classicalHermitianAntiDiscriminantGradientCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)) (ENNReal.ofReal p) := by
  obtain ⟨b,hb,_,h⟩ := sourceG6_antiDiscriminant_uniform_majorant p hp q hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  exact hb.mono (fun n => h a le_rfl n)

/-- The full Hermitian vector Fourier norms are an outer ℓp sequence. -/
theorem sourceG6_antiDiscriminant_norms_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => ‖classicalHermitianAntiDiscriminantGradientCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)‖) (ENNReal.ofReal p) :=
  (sourceG6_antiDiscriminant_memlp p hp q hq B hB N₀ ν hν a).norm

/-- Signed source coordinates: the first physical Fourier index is reversed. -/
def sourceG6SignedAssembly {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q) : CoeffPair q :=
  Complex.I • (CoeffPair.toMax q).symm
    (Coeff.reflection (F (ContinuousLinearMap.fst ℝ ℂ ℂ)),F (ContinuousLinearMap.snd ℝ ℂ ℂ))

theorem norm_sourceG6SignedAssembly_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    (F : ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q) (K : ℝ)
    (hF : ∀ P, ‖P‖ ≤ 1 → ‖F P‖ ≤ K) :
    ‖sourceG6SignedAssembly F‖ ≤ (2 : ℝ)^(1/q.toReal)*K := by
  rw [sourceG6SignedAssembly,norm_smul,Complex.norm_I,one_mul]
  apply (CoeffPair.norm_toMax_symm_le hq _).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Prod.norm_def,LinearIsometryEquiv.norm_map] using
    max_le (hF _ (ContinuousLinearMap.norm_fst_le ℝ ℂ ℂ))
      (hF _ (ContinuousLinearMap.norm_snd_le ℝ ℂ ℂ))

/-- The unchanged discriminant assertion of G.6, on every exact periodic H¹ source ball. -/
theorem sourceCorollaryG6_discriminant_hermitian
    (p : ℝ) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal (p/(p-1)))]
    (M : ℝ) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖classicalHermitianDiscriminantGradientCoefficients (q := ENNReal.ofReal (p/(p-1)))
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
            (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)))
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)‖ ≤ b n :=
  sourceG6_discriminant_uniform_majorant p (by linarith) _
    (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)) M (Real.pi/4) (by positivity) N₀ ν hν

/-- The anti-discriminant assertion with the corrected wave subscripts, on every exact periodic H¹ source ball. -/
theorem sourceCorollaryG6_antiDiscriminant_corrected_hermitian
    (p : ℝ) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal (p/(p-1)))]
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖classicalHermitianAntiDiscriminantGradientCoefficients (q := ENNReal.ofReal (p/(p-1)))
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
            (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)))
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)‖ ≤ b n :=
  sourceG6_antiDiscriminant_uniform_majorant p (by linarith) _
    (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)) M B hB N₀ ν hν

/-- Actual i times the gradient in the source's finite-exponent signed pair space. -/
def sourceG6DiscriminantCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) : CoeffPair q :=
  sourceG6SignedAssembly (classicalDiscriminantGradientFourierCoefficients hq φ z)

@[simp] theorem sourceG6DiscriminantCoefficients_fst {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) (k : ℤ) :
    (sourceG6DiscriminantCoefficients hq φ z).fst k =
      Complex.I* NLS.Fourier.intervalFourierCoefficient 1 (fun t => (classicalDiscriminantGradient φ z t).1) (-k) := by
  simp [sourceG6DiscriminantCoefficients,sourceG6SignedAssembly]

@[simp] theorem sourceG6DiscriminantCoefficients_snd {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) (k : ℤ) :
    (sourceG6DiscriminantCoefficients hq φ z).snd k =
      Complex.I* NLS.Fourier.intervalFourierCoefficient 1 (fun t => (classicalDiscriminantGradient φ z t).2) k := by
  simp [sourceG6DiscriminantCoefficients,sourceG6SignedAssembly]

/-- Equation (1.2)'s exact combined coefficient energy, including the signed first index. -/
theorem sourceG6DiscriminantCoefficients_norm_rpow {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hqfin : q ≠ ⊤)
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) :
    ‖sourceG6DiscriminantCoefficients hq φ z‖^q.toReal = ∑' k : ℤ,
      (‖NLS.Fourier.intervalFourierCoefficient 1 (fun t => (classicalDiscriminantGradient φ z t).1) (-k)‖^q.toReal+
       ‖NLS.Fourier.intervalFourierCoefficient 1 (fun t => (classicalDiscriminantGradient φ z t).2) k‖^q.toReal) := by
  rw [CoeffPair.norm_rpow_eq_tsum hqfin]
  simp only [sourceG6DiscriminantCoefficients_fst,sourceG6DiscriminantCoefficients_snd,norm_mul,Complex.norm_I,one_mul]

/-- Uniformity in the exact finite-exponent source output norm and exact H¹ input norm. -/
theorem sourceG6_discriminant_sourceNorm_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hqfin : q ≠ ⊤)
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖sourceG6DiscriminantCoefficients
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)‖ ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalDiscriminantGradient_fourier_uniform_memlp p hp q hq
    (2*max M 0) (by positivity) B hB N₀ ν hν
  refine ⟨(fun n => (2 : ℝ)^(1/q.toReal)*‖b n‖),hb.norm.const_mul _,fun n => by positivity,?_⟩
  intro a ha n
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*max M 0 :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by nlinarith [le_max_left M 0])
  apply (norm_sourceG6SignedAssembly_le hqfin _ (b n) ?_).trans
    (mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by positivity))
  intro P hP
  exact h _ ha' P hP n

/-- G.6 in both exact source norms; the anti-discriminant reference is corrected to -2*n. -/
theorem sourceCorollaryG6_discriminant
    (p : ℝ) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal (p/(p-1)))]
    (M : ℝ) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖sourceG6DiscriminantCoefficients (q := ENNReal.ofReal (p/(p-1)))
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
            (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)))
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)‖ ≤ b n :=
  sourceG6_discriminant_sourceNorm_majorant p (by linarith) _ ENNReal.ofReal_ne_top
    (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)) M (Real.pi/4) (by positivity) N₀ ν hν

/-- Actual i times the gradient in the source's finite-exponent signed pair space. -/
def sourceG6AntiDiscriminantCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z w : ℂ) : CoeffPair q :=
  sourceG6SignedAssembly (classicalAntiDiscriminantGradientFourierCoefficients hq φ z w)

@[simp] theorem sourceG6AntiDiscriminantCoefficients_fst {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z w : ℂ) (k : ℤ) :
    (sourceG6AntiDiscriminantCoefficients hq φ z w).fst k =
      Complex.I* NLS.Fourier.intervalFourierCoefficient 1 (fun t => (classicalAntiDiscriminantGradientRemainder φ z w t).1) (-k) := by
  simp [sourceG6AntiDiscriminantCoefficients,sourceG6SignedAssembly]

@[simp] theorem sourceG6AntiDiscriminantCoefficients_snd {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z w : ℂ) (k : ℤ) :
    (sourceG6AntiDiscriminantCoefficients hq φ z w).snd k =
      Complex.I* NLS.Fourier.intervalFourierCoefficient 1 (fun t => (classicalAntiDiscriminantGradientRemainder φ z w t).2) k := by
  simp [sourceG6AntiDiscriminantCoefficients,sourceG6SignedAssembly]

/-- Equation (1.2)'s exact combined coefficient energy, including the signed first index. -/
theorem sourceG6AntiDiscriminantCoefficients_norm_rpow {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hqfin : q ≠ ⊤)
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z w : ℂ) :
    ‖sourceG6AntiDiscriminantCoefficients hq φ z w‖^q.toReal = ∑' k : ℤ,
      (‖NLS.Fourier.intervalFourierCoefficient 1 (fun t => (classicalAntiDiscriminantGradientRemainder φ z w t).1) (-k)‖^q.toReal+
       ‖NLS.Fourier.intervalFourierCoefficient 1 (fun t => (classicalAntiDiscriminantGradientRemainder φ z w t).2) k‖^q.toReal) := by
  rw [CoeffPair.norm_rpow_eq_tsum hqfin]
  simp only [sourceG6AntiDiscriminantCoefficients_fst,sourceG6AntiDiscriminantCoefficients_snd,norm_mul,Complex.norm_I,one_mul]

/-- Uniformity in the exact finite-exponent source output norm and exact H¹ input norm. -/
theorem sourceG6_antiDiscriminant_sourceNorm_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hqfin : q ≠ ⊤)
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖sourceG6AntiDiscriminantCoefficients
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)‖ ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalAntiDiscriminantGradient_fourier_uniform_memlp p hp q hq
    (2*max M 0) (by positivity) B hB N₀ ν hν
  refine ⟨(fun n => (2 : ℝ)^(1/q.toReal)*‖b n‖),hb.norm.const_mul _,fun n => by positivity,?_⟩
  intro a ha n
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*max M 0 :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by nlinarith [le_max_left M 0])
  apply (norm_sourceG6SignedAssembly_le hqfin _ (b n) ?_).trans
    (mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by positivity))
  intro P hP
  simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using h _ ha' P hP n

/-- G.6 in both exact source norms; the anti-discriminant reference is corrected to -2*n. -/
theorem sourceCorollaryG6_antiDiscriminant_corrected
    (p : ℝ) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal (p/(p-1)))]
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ‖sourceG6AntiDiscriminantCoefficients (q := ENNReal.ofReal (p/(p-1)))
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
            (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)))
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)‖ ≤ b n :=
  sourceG6_antiDiscriminant_sourceNorm_majorant p (by linarith) _ ENNReal.ofReal_ne_top
    (conjugate_exponent_ennreal_gt_gradient_threshold p (by linarith)) M B hB N₀ ν hν

/-- No second component can repair the literal error in the exact source pair norm. -/
theorem not_memlp_sourceG6Printed_pair_norms (c : ℤ → Coeff 2) :
    ¬Memℓp (fun n : ℤ => ‖(CoeffPair.toMax 2).symm
      (Coeff.reflection (sourceG6PrintedAntiErrorCoefficients n),c n)‖) 2 := by
  intro h
  apply not_memlp_sourceG6PrintedAntiError_norms
  apply h.mono
  intro n
  have hc := WithLp.norm_fst_le (Coeff 2) ((CoeffPair.toMax 2).symm
    (Coeff.reflection (sourceG6PrintedAntiErrorCoefficients n),c n))
  simpa using hc

/-- Actual signed source coefficient pairs are summable in the exact finite-q norm. -/
theorem sourceG6_discriminant_source_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hqfin : q ≠ ⊤)
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => sourceG6DiscriminantCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)) (ENNReal.ofReal p) := by
  obtain ⟨b,hb,_,h⟩ := sourceG6_discriminant_sourceNorm_majorant p hp q hqfin hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  exact hb.mono (fun n => h a le_rfl n)

/-- Actual signed source coefficient pairs are summable in the exact finite-q norm. -/
theorem sourceG6_antiDiscriminant_source_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hqfin : q ≠ ⊤)
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => sourceG6AntiDiscriminantCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) ((Real.pi : ℂ)*n)) (ENNReal.ofReal p) := by
  obtain ⟨b,hb,_,h⟩ := sourceG6_antiDiscriminant_sourceNorm_majorant p hp q hqfin hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  exact hb.mono (fun n => h a le_rfl n)

end NLS.ZakharovShabat
