import NLS.ZakharovShabat.ResolventAnalytic
import NLS.FunctionalAnalysis.SquaredNeumann

/-!
# The double free resolvent and squared Neumann inversion

We construct `R₀ Φ R₀ : FL^p → FL^1`, prove its coefficient formulas, and
factor `(Φ R₀)²` through it. A small operator square gives a two-sided inverse
of the spectral pencil, agreeing with the full resolvent.

The bound here is the global composition bound. The frequency-dependent tail
estimate of Lemma 3.4 is proved in `DoubleResolventEstimates`.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Potential convolution from summable pairs to the base space. -/
def potentialFromL1 (φ : PairSpace p) : PairSpace 1 →L[ℂ] PairSpace p :=
  ((Coeff.convolutionCLM φ.1).comp (ContinuousLinearMap.snd ℂ _ _)).prod
    ((Coeff.convolutionCLM φ.2).comp (ContinuousLinearMap.fst ℂ _ _))

@[simp] theorem potentialFromL1_apply (φ : PairSpace p) (a : PairSpace 1) :
    potentialFromL1 φ a = (Coeff.convolution φ.1 a.2, Coeff.convolution φ.2 a.1) := rfl

theorem norm_potentialFromL1_apply_le (φ : PairSpace p) (a : PairSpace 1) :
    ‖potentialFromL1 φ a‖ ≤ ‖φ‖ * ‖a‖ := by
  apply norm_prod_le_iff.mpr
  constructor
  · exact (Coeff.norm_convolution_le _ _).trans
      (mul_le_mul (norm_fst_le φ) (norm_snd_le a) (norm_nonneg _) (norm_nonneg _))
  · exact (Coeff.norm_convolution_le _ _).trans
      (mul_le_mul (norm_snd_le φ) (norm_fst_le a) (norm_nonneg _) (norm_nonneg _))

theorem norm_potentialFromL1_le (φ : PairSpace p) : ‖potentialFromL1 φ‖ ≤ ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_potentialFromL1_apply_le φ)

theorem potentialFreeResolvent_eq_comp_L1 (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) :
    potentialFreeResolvent hp φ z hz = (potentialFromL1 φ).comp (freeResolventToL1 hp z hz) := by
  apply ContinuousLinearMap.ext
  intro a
  exact potentialFreeResolvent_apply hp φ z hz a

/-- The sandwich `R₀(z) Φ R₀(z)`, with summable output. -/
def doubleResolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice) :
    PairSpace p →L[ℂ] PairSpace 1 :=
  (freeResolventToL1 hp z hz).comp (potentialFreeResolvent hp φ z hz)

/-- First component in the raw period-two scalar Fourier convention. -/
theorem doubleResolvent_fst_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (a : PairSpace p) (j : ℤ) :
    (doubleResolvent hp φ z hz a).1 j =
      ∑' k : ℤ, φ.1 (j - k) * a.2 k /
        ((z + (Real.pi : ℂ) * j) * (z - (Real.pi : ℂ) * k)) := by
  simp only [doubleResolvent, ContinuousLinearMap.comp_apply, freeResolventToL1_fst_apply,
    potentialFreeResolvent_apply, Coeff.convolution_apply, freeResolventToL1_snd_apply]
  rw [← tsum_div_const]
  apply tsum_congr
  intro k
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Second component, with the opposite free Fourier symbol. -/
theorem doubleResolvent_snd_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (a : PairSpace p) (j : ℤ) :
    (doubleResolvent hp φ z hz a).2 j =
      ∑' k : ℤ, φ.2 (j - k) * a.1 k /
        ((z - (Real.pi : ℂ) * j) * (z + (Real.pi : ℂ) * k)) := by
  simp only [doubleResolvent, ContinuousLinearMap.comp_apply, freeResolventToL1_snd_apply,
    potentialFreeResolvent_apply, Coeff.convolution_apply, freeResolventToL1_fst_apply]
  rw [← tsum_div_const]
  apply tsum_congr
  intro k
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The global estimate before splitting near and far frequencies. -/
theorem norm_doubleResolvent_le (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) :
    ‖doubleResolvent hp φ z hz‖ ≤ freeL1Bound p hp z hz ^ 2 * ‖φ‖ := by
  calc
    _ ≤ ‖freeResolventToL1 hp z hz‖ * ‖potentialFreeResolvent hp φ z hz‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ freeL1Bound p hp z hz * (freeL1Bound p hp z hz * ‖φ‖) :=
      mul_le_mul (norm_freeResolventToL1_le hp z hz)
        (norm_potentialFreeResolvent_le hp φ z hz) (norm_nonneg _)
        (freeL1Bound_nonneg p hp z hz)
    _ = _ := by ring

theorem potentialFreeResolvent_sq_eq_comp (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) :
    potentialFreeResolvent hp φ z hz ^ 2 =
      (potentialFromL1 φ).comp (doubleResolvent hp φ z hz) := by
  rw [pow_two, doubleResolvent, ← ContinuousLinearMap.comp_assoc,
    ← potentialFreeResolvent_eq_comp_L1]
  rfl

/-- This bound transfers the tail estimate of Lemma 3.4 to the operator square. -/
theorem norm_potentialFreeResolvent_sq_le (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) :
    ‖potentialFreeResolvent hp φ z hz ^ 2‖ ≤ ‖φ‖ * ‖doubleResolvent hp φ z hz‖ := by
  rw [potentialFreeResolvent_sq_eq_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_potentialFromL1_le φ) (norm_nonneg _))

/-- Smallness of the square; no smallness of `Φ R₀` itself is required. -/
def SquaredNeumannCondition (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) : Prop := ‖potentialFreeResolvent hp φ z hz ^ 2‖ < 1

theorem squaredNeumannCondition_of_doubleResolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : ‖φ‖ * ‖doubleResolvent hp φ z hz‖ < 1) :
    SquaredNeumannCondition hp φ z hz :=
  (norm_potentialFreeResolvent_sq_le hp φ z hz).trans_lt h

theorem squaredNeumannCondition_of_neumannCondition (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    SquaredNeumannCondition hp φ z hz := by
  have hK := (norm_potentialFreeResolvent_le hp φ z hz).trans_lt h
  change ‖potentialFreeResolvent hp φ z hz ^ 2‖ < 1
  rw [pow_two]
  exact (norm_mul_le _ _).trans_lt (by nlinarith [norm_nonneg (potentialFreeResolvent hp φ z hz)])

/-- The inverse into the full one-derivative domain from the squared criterion. -/
def squaredResolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : SquaredNeumannCondition hp φ z hz) :
    PairSpace p →L[ℂ] Domain p :=
  (freeResolventToDomain z hz).comp
    (SquaredNeumann.correction (potentialFreeResolvent hp φ z hz) h)

@[simp] theorem spectralPencil_squaredResolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : SquaredNeumannCondition hp φ z hz) (a : PairSpace p) :
    spectralPencil hp φ z (squaredResolventToDomain hp φ z hz h a) = a := by
  rw [spectralPencil_factorization hp φ z hz]
  simp only [squaredResolventToDomain, ContinuousLinearMap.comp_apply,
    freePencil_freeResolventToDomain]
  exact SquaredNeumann.correction_right _ h a

@[simp] theorem squaredResolventToDomain_spectralPencil (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : SquaredNeumannCondition hp φ z hz) (f : Domain p) :
    squaredResolventToDomain hp φ z hz h (spectralPencil hp φ z f) = f := by
  rw [spectralPencil_factorization hp φ z hz]
  simp only [squaredResolventToDomain, ContinuousLinearMap.comp_apply]
  rw [SquaredNeumann.correction_left _ h, freeResolventToDomain_freePencil]

theorem mem_resolventSet_of_squaredNeumannCondition (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : SquaredNeumannCondition hp φ z hz) :
    z ∈ resolventSet hp φ :=
  ⟨Function.LeftInverse.injective (squaredResolventToDomain_spectralPencil hp φ z hz h),
    Function.RightInverse.surjective (spectralPencil_squaredResolventToDomain hp φ z hz h)⟩

theorem resolventToDomain_eq_squared (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : SquaredNeumannCondition hp φ z hz) :
    resolventToDomain hp φ z = squaredResolventToDomain hp φ z hz h := by
  apply ContinuousLinearMap.ext
  intro a
  have hmem := mem_resolventSet_of_squaredNeumannCondition hp φ z hz h
  apply hmem.injective
  rw [spectralPencil_resolventToDomain hp φ z hmem, spectralPencil_squaredResolventToDomain]

/-- The full resolvent has the squared Neumann representation. -/
theorem resolvent_eq_squared (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : SquaredNeumannCondition hp φ z hz) :
    resolvent hp φ z = (freeResolvent z hz).comp
      (SquaredNeumann.correction (potentialFreeResolvent hp φ z hz) h) := by
  rw [resolvent, resolventToDomain_eq_squared hp φ z hz h, squaredResolventToDomain,
    ← ContinuousLinearMap.comp_assoc]
  rfl

theorem norm_resolvent_le_of_squaredNeumannCondition (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : SquaredNeumannCondition hp φ z hz) :
    ‖resolvent hp φ z‖ ≤ (freeGap z)⁻¹ *
      ((1 + ‖potentialFreeResolvent hp φ z hz‖) * (1 - ‖potentialFreeResolvent hp φ z hz ^ 2‖)⁻¹) := by
  rw [resolvent_eq_squared hp φ z hz h]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
    (norm_freeResolvent_le z hz) (SquaredNeumann.norm_correction_le _ h)
    (norm_nonneg _) (inv_nonneg.mpr (freeGap_pos hz).le))

/-- A bound in terms of the sandwich, ready for the frequency-tail estimate. -/
theorem norm_resolvent_le_of_doubleResolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : ‖φ‖ * ‖doubleResolvent hp φ z hz‖ < 1) :
    ‖resolvent hp φ z‖ ≤ (freeGap z)⁻¹ *
      ((1 + freeL1Bound p hp z hz * ‖φ‖) * (1 - ‖φ‖ * ‖doubleResolvent hp φ z hz‖)⁻¹) := by
  have hs := squaredNeumannCondition_of_doubleResolvent hp φ z hz h
  refine (norm_resolvent_le_of_squaredNeumannCondition hp φ z hz hs).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (freeGap_pos hz).le)
  apply mul_le_mul (add_le_add le_rfl (norm_potentialFreeResolvent_le hp φ z hz))
  · exact inv_anti₀ (sub_pos.mpr h)
      (sub_le_sub_left (norm_potentialFreeResolvent_sq_le hp φ z hz) 1)
  · exact inv_nonneg.mpr (sub_pos.mpr hs).le
  · exact add_nonneg zero_le_one (mul_nonneg (freeL1Bound_nonneg p hp z hz) (norm_nonneg _))

/-- If either potential component vanishes, `Φ R₀` is nilpotent of order at most two. -/
theorem potentialFreeResolvent_sq_eq_zero_of_oneSided (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (hφ : φ.1 = 0 ∨ φ.2 = 0) :
    potentialFreeResolvent hp φ z hz ^ 2 = 0 := by
  apply ContinuousLinearMap.ext
  intro a
  rw [pow_two]
  change potentialFreeResolvent hp φ z hz (potentialFreeResolvent hp φ z hz a) = 0
  rcases hφ with hφ | hφ <;>
    apply Prod.ext <;> ext j <;>
      simp [potentialFreeResolvent_apply, Coeff.convolution_apply, hφ]

/-- One-sided potentials of any size satisfy the squared criterion off the free lattice. -/
theorem squaredNeumannCondition_of_oneSided (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (hφ : φ.1 = 0 ∨ φ.2 = 0) :
    SquaredNeumannCondition hp φ z hz := by
  unfold SquaredNeumannCondition
  rw [potentialFreeResolvent_sq_eq_zero_of_oneSided hp φ z hz hφ, norm_zero]
  exact zero_lt_one

/-- For a one-sided potential, the exact resolvent expansion has two terms. -/
theorem resolvent_eq_two_terms_of_oneSided (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (hφ : φ.1 = 0 ∨ φ.2 = 0) :
    resolvent hp φ z = freeResolvent z hz +
      (freeResolvent z hz).comp (potentialFreeResolvent hp φ z hz) := by
  have hs := squaredNeumannCondition_of_oneSided hp φ z hz hφ
  rw [resolvent_eq_squared hp φ z hz hs,
    SquaredNeumann.correction_eq_one_add_of_sq_eq_zero _ hs
      (potentialFreeResolvent_sq_eq_zero_of_oneSided hp φ z hz hφ)]
  rw [ContinuousLinearMap.comp_add]
  rfl

end NLS.ZakharovShabat
