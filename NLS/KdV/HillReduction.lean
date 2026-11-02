import NLS.KdV.HillComplement
import NLS.SequenceSpaces.WeightedSingle
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.FunctionalAnalysis.FiniteSpectralDeterminant

/-!
# The two-mode Hill reduction in Fourier coefficients

The effective operator is `A_lambda - P_n (1-T_n)^(-1) V`, as on
page 28 of arXiv:1502.04550v1. All maps below are constructed from the
actual Fourier convolution and the proved complementary inverse. No
periodic differential-operator identification is assumed here.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The canonical bounded inverse of the tail equation. -/
def hillTailInverse (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2 :=
  Classical.choose (exists_hillTailCorrection w q n hn z hz hcut)

theorem hillTailInverse_left (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (a : WeightedCoeff w.toWeight 2) :
    hillTailInverse w q n hn z hz hcut (a - hillTailPerturbation w q n hn z hz a) = a :=
  congrArg (fun T : WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2 => T a)
    (Classical.choose_spec (exists_hillTailCorrection w q n hn z hz hcut)).2.1

theorem hillTailInverse_right (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (a : WeightedCoeff w.toWeight 2) :
    hillTailInverse w q n hn z hz hcut a -
      hillTailPerturbation w q n hn z hz (hillTailInverse w q n hn z hz hcut a) = a :=
  congrArg (fun T : WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2 => T a)
    (Classical.choose_spec (exists_hillTailCorrection w q n hn z hz hcut)).1

theorem norm_hillTailInverse_le (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) : ‖hillTailInverse w q n hn z hz hcut‖ ≤ 2 :=
  (Classical.choose_spec (exists_hillTailCorrection w q n hn z hz hcut)).2.2

theorem hillTailInverse_unique (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (a b : WeightedCoeff w.toWeight 2)
    (hab : a - hillTailPerturbation w q n hn z hz a = b) :
    a = hillTailInverse w q n hn z hz hcut b := by
  rw [← hab, hillTailInverse_left]

/-- The two resonant Fourier modes with their raw amplitudes. -/
def hillModes (w : Weight) (n : ℕ) : (ℂ × ℂ) →L[ℂ] WeightedCoeff w 1 :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight (WeightedCoeff.single w (n : ℤ) 1) +
    (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight (WeightedCoeff.single w (-(n : ℤ)) 1)

@[simp] theorem hillModes_apply (w : Weight) (n : ℕ) (u : ℂ × ℂ) (k : ℤ) :
    (hillModes w n u).val k =
      (if k = (n : ℤ) then u.1 else 0) + (if k = -(n : ℤ) then u.2 else 0) := by
  simp [hillModes, WeightedCoeff.single_val, Pi.single_apply]

@[simp] theorem hillModes_pos (w : Weight) (n : ℕ) (hn : 1 ≤ n) (u : ℂ × ℂ) :
    (hillModes w n u).val n = u.1 := by
  simp [hillModes_apply, show (n : ℤ) ≠ -(n : ℤ) by omega]

@[simp] theorem hillModes_neg (w : Weight) (n : ℕ) (hn : 1 ≤ n) (u : ℂ × ℂ) :
    (hillModes w n u).val (-(n : ℤ)) = u.2 := by
  simp [hillModes_apply, show -(n : ℤ) ≠ (n : ℤ) by omega]

/-- Reading the two resonant raw coefficients is continuous at either exponent. -/
def hillModeCoordinates (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    WeightedCoeff w p →L[ℂ] (ℂ × ℂ) :=
  (WeightedCoeff.evalCLM w p (n : ℤ)).prod (WeightedCoeff.evalCLM w p (-(n : ℤ)))

@[simp] theorem hillModeCoordinates_apply (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (n : ℕ) (a : WeightedCoeff w p) :
    hillModeCoordinates w p n a = (a.val n, a.val (-(n : ℤ))) := rfl

@[simp] theorem hillModeCoordinates_modes (w : Weight) (n : ℕ) (hn : 1 ≤ n)
    (u : ℂ × ℂ) : hillModeCoordinates w 1 n (hillModes w n u) = u := by
  ext <;> simp [hillModes_pos w n hn, hillModes_neg w n hn]

/-- `V` restricted to the resonant two-dimensional space, by literal convolution. -/
def hillModePotential (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2) (n : ℕ) :
    (ℂ × ℂ) →L[ℂ] WeightedCoeff w.toWeight 2 :=
  (w.convolutionCLM q).comp (hillModes w.toWeight n)

/-- The corrected potential `T_hat * V` on resonant amplitudes. -/
def hillEffectivePotential (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) : (ℂ × ℂ) →L[ℂ] WeightedCoeff w.toWeight 2 :=
  (hillTailInverse w q n hn z hz hcut).comp (hillModePotential w q n)

/-- The actual two-mode effective operator. No equality of its two diagonal
correction terms is assumed. -/
def hillReducedOperator (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (z - (freeHillValue n : ℂ)) • ContinuousLinearMap.id ℂ (ℂ × ℂ) -
    (hillModeCoordinates w.toWeight 2 n).comp (hillEffectivePotential w q n hn z hz hcut)

/-- Reconstruct all Fourier modes from two resonant amplitudes. -/
def hillReconstruct (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) : (ℂ × ℂ) →L[ℂ] WeightedCoeff w.toWeight 1 :=
  hillModes w.toWeight n +
    (hillComplementToL1 w.toWeight n hn z hz).comp (hillEffectivePotential w q n hn z hz hcut)

@[simp] theorem hillModeCoordinates_reconstruct (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (u : ℂ × ℂ) :
    hillModeCoordinates w.toWeight 1 n (hillReconstruct w q n hn z hz hcut u) = u := by
  ext <;> simp [hillReconstruct, hillModes_pos w.toWeight n hn, hillModes_neg w.toWeight n hn]

theorem hillReconstruct_injective (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    Function.Injective (hillReconstruct w q n hn z hz hcut) := by
  exact Function.LeftInverse.injective
    (hillModeCoordinates_reconstruct w q n hn z hz hcut)

/-- The reconstructed sequence has precisely its constructed effective potential. -/
theorem convolution_hillReconstruct (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (u : ℂ × ℂ) :
    w.convolution q (hillReconstruct w q n hn z hz hcut u) =
      hillEffectivePotential w q n hn z hz hcut u := by
  change w.convolution q (hillModes w.toWeight n u + _) = _
  rw [w.convolution_add_right]
  have h := hillTailInverse_right w q n hn z hz hcut (hillModePotential w q n u)
  change hillEffectivePotential w q n hn z hz hcut u -
    hillTailPerturbation w q n hn z hz (hillEffectivePotential w q n hn z hz hcut u) =
      hillModePotential w q n u at h
  change hillModePotential w q n u +
    hillTailPerturbation w q n hn z hz (hillEffectivePotential w q n hn z hz hcut u) = _
  rw [← h]
  abel

/-- The literal Fourier eigen-equation, on summable weighted coefficients.
It is not a claim that these coefficients have already been identified with
a periodic differential-operator domain. -/
def IsHillFourierEigenvector (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (z : ℂ) (f : WeightedCoeff w.toWeight 1) : Prop :=
  ∀ k : ℤ, (z-(freeHillValue k : ℂ))*f.val k = (w.convolution q f).val k

/-- A vector in the effective kernel reconstructs to the full Fourier equation. -/
theorem hillReconstruct_isEigenvector (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (u : ℂ × ℂ)
    (hu : hillReducedOperator w q n hn z hz hcut u = 0) :
    IsHillFourierEigenvector w q z (hillReconstruct w q n hn z hz hcut u) := by
  intro k
  rw [convolution_hillReconstruct]
  by_cases hkp : k = (n : ℤ)
  · subst k
    have hr := congrArg Prod.fst (hillModeCoordinates_reconstruct w q n hn z hz hcut u)
    change (hillReconstruct w q n hn z hz hcut u).val n = u.1 at hr
    rw [hr]
    have he := congrArg Prod.fst hu
    exact sub_eq_zero.mp he
  by_cases hkm : k = -(n : ℤ)
  · subst k
    have hr := congrArg Prod.snd (hillModeCoordinates_reconstruct w q n hn z hz hcut u)
    change (hillReconstruct w q n hn z hz hcut u).val (-(n : ℤ)) = u.2 at hr
    rw [hr, freeHillValue_neg]
    have he := congrArg Prod.snd hu
    exact sub_eq_zero.mp he
  have hk : k.natAbs ≠ n := fun h => (Int.natAbs_eq_iff.mp h).elim hkp hkm
  change (z-(freeHillValue k : ℂ)) * ((hillModes w.toWeight n u).val k +
    (hillComplementToL1 w.toWeight n hn z hz (hillEffectivePotential w q n hn z hz hcut u)).val k) = _
  rw [hillModes_apply, if_neg hkp, if_neg hkm, zero_add, zero_add,
    hillComplementToL1_apply, if_neg hk, ← mul_assoc,
    mul_inv_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

/-- Any full Fourier solution splits into its resonant part and its actual
complementary inverse; this is proved coefficient by coefficient. -/
theorem hillFourierEigenvector_decompose (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (f : WeightedCoeff w.toWeight 1)
    (hf : IsHillFourierEigenvector w q z f) :
    f = hillModes w.toWeight n (hillModeCoordinates w.toWeight 1 n f) +
      hillComplementToL1 w.toWeight n hn z hz (w.convolution q f) := by
  apply Subtype.ext
  funext k
  rw [WeightedCoeff.add_val, hillModes_apply, hillComplementToL1_apply]
  by_cases hkp : k = (n : ℤ)
  · subst k
    simp [show (n : ℤ) ≠ -(n : ℤ) by omega]
  by_cases hkm : k = -(n : ℤ)
  · subst k
    simp [show -(n : ℤ) ≠ (n : ℤ) by omega]
  have hk : k.natAbs ≠ n := fun h => (Int.natAbs_eq_iff.mp h).elim hkp hkm
  rw [if_neg hkp, if_neg hkm, if_neg hk, zero_add, zero_add]
  rw [← hf k, ← mul_assoc, inv_mul_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

/-- The potential of every Fourier eigenvector is the uniquely corrected
potential of its resonant amplitudes. -/
theorem hillFourierEigenvector_potential (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (f : WeightedCoeff w.toWeight 1) (hf : IsHillFourierEigenvector w q z f) :
    w.convolution q f = hillEffectivePotential w q n hn z hz hcut
      (hillModeCoordinates w.toWeight 1 n f) := by
  apply hillTailInverse_unique w q n hn z hz hcut
  apply sub_eq_iff_eq_add.mpr
  have he := congrArg (w.convolution q) (hillFourierEigenvector_decompose w q n hn z hz f hf)
  rw [w.convolution_add_right] at he
  exact he

/-- The two resonant amplitudes of every full Fourier solution lie in the
constructed two-dimensional effective kernel. -/
theorem hillFourierEigenvector_reduced (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (f : WeightedCoeff w.toWeight 1) (hf : IsHillFourierEigenvector w q z f) :
    hillReducedOperator w q n hn z hz hcut (hillModeCoordinates w.toWeight 1 n f) = 0 := by
  apply Prod.ext
  · change (z-(freeHillValue n : ℂ))*f.val n -
      (hillEffectivePotential w q n hn z hz hcut (hillModeCoordinates w.toWeight 1 n f)).val n = 0
    rw [← hillFourierEigenvector_potential w q n hn z hz hcut f hf]
    exact sub_eq_zero.mpr (hf n)
  · change (z-(freeHillValue n : ℂ))*f.val (-(n : ℤ)) -
      (hillEffectivePotential w q n hn z hz hcut (hillModeCoordinates w.toWeight 1 n f)).val (-(n : ℤ)) = 0
    rw [← hillFourierEigenvector_potential w q n hn z hz hcut f hf]
    apply sub_eq_zero.mpr
    simpa only [freeHillValue_neg] using hf (-(n : ℤ))

/-- Reconstruction recovers every full Fourier eigenvector, not merely its
eigenvalue or resonant projection. -/
theorem hillFourierEigenvector_reconstruct (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (f : WeightedCoeff w.toWeight 1) (hf : IsHillFourierEigenvector w q z f) :
    f = hillReconstruct w q n hn z hz hcut (hillModeCoordinates w.toWeight 1 n f) := by
  change f = hillModes w.toWeight n (hillModeCoordinates w.toWeight 1 n f) +
    hillComplementToL1 w.toWeight n hn z hz
      (hillEffectivePotential w q n hn z hz hcut (hillModeCoordinates w.toWeight 1 n f))
  rw [← hillFourierEigenvector_potential w q n hn z hz hcut f hf]
  exact hillFourierEigenvector_decompose w q n hn z hz f hf

/-- Exact equivalence between nontrivial Fourier solutions and the effective
two-mode kernel. No spectral labeling or multiplicity is asserted. -/
theorem exists_hillFourierEigenvector_iff (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    (∃ f : WeightedCoeff w.toWeight 1, f ≠ 0 ∧ IsHillFourierEigenvector w q z f) ↔
      ∃ u : ℂ × ℂ, u ≠ 0 ∧ hillReducedOperator w q n hn z hz hcut u = 0 := by
  constructor
  · rintro ⟨f, hf0, hf⟩
    refine ⟨hillModeCoordinates w.toWeight 1 n f, ?_,
      hillFourierEigenvector_reduced w q n hn z hz hcut f hf⟩
    intro hu0
    have he := hillFourierEigenvector_reconstruct w q n hn z hz hcut f hf
    rw [hu0, map_zero] at he
    exact hf0 he
  · rintro ⟨u, hu0, hu⟩
    refine ⟨hillReconstruct w q n hn z hz hcut u, ?_,
      hillReconstruct_isEigenvector w q n hn z hz hcut u hu⟩
    exact fun hf0 => hu0 ((hillReconstruct_injective w q n hn z hz hcut)
      (hf0.trans (map_zero _).symm))

/-- The two-dimensional determinant vanishes exactly when the literal Fourier
eigen-equation has a nonzero solution. The periodic operator interpretation
and the order of a zero as an eigenvalue multiplicity remain separate. -/
theorem hillReduced_det_eq_zero_iff (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    (hillReducedOperator w q n hn z hz hcut).toLinearMap.det = 0 ↔
      ∃ f : WeightedCoeff w.toWeight 1, f ≠ 0 ∧ IsHillFourierEigenvector w q z f := by
  rw [exists_hillFourierEigenvector_iff w q n hn z hz hcut,
    LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨u, hu, hu0⟩
    exact ⟨u, hu0, hu⟩
  · rintro ⟨u, hu0, hu⟩
    exact ⟨u, hu, hu0⟩

/-- At zero potential the effective operator is the free scalar diagonal. -/
theorem hillReducedOperator_zero (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖(0 : WeightedCoeff w.toWeight 2)‖ ≤ (n : ℝ)) :
    hillReducedOperator w 0 n hn z hz hcut =
      (z - (freeHillValue n : ℂ)) • ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
  simp [hillReducedOperator, hillEffectivePotential, hillModePotential]

/-- The free effective determinant has the squared Hill dispersion factor,
including its multiplicity two at the unperturbed positive mode. -/
theorem hillReduced_det_zero_potential (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖(0 : WeightedCoeff w.toWeight 2)‖ ≤ (n : ℝ)) :
    (hillReducedOperator w 0 n hn z hz hcut).toLinearMap.det =
      (z - (freeHillValue n : ℂ))^2 := by
  rw [hillReducedOperator_zero]
  change ((z - (freeHillValue n : ℂ)) • (LinearMap.id : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ))).det = _
  simp [LinearMap.det_smul, Module.finrank_prod]

end NLS.KdV
