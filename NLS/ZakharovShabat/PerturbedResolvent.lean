import NLS.ZakharovShabat.ResolventEstimates
import NLS.ZakharovShabat.FreeResolventCompact
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A Neumann-series resolvent for nonzero potentials

We factor `z - L(φ) = (1 - Φ R₀(z)) (z - L₀)` and invert the first factor
when its norm is strictly below one. All smallness assumptions are explicit.
This implements the perturbative construction preceding Corollary 3.3; the
uniform numerical regions from Lemma 3.2(ii–iii) remain separate estimates.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bounded base-space perturbation `Φ R₀(z)`. -/
def potentialFreeResolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice) :
    PairSpace p →L[ℂ] PairSpace p :=
  (potentialOperator hp φ).comp (freeResolventToDomain z hz)

theorem potentialFreeResolvent_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (a : PairSpace p) :
    potentialFreeResolvent hp φ z hz a =
      (Coeff.convolution φ.1 (freeResolventToL1 hp z hz a).2,
        Coeff.convolution φ.2 (freeResolventToL1 hp z hz a).1) := by
  apply Prod.ext <;> ext n <;>
    simp [potentialFreeResolvent, potentialMul_apply, Coeff.convolution_apply]

theorem norm_potentialFreeResolvent_apply_le (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (a : PairSpace p) :
    ‖potentialFreeResolvent hp φ z hz a‖ ≤ freeL1Bound p hp z hz * ‖φ‖ * ‖a‖ := by
  rw [potentialFreeResolvent_apply]
  have hR := norm_freeResolventToL1_apply_le hp z hz a
  apply norm_prod_le_iff.mpr
  constructor
  · calc
      _ ≤ ‖φ.1‖ * ‖(freeResolventToL1 hp z hz a).2‖ := Coeff.norm_convolution_le _ _
      _ ≤ ‖φ‖ * (freeL1Bound p hp z hz * ‖a‖) :=
        mul_le_mul (norm_fst_le φ) ((norm_snd_le _).trans hR) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ ‖φ.2‖ * ‖(freeResolventToL1 hp z hz a).1‖ := Coeff.norm_convolution_le _ _
      _ ≤ ‖φ‖ * (freeL1Bound p hp z hz * ‖a‖) :=
        mul_le_mul (norm_snd_le φ) ((norm_fst_le _).trans hR) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring

theorem norm_potentialFreeResolvent_le (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) :
    ‖potentialFreeResolvent hp φ z hz‖ ≤ freeL1Bound p hp z hz * ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (freeL1Bound_nonneg p hp z hz) (norm_nonneg φ))
    (norm_potentialFreeResolvent_apply_le hp φ z hz)

/-- An explicit sufficient condition for Neumann inversion. -/
def NeumannCondition (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice) : Prop :=
  freeL1Bound p hp z hz * ‖φ‖ < 1

private theorem perturbation_norm_lt_one (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    ‖potentialFreeResolvent hp φ z hz‖ < 1 :=
  (norm_potentialFreeResolvent_le hp φ z hz).trans_lt h

/-- The convergent geometric correction `(1 - Φ R₀(z))⁻¹`. -/
def neumannCorrection (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice)
    (h : NeumannCondition hp φ z hz) : PairSpace p →L[ℂ] PairSpace p :=
  ↑(Units.oneSub (potentialFreeResolvent hp φ z hz) (perturbation_norm_lt_one hp φ z hz h))⁻¹

theorem neumannCorrection_hasSum (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    HasSum (fun n : ℕ => potentialFreeResolvent hp φ z hz ^ n) (neumannCorrection hp φ z hz h) :=
  (summable_geometric_of_norm_lt_one (perturbation_norm_lt_one hp φ z hz h)).hasSum

theorem neumannCorrection_left (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) (a : PairSpace p) :
    neumannCorrection hp φ z hz h (a - potentialFreeResolvent hp φ z hz a) = a := by
  have he := geom_series_mul_neg (potentialFreeResolvent hp φ z hz)
    (perturbation_norm_lt_one hp φ z hz h)
  exact congrArg (fun T : PairSpace p →L[ℂ] PairSpace p => T a) he

theorem neumannCorrection_right (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) (a : PairSpace p) :
    neumannCorrection hp φ z hz h a -
      potentialFreeResolvent hp φ z hz (neumannCorrection hp φ z hz h a) = a := by
  have he := mul_neg_geom_series (potentialFreeResolvent hp φ z hz)
    (perturbation_norm_lt_one hp φ z hz h)
  exact congrArg (fun T : PairSpace p →L[ℂ] PairSpace p => T a) he

theorem spectralPencil_factorization (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (f : Domain p) :
    spectralPencil hp φ z f = freePencil z f -
      potentialFreeResolvent hp φ z hz (freePencil z f) := by
  simp only [potentialFreeResolvent, ContinuousLinearMap.comp_apply, freeResolventToDomain_freePencil]
  change z • domainInclusion f - (freeOperator f + potentialOperator hp φ f) =
    (z • domainInclusion f - freeOperator f) - potentialOperator hp φ f
  abel

/-- The perturbed inverse takes base-space data into the full operator domain. -/
def perturbedResolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) : PairSpace p →L[ℂ] Domain p :=
  (freeResolventToDomain z hz).comp (neumannCorrection hp φ z hz h)

@[simp] theorem spectralPencil_perturbedResolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) (a : PairSpace p) :
    spectralPencil hp φ z (perturbedResolventToDomain hp φ z hz h a) = a := by
  rw [spectralPencil_factorization hp φ z hz]
  simp only [perturbedResolventToDomain, ContinuousLinearMap.comp_apply,
    freePencil_freeResolventToDomain]
  exact neumannCorrection_right hp φ z hz h a

@[simp] theorem perturbedResolventToDomain_spectralPencil (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) (f : Domain p) :
    perturbedResolventToDomain hp φ z hz h (spectralPencil hp φ z f) = f := by
  rw [spectralPencil_factorization hp φ z hz]
  simp only [perturbedResolventToDomain, ContinuousLinearMap.comp_apply,
    neumannCorrection_left, freeResolventToDomain_freePencil]

/-- The perturbed spectral equation is a continuous linear equivalence under the smallness condition. -/
def spectralPencilEquiv (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice)
    (h : NeumannCondition hp φ z hz) : Domain p ≃L[ℂ] PairSpace p :=
  { spectralPencil hp φ z with
    invFun := perturbedResolventToDomain hp φ z hz h
    left_inv := perturbedResolventToDomain_spectralPencil hp φ z hz h
    right_inv := spectralPencil_perturbedResolventToDomain hp φ z hz h
    continuous_invFun := (perturbedResolventToDomain hp φ z hz h).continuous }

/-- The perturbed resolvent on the base space. -/
def perturbedResolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice)
    (h : NeumannCondition hp φ z hz) : PairSpace p →L[ℂ] PairSpace p :=
  (freeResolvent z hz).comp (neumannCorrection hp φ z hz h)

@[simp] theorem perturbedResolvent_eq_inclusion (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    perturbedResolvent hp φ z hz h = domainInclusion.comp (perturbedResolventToDomain hp φ z hz h) := by
  exact ContinuousLinearMap.comp_assoc domainInclusion (freeResolventToDomain z hz)
    (neumannCorrection hp φ z hz h)

/-- A compact free resolvent remains compact after the bounded Neumann correction. -/
theorem isCompactOperator_perturbedResolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    IsCompactOperator (perturbedResolvent hp φ z hz h) :=
  (isCompactOperator_freeResolvent (p := p) z hz).comp_clm (neumannCorrection hp φ z hz h)

/-- The geometric correction has the usual `1 / (1 - bound)` norm estimate. -/
theorem norm_neumannCorrection_le (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    ‖neumannCorrection hp φ z hz h‖ ≤ (1 - freeL1Bound p hp z hz * ‖φ‖)⁻¹ := by
  have hK := norm_potentialFreeResolvent_le hp φ z hz
  have hgeom := tsum_geometric_le_of_norm_lt_one (potentialFreeResolvent hp φ z hz)
    (perturbation_norm_lt_one hp φ z hz h)
  have hid : ‖(1 : PairSpace p →L[ℂ] PairSpace p)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc
    _ ≤ ‖(1 : PairSpace p →L[ℂ] PairSpace p)‖ - 1 +
        (1 - ‖potentialFreeResolvent hp φ z hz‖)⁻¹ := hgeom
    _ ≤ (1 - ‖potentialFreeResolvent hp φ z hz‖)⁻¹ := by linarith
    _ ≤ (1 - freeL1Bound p hp z hz * ‖φ‖)⁻¹ :=
      inv_anti₀ (sub_pos.mpr h) (by linarith)

/-- The perturbed inverse retains one derivative of regularity. -/
theorem norm_perturbedResolventToDomain_le (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    ‖perturbedResolventToDomain hp φ z hz h‖ ≤
      freeDomainBound z * (1 - freeL1Bound p hp z hz * ‖φ‖)⁻¹ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (norm_freeResolventToDomain_le z hz) (norm_neumannCorrection_le hp φ z hz h)
      (norm_nonneg _) (freeDomainBound_nonneg hz))

/-- A quantitative base-space bound for the perturbed resolvent. -/
theorem norm_perturbedResolvent_le (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    ‖perturbedResolvent hp φ z hz h‖ ≤
      (freeGap z)⁻¹ * (1 - freeL1Bound p hp z hz * ‖φ‖)⁻¹ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (norm_freeResolvent_le z hz) (norm_neumannCorrection_le hp φ z hz h)
      (norm_nonneg _) (inv_nonneg.mpr (freeGap_pos hz).le))

/-- Every zero potential satisfies the Neumann criterion away from the free lattice. -/
theorem neumannCondition_zero (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    NeumannCondition hp (0 : PairSpace p) z hz := by simp [NeumannCondition]

/-- For `p=1`, the entire region `|Im z| > ‖φ‖` satisfies the criterion. -/
theorem neumannCondition_one (φ : PairSpace 1) (z : ℂ) (hz : z ∉ freeLattice)
    (hregion : ‖φ‖ < |z.im|) : NeumannCondition (by simp) φ z hz := by
  have habs : 0 < |z.im| := (norm_nonneg φ).trans_lt hregion
  have hC := freeL1Bound_one_le z hz (abs_pos.mp habs)
  exact (mul_le_mul_of_nonneg_right hC (norm_nonneg φ)).trans_lt
    (by simpa [div_eq_mul_inv, mul_comm] using (div_lt_one habs).mpr hregion)

/-- Every `l1` potential has a nonempty region of compact resolvents. -/
theorem exists_neumannParameter_one (φ : PairSpace 1) :
    ∃ z : ℂ, ∃ hz : z ∉ freeLattice, NeumannCondition (by simp) φ z hz := by
  let z : ℂ := (‖φ‖ + 1 : ℂ) * Complex.I
  have him : z.im = ‖φ‖ + 1 := by simp [z]
  have hpos : 0 < ‖φ‖ + 1 := by positivity
  have hz : z ∉ freeLattice := notMem_freeLattice_of_im_ne_zero (by rw [him]; exact hpos.ne')
  refine ⟨z, hz, neumannCondition_one φ z hz ?_⟩
  rw [him, abs_of_pos hpos]
  linarith

end NLS.ZakharovShabat
