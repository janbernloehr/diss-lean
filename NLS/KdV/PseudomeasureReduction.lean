import NLS.KdV.PseudomeasureMultiplication
import NLS.KdV.PseudomeasureTailInverse
import NLS.KdV.SingularHillPhysical
import NLS.KdV.HillReduction

/-! # Two-mode reduction on the full singular Hill domain

This uses the shared two-mode coordinates and the endpoint tail inverse.
The reconstructed vectors are original H1 distributions, and the converse
starts with every original H1 eigenvector. Endpoint regularity of its
potential term is supplied by `endpointH1Multiplication`, not assumed.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The shared raw resonant modes, realized on the original physical H1 domain. -/
def endpointHillH1Modes (n : ℕ) : (ℂ × ℂ) →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (sobolevCoefficients 1 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.exponentInclusion _ (by norm_num : (1:ℝ≥0∞) ≤ 2)).comp
      (hillModes (Weight.sobolev 1) n))

/-- The original physical coefficients of the resonant H1 vector. -/
theorem endpointHillH1Modes_coefficient (n : ℕ) (u : ℂ × ℂ) (k : ℤ) :
    (endpointHillH1Modes n u).val (mode (-k)) =
      (if k = (n:ℤ) then u.1 else 0) + (if k = -(n:ℤ) then u.2 else 0) := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (WeightedCoeff.exponentInclusion_apply _ (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (hillModes (Weight.sobolev 1) n u) k).trans (hillModes_apply _ n u k)

/-- Read the actual resonant amplitudes of an original H1 distribution. -/
def endpointHillH1Coordinates (n : ℕ) : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] (ℂ × ℂ) :=
  (hillModeCoordinates (Weight.sobolev 1) 2 n).comp
    (sobolevCoefficients 1 2).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem endpointHillH1Coordinates_apply (n : ℕ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    endpointHillH1Coordinates n f = (f.val (mode (-(n:ℤ))), f.val (mode (n:ℤ))) := by
  change (f.val (mode (-(n:ℤ))), f.val (mode (-(-(n:ℤ))))) = _
  simp only [neg_neg]

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- The full singular potential applied to the resonant physical H1 modes. -/
def endpointHillModePotential : (ℂ × ℂ) →L[ℂ]
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  (endpointH1Multiplication r hr hr1 q).comp (endpointHillH1Modes n)

/-- The actually inverted endpoint potential of the two resonant amplitudes. -/
def endpointHillEffectivePotential : (ℂ × ℂ) →L[ℂ]
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  (endpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hsmall).comp
    (endpointHillModePotential r hr hr1 n q)

/-- The effective two-dimensional singular Hill operator. -/
def endpointHillReducedOperator : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (z-(freeHillValue n:ℂ)) • ContinuousLinearMap.id ℂ (ℂ × ℂ) -
    (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n).comp
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall)

/-- Reconstruction has values in the original H1 domain for every amplitude. -/
def endpointHillReconstruct : (ℂ × ℂ) →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  endpointHillH1Modes n +
    (endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz).comp
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall)

/-- Every original coefficient of the physically reconstructed vector. -/
theorem endpointHillReconstruct_coefficient (u : ℂ × ℂ) (k : ℤ) :
    (endpointHillReconstruct r hr hr1 n hn z hz q hsmall u).val (mode (-k)) =
      ((if k = (n:ℤ) then u.1 else 0) + (if k = -(n:ℤ) then u.2 else 0)) +
        reducedHillSymbol n hn z hz k *
          (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u).val k := by
  change (endpointHillH1Modes n u).val (mode (-k)) +
    (endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u)).val (mode (-k)) = _
  rw [endpointHillH1Modes_coefficient, endpointReducedHillResolventH1Original_coefficient]

/-- Reconstruction preserves exactly the two resonant amplitudes. -/
theorem endpointHillH1Coordinates_reconstruct (u : ℂ × ℂ) :
    endpointHillH1Coordinates n (endpointHillReconstruct r hr hr1 n hn z hz q hsmall u) = u := by
  apply Prod.ext
  · change (endpointHillReconstruct r hr hr1 n hn z hz q hsmall u).val (mode (-(n:ℤ))) = u.1
    rw [endpointHillReconstruct_coefficient]
    simp [reducedHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
  · change (endpointHillReconstruct r hr hr1 n hn z hz q hsmall u).val (mode (-(-(n:ℤ)))) = u.2
    rw [endpointHillReconstruct_coefficient]
    simp [reducedHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]

/-- Nontrivial amplitudes reconstruct to nontrivial physical H1 vectors. -/
theorem endpointHillReconstruct_injective :
    Function.Injective (endpointHillReconstruct r hr hr1 n hn z hz q hsmall) :=
  Function.LeftInverse.injective (endpointHillH1Coordinates_reconstruct r hr hr1 n hn z hz q hsmall)

/-- The potential of the reconstructed physical vector is its effective potential. -/
theorem endpointH1Multiplication_reconstruct (u : ℂ × ℂ) :
    endpointH1Multiplication r hr hr1 q (endpointHillReconstruct r hr hr1 n hn z hz q hsmall u) =
      endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u := by
  have h := endpointHillTailInverse_right SpectralWeight.one r hr hr1 n hn z hz q hsmall
    (endpointHillModePotential r hr hr1 n q u)
  change endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u -
    unshiftedEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u) =
        endpointHillModePotential r hr hr1 n q u at h
  change endpointH1Multiplication r hr hr1 q (endpointHillH1Modes n u +
    endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u)) = _
  rw [map_add]
  have hR := congrArg (fun T => T (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u))
    (endpointH1Multiplication_resolvent r hr hr1 n hn z hz q)
  simp only [ContinuousLinearMap.comp_apply] at hR
  rw [hR]
  change endpointHillModePotential r hr hr1 n q u + _ = _
  rw [← h]
  abel

/-- A vector in the effective kernel gives an eigenvector of the actual
singular Hill operator on its full original H1 domain. -/
theorem endpointHillReconstruct_isEigenvector (u : ℂ × ℂ)
    (hu : endpointHillReducedOperator r hr hr1 n hn z hz q hsmall u = 0) :
    singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)
      (endpointHillReconstruct r hr hr1 n hn z hz q hsmall u) =
      z • singularHillDomainInclusion (endpointHillReconstruct r hr hr1 n hn z hz q hsmall u) := by
  rw [singularHillOperator_eigen_iff]
  intro k
  simp only [endpointHillHminusOne_coefficient]
  have hV := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => a.val k)
    (endpointH1Multiplication_reconstruct r hr hr1 n hn z hz q hsmall u)
  rw [endpointH1Multiplication_apply] at hV
  rw [hV, endpointHillReconstruct_coefficient]
  by_cases hkp : k = (n:ℤ)
  · subst k
    have he := congrArg Prod.fst hu
    change (z-(freeHillValue n:ℂ))*u.1 -
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u).val n = 0 at he
    simpa [reducedHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega] using sub_eq_zero.mp he
  by_cases hkm : k = -(n:ℤ)
  · subst k
    have he := congrArg Prod.snd hu
    change (z-(freeHillValue n:ℂ))*u.2 -
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u).val (-(n:ℤ)) = 0 at he
    simpa [reducedHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega] using sub_eq_zero.mp he
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, reducedHillSymbol, if_neg hk]
  rw [← mul_assoc, mul_inv_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

/-- Every original H1 eigenvector splits into its physical resonant modes
and the reduced inverse applied to its endpoint potential. -/
theorem singularHillEigenvector_decompose (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    f = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
      endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz
        (endpointH1Multiplication r hr hr1 q f) := by
  have he := (singularHillOperator_eigen_iff _ z f).mp hf
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  change f.val (mode (-k)) =
    (endpointHillH1Modes n (endpointHillH1Coordinates n f)).val (mode (-k)) +
      (endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz
        (endpointH1Multiplication r hr hr1 q f)).val (mode (-k))
  rw [endpointHillH1Modes_coefficient, endpointReducedHillResolventH1Original_coefficient,
    endpointHillH1Coordinates_apply]
  by_cases hkp : k = (n:ℤ)
  · subst k
    simp [reducedHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
  by_cases hkm : k = -(n:ℤ)
  · subst k
    simp [reducedHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, reducedHillSymbol, if_neg hk]
  have hkq := he k
  simp only [endpointHillHminusOne_coefficient] at hkq
  rw [← endpointH1Multiplication_apply r hr hr1 q f k] at hkq
  rw [← hkq, ← mul_assoc, inv_mul_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

/-- The potential of every physical H1 eigenvector is the unique solved tail
potential of its two resonant amplitudes. -/
theorem singularHillEigenvector_potential (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    endpointH1Multiplication r hr hr1 q f =
      endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall (endpointHillH1Coordinates n f) := by
  apply endpointHillTailInverse_unique SpectralWeight.one r hr hr1 n hn z hz q hsmall
  have he := congrArg (endpointH1Multiplication r hr hr1 q)
    (singularHillEigenvector_decompose r hr hr1 n hn z hz q f hf)
  rw [map_add] at he
  have hR := congrArg (fun T => T (endpointH1Multiplication r hr hr1 q f))
    (endpointH1Multiplication_resolvent r hr hr1 n hn z hz q)
  simp only [ContinuousLinearMap.comp_apply] at hR
  rw [hR] at he
  exact sub_eq_iff_eq_add.mpr he

/-- Every full-domain physical eigenvector satisfies the effective equation. -/
theorem singularHillEigenvector_reduced (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    endpointHillReducedOperator r hr hr1 n hn z hz q hsmall (endpointHillH1Coordinates n f) = 0 := by
  have he := (singularHillOperator_eigen_iff _ z f).mp hf
  apply Prod.ext
  · change (z-(freeHillValue n:ℂ))*f.val (mode (-(n:ℤ))) -
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall
        (endpointHillH1Coordinates n f)).val n = 0
    rw [← singularHillEigenvector_potential r hr hr1 n hn z hz q hsmall f hf,
      endpointH1Multiplication_apply]
    exact sub_eq_zero.mpr (by simpa only [endpointHillHminusOne_coefficient] using he n)
  · change (z-(freeHillValue n:ℂ))*f.val (mode (-(-(n:ℤ)))) -
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall
        (endpointHillH1Coordinates n f)).val (-(n:ℤ)) = 0
    rw [neg_neg]
    rw [← singularHillEigenvector_potential r hr hr1 n hn z hz q hsmall f hf,
      endpointH1Multiplication_apply]
    exact sub_eq_zero.mpr (by simpa only [endpointHillHminusOne_coefficient,
      freeHillValue_neg, neg_neg] using he (-(n:ℤ)))

/-- Reconstruction recovers every original physical H1 eigenvector. -/
theorem singularHillEigenvector_reconstruct (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    f = endpointHillReconstruct r hr hr1 n hn z hz q hsmall (endpointHillH1Coordinates n f) := by
  change f = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
    endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hsmall (endpointHillH1Coordinates n f))
  rw [← singularHillEigenvector_potential r hr hr1 n hn z hz q hsmall f hf]
  exact singularHillEigenvector_decompose r hr hr1 n hn z hz q f hf

/-- Exact equivalence on the entire original H1 domain, with no additional
endpoint regularity assumption on the eigenvector or its potential. -/
theorem exists_singularHillEigenvector_iff :
    (∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
        z • singularHillDomainInclusion f) ↔
      ∃ u : ℂ × ℂ, u ≠ 0 ∧ endpointHillReducedOperator r hr hr1 n hn z hz q hsmall u = 0 := by
  constructor
  · rintro ⟨f,hf0,hf⟩
    refine ⟨endpointHillH1Coordinates n f, ?_,
      singularHillEigenvector_reduced r hr hr1 n hn z hz q hsmall f hf⟩
    intro hu0
    have he := singularHillEigenvector_reconstruct r hr hr1 n hn z hz q hsmall f hf
    rw [hu0, map_zero] at he
    exact hf0 he
  · rintro ⟨u,hu0,hu⟩
    refine ⟨endpointHillReconstruct r hr hr1 n hn z hz q hsmall u, ?_,
      endpointHillReconstruct_isEigenvector r hr hr1 n hn z hz q hsmall u hu⟩
    intro hf0
    apply hu0
    have he := endpointHillH1Coordinates_reconstruct r hr hr1 n hn z hz q hsmall u
    rw [hf0, map_zero] at he
    exact he.symm

/-- Vanishing of the constructed two-mode determinant is equivalent to a
nonzero physical singular Hill eigenvector in the full original H1 domain. -/
theorem endpointHillReduced_det_eq_zero_iff :
    (endpointHillReducedOperator r hr hr1 n hn z hz q hsmall).toLinearMap.det = 0 ↔
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
        singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
          z • singularHillDomainInclusion f := by
  rw [exists_singularHillEigenvector_iff r hr hr1 n hn z hz q hsmall,
    LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨u,hu,hu0⟩
    exact ⟨u,hu0,hu⟩
  · rintro ⟨u,hu0,hu⟩
    exact ⟨u,hu,hu0⟩

/-- A single explicit tail cutoff supplies the physical determinant criterion
uniformly on every endpoint norm ball and the whole corrected strip.
The smallness proof is produced here, not assumed from a caller. -/
theorem exists_endpointHill_uniform_physical_reduction (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤, ‖q‖ ≤ R →
      ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n → ∀ (z : ℂ) (hz : z ∈ reducedHillStrip n),
      ∃ hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2,
        (endpointHillReducedOperator r hr hr1 n hn z hz q hsmall).toLinearMap.det = 0 ↔
          ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
            singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
              z • singularHillDomainInclusion f := by
  obtain ⟨N,hN,hcut⟩ := exists_endpointHill_cutoff r hr1 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn hnN z hz
  have hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg (endpointHillConstant_pos r hr1).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hnN)
  exact ⟨hs,endpointHillReduced_det_eq_zero_iff r hr hr1 n hn z hz q hs⟩

/-- The constructed effective kernel is linearly equivalent to the whole
physical eigenspace, preserving both original resonant amplitudes. -/
def endpointHillKernelEquiv :
    LinearMap.ker (endpointHillReducedOperator r hr hr1 n hn z hz q hsmall).toLinearMap ≃ₗ[ℂ]
      singularHillEigenspace (endpointHillHminusOne SpectralWeight.one r hr1 q) z where
  toFun u := ⟨endpointHillReconstruct r hr hr1 n hn z hz q hsmall u.val,
    (mem_singularHillEigenspace_iff _ _ _).mpr
      (endpointHillReconstruct_isEigenvector r hr hr1 n hn z hz q hsmall u.val u.property)⟩
  invFun f := ⟨endpointHillH1Coordinates n f.val,
    singularHillEigenvector_reduced r hr hr1 n hn z hz q hsmall f.val
      ((mem_singularHillEigenspace_iff _ _ _).mp f.property)⟩
  left_inv u := Subtype.ext (endpointHillH1Coordinates_reconstruct r hr hr1 n hn z hz q hsmall u.val)
  right_inv f := Subtype.ext (singularHillEigenvector_reconstruct r hr hr1 n hn z hz q hsmall f.val
    ((mem_singularHillEigenspace_iff _ _ _).mp f.property)).symm
  map_add' u v := Subtype.ext (map_add _ u.val v.val)
  map_smul' c u := Subtype.ext (map_smul _ c u.val)

include hr n hn hz hsmall in
/-- In the verified tail range every physical eigenspace is finite dimensional. -/
theorem finiteDimensional_singularHillEigenspace :
    FiniteDimensional ℂ (singularHillEigenspace (endpointHillHminusOne SpectralWeight.one r hr1 q) z) :=
  FiniteDimensional.of_injective
    (endpointHillKernelEquiv r hr hr1 n hn z hz q hsmall).symm.toLinearMap
    (endpointHillKernelEquiv r hr hr1 n hn z hz q hsmall).symm.injective

include hr n hn hz hsmall in
/-- Geometric multiplicity is at most two on the corrected tail strips.
Algebraic multiplicity and orders of determinant zeros are separate claims. -/
theorem finrank_singularHillEigenspace_le_two :
    Module.finrank ℂ (singularHillEigenspace (endpointHillHminusOne SpectralWeight.one r hr1 q) z) ≤ 2 := by
  rw [← (endpointHillKernelEquiv r hr hr1 n hn z hz q hsmall).finrank_eq]
  have h := Submodule.finrank_le
    (LinearMap.ker (endpointHillReducedOperator r hr hr1 n hn z hz q hsmall).toLinearMap)
  simpa [Module.finrank_prod] using h

end NLS.KdV
