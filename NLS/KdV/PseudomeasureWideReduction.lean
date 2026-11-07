import NLS.KdV.PseudomeasureWideLocalization
import NLS.KdV.PseudomeasureComplexPairs

/-! Exact two-mode reduction on the full printed 12n strip, n≥2.
Reconstruction takes values in the original H1 domain and the converse
starts with every physical eigenvector. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hsmall : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- The effective two-dimensional singular Hill operator. -/
def wideEndpointHillReducedOperator : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (z-(freeHillValue n:ℂ)) • ContinuousLinearMap.id ℂ (ℂ × ℂ) -
    (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n).comp
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall)

/-- Reconstruction has values in the original H1 domain for every amplitude. -/
def wideEndpointHillReconstruct : (ℂ × ℂ) →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  endpointHillH1Modes n +
    (wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz).comp
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall)

/-- Every original coefficient of the physically reconstructed vector. -/
theorem wideEndpointHillReconstruct_coefficient (u : ℂ × ℂ) (k : ℤ) :
    (wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall u).val (mode (-k)) =
      ((if k = (n:ℤ) then u.1 else 0) + (if k = -(n:ℤ) then u.2 else 0)) +
        wideHillSymbol n z k *
          (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u).val k := by
  change (endpointHillH1Modes n u).val (mode (-k)) +
    (wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u)).val (mode (-k)) = _
  rw [endpointHillH1Modes_coefficient, wideEndpointHillResolventH1_coefficient]

/-- Reconstruction preserves exactly the two resonant amplitudes. -/
theorem endpointHillH1Coordinates_wideReconstruct (u : ℂ × ℂ) :
    endpointHillH1Coordinates n (wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall u) = u := by
  apply Prod.ext
  · change (wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall u).val (mode (-(n:ℤ))) = u.1
    rw [wideEndpointHillReconstruct_coefficient]
    simp [wideHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
  · change (wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall u).val (mode (-(-(n:ℤ)))) = u.2
    rw [wideEndpointHillReconstruct_coefficient]
    simp [wideHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]

/-- Nontrivial amplitudes reconstruct to nontrivial physical H1 vectors. -/
theorem wideEndpointHillReconstruct_injective :
    Function.Injective (wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall) :=
  Function.LeftInverse.injective (endpointHillH1Coordinates_wideReconstruct r hr hr1 n hn z hz q hsmall)

/-- The potential of the reconstructed physical vector is its effective potential. -/
theorem endpointH1Multiplication_wideReconstruct (u : ℂ × ℂ) :
    endpointH1Multiplication r hr hr1 q (wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall u) =
      wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u := by
  have h := wideEndpointHillTailInverse_right SpectralWeight.one r hr hr1 n hn z hz q hsmall
    (endpointHillModePotential r hr hr1 n q u)
  change wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u -
    wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u) =
        endpointHillModePotential r hr hr1 n q u at h
  change endpointH1Multiplication r hr hr1 q (endpointHillH1Modes n u +
    wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u)) = _
  rw [map_add]
  have hR := congrArg (fun T => T (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u))
    (endpointH1Multiplication_wideResolvent r hr hr1 n hn z hz q)
  simp only [ContinuousLinearMap.comp_apply] at hR
  rw [hR]
  change endpointHillModePotential r hr hr1 n q u + _ = _
  rw [← h]
  abel

/-- A vector in the effective kernel gives an eigenvector of the actual
singular Hill operator on its full original H1 domain. -/
theorem wideEndpointHillReconstruct_isEigenvector (u : ℂ × ℂ)
    (hu : wideEndpointHillReducedOperator r hr hr1 n hn z hz q hsmall u = 0) :
    singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)
      (wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall u) =
      z • singularHillDomainInclusion (wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall u) := by
  rw [singularHillOperator_eigen_iff]
  intro k
  simp only [endpointHillHminusOne_coefficient]
  have hV := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => a.val k)
    (endpointH1Multiplication_wideReconstruct r hr hr1 n hn z hz q hsmall u)
  rw [endpointH1Multiplication_apply] at hV
  rw [hV, wideEndpointHillReconstruct_coefficient]
  by_cases hkp : k = (n:ℤ)
  · subst k
    have he := congrArg Prod.fst hu
    change (z-(freeHillValue n:ℂ))*u.1 -
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u).val n = 0 at he
    simpa [wideHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega] using sub_eq_zero.mp he
  by_cases hkm : k = -(n:ℤ)
  · subst k
    have he := congrArg Prod.snd hu
    change (z-(freeHillValue n:ℂ))*u.2 -
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall u).val (-(n:ℤ)) = 0 at he
    simpa [wideHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega] using sub_eq_zero.mp he
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, wideHillSymbol, if_neg hk]
  rw [← mul_assoc, mul_inv_cancel₀ (wideHill_denominator_ne_zero n hn z hz k hk), one_mul]

/-- Every full-domain physical eigenvector satisfies the effective equation. -/
theorem singularHillEigenvector_wide_reduced (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    wideEndpointHillReducedOperator r hr hr1 n hn z hz q hsmall (endpointHillH1Coordinates n f) = 0 := by
  have he := (singularHillOperator_eigen_iff _ z f).mp hf
  apply Prod.ext
  · change (z-(freeHillValue n:ℂ))*f.val (mode (-(n:ℤ))) -
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall
        (endpointHillH1Coordinates n f)).val n = 0
    rw [← singularHillEigenvector_potential_wide r hr hr1 n hn z hz q hsmall f hf,
      endpointH1Multiplication_apply]
    exact sub_eq_zero.mpr (by simpa only [endpointHillHminusOne_coefficient] using he n)
  · change (z-(freeHillValue n:ℂ))*f.val (mode (-(-(n:ℤ)))) -
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall
        (endpointHillH1Coordinates n f)).val (-(n:ℤ)) = 0
    rw [neg_neg]
    rw [← singularHillEigenvector_potential_wide r hr hr1 n hn z hz q hsmall f hf,
      endpointH1Multiplication_apply]
    exact sub_eq_zero.mpr (by simpa only [endpointHillHminusOne_coefficient,
      freeHillValue_neg, neg_neg] using he (-(n:ℤ)))

/-- Reconstruction recovers every original physical H1 eigenvector. -/
theorem singularHillEigenvector_wide_reconstruct (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    f = wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall (endpointHillH1Coordinates n f) := by
  change f = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
    wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hsmall (endpointHillH1Coordinates n f))
  rw [← singularHillEigenvector_potential_wide r hr hr1 n hn z hz q hsmall f hf]
  exact singularHillEigenvector_decompose_wide r hr hr1 n hn z hz q f hf

/-- Exact equivalence on the entire original H1 domain, with no additional
endpoint regularity assumption on the eigenvector or its potential. -/
theorem exists_singularHillEigenvector_wide_iff :
    (∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
        z • singularHillDomainInclusion f) ↔
      ∃ u : ℂ × ℂ, u ≠ 0 ∧ wideEndpointHillReducedOperator r hr hr1 n hn z hz q hsmall u = 0 := by
  constructor
  · rintro ⟨f,hf0,hf⟩
    refine ⟨endpointHillH1Coordinates n f, ?_,
      singularHillEigenvector_wide_reduced r hr hr1 n hn z hz q hsmall f hf⟩
    intro hu0
    have he := singularHillEigenvector_wide_reconstruct r hr hr1 n hn z hz q hsmall f hf
    rw [hu0, map_zero] at he
    exact hf0 he
  · rintro ⟨u,hu0,hu⟩
    refine ⟨wideEndpointHillReconstruct r hr hr1 n hn z hz q hsmall u, ?_,
      wideEndpointHillReconstruct_isEigenvector r hr hr1 n hn z hz q hsmall u hu⟩
    intro hf0
    apply hu0
    have he := endpointHillH1Coordinates_wideReconstruct r hr hr1 n hn z hz q hsmall u
    rw [hf0, map_zero] at he
    exact he.symm

/-- Vanishing of the constructed two-mode determinant is equivalent to a
nonzero physical singular Hill eigenvector in the full original H1 domain. -/
theorem wideEndpointHillReduced_det_eq_zero_iff :
    (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hsmall).toLinearMap.det = 0 ↔
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
        singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
          z • singularHillDomainInclusion f := by
  rw [exists_singularHillEigenvector_wide_iff r hr hr1 n hn z hz q hsmall,
    LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨u,hu,hu0⟩
    exact ⟨u,hu0,hu⟩
  · rintro ⟨u,hu0,hu⟩
    exact ⟨u,hu,hu0⟩

end NLS.KdV
