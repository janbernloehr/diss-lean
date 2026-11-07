import NLS.KdV.PseudomeasureWideReconstruction

/-! Exact full-domain inhomogeneous reduction on the entire printed 12n
strip, using the same total analytic response and reconstruction families. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

theorem analyticAt_endpointResponseFamily_wide (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointResponseFamily r hr hr1 n) p := by
  have hR := (analyticAt_endpointH1ResolventFamily_wide r hr1 n hn p.2 hz).comp
    ((ContinuousLinearMap.snd ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p)
  exact SchurComplement.analyticAt_compCLM hR
    (analyticAt_endpointInverseFamily_wide r hr hr1 n hn p hz hs)

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hz in
theorem endpointPhysicalPencil_inhomogeneous_decompose_wide
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g) :
    f = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
      endpointH1ResolventFamily r hr1 n z (endpointH1Multiplication r hr hr1 q f + g) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  change f.val (mode (-k)) =
    (endpointHillH1Modes n (endpointHillH1Coordinates n f)).val (mode (-k)) +
      (endpointH1ResolventFamily r hr1 n z (endpointH1Multiplication r hr hr1 q f + g)).val (mode (-k))
  rw [endpointHillH1Modes_coefficient, endpointH1ResolventFamily_coefficient_wide r hr1 n hn z hz,
    endpointHillH1Coordinates_apply]
  by_cases hkp : k = (n:ℤ)
  · subst k
    simp [wideHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
  by_cases hkm : k = -(n:ℤ)
  · subst k
    simp [wideHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, wideHillSymbol, if_neg hk]
  change f.val (mode (-k)) = (z-(freeHillValue k:ℂ))⁻¹ *
    ((endpointH1Multiplication r hr hr1 q f).val k + g.val k)
  rw [← endpointPhysicalPencil_inhomogeneous_coefficient r hr hr1 z q g f hf k,
    ← mul_assoc, inv_mul_cancel₀ (wideHill_denominator_ne_zero n hn z hz k hk), one_mul]


include hn hz hs in
theorem endpointPhysicalPencil_inhomogeneous_totalForcing_wide
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g) :
    endpointH1Multiplication r hr hr1 q f + g =
      endpointInverseFamily r hr hr1 n (q,z)
        (endpointHillModePotential r hr hr1 n q (endpointHillH1Coordinates n f) + g) := by
  rw [endpointInverseFamily_eq_wide r hr hr1 n hn (q,z) hz hs]
  apply wideEndpointHillTailInverse_unique SpectralWeight.one r hr hr1 n hn z hz q hs
  have he := congrArg (endpointH1Multiplication r hr hr1 q)
    (endpointPhysicalPencil_inhomogeneous_decompose_wide r hr hr1 n hn z hz q g f hf)
  rw [map_add, endpointH1ResolventFamily_eq_wide r hr1 n hn z hz] at he
  have hR := congrArg (fun T => T (endpointH1Multiplication r hr hr1 q f + g))
    (endpointH1Multiplication_wideResolvent r hr hr1 n hn z hz q)
  simp only [ContinuousLinearMap.comp_apply] at hR
  rw [hR] at he
  change endpointH1Multiplication r hr hr1 q f =
    endpointHillModePotential r hr hr1 n q (endpointHillH1Coordinates n f) + _ at he
  nth_rw 1 [he]
  abel


include hn hz hs in
theorem endpointPhysicalPencil_inhomogeneous_reconstruct_wide
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g) :
    f = endpointReconstructionFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f) +
      endpointResponseFamily r hr hr1 n (q,z) g := by
  calc
    f = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
        endpointH1ResolventFamily r hr1 n z (endpointH1Multiplication r hr hr1 q f + g) :=
      endpointPhysicalPencil_inhomogeneous_decompose_wide r hr hr1 n hn z hz q g f hf
    _ = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
        endpointH1ResolventFamily r hr1 n z
          (endpointInverseFamily r hr hr1 n (q,z)
            (endpointHillModePotential r hr hr1 n q (endpointHillH1Coordinates n f) + g)) := by
      rw [endpointPhysicalPencil_inhomogeneous_totalForcing_wide r hr hr1 n hn z hz q hs g f hf]
    _ = _ := by
      simp only [endpointReconstructionFamily, endpointResponseFamily, endpointEffectiveFamily,
        endpointModePotentialFamily_eq, _root_.add_apply, ContinuousLinearMap.comp_apply, map_add, add_assoc]


include hn hz in
theorem endpointResponseFamily_coordinates_wide :
    (endpointHillH1Coordinates n).comp (endpointResponseFamily r hr hr1 n (q,z)) = 0 := by
  apply ContinuousLinearMap.ext
  intro g
  apply Prod.ext
  · change (endpointH1ResolventFamily r hr1 n z
      (endpointInverseFamily r hr hr1 n (q,z) g)).val (mode (-(n:ℤ))) = 0
    rw [endpointH1ResolventFamily_coefficient_wide r hr1 n hn z hz]
    simp [wideHillSymbol]
  · change (endpointH1ResolventFamily r hr1 n z
      (endpointInverseFamily r hr hr1 n (q,z) g)).val (mode (-(-(n:ℤ)))) = 0
    rw [endpointH1ResolventFamily_coefficient_wide r hr1 n hn z hz]
    simp [wideHillSymbol]


include hn hz hs in
theorem endpointResponseFamily_residual_wide
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    endpointPhysicalPencilFamily r hr1 (q,z) (endpointResponseFamily r hr hr1 n (q,z) g) =
      endpointHillHminusOne SpectralWeight.one r hr1 g -
        singularHillDomainInclusion (endpointHillH1Modes n
          (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
            (endpointInverseFamily r hr hr1 n (q,z) g))) := by
  let a := endpointInverseFamily r hr hr1 n (q,z) g
  let T := wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q
  have hK : a-T a = g := by
    simpa only [a, T, endpointInverseFamily_eq_wide r hr hr1 n hn (q,z) hz hs] using
      wideEndpointHillTailInverse_right SpectralWeight.one r hr hr1 n hn z hz q hs g
  have hM : hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q)
      (endpointH1ResolventFamily r hr1 n z a) =
        endpointHillHminusOne SpectralWeight.one r hr1 (T a) := by
    rw [← endpointH1Multiplication_physical r hr hr1 q]
    apply congrArg (endpointHillHminusOne SpectralWeight.one r hr1)
    rw [endpointH1ResolventFamily_eq_wide r hr1 n hn z hz]
    exact congrArg (fun S => S a) (endpointH1Multiplication_wideResolvent r hr hr1 n hn z hz q)
  change z • singularHillDomainInclusion (endpointH1ResolventFamily r hr1 n z a) -
    (singularHillLaplacian (endpointH1ResolventFamily r hr1 n z a) +
      hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q)
        (endpointH1ResolventFamily r hr1 n z a)) = _
  rw [hM, sub_add_eq_sub_sub, endpointH1ResolventFamily_free_residual_wide r hr1 n hn z hz]
  have he : endpointHillHminusOne SpectralWeight.one r hr1 a -
      endpointHillHminusOne SpectralWeight.one r hr1 (T a) =
        endpointHillHminusOne SpectralWeight.one r hr1 g := by
    rw [← map_sub, hK]
  rw [← he]
  abel


include hn hz hs in
theorem endpointPhysicalPencil_reconstruction_iff_wide
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (u : ℂ × ℂ) :
    endpointPhysicalPencilFamily r hr1 (q,z)
      (endpointReconstructionFamily r hr hr1 n (q,z) u +
        endpointResponseFamily r hr hr1 n (q,z) g) =
      endpointHillHminusOne SpectralWeight.one r hr1 g ↔
    endpointReducedFamily r hr hr1 n (q,z) u =
      hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
        (endpointInverseFamily r hr hr1 n (q,z) g) := by
  have hF := congrArg (fun T => T u)
    (endpointReconstructionFamily_residual_wide r hr hr1 n hn (q,z) hz hs)
  simp only [ContinuousLinearMap.comp_apply] at hF
  rw [map_add, hF, endpointResponseFamily_residual_wide r hr hr1 n hn z hz q hs]
  let J := fun v : ℂ × ℂ => singularHillDomainInclusion (endpointHillH1Modes n v)
  have hi : Function.Injective J := singularHillDomainInclusion_injective.comp
    (Function.LeftInverse.injective (endpointHillH1Coordinates_modes n (by omega)))
  change J (endpointReducedFamily r hr hr1 n (q,z) u) +
    (endpointHillHminusOne SpectralWeight.one r hr1 g -
      J (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
        (endpointInverseFamily r hr hr1 n (q,z) g))) = _ ↔ _
  constructor
  · intro he
    apply hi
    rw [← add_sub_assoc, sub_eq_iff_eq_add] at he
    exact add_right_cancel (he.trans (add_comm _ _))
  · intro he
    rw [he]
    abel


include hn hz hs in
theorem endpointPhysicalPencil_inhomogeneous_reduced_wide
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g) :
    endpointReducedFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f) =
      hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
        (endpointInverseFamily r hr hr1 n (q,z) g) := by
  apply (endpointPhysicalPencil_reconstruction_iff_wide r hr hr1 n hn z hz q hs g _).mp
  rw [← endpointPhysicalPencil_inhomogeneous_reconstruct_wide r hr hr1 n hn z hz q hs g f hf]
  exact hf


include hn hz hs in
theorem endpointPhysicalPencil_inhomogeneous_iff_wide
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g ↔
    f = endpointReconstructionFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f) +
        endpointResponseFamily r hr hr1 n (q,z) g ∧
      endpointReducedFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f) =
        hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
          (endpointInverseFamily r hr hr1 n (q,z) g) := by
  constructor
  · intro hf
    exact ⟨endpointPhysicalPencil_inhomogeneous_reconstruct_wide r hr hr1 n hn z hz q hs g f hf,
      endpointPhysicalPencil_inhomogeneous_reduced_wide r hr hr1 n hn z hz q hs g f hf⟩
  · rintro ⟨hd, he⟩
    have hsol := (endpointPhysicalPencil_reconstruction_iff_wide r hr hr1 n hn z hz q hs g _).mpr he
    rw [← hd] at hsol
    exact hsol


end NLS.KdV
