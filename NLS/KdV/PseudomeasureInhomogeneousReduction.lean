import NLS.KdV.PseudomeasureReconstructionAnalytic
import NLS.KdV.SingularHillOperatorDomain

/-!
# Inhomogeneous reduction on the entire physical H1 domain

The right-hand side is arbitrary endpoint data, represented in the original
H-minus-one space. Every H1 solution splits into the analytic resonant lift
and an analytic complementary response. This converse is needed for physical
root chains; a homogeneous eigenvector equivalence alone is insufficient.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The analytic complementary response to an endpoint right-hand side. -/
def endpointResponseFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ →L[ℂ]
      FourierLebesgueSpace (2:ℝ) 1 2 :=
  (endpointH1ResolventFamily r hr1 n p.2).comp (endpointInverseFamily r hr hr1 n p)

/-- The full complementary H1 response is jointly operator-norm analytic. -/
theorem analyticAt_endpointResponseFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointResponseFamily r hr hr1 n) p := by
  have hR := (analyticAt_endpointH1ResolventFamily r hr1 n hn p.2 hz).comp
    ((ContinuousLinearMap.snd ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p)
  exact SchurComplement.analyticAt_compCLM hR
    (analyticAt_endpointInverseFamily r hr hr1 n hn p hz hs)

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- The inhomogeneous physical pencil equation retains its exact raw Fourier equation. -/
theorem endpointPhysicalPencil_inhomogeneous_coefficient
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g) (k : ℤ) :
    (z-(freeHillValue k:ℂ))*f.val (mode (-k)) =
      (endpointH1Multiplication r hr hr1 q f).val k + g.val k := by
  change z • singularHillDomainInclusion f -
    (singularHillLaplacian f + hminusOneMultiplication
      (endpointHillHminusOne SpectralWeight.one r hr1 q) f) = _ at hf
  rw [← endpointH1Multiplication_physical r hr hr1 q f] at hf
  have he := congrArg (fun u : FourierLebesgueSpace (2:ℝ) (-1) 2 => u.val (mode (-k))) hf
  change z * (singularHillDomainInclusion f).val (mode (-k)) -
    ((singularHillLaplacian f).val (mode (-k)) +
      (endpointHillHminusOne SpectralWeight.one r hr1
        (endpointH1Multiplication r hr hr1 q f)).val (mode (-k))) =
      (endpointHillHminusOne SpectralWeight.one r hr1 g).val (mode (-k)) at he
  rw [singularHillDomainInclusion_coefficient, singularHillLaplacian_coefficient,
    endpointHillHminusOne_coefficient, endpointHillHminusOne_coefficient] at he
  linear_combination he

include hn hz in
/-- Every original H1 inhomogeneous solution admits the exact free-mode decomposition. -/
theorem endpointPhysicalPencil_inhomogeneous_decompose
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
  rw [endpointHillH1Modes_coefficient, endpointH1ResolventFamily_coefficient r hr1 n hn z hz,
    endpointHillH1Coordinates_apply]
  by_cases hkp : k = (n:ℤ)
  · subst k
    simp [reducedHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
  by_cases hkm : k = -(n:ℤ)
  · subst k
    simp [reducedHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, reducedHillSymbol, if_neg hk]
  change f.val (mode (-k)) = (z-(freeHillValue k:ℂ))⁻¹ *
    ((endpointH1Multiplication r hr hr1 q f).val k + g.val k)
  rw [← endpointPhysicalPencil_inhomogeneous_coefficient r hr hr1 z q g f hf k,
    ← mul_assoc, inv_mul_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

include hn hz hs in
/-- The solved total forcing of every physical solution is the canonical tail inverse. -/
theorem endpointPhysicalPencil_inhomogeneous_totalForcing
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g) :
    endpointH1Multiplication r hr hr1 q f + g =
      endpointInverseFamily r hr hr1 n (q,z)
        (endpointHillModePotential r hr hr1 n q (endpointHillH1Coordinates n f) + g) := by
  rw [endpointInverseFamily_eq r hr hr1 n hn (q,z) hz hs]
  apply endpointHillTailInverse_unique SpectralWeight.one r hr hr1 n hn z hz q hs
  have he := congrArg (endpointH1Multiplication r hr hr1 q)
    (endpointPhysicalPencil_inhomogeneous_decompose r hr hr1 n hn z hz q g f hf)
  rw [map_add, endpointH1ResolventFamily_eq r hr1 n hn z hz] at he
  have hR := congrArg (fun T => T (endpointH1Multiplication r hr hr1 q f + g))
    (endpointH1Multiplication_resolvent r hr hr1 n hn z hz q)
  simp only [ContinuousLinearMap.comp_apply] at hR
  rw [hR] at he
  change endpointH1Multiplication r hr hr1 q f =
    endpointHillModePotential r hr hr1 n q (endpointHillH1Coordinates n f) + _ at he
  nth_rw 1 [he]
  abel

include hn hz hs in
/-- Full-domain inhomogeneous reconstruction: the resonant lift plus the
complementary response recovers every original physical H1 solution. -/
theorem endpointPhysicalPencil_inhomogeneous_reconstruct
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g) :
    f = endpointReconstructionFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f) +
      endpointResponseFamily r hr hr1 n (q,z) g := by
  calc
    f = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
        endpointH1ResolventFamily r hr1 n z (endpointH1Multiplication r hr hr1 q f + g) :=
      endpointPhysicalPencil_inhomogeneous_decompose r hr hr1 n hn z hz q g f hf
    _ = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
        endpointH1ResolventFamily r hr1 n z
          (endpointInverseFamily r hr hr1 n (q,z)
            (endpointHillModePotential r hr hr1 n q (endpointHillH1Coordinates n f) + g)) := by
      rw [endpointPhysicalPencil_inhomogeneous_totalForcing r hr hr1 n hn z hz q hs g f hf]
    _ = _ := by
      simp only [endpointReconstructionFamily, endpointResponseFamily, endpointEffectiveFamily,
        endpointModePotentialFamily_eq, _root_.add_apply, ContinuousLinearMap.comp_apply, map_add, add_assoc]

include hn hz in
/-- The complementary response has zero physical resonant coordinates. -/
theorem endpointResponseFamily_coordinates :
    (endpointHillH1Coordinates n).comp (endpointResponseFamily r hr hr1 n (q,z)) = 0 := by
  apply ContinuousLinearMap.ext
  intro g
  apply Prod.ext
  · change (endpointH1ResolventFamily r hr1 n z
      (endpointInverseFamily r hr hr1 n (q,z) g)).val (mode (-(n:ℤ))) = 0
    rw [endpointH1ResolventFamily_coefficient r hr1 n hn z hz]
    simp [reducedHillSymbol]
  · change (endpointH1ResolventFamily r hr1 n z
      (endpointInverseFamily r hr hr1 n (q,z) g)).val (mode (-(-(n:ℤ)))) = 0
    rw [endpointH1ResolventFamily_coefficient r hr1 n hn z hz]
    simp [reducedHillSymbol]

include hn hz hs in
/-- The complementary response solves the full physical equation with exactly
the finite resonant defect of the solved forcing. -/
theorem endpointResponseFamily_residual
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    endpointPhysicalPencilFamily r hr1 (q,z) (endpointResponseFamily r hr hr1 n (q,z) g) =
      endpointHillHminusOne SpectralWeight.one r hr1 g -
        singularHillDomainInclusion (endpointHillH1Modes n
          (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
            (endpointInverseFamily r hr hr1 n (q,z) g))) := by
  let a := endpointInverseFamily r hr hr1 n (q,z) g
  let T := unshiftedEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q
  have hK : a-T a = g := by
    simpa only [a, T, endpointInverseFamily_eq r hr hr1 n hn (q,z) hz hs] using
      endpointHillTailInverse_right SpectralWeight.one r hr hr1 n hn z hz q hs g
  have hM : hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q)
      (endpointH1ResolventFamily r hr1 n z a) =
        endpointHillHminusOne SpectralWeight.one r hr1 (T a) := by
    rw [← endpointH1Multiplication_physical r hr hr1 q]
    apply congrArg (endpointHillHminusOne SpectralWeight.one r hr1)
    rw [endpointH1ResolventFamily_eq r hr1 n hn z hz]
    exact congrArg (fun S => S a) (endpointH1Multiplication_resolvent r hr hr1 n hn z hz q)
  change z • singularHillDomainInclusion (endpointH1ResolventFamily r hr1 n z a) -
    (singularHillLaplacian (endpointH1ResolventFamily r hr1 n z a) +
      hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q)
        (endpointH1ResolventFamily r hr1 n z a)) = _
  rw [hM, sub_add_eq_sub_sub, endpointH1ResolventFamily_free_residual r hr1 n hn z hz]
  have he : endpointHillHminusOne SpectralWeight.one r hr1 a -
      endpointHillHminusOne SpectralWeight.one r hr1 (T a) =
        endpointHillHminusOne SpectralWeight.one r hr1 g := by
    rw [← map_sub, hK]
  rw [← he]
  abel

/-- Reading the two physical modes recovers their amplitudes exactly. -/
theorem endpointHillH1Coordinates_modes (m : ℕ) (hm : 1 ≤ m) (u : ℂ × ℂ) :
    endpointHillH1Coordinates m (endpointHillH1Modes m u) = u := by
  rw [endpointHillH1Coordinates_apply]
  apply Prod.ext
  · rw [endpointHillH1Modes_coefficient]
    simp [show (m:ℤ) ≠ -(m:ℤ) by omega]
  · simpa [show -(m:ℤ) ≠ (m:ℤ) by omega] using
      endpointHillH1Modes_coefficient m u (-(m:ℤ))

include hn hz hs in
/-- The constructed physical solution satisfies the full inhomogeneous
equation exactly when its two amplitudes satisfy the actual reduced system. -/
theorem endpointPhysicalPencil_reconstruction_iff
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (u : ℂ × ℂ) :
    endpointPhysicalPencilFamily r hr1 (q,z)
      (endpointReconstructionFamily r hr hr1 n (q,z) u +
        endpointResponseFamily r hr hr1 n (q,z) g) =
      endpointHillHminusOne SpectralWeight.one r hr1 g ↔
    endpointReducedFamily r hr hr1 n (q,z) u =
      hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
        (endpointInverseFamily r hr hr1 n (q,z) g) := by
  have hF := congrArg (fun T => T u)
    (endpointReconstructionFamily_residual r hr hr1 n hn (q,z) hz hs)
  simp only [ContinuousLinearMap.comp_apply] at hF
  rw [map_add, hF, endpointResponseFamily_residual r hr hr1 n hn z hz q hs]
  let J := fun v : ℂ × ℂ => singularHillDomainInclusion (endpointHillH1Modes n v)
  have hi : Function.Injective J := singularHillDomainInclusion_injective.comp
    (Function.LeftInverse.injective (endpointHillH1Coordinates_modes n hn))
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
/-- Every original H1 solution satisfies the finite inhomogeneous equation. -/
theorem endpointPhysicalPencil_inhomogeneous_reduced
    (g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : endpointPhysicalPencilFamily r hr1 (q,z) f =
      endpointHillHminusOne SpectralWeight.one r hr1 g) :
    endpointReducedFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f) =
      hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
        (endpointInverseFamily r hr hr1 n (q,z) g) := by
  apply (endpointPhysicalPencil_reconstruction_iff r hr hr1 n hn z hz q hs g _).mp
  rw [← endpointPhysicalPencil_inhomogeneous_reconstruct r hr hr1 n hn z hz q hs g f hf]
  exact hf

include hn hz hs in
/-- Exact full-domain inhomogeneous normal form: both reconstruction and the
finite equation are necessary and sufficient, including at determinant zeros. -/
theorem endpointPhysicalPencil_inhomogeneous_iff
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
    exact ⟨endpointPhysicalPencil_inhomogeneous_reconstruct r hr hr1 n hn z hz q hs g f hf,
      endpointPhysicalPencil_inhomogeneous_reduced r hr hr1 n hn z hz q hs g f hf⟩
  · rintro ⟨hd, he⟩
    have hsol := (endpointPhysicalPencil_reconstruction_iff r hr hr1 n hn z hz q hs g _).mpr he
    rw [← hd] at hsol
    exact hsol

end NLS.KdV
