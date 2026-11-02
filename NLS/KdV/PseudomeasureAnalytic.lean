import NLS.KdV.FreeHillAnalytic
import NLS.KdV.PseudomeasureReduction
import NLS.FunctionalAnalysis.AnalyticSchurComplement

/-! # Jointly analytic endpoint Hill determinants

All operator families agree with the actual singular-potential reduction.
Analyticity is in the endpoint Banach norm, jointly in the potential and
spectral parameter, at every point of the corrected closed strip where the
proved tail estimate supplies invertibility.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The strict endpoint range supplies the l1 symbol needed for the regular Wiener output. -/
def endpointInverseWienerWeight (r : ℝ) (hr1 : r < 1/2) : Coeff 1 :=
  ⟨fun k => (Weight.sobolev (2-2*r) k:ℂ)⁻¹,
    Weight.inverse_sobolev_memlp (by norm_num) (by norm_num; linarith)⟩

/-- Exact factorization of the source and target weights of the free inverse. -/
theorem endpointWienerSymbol_weight_identity (r : ℝ) (k : ℤ) :
    (Weight.sobolev 2 k:ℂ)*(Weight.sobolev (2-2*r) k:ℂ)⁻¹ =
      (Weight.sobolev r k:ℂ)/(SpectralWeight.one.negativeSobolev r k:ℂ) := by
  have h2 : Weight.sobolev 2 k =
      Weight.sobolev (2-2*r) k * Weight.sobolev r k * Weight.sobolev r k := by
    calc
      _ = Weight.sobolev ((2-2*r)+r+r) k := by rw [show (2-2*r)+r+r = (2:ℝ) by ring]
      _ = _ := by rw [Weight.sobolev_add, Weight.sobolev_add]
  simp only [h2, Complex.ofReal_mul, SpectralWeight.negativeSobolev_apply,
    SpectralWeight.one_apply, Complex.ofReal_div, Complex.ofReal_one]
  let A : ℂ := (Weight.sobolev (2-2*r) k:ℂ)
  let B : ℂ := (Weight.sobolev r k:ℂ)
  have hA : A ≠ 0 := (Weight.sobolev (2-2*r)).complex_ne_zero k
  change (A*B*B)*A⁻¹ = B/(1/B)
  calc
    _ = (A*A⁻¹)*(B*B) := by ring
    _ = _ := by simp [hA, div_eq_mul_inv]

/-- The total regular-Wiener reciprocal symbol in l1. -/
def endpointWienerSymbolFamily (r : ℝ) (hr1 : r < 1/2) (n : ℕ) (z : ℂ) : Coeff 1 :=
  Coeff.holderProduct (p := ⊤) (r := 1) (q := 1)
    (hillOrderTwoSymbolFamily n z) (endpointInverseWienerWeight r hr1)

/-- Its exact normalized multiplier coordinates on the original closed strip. -/
theorem endpointWienerSymbolFamily_apply (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    endpointWienerSymbolFamily r hr1 n z k =
      ((Weight.sobolev r k:ℂ)/(SpectralWeight.one.negativeSobolev r k:ℂ))*
        reducedHillSymbol n hn z hz k := by
  change hillOrderTwoSymbolFamily n z k * (Weight.sobolev (2-2*r) k:ℂ)⁻¹ = _
  rw [hillOrderTwoSymbolFamily_eq_symbol n hn z hz k]
  calc
    _ = ((Weight.sobolev 2 k:ℂ)*(Weight.sobolev (2-2*r) k:ℂ)⁻¹)*
        reducedHillSymbol n hn z hz k := by ring
    _ = _ := by rw [endpointWienerSymbol_weight_identity]

/-- Norm analyticity of the l1 reciprocal symbol, including closed-strip boundary points. -/
theorem analyticAt_endpointWienerSymbolFamily (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (endpointWienerSymbolFamily r hr1 n) z := by
  let P : Coeff ⊤ →L[ℂ] Coeff 1 →L[ℂ] Coeff 1 := Coeff.holderProduct
  change AnalyticAt ℂ ((P.flip (endpointInverseWienerWeight r hr1)) ∘ hillOrderTwoSymbolFamily n) z
  exact ((P.flip (endpointInverseWienerWeight r hr1)).analyticAt _).comp
    (analyticAt_hillOrderTwoSymbolFamily n hn z hz)

/-- The proof-independent free inverse from endpoint data to the regular Wiener predual. -/
def endpointWienerResolventFamily (r : ℝ) (hr1 : r < 1/2) (n : ℕ) (z : ℂ) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ →L[ℂ]
      WeightedCoeff (Weight.sobolev r) 1 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev r) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((Coeff.holderProduct (p := ⊤) (r := 1) (q := 1)).flip
      (endpointWienerSymbolFamily r hr1 n z)).comp
        (WeightedCoeff.weightIsometry (SpectralWeight.one.negativeSobolev r) ⊤).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The analytic operator retains the exact raw reduced inverse coefficients. -/
theorem endpointWienerResolventFamily_apply (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointWienerResolventFamily r hr1 n z a).val k =
      reducedHillSymbol n hn z hz k * a.val k := by
  change ((SpectralWeight.one.negativeSobolev r k:ℂ)*a.val k*
    endpointWienerSymbolFamily r hr1 n z k)/(Weight.sobolev r k:ℂ) = _
  rw [endpointWienerSymbolFamily_apply r hr1 n hn z hz k]
  let W : ℂ := (SpectralWeight.one.negativeSobolev r k:ℂ)
  let V : ℂ := (Weight.sobolev r k:ℂ)
  have hW : W ≠ 0 := (SpectralWeight.one.negativeSobolev r).complex_ne_zero k
  have hV : V ≠ 0 := (Weight.sobolev r).complex_ne_zero k
  change (W*a.val k*((V/W)*reducedHillSymbol n hn z hz k))/V = _
  calc
    _ = (W/W)*(V/V)*(reducedHillSymbol n hn z hz k*a.val k) := by ring
    _ = _ := by rw [div_self hW, div_self hV, one_mul, one_mul]

/-- Equality to the already constructed physical H1 reduced inverse followed
by the original H1-to-Wiener inclusion. -/
theorem endpointWienerResolventFamily_eq (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    endpointWienerResolventFamily r hr1 n z = (endpointH1ToWiener r hr1).comp
      (endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz) := by
  ext a
  apply Subtype.ext
  funext k
  rw [endpointWienerResolventFamily_apply r hr1 n hn z hz]
  exact ((endpointH1ToWiener_apply r hr1 _ k).trans
    (endpointReducedHillResolventH1Original_coefficient SpectralWeight.one r hr1 n hn z hz a k)).symm

/-- Analyticity of the free inverse in the bounded-operator norm. -/
theorem analyticAt_endpointWienerResolventFamily (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (endpointWienerResolventFamily r hr1 n) z := by
  let P : Coeff ⊤ →L[ℂ] Coeff 1 →L[ℂ] Coeff 1 := Coeff.holderProduct
  have hP := (P.flip.analyticAt (endpointWienerSymbolFamily r hr1 n z)).comp
    (analyticAt_endpointWienerSymbolFamily r hr1 n hn z hz)
  exact SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM hP analyticAt_const)

/-- The actual endpoint tail family, jointly parameterized by q and lambda. -/
def endpointTailFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ →L[ℂ]
      WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  (WeightedCoeff.signedSobolevConvolutionBilinear r hr p.1).comp
    (endpointWienerResolventFamily r hr1 n p.2)

/-- No formal replacement of the source Fourier operator is used. -/
theorem endpointTailFamily_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n) :
    endpointTailFamily r hr hr1 n p =
      unshiftedEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn p.2 hz p.1 := by
  ext a
  apply Subtype.ext
  funext m
  change (WeightedCoeff.signedSobolevConvolutionBilinear r hr p.1
    (endpointWienerResolventFamily r hr1 n p.2 a)).val m = _
  rw [WeightedCoeff.signedSobolevConvolutionBilinear_eq, WeightedCoeff.signedSobolevConvolutionCLM_apply,
    WeightedCoeff.signedSobolevConvolution_apply, unshiftedEndpointHillPerturbation_apply]
  apply tsum_congr
  intro k
  rw [endpointWienerResolventFamily_apply r hr1 n hn p.2 hz]
  ring

/-- Joint endpoint-operator norm analyticity at every closed-strip parameter. -/
theorem analyticAt_endpointTailFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n) : AnalyticAt ℂ (endpointTailFamily r hr hr1 n) p := by
  have hq := ((WeightedCoeff.signedSobolevConvolutionBilinear r hr).analyticAt p.1).comp
    ((ContinuousLinearMap.fst ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p)
  have hR := (analyticAt_endpointWienerResolventFamily r hr1 n hn p.2 hz).comp
    ((ContinuousLinearMap.snd ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p)
  exact SchurComplement.analyticAt_compCLM hq hR

/-- The already proved numerical cutoff gives invertibility on the original carrier,
even though the half-contraction estimate was established in shifted norms. -/
theorem isUnit_one_sub_endpointTailFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    IsUnit (1-endpointTailFamily r hr hr1 n p) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro a b hab
    have h := congrArg (endpointHillTailInverse SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs) hab
    change endpointHillTailInverse SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs
      (a-endpointTailFamily r hr hr1 n p a) =
        endpointHillTailInverse SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs
          (b-endpointTailFamily r hr hr1 n p b) at h
    rw [endpointTailFamily_eq r hr hr1 n hn p hz, endpointHillTailInverse_left,
      endpointHillTailInverse_left] at h
    exact h
  · intro a
    refine ⟨endpointHillTailInverse SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs a,?_⟩
    change endpointHillTailInverse SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs a -
      endpointTailFamily r hr hr1 n p
        (endpointHillTailInverse SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs a) = a
    rw [endpointTailFamily_eq r hr hr1 n hn p hz, endpointHillTailInverse_right]

/-- A single proof-independent inverse family on the entire parameter space. -/
def endpointInverseFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ →L[ℂ]
      WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  Ring.inverse (1-endpointTailFamily r hr hr1 n p)

/-- The analytic inverse is exactly the previously proved actual tail inverse. -/
theorem endpointInverseFamily_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    endpointInverseFamily r hr hr1 n p =
      endpointHillTailInverse SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs := by
  let K := endpointTailFamily r hr hr1 n p
  let R := endpointHillTailInverse SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs
  have hu : IsUnit (1-K) := isUnit_one_sub_endpointTailFamily r hr hr1 n hn p hz hs
  have hR : (1-K)*R = 1 := by
    ext a
    change R a-K (R a) = a
    simpa only [K,R,endpointTailFamily_eq r hr hr1 n hn p hz] using
      endpointHillTailInverse_right SpectralWeight.one r hr hr1 n hn p.2 hz p.1 hs a
  change Ring.inverse (1-K) = R
  calc
    Ring.inverse (1-K) = Ring.inverse (1-K)*1 := (mul_one _).symm
    _ = Ring.inverse (1-K)*((1-K)*R) := by rw [hR]
    _ = (Ring.inverse (1-K)*(1-K))*R := (mul_assoc _ _ _).symm
    _ = R := by rw [Ring.inverse_mul_cancel _ hu, one_mul]

/-- Analyticity persists even at a zero of the effective determinant: only
the complementary operator is inverted here. -/
theorem analyticAt_endpointInverseFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointInverseFamily r hr hr1 n) p := by
  have hT := analyticAt_endpointTailFamily r hr hr1 n hn p hz
  have hA : AnalyticAt ℂ (fun y : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ =>
      (1 : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ →L[ℂ]
        WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)-endpointTailFamily r hr hr1 n y) p :=
    analyticAt_const.sub hT
  exact (analyticOnNhd_inverse (𝕜 := ℂ) _
    (isUnit_one_sub_endpointTailFamily r hr hr1 n hn p hz hs)).comp
      (f := fun y : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ =>
        (1 : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ →L[ℂ]
          WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)-endpointTailFamily r hr hr1 n y) hA

/-- The parameter family of physical potential terms on the two resonant modes. -/
def endpointModePotentialFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    (ℂ × ℂ) →L[ℂ] WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  (WeightedCoeff.signedSobolevConvolutionBilinear r hr p.1).comp
    ((endpointH1ToWiener r hr1).comp (endpointHillH1Modes n))

/-- Agreement of the analytic family with the original physical mode potential. -/
theorem endpointModePotentialFamily_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    endpointModePotentialFamily r hr hr1 n p = endpointHillModePotential r hr hr1 n p.1 := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [endpointModePotentialFamily, endpointHillModePotential, endpointH1Multiplication,
    ContinuousLinearMap.comp_apply, WeightedCoeff.signedSobolevConvolutionBilinear_eq]

/-- Joint analyticity of the resonant source terms. -/
theorem analyticAt_endpointModePotentialFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    AnalyticAt ℂ (endpointModePotentialFamily r hr hr1 n) p := by
  have hq := ((WeightedCoeff.signedSobolevConvolutionBilinear r hr).analyticAt p.1).comp
    ((ContinuousLinearMap.fst ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p)
  exact SchurComplement.analyticAt_compCLM hq analyticAt_const

/-- The total family of effective corrected potentials. -/
def endpointEffectiveFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    (ℂ × ℂ) →L[ℂ] WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  (endpointInverseFamily r hr hr1 n p).comp (endpointModePotentialFamily r hr hr1 n p)

/-- The actual two-mode operator, now as one family independent of proof arguments. -/
def endpointReducedFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (p.2-(freeHillValue n:ℂ)) • ContinuousLinearMap.id ℂ (ℂ × ℂ) -
    (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n).comp
      (endpointEffectiveFamily r hr hr1 n p)

/-- Exact equality with the constructed source effective operator. -/
theorem endpointReducedFamily_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    endpointReducedFamily r hr hr1 n p = endpointHillReducedOperator r hr hr1 n hn p.2 hz p.1 hs := by
  unfold endpointReducedFamily endpointHillReducedOperator endpointEffectiveFamily endpointHillEffectivePotential
  rw [endpointInverseFamily_eq r hr hr1 n hn p hz hs, endpointModePotentialFamily_eq]

/-- Joint bounded-operator norm analyticity of the effective two-mode family. -/
theorem analyticAt_endpointReducedFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointReducedFamily r hr hr1 n) p := by
  have hE := SchurComplement.analyticAt_compCLM
    (analyticAt_endpointInverseFamily r hr hr1 n hn p hz hs)
    (analyticAt_endpointModePotentialFamily r hr hr1 n p)
  have hz' := (ContinuousLinearMap.snd ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p
  exact ((hz'.sub analyticAt_const).smul analyticAt_const).sub
    (SchurComplement.analyticAt_compCLM analyticAt_const hE)

/-- One analytic scalar function for the singular physical endpoint reduction. -/
def endpointReducedDeterminant (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) : ℂ :=
  (endpointReducedFamily r hr hr1 n p).toLinearMap.det

/-- The determinant is jointly analytic in the full endpoint potential norm
and spectral parameter, including its zeros and closed-strip boundary points. -/
theorem analyticAt_endpointReducedDeterminant (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointReducedDeterminant r hr hr1 n) p :=
  FiniteSpectralDeterminant.analyticAt_det (analyticAt_endpointReducedFamily r hr hr1 n hn p hz hs)

/-- The analytic determinant detects the actual full-domain physical eigen-equation. -/
theorem endpointReducedDeterminant_eq_zero_iff (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    endpointReducedDeterminant r hr hr1 n p = 0 ↔
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
        singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 p.1) f =
          p.2 • singularHillDomainInclusion f := by
  rw [endpointReducedDeterminant, endpointReducedFamily_eq r hr hr1 n hn p hz hs,
    endpointHillReduced_det_eq_zero_iff]

end NLS.KdV
