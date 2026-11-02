import NLS.KdV.HillReduction
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.FunctionalAnalysis.AnalyticSchurComplement

/-!
# Analytic dependence of the actual Hill reduction

The reciprocal coefficients are assembled by the generic total sequence
constructor. Their proved Hilbert bound upgrades the scalar reciprocal
functions to Banach analyticity. The resulting operator families agree
with the constructed Hill complement and two-mode reduction wherever
their explicit strip and norm-cutoff hypotheses hold.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- The open interior of the already proved radius-6n strip. -/
def openHillStrip (n : ℕ) : Set ℂ := {z | |z.re-freeHillValue n| < 6*(n : ℝ)}

theorem isOpen_openHillStrip (n : ℕ) : IsOpen (openHillStrip n) := by
  apply isOpen_lt _ continuous_const
  exact (Complex.continuous_re.sub continuous_const).abs

theorem openHillStrip_subset (n : ℕ) : openHillStrip n ⊆ reducedHillStrip n :=
  fun z hz => (show |z.re-freeHillValue n| < 6*(n : ℝ) from hz).le

/-- A total Hilbert-valued reciprocal family; analyticity is asserted only
where the actual reciprocal coordinates and uniform bounds are proved. -/
def hillReciprocal (n : ℕ) (z : ℂ) : Coeff 2 :=
  Coeff.ofFunctionOrZero 2
    (fun k => if k.natAbs = n then 0 else (z-(freeHillValue k : ℂ))⁻¹)

theorem hillReciprocal_eq_symbol (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) :
    hillReciprocal n z = reducedHillHilbertSymbol n hn z hz :=
  Coeff.ofFunctionOrZero_eq_of_coordinates _ _ (reducedHillHilbertSymbol_apply n hn z hz)

theorem hillReciprocal_apply (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    hillReciprocal n z k = if k.natAbs = n then 0 else (z-(freeHillValue k : ℂ))⁻¹ := by
  rw [hillReciprocal_eq_symbol n hn z hz, reducedHillHilbertSymbol_apply]

theorem norm_hillReciprocal_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) : ‖hillReciprocal n z‖ ≤ 4/(n : ℝ) := by
  rw [hillReciprocal_eq_symbol n hn z hz]
  exact norm_reducedHillHilbertSymbol_le n hn z hz

/-- Analyticity is in the Hilbert norm, not merely coordinatewise. -/
theorem analyticOnNhd_hillReciprocal (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillReciprocal n) (openHillStrip n) := by
  apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ (isOpen_openHillStrip n) _ (4/(n : ℝ))
    (fun z hz => norm_hillReciprocal_le n hn z (openHillStrip_subset n hz))
  intro k z hz
  by_cases hk : k.natAbs = n
  · apply (analyticAt_const (v := (0 : ℂ))).congr
    filter_upwards [(isOpen_openHillStrip n).mem_nhds hz] with y hy
    rw [hillReciprocal_apply n hn y (openHillStrip_subset n hy), if_pos hk]
  · have hi : AnalyticAt ℂ (fun y : ℂ => (y-(freeHillValue k : ℂ))⁻¹) z :=
      (analyticAt_id.sub analyticAt_const).inv
        (freeHill_denominator_ne_zero hn (openHillStrip_subset n hz) hk)
    apply hi.congr
    filter_upwards [(isOpen_openHillStrip n).mem_nhds hz] with y hy
    rw [hillReciprocal_apply n hn y (openHillStrip_subset n hy), if_neg hk]

/-- A proof-independent complementary inverse family on the full parameter plane. -/
def hillComplementFamily (w : Weight) (n : ℕ) (z : ℂ) :
    WeightedCoeff w 2 →L[ℂ] WeightedCoeff w 1 :=
  WeightedCoeff.holderMultiplier w (hillReciprocal n z)

theorem hillComplementFamily_eq (w : Weight) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) :
    hillComplementFamily w n z = hillComplementToL1 w n hn z hz := by
  unfold hillComplementFamily hillComplementToL1
  rw [hillReciprocal_eq_symbol n hn z hz]

theorem analyticOnNhd_hillComplementFamily (w : Weight) (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillComplementFamily w n) (openHillStrip n) := by
  intro z hz
  let P : Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] Coeff 1 := Coeff.holderProduct
  have hp := (P.flip.analyticAt (hillReciprocal n z)).comp (analyticOnNhd_hillReciprocal n hn z hz)
  exact SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM hp analyticAt_const)

/-- The joint (potential, spectral parameter) tail family. -/
def hillTailFamily (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) :
    WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2 :=
  (w.convolutionCLM p.1).comp (hillComplementFamily w.toWeight n p.2)

theorem hillTailFamily_eq (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n) :
    hillTailFamily w n p = hillTailPerturbation w p.1 n hn p.2 hz := by
  unfold hillTailFamily hillTailPerturbation
  rw [hillComplementFamily_eq w.toWeight n hn p.2 hz]

/-- The tail family is jointly analytic without an assumed inverse bound. -/
theorem analyticAt_hillTailFamily (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ openHillStrip n) :
    AnalyticAt ℂ (hillTailFamily w n) p := by
  have hq := (w.convolutionCLM.analyticAt p.1).comp
    ((ContinuousLinearMap.fst ℂ (WeightedCoeff w.toWeight 2) ℂ).analyticAt p)
  have hc := (analyticOnNhd_hillComplementFamily w.toWeight n hn p.2 hz).comp
    ((ContinuousLinearMap.snd ℂ (WeightedCoeff w.toWeight 2) ℂ).analyticAt p)
  exact SchurComplement.analyticAt_compCLM hq hc

theorem isUnit_one_sub_hillTailFamily (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) : IsUnit (1-hillTailFamily w n p) := by
  apply isUnit_one_sub_of_norm_lt_one
  rw [hillTailFamily_eq w n hn p hz]
  exact (norm_hillTailPerturbation_le_half w p.1 n hn p.2 hz hcut).trans_lt (by norm_num)

/-- The total ring inverse supplies one analytic family, including at
parameters where the effective two-mode operator is singular. -/
def hillInverseFamily (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) :
    WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2 :=
  Ring.inverse (1-hillTailFamily w n p)

theorem hillInverseFamily_eq (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) :
    hillInverseFamily w n p = hillTailInverse w p.1 n hn p.2 hz hcut := by
  let K := hillTailFamily w n p
  let R := hillTailInverse w p.1 n hn p.2 hz hcut
  have hu : IsUnit (1-K) := isUnit_one_sub_hillTailFamily w n hn p hz hcut
  have hr : (1-K)*R = 1 := by
    ext a
    change R a - K (R a) = a
    simpa only [K, R, hillTailFamily_eq w n hn p hz] using
      hillTailInverse_right w p.1 n hn p.2 hz hcut a
  change Ring.inverse (1-K) = R
  calc
    Ring.inverse (1-K) = Ring.inverse (1-K)*1 := (mul_one _).symm
    _ = Ring.inverse (1-K)*((1-K)*R) := by rw [hr]
    _ = (Ring.inverse (1-K)*(1-K))*R := (mul_assoc _ _ _).symm
    _ = R := by rw [Ring.inverse_mul_cancel _ hu, one_mul]

theorem analyticAt_hillInverseFamily (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ openHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) : AnalyticAt ℂ (hillInverseFamily w n) p := by
  have hi : AnalyticAt ℂ (fun y : WeightedCoeff w.toWeight 2 × ℂ =>
      (1 : WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2)-hillTailFamily w n y) p :=
    analyticAt_const.sub (analyticAt_hillTailFamily w n hn p hz)
  exact (analyticOnNhd_inverse (𝕜 := ℂ) _
    (isUnit_one_sub_hillTailFamily w n hn p (openHillStrip_subset n hz) hcut)).comp
      (f := fun y : WeightedCoeff w.toWeight 2 × ℂ =>
        (1 : WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2)-hillTailFamily w n y) hi

/-- Jointly parameterized effective potential. -/
def hillEffectiveFamily (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) : (ℂ × ℂ) →L[ℂ] WeightedCoeff w.toWeight 2 :=
  (hillInverseFamily w n p).comp (hillModePotential w p.1 n)

/-- The proof-independent two-mode operator family. -/
def hillReducedFamily (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (p.2-(freeHillValue n : ℂ)) • ContinuousLinearMap.id ℂ (ℂ × ℂ) -
    (hillModeCoordinates w.toWeight 2 n).comp (hillEffectiveFamily w n p)

theorem hillReducedFamily_eq (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) :
    hillReducedFamily w n p = hillReducedOperator w p.1 n hn p.2 hz hcut := by
  unfold hillReducedFamily hillReducedOperator hillEffectiveFamily hillEffectivePotential
  rw [hillInverseFamily_eq w n hn p hz hcut]

theorem analyticAt_hillReducedFamily (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ openHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) : AnalyticAt ℂ (hillReducedFamily w n) p := by
  have hq := (w.convolutionCLM.analyticAt p.1).comp
    ((ContinuousLinearMap.fst ℂ (WeightedCoeff w.toWeight 2) ℂ).analyticAt p)
  have hv : AnalyticAt ℂ (fun y : WeightedCoeff w.toWeight 2 × ℂ => hillModePotential w y.1 n) p :=
    SchurComplement.analyticAt_compCLM hq analyticAt_const
  have he : AnalyticAt ℂ (hillEffectiveFamily w n) p :=
    SchurComplement.analyticAt_compCLM (analyticAt_hillInverseFamily w n hn p hz hcut) hv
  have hz' := (ContinuousLinearMap.snd ℂ (WeightedCoeff w.toWeight 2) ℂ).analyticAt p
  exact ((hz'.sub analyticAt_const).smul analyticAt_const).sub
    (SchurComplement.analyticAt_compCLM analyticAt_const he)

/-- One scalar determinant function, with analytic norm-valued inputs. -/
def hillReducedDeterminant (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) : ℂ := (hillReducedFamily w n p).toLinearMap.det

theorem analyticAt_hillReducedDeterminant (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ openHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) : AnalyticAt ℂ (hillReducedDeterminant w n) p :=
  FiniteSpectralDeterminant.analyticAt_det (analyticAt_hillReducedFamily w n hn p hz hcut)

theorem hillReducedDeterminant_eq (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) :
    hillReducedDeterminant w n p = (hillReducedOperator w p.1 n hn p.2 hz hcut).toLinearMap.det := by
  rw [hillReducedDeterminant, hillReducedFamily_eq w n hn p hz hcut]

end NLS.KdV
