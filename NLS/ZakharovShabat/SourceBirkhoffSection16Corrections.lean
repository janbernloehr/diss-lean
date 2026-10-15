import NLS.ZakharovShabat.SourceGapWeightedEtaAuxiliary
import NLS.ZakharovShabat.SourceTheorem12_1Functions
import NLS.ZakharovShabat.SourceSingleRootQuotientNormalization

/-!
# Explicit free-source checks of Section 16 conventions

The actual free derivative detects the inverse-series y sign. The literal
negative product printed as zeta equals minus one at the free centers;
at the zero center its quotient by the actual psi numerator is plus one half.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceSection15OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

-- The printed plus-basis inverse already fails for the actual free Jacobian.
theorem freeJacobian_y_mode (D : SourceSection15OriginalData hp hp1 W₀ W V s) (n : ℤ) :
    sourceBirkhoffJacobian hp hp1 s 0 (sourceBirkhoffFreeYGradient p n) =
      -(0, lp.single p (-n) 1) := by
  rw [D.complex.jacobian_zero]
  exact sourceBirkhoffFourier_freeY n

-- The literal leading minus on the printed zeta product gives -1 at every free center.
theorem printed_auxiliary_product_free (D : SourceSection15OriginalData hp hp1 W₀ W V s) (n : ℤ) :
    -sourceSingleRootQuotientJointProduct hp hp1 n
      ((Real.pi : ℂ)*n, ((s n 0 : Coeff p), (0 : CoeffPair p))) = -1 := by
  rw [D.previous.previous.previous.psi.displacement_zero]
  simp only [ZeroMemClass.coe_zero]
  rw [sourceSingleRootQuotient_zero_free hp hp1 n _
    (sourceStandardRootOmittedDomain_zero_source_contains_center hp hp1 n)]

theorem printed_auxiliary_quotient_zero (D : SourceSection15OriginalData hp hp1 W₀ W V s) :
    (-sourceSingleRootQuotientJointProduct hp hp1 0
      (0, ((s 0 0 : Coeff p), (0 : CoeffPair p)))) /
        sourcePsiCandidate 0 (0, (s 0 0 : Coeff p)) = (1/2 : ℂ) := by
  have hz := printed_auxiliary_product_free D 0
  simp only [Int.cast_zero, mul_zero] at hz
  rw [hz, D.previous.previous.previous.psi.numerator_zero]
  have hc := freeSineQuotient_center 0
  simp only [Int.cast_zero, mul_zero, Complex.cos_zero] at hc
  rw [sourcePsiFree, hc]
  norm_num

end SourceSection15OriginalData
local instance : Fact (1 ≤ (4:ℝ≥0∞)) := ⟨by norm_num⟩

/-- A single free x mode is not norm one in the genuine source norm at p=4. -/
theorem sourceBirkhoffFreeXGradient_norm_fourth (n : ℤ) :
    ‖sourceBirkhoffFreeXGradient 4 n‖^4 = (1/2 : ℝ) := by
  let v := sourceBirkhoffFreeXGradient 4 n
  have hfst : ‖v.fst‖ = (Real.sqrt 2)⁻¹ := by
    change ‖(-(Real.sqrt 2 : ℂ)⁻¹) • (lp.single 4 n 1 + (0 : Coeff 4))‖ = _
    rw [add_zero,norm_smul,lp.norm_single (by norm_num),norm_one,mul_one,norm_neg,norm_inv]
    simp
  have hsnd : ‖v.snd‖ = (Real.sqrt 2)⁻¹ := by
    change ‖(-(Real.sqrt 2 : ℂ)⁻¹) • ((0 : Coeff 4) + lp.single 4 (-n) 1)‖ = _
    rw [zero_add,norm_smul,lp.norm_single (by norm_num),norm_one,mul_one,norm_neg,norm_inv]
    simp
  have hpow : (Real.sqrt 2)⁻¹^4 = (1/4 : ℝ) := by
    rw [inv_pow,show Real.sqrt 2 ^ 4 = (4 : ℝ) by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]]
    norm_num
  change ‖v‖^4 = _
  rw [WithLp.prod_norm_eq_of_nat (p := (4:ℝ≥0∞)) 4 (by norm_num) v,hfst,hsnd,hpow]
  norm_num only
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num)]
  norm_num


end NLS.ZakharovShabat
