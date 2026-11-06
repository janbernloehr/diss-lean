import NLS.SequenceSpaces.Weighted
import NLS.SequenceSpaces.Multiplier

/-! Exact bounded transport from a divided positive frequency packet to
its original weak Sobolev-weighted sequence. The raw positive coefficient
is multiplied by its own index, while the actual (-1)-weight remains. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.Coeff

def positiveIndexWeakFunction (j : ℤ) : ℂ :=
  if 0<j then (Weight.sobolev (-1) j : ℂ)*(j : ℂ) else 0

theorem norm_positiveIndexWeakFunction_le (j : ℤ) : ‖positiveIndexWeakFunction j‖≤1 := by
  rw [positiveIndexWeakFunction]
  split_ifs with hj
  · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Weight.positive _ j).le,
      Complex.norm_intCast,abs_of_pos (by exact_mod_cast hj : (0 : ℝ)<j)]
    rw [Weight.sobolev_apply,abs_of_pos (by exact_mod_cast hj : (0 : ℝ)<j),Real.rpow_neg_one]
    have he : (1+(j : ℝ))⁻¹*(j : ℝ)=(j : ℝ)/(1+(j : ℝ)) := by ring
    rw [he]
    exact (div_le_one (by positivity : (0 : ℝ)<1+(j : ℝ))).mpr (by linarith)
  · simp only [norm_zero];norm_num

def positiveIndexWeakSymbol : Coeff ⊤ :=
  ⟨positiveIndexWeakFunction,memℓp_infty ⟨1,by rintro _ ⟨j,rfl⟩;exact norm_positiveIndexWeakFunction_le j⟩⟩

theorem norm_positiveIndexWeakSymbol_le : ‖positiveIndexWeakSymbol‖≤1 :=
  lp.norm_le_of_forall_le zero_le_one norm_positiveIndexWeakFunction_le

variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

def positiveIndexWeakLift : Coeff r →L[ℂ] WeightedCoeff (Weight.sobolev (-1)) r :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) r).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (multiplierCLM positiveIndexWeakSymbol)

theorem positiveIndexWeakLift_positive (a : Coeff r) (n : ℕ+) :
    (positiveIndexWeakLift a).val (n : ℤ)=(n : ℂ)*a (n : ℤ) := by
  change ((if (0 : ℤ)<n then (Weight.sobolev (-1) (n : ℤ) : ℂ)*(n : ℂ) else 0)*a (n : ℤ))/
    (Weight.sobolev (-1) (n : ℤ) : ℂ)=_
  rw [if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n)]
  rw [mul_assoc,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]

theorem positiveIndexWeakLift_nonpositive (a : Coeff r) (j : ℤ) (hj : j≤0) :
    (positiveIndexWeakLift a).val j=0 := by
  change ((if 0<j then (Weight.sobolev (-1) j : ℂ)*(j : ℂ) else 0)*a j)/
    (Weight.sobolev (-1) j : ℂ)=0
  rw [if_neg (by omega),zero_mul,zero_div]

theorem norm_positiveIndexWeakLift_le (a : Coeff r) : ‖positiveIndexWeakLift a‖≤‖a‖ := by
  change ‖(WeightedCoeff.weightIsometry (Weight.sobolev (-1)) r).symm
    (multiplier positiveIndexWeakSymbol a)‖≤_
  rw [LinearIsometryEquiv.norm_map]
  exact (norm_multiplier_le _ _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right norm_positiveIndexWeakSymbol_le (norm_nonneg a))

end NLS.Coeff
