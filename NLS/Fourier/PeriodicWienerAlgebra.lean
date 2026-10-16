import NLS.Fourier.PeriodicFourierLebesgueProduct

/-!
# The original periodic Wiener algebra

The original FL¹ distribution space, already complete, is a commutative normed
complex algebra with norm-one identity. Its continuous representative is an
injective algebra homomorphism into continuous functions on the physical circle.
The multiplication is exactly the product of Lemma A.7.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
namespace PeriodicFourierLebesgue
variable {L : ℝ} [Fact (0 < L)]

/-- The original Wiener element with coefficient one at zero and zero elsewhere. -/
def wienerOne : PeriodicFourierLebesgue L Weight.one 1 :=
  (unweightedCoefficients 1).symm (lp.single 1 0 1)

/-- The identity element represents the actual constant function one. -/
theorem continuousRepresentative_wienerOne : continuousRepresentative (wienerOne (L := L)) = 1 := by
  unfold continuousRepresentative wienerOne
  rw [LinearIsometryEquiv.apply_symm_apply]
  unfold continuousSynthesisPeriod
  simp only [lp.single_apply,Pi.single_apply,ite_smul,zero_smul,one_smul,tsum_ite_eq]
  ext x
  exact fourier_zero

/-- Continuous representatives distinguish original Wiener elements. -/
theorem continuousRepresentative_injective : Function.Injective (continuousRepresentative (L := L)) := by
  intro u v huv
  apply Subtype.ext
  rw [← continuousRepresentative_represents u,← continuousRepresentative_represents v,huv]

/-- The zero original distribution has zero continuous representative. -/
theorem continuousRepresentative_zero : continuousRepresentative (0 : PeriodicFourierLebesgue L Weight.one 1) = 0 :=
  map_zero (continuousRepresentativeCLM (L := L))

/-- Continuous representatives preserve addition. -/
theorem continuousRepresentative_add (u v : PeriodicFourierLebesgue L Weight.one 1) :
    continuousRepresentative (u+v) = continuousRepresentative u + continuousRepresentative v :=
  map_add continuousRepresentativeCLM u v

/-- The endpoint Young relation used for Wiener multiplication. -/
theorem youngRelation_wiener : YoungRelation (1:ℝ≥0∞) 1 1 := by simp [YoungRelation]

/-- Wiener multiplication is the original-distribution Young product. -/
instance instWienerMul : Mul (PeriodicFourierLebesgue L Weight.one 1) := ⟨youngProduct youngRelation_wiener⟩
/-- The Wiener identity is the constant distribution one. -/
instance instWienerOne : One (PeriodicFourierLebesgue L Weight.one 1) := ⟨wienerOne⟩

/-- Wiener multiplication agrees with pointwise multiplication. -/
theorem continuousRepresentative_mul (u v : PeriodicFourierLebesgue L Weight.one 1) :
    continuousRepresentative (u*v) = continuousRepresentative u * continuousRepresentative v :=
  continuousRepresentative_youngProduct u v

/-- The Wiener identity represents the constant function one. -/
theorem continuousRepresentative_one : continuousRepresentative (1 : PeriodicFourierLebesgue L Weight.one 1) = 1 :=
  continuousRepresentative_wienerOne

/-- The original Wiener space is a commutative ring. -/
instance instWienerCommRing : CommRing (PeriodicFourierLebesgue L Weight.one 1) where
  __ := (inferInstance : AddCommGroup (PeriodicFourierLebesgue L Weight.one 1))
  one := 1
  mul := (· * ·)
  mul_assoc u v w := by
    apply continuousRepresentative_injective
    simp only [continuousRepresentative_mul,mul_assoc]
  one_mul u := by
    apply continuousRepresentative_injective
    rw [continuousRepresentative_mul,continuousRepresentative_one,one_mul]
  mul_one u := by
    apply continuousRepresentative_injective
    rw [continuousRepresentative_mul,continuousRepresentative_one,mul_one]
  left_distrib u v w := youngProduct_add_right _ u v w
  right_distrib u v w := youngProduct_add_left _ u v w
  zero_mul u := by
    apply continuousRepresentative_injective
    rw [continuousRepresentative_mul,continuousRepresentative_zero,zero_mul]
  mul_zero u := by
    apply continuousRepresentative_injective
    rw [continuousRepresentative_mul,continuousRepresentative_zero,mul_zero]
  mul_comm u v := youngProduct_comm _ u v

/-- The coefficient norm is submultiplicative on the original Wiener ring. -/
instance instWienerNormedCommRing : NormedCommRing (PeriodicFourierLebesgue L Weight.one 1) where
  __ := instWienerCommRing
  __ := (inferInstance : NormedAddCommGroup (PeriodicFourierLebesgue L Weight.one 1))
  norm_mul_le u v := norm_youngProduct_le _ u v
  dist_eq u v := dist_eq_norm_neg_add u v

/-- The original Wiener ring is a normed complex algebra. -/
instance instWienerNormedAlgebra : NormedAlgebra ℂ (PeriodicFourierLebesgue L Weight.one 1) where
  toAlgebra := Algebra.ofModule
    (fun c u v => youngProduct_smul_left youngRelation_wiener c u v)
    (fun c u v => youngProduct_smul_right youngRelation_wiener c u v)
  norm_smul_le c u := le_of_eq (norm_smul c u)

/-- The original Wiener identity has norm exactly one. -/
instance instWienerNormOneClass : NormOneClass (PeriodicFourierLebesgue L Weight.one 1) where
  norm_one := by
    change ‖(unweightedCoefficients (L := L) 1).symm (lp.single 1 0 1)‖ = 1
    rw [LinearIsometryEquiv.norm_map,lp.norm_single (by norm_num)]
    exact norm_one

/-- The injective algebra map from original Wiener distributions to continuous functions. -/
def wienerContinuousAlgHom : PeriodicFourierLebesgue L Weight.one 1 →ₐ[ℂ] C(AddCircle L,ℂ) where
  toFun := continuousRepresentative
  map_one' := continuousRepresentative_one
  map_mul' := continuousRepresentative_mul
  map_zero' := continuousRepresentative_zero
  map_add' := continuousRepresentative_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]
    change continuousRepresentativeCLM (c • (1 : PeriodicFourierLebesgue L Weight.one 1)) = _
    rw [map_smul,continuousRepresentativeCLM_apply,continuousRepresentative_one]


end PeriodicFourierLebesgue
end NLS.Fourier
