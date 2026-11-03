import NLS.Dynamics.RealComplexBirkhoffCoordinates

/-! # The real Banach space of conjugate complex Birkhoff pairs -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The article's real target in complex coordinates. -/
def conjugatePairSubmodule (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (Coeff p × Coeff p) where
  carrier := IsConjugatePair
  zero_mem' := by intro n; simp
  add_mem' := by
    intro a b ha hb n
    change a.2 n+b.2 n = conj (a.1 n+b.1 n)
    rw [map_add,ha n,hb n]
  smul_mem' := by
    intro r a ha n
    change (r : ℂ)*a.2 n = conj ((r : ℂ)*a.1 n)
    rw [map_mul,Complex.conj_ofReal,ha n]

/-- Exact real linear coordinates on the conjugate-pair target. -/
def conjugatePairEquiv : (RealCoeff p × RealCoeff p) ≃L[ℝ] conjugatePairSubmodule p where
  toFun z := ⟨encodeReal z,encodeReal_real z⟩
  invFun z := decodeReal z.val
  left_inv := decodeReal_encodeReal
  right_inv z := by apply Subtype.ext; exact encodeReal_decodeReal z.val z.property
  map_add' a b := by apply Subtype.ext; exact encodeReal.map_add a b
  map_smul' r a := by apply Subtype.ext; exact encodeReal.map_smul r a
  continuous_toFun := encodeReal.continuous.subtype_mk _
  continuous_invFun := decodeReal.continuous.comp continuous_subtype_val

@[simp] theorem conjugatePairEquiv_val (z : RealCoeff p × RealCoeff p) :
    (conjugatePairEquiv z).val = encodeReal z := rfl
/-- The physical conjugation relation defines a closed subspace. -/
theorem isClosed_conjugatePairSubmodule :
    IsClosed (conjugatePairSubmodule p : Set (Coeff p × Coeff p)) := by
  change IsClosed {z : Coeff p × Coeff p | ∀ n : ℤ, z.2 n = conj (z.1 n)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  exact isClosed_eq
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp continuous_snd)
    (continuous_conj.comp ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp continuous_fst))

instance conjugatePairCompleteSpace : CompleteSpace (conjugatePairSubmodule p) :=
  isClosed_conjugatePairSubmodule.completeSpace_coe

end NLS.Birkhoff
