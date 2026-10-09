import NLS.SequenceSpaces.RealOperator
import NLS.SequenceSpaces.RealFormIdentity

/-! # Closed real coefficient space and inverses of real operators -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The closed real subspace of the complex coefficient space. -/
def realSubmodule (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (Coeff p) where
  carrier := realLocus p
  zero_mem' := by intro n; simp
  add_mem' := by intro a b ha hb n; change (a n+b n).im = 0; simp [ha n,hb n]
  smul_mem' := by intro r a ha n; change (r • a n).im = 0; simp [ha n]

/-- The real coefficient subspace is closed in the full sequence norm. -/
theorem isClosed_realSubmodule : IsClosed (realSubmodule p : Set (Coeff p)) := by
  have he : (realSubmodule p : Set (Coeff p)) = ⋂ n : ℤ, {a : Coeff p | (a n).im = 0} := by
    ext a
    simp only [SetLike.mem_coe,mem_iInter,mem_ofPred_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun n => isClosed_eq
    (Complex.continuous_im.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous) continuous_const

omit [Fact (1 ≤ p)] in
/-- Reality is exactly invariance under coordinatewise conjugation. -/
theorem mem_realLocus_iff_star_eq (a : Coeff p) : a ∈ realLocus p ↔ star a = a := by
  constructor
  · intro ha
    ext n
    exact Complex.conj_eq_iff_im.mpr (ha n)
  · intro ha n
    exact Complex.conj_eq_iff_im.mp (congrArg (fun z : Coeff p => z n) ha)

/-- An invertible operator with real matrix entries has a real inverse. -/
theorem inverse_mapsTo_realLocus_of_real_entries (hp : p ≠ ⊤)
    (A : Coeff p →L[ℂ] Coeff p) (hu : IsUnit A)
    (hreal : ∀ m k : ℤ, ((A (lp.single p k 1)) m).im = 0) :
    MapsTo ⇑(Ring.inverse A) (realLocus p) (realLocus p) := by
  intro z hz
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).injective
  have hAz : A (Ring.inverse A z) = z :=
    congrArg (fun T : Coeff p →L[ℂ] Coeff p => T z) (Ring.mul_inverse_cancel A hu)
  apply (mem_realLocus_iff_star_eq _).mpr
  apply hinj
  rw [operator_star_of_real_entries hp A hreal,hAz,(mem_realLocus_iff_star_eq z).mp hz]

end NLS.Coeff
