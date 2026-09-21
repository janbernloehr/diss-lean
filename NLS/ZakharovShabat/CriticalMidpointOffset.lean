import NLS.ZakharovShabat.DiscriminantPairFactorization
import NLS.ZakharovShabat.UniformCanonicalCriticalPoints
import NLS.ZakharovShabat.CanonicalPeriodicDisplacementBounds

/-!
# Canonical critical-to-midpoint offsets in lp

The offset is the critical displacement minus the average endpoint
displacement. Its norm is locally uniformly bounded, which supplies the
bounded factor multiplying the remaining-product derivative in Lemma 8.6.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The critical-to-midpoint offset as a coefficient sequence. -/
def canonicalCriticalMidpointOffset (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) : Coeff p :=
  canonicalCriticalDisplacement hp hp1 φ heven-(1/2 : ℂ) •
    (canonicalPeriodicLeftDisplacement hp hp1 φ heven+canonicalPeriodicRightDisplacement hp hp1 φ heven)

@[simp] theorem canonicalCriticalMidpointOffset_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalCriticalMidpointOffset hp hp1 φ heven n =
      canonicalCriticalPoints hp hp1 φ heven n-canonicalPeriodicMidpoint hp hp1 φ heven n := by
  simp only [canonicalCriticalMidpointOffset,lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,lp.coeFn_add,Pi.add_apply,canonicalCriticalDisplacement_apply,
    canonicalPeriodicLeftDisplacement_apply,canonicalPeriodicRightDisplacement_apply,canonicalPeriodicMidpoint]
  ring

/-- The midpoint offset norm is bounded by the three displacement norms. -/
theorem norm_canonicalCriticalMidpointOffset_le (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) :
    ‖canonicalCriticalMidpointOffset hp hp1 φ heven‖ ≤ ‖canonicalCriticalDisplacement hp hp1 φ heven‖+
      (‖canonicalPeriodicLeftDisplacement hp hp1 φ heven‖+‖canonicalPeriodicRightDisplacement hp hp1 φ heven‖)/2 := by
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat]
  exact add_le_add le_rfl (by
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using
      mul_le_mul_of_nonneg_left (norm_add_le (canonicalPeriodicLeftDisplacement hp hp1 φ heven)
        (canonicalPeriodicRightDisplacement hp hp1 φ heven)) (by norm_num : (0 : ℝ) ≤ 1/2))

/-- One open convex potential neighborhood bounds the actual critical-to-midpoint offset norm. -/
theorem exists_uniform_canonicalCriticalMidpointOffset_bound (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ‖canonicalCriticalMidpointOffset hp hp1 ψ heven‖ ≤ R := by
  obtain ⟨_,_,Uc,hoc,hcc,hφc,h0c,A,hA,hcrit⟩ := exists_uniform_canonicalCriticalPoints hp hp1 φ
  obtain ⟨Ue,hoe,hce,hφe,h0e,B,hB,hend⟩ := exists_uniform_bounded_canonicalPeriodicDisplacements hp hp1 φ
  refine ⟨Uc ∩ Ue,hoc.inter hoe,hcc.inter hce,⟨hφc,hφe⟩,⟨h0c,h0e⟩,A+B,by positivity,fun ψ hψ heven => ?_⟩
  apply (norm_canonicalCriticalMidpointOffset_le hp hp1 ψ heven).trans
  have hc := (hcrit ψ hψ.1 heven).2
  obtain ⟨hl,hr⟩ := hend ψ hψ.2 heven
  linarith

end NLS.ZakharovShabat
