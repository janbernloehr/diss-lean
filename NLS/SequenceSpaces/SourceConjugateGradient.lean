import NLS.SequenceSpaces.ConjugateCotangent
import NLS.SequenceSpaces.Reflection

/-! # Physical conjugate Fourier gradients of source functionals

A source functional has two conjugate coefficient representatives.
Frequency reversal converts them to physical gradient coefficients for the
bilinear variation formula. The resulting map is bounded and complex linear.
-/

noncomputable section
open scoped ENNReal
namespace NLS.CoeffPair
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Physical Fourier coefficients, with the bilinear source index reversed. -/
def conjugateGradient (hp : p ≠ ⊤) (hq : q ≠ ⊤) (L : CoeffPair p →L[ℂ] ℂ) : CoeffPair q :=
  inlCLM (Coeff.reflection (Coeff.conjugateCotangent hp hq (L.comp inlCLM)))+
  inrCLM (Coeff.reflection (Coeff.conjugateCotangent hp hq (L.comp inrCLM)))

@[simp] theorem conjugateGradient_fst (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : CoeffPair p →L[ℂ] ℂ) (n : ℤ) :
    (conjugateGradient hp hq L).fst n = L (inlCLM (lp.single p (-n) 1)) := by
  simp [conjugateGradient]

@[simp] theorem conjugateGradient_snd (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : CoeffPair p →L[ℂ] ℂ) (n : ℤ) :
    (conjugateGradient hp hq L).snd n = L (inrCLM (lp.single p (-n) 1)) := by
  simp [conjugateGradient]

/-- The physical conjugate pair norm is bounded by twice the source operator norm. -/
theorem norm_conjugateGradient_le (hp : p ≠ ⊤) (hq : q ≠ ⊤) (L : CoeffPair p →L[ℂ] ℂ) :
    ‖conjugateGradient hp hq L‖ ≤ 2*‖L‖ := by
  have hleft : ‖L.comp inlCLM‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro a
    simpa only [ContinuousLinearMap.comp_apply,norm_inlCLM] using L.le_opNorm (inlCLM a)
  have hright : ‖L.comp inrCLM‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro a
    simpa only [ContinuousLinearMap.comp_apply,norm_inrCLM] using L.le_opNorm (inrCLM a)
  calc
    _ ≤ ‖Coeff.conjugateCotangent hp hq (L.comp inlCLM)‖+
        ‖Coeff.conjugateCotangent hp hq (L.comp inrCLM)‖ := by
      simpa only [conjugateGradient,norm_inlCLM,norm_inrCLM,LinearIsometryEquiv.norm_map] using
        norm_add_le
          (inlCLM (p := q) (Coeff.reflection (Coeff.conjugateCotangent hp hq (L.comp inlCLM))))
          (inrCLM (p := q) (Coeff.reflection (Coeff.conjugateCotangent hp hq (L.comp inrCLM))))
    _ ≤ ‖L‖+‖L‖ := add_le_add ((Coeff.norm_conjugateCotangent_le hp hq _).trans hleft)
      ((Coeff.norm_conjugateCotangent_le hp hq _).trans hright)
    _ = _ := by ring

/-- Recovery of the physical gradient is a bounded complex-linear operation. -/
def conjugateGradientCLM (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    (CoeffPair p →L[ℂ] ℂ) →L[ℂ] CoeffPair q :=
  LinearMap.mkContinuous
    { toFun := conjugateGradient hp hq
      map_add' := by
        intro L K
        apply (toMax q).injective
        apply Prod.ext <;> ext n <;> simp
      map_smul' := by
        intro c L
        apply (toMax q).injective
        apply Prod.ext <;> ext n <;> simp }
    2 (norm_conjugateGradient_le hp hq)

@[simp] theorem conjugateGradientCLM_apply (hp : p ≠ ⊤) (hq : q ≠ ⊤) (L : CoeffPair p →L[ℂ] ℂ) :
    conjugateGradientCLM hp hq L = conjugateGradient hp hq L := rfl

/-- The physical coefficient pair represents the entire source derivative
through unconjugated duality and reversed frequencies. -/
theorem dualPairing_conjugateGradient (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : CoeffPair p →L[ℂ] ℂ) (h : CoeffPair p) :
    Coeff.dualPairing (Coeff.reflection (conjugateGradient hp hq L).fst) h.fst+
      Coeff.dualPairing (Coeff.reflection (conjugateGradient hp hq L).snd) h.snd = L h := by
  have hleft := Coeff.eq_dualPairing_of_single hp (L.comp inlCLM)
    (Coeff.reflection (conjugateGradient hp hq L).fst) (by intro n; simp)
  have hright := Coeff.eq_dualPairing_of_single hp (L.comp inrCLM)
    (Coeff.reflection (conjugateGradient hp hq L).snd) (by intro n; simp)
  rw [← hleft,← hright]
  change L (inlCLM h.fst)+L (inrCLM h.snd) = L h
  rw [← map_add]
  congr 1
  apply (toMax p).injective
  apply Prod.ext <;> simp

/-- A summable sequence of source operators gives a summable sequence of
physical conjugate Fourier gradients. -/
theorem memlp_conjugateGradient {r : ℝ≥0∞} (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : ℤ → CoeffPair p →L[ℂ] ℂ) (hL : Memℓp L r) :
    Memℓp (fun n => conjugateGradient hp hq (L n)) r := by
  apply (hL.norm.const_mul 2).mono
  intro n
  exact norm_conjugateGradient_le hp hq (L n)

end NLS.CoeffPair
