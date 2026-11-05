import NLS.SequenceSpaces.AnalyticSuperposition
import NLS.ComplexAnalysis.RealArsinhExtension

/-! # Inverse hyperbolic sine acts analytically near every real lp sequence -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def arsinhSuperposition (a : Coeff p) : Coeff p :=
  ofFunctionOrZero p (fun n => NLS.ComplexAnalysis.realArsinhExtension (a n))

theorem exists_local_analytic_arsinhSuperposition (hp : p ≠ ⊤)
    (a : Coeff p) (ha : ∀ n : ℤ, (a n).im = 0) :
    ∃ V : Set (Coeff p), IsOpen V ∧ a ∈ V ∧ AnalyticOnNhd ℂ arsinhSuperposition V ∧
      ∀ b ∈ V, ∀ n, arsinhSuperposition b n = NLS.ComplexAnalysis.realArsinhExtension (b n) := by
  obtain ⟨L,r,hL,hr,hf,hb⟩ := NLS.ComplexAnalysis.exists_realArsinhExtension_linear_bound
  apply exists_local_analytic_superposition hp _ L r hL.le hr hf hb a
  intro n
  have he : ((a n).re : ℂ) = a n := by
    apply Complex.ext
    · rfl
    · exact (ha n).symm
  rw [← he]
  exact NLS.ComplexAnalysis.analyticAt_realArsinhExtension_ofReal _

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem exists_local_analytic_arsinhSuperposition_comp (hp : p ≠ ⊤)
    (A : X → Coeff p) (W : Set X) (hW : IsOpen W)
    (q : X) (hq : q ∈ W) (hA : AnalyticOnNhd ℂ A W)
    (hreal : ∀ n : ℤ, (A q n).im = 0) :
    ∃ V : Set X, ∃ K : X → Coeff p, IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      AnalyticOnNhd ℂ K V ∧ ∀ b ∈ V, ∀ n,
        K b n = NLS.ComplexAnalysis.realArsinhExtension (A b n) := by
  obtain ⟨T,hT,hqT,hars,hval⟩ := exists_local_analytic_arsinhSuperposition hp (A q) hreal
  let V := W ∩ A ⁻¹' T
  have hV : IsOpen V := hA.continuousOn.isOpen_inter_preimage hW hT
  refine ⟨V,fun b => arsinhSuperposition (A b),hV,⟨hq,hqT⟩,inter_subset_left,
    fun b hb => (hars _ hb.2).comp (f := A) (hA b hb.1),?_⟩
  intro b hb n
  exact hval _ hb.2 n

end NLS.Coeff
