import NLS.SequenceSpaces.PhaseRotation

/-! # Opposite phase rotations of complex Birkhoff coordinates

The two components rotate with opposite signs. Their products (the actions)
are constant, conjugate pairs remain conjugate, and finite-exponent curves
are continuous in the full sequence norm.
-/
noncomputable section
open Complex Set
open scoped ENNReal ComplexConjugate
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reality for complex Birkhoff coordinates is conjugation at the same index. -/
def IsConjugatePair (z : Coeff p × Coeff p) : Prop := ∀ n : ℤ, z.2 n = conj (z.1 n)

/-- Opposite phase rotations with the signs in equation (4.14). -/
def phaseFlow (ω : ℤ → ℝ) (t : ℝ) (z : Coeff p × Coeff p) : Coeff p × Coeff p :=
  (Coeff.phaseFlow ω t z.1,Coeff.phaseFlow ω (-t) z.2)

@[simp] theorem phaseFlow_fst (ω : ℤ → ℝ) (t : ℝ) (z : Coeff p × Coeff p) (n : ℤ) :
    (phaseFlow ω t z).1 n = Complex.exp (((t*ω n : ℝ) : ℂ)*I)*z.1 n := rfl

@[simp] theorem phaseFlow_snd (ω : ℤ → ℝ) (t : ℝ) (z : Coeff p × Coeff p) (n : ℤ) :
    (phaseFlow ω t z).2 n = Complex.exp (((-t*ω n : ℝ) : ℂ)*I)*z.2 n := rfl

@[simp] theorem phaseFlow_zero (ω : ℤ → ℝ) (z : Coeff p × Coeff p) : phaseFlow ω 0 z = z := by
  simp [phaseFlow]

/-- Time addition holds for every real frequency sequence. -/
theorem phaseFlow_add (ω : ℤ → ℝ) (t u : ℝ) (z : Coeff p × Coeff p) :
    phaseFlow ω t (phaseFlow ω u z) = phaseFlow ω (t+u) z := by
  apply Prod.ext
  · exact Coeff.phaseFlow_add ω t u z.1
  · simpa only [phaseFlow,neg_add] using Coeff.phaseFlow_add ω (-t) (-u) z.2

/-- Each complex action z_n w_n is preserved exactly. -/
theorem phaseFlow_action (ω : ℤ → ℝ) (t : ℝ) (z : Coeff p × Coeff p) (n : ℤ) :
    (phaseFlow ω t z).1 n*(phaseFlow ω t z).2 n = z.1 n*z.2 n := by
  rw [phaseFlow_fst,phaseFlow_snd]
  calc
    _ = (Complex.exp (((t*ω n : ℝ) : ℂ)*I)*Complex.exp (((-t*ω n : ℝ) : ℂ)*I)) * (z.1 n*z.2 n) := by ring
    _ = z.1 n*z.2 n := by
      rw [← Complex.exp_add]
      have he : (((t*ω n : ℝ) : ℂ)*I) + (((-t*ω n : ℝ) : ℂ)*I) = 0 := by push_cast; ring
      rw [he, Complex.exp_zero, one_mul]

/-- The flow preserves the two component norms separately. -/
theorem phaseFlow_norms (ω : ℤ → ℝ) (t : ℝ) (z : Coeff p × Coeff p) :
    ‖(phaseFlow ω t z).1‖ = ‖z.1‖ ∧ ‖(phaseFlow ω t z).2‖ = ‖z.2‖ :=
  ⟨(Coeff.phaseFlow ω t).norm_map _, (Coeff.phaseFlow ω (-t)).norm_map _⟩

@[simp] theorem norm_phaseFlow (ω : ℤ → ℝ) (t : ℝ) (z : Coeff p × Coeff p) :
    ‖phaseFlow ω t z‖ = ‖z‖ := by
  simp only [Prod.norm_def, (phaseFlow_norms ω t z).1, (phaseFlow_norms ω t z).2]

/-- Opposite phases preserve the actual complex-coordinate real locus. -/
theorem phaseFlow_real (ω : ℤ → ℝ) (t : ℝ) (z : Coeff p × Coeff p)
    (hz : IsConjugatePair z) : IsConjugatePair (phaseFlow ω t z) := by
  intro n
  rw [phaseFlow_snd,phaseFlow_fst,map_mul,← Complex.exp_conj,hz n]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul, ofReal_neg]
  ring

/-- Continuous real frequencies need only vary coordinatewise for norm-continuous trajectories. -/
theorem continuous_phaseFlow_family {X : Type*} [TopologicalSpace X]
    (hp : p ≠ ⊤) (ω : X → ℤ → ℝ) (z : X → Coeff p × Coeff p)
    (hω : ∀ n, Continuous (fun x => ω x n)) (hz : Continuous z) :
    Continuous (fun x : ℝ × X => phaseFlow (ω x.2) x.1 (z x.2)) := by
  apply Continuous.prodMk
  · exact Coeff.continuous_phaseMultiply_family hp
      (fun x : ℝ × X => fun n => x.1*ω x.2 n) (fun x => (z x.2).1)
      (fun n => continuous_fst.mul ((hω n).comp continuous_snd)) (hz.fst.comp continuous_snd)
  · exact Coeff.continuous_phaseMultiply_family hp
      (fun x : ℝ × X => fun n => -x.1*ω x.2 n) (fun x => (z x.2).2)
      (fun n => continuous_fst.neg.mul ((hω n).comp continuous_snd)) (hz.snd.comp continuous_snd)

end NLS.Birkhoff
