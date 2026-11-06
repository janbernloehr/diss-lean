import NLS.ComplexAnalysis.OddSquareDescent

/-! Filled energy descent respects equality of entire frequency slices,
including the removable value at zero. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {A B : Type}

theorem oddSquareDescent_congr_slice (F : ℂ × A → ℂ) (G : ℂ × B → ℂ)
    (a : A) (b : B) (h : ∀ z : ℂ, F (z,a) = G (z,b)) (E : ℂ) :
    oddSquareDescent F (E,a) = oddSquareDescent G (E,b) := by
  have he : (fun z : ℂ => F (z,a)-F (-z,a)) = (fun z : ℂ => G (z,b)-G (-z,b)) :=
    funext (fun z => by rw [h z,h (-z)])
  simp only [oddSquareDescent,oddPartQuotient,jointDSlopeZero]
  rw [he]

end NLS.ComplexAnalysis
