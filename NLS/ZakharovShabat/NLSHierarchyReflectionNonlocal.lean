import NLS.ZakharovShabat.NLSHierarchyReflectionCoupling

/-! # All-order corrected nonlocal Hamiltonian recurrence on smooth reflections

The scalar primitive has positive sign on the right and multiplies J*phi.
The independently constructed boundary coupling vanishes for BOTH printed
reflection signs. The full native Sobolev extension is a separate step.
-/
noncomputable section
open Complex MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Both spatial reflection signs give the corrected all-order recurrence
at every real point, with the genuine physical zero-initial integral. -/
theorem classicalNLSHierarchyGradient_reflection_nonlocal
    (ε : ℂ) (hε : ε=1 ∨ ε = -1) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hTa : ∀ x, ε*a (1-x)=a x) (hTb : ∀ x, ε*b (1-x)=b x) (m : ℕ) (x : ℝ) :
    (I*(classicalNLSHierarchyGradient a b (2*m+2) x).1,
     -I*(classicalNLSHierarchyGradient a b (2*m+2) x).2) =
      (deriv (fun y => (classicalNLSHierarchyGradient a b (2*m+1) y).1) x+
        2*I*b x*(∫ y in (0:ℝ)..x, classicalNLSHierarchyRPairing a b (2*m+1) y),
       deriv (fun y => (classicalNLSHierarchyGradient a b (2*m+1) y).2) x-
        2*I*a x*(∫ y in (0:ℝ)..x, classicalNLSHierarchyRPairing a b (2*m+1) y)) := by
  have he := classicalNLSHierarchyGradient_coupled_recurrence a b ha hb hpa hpb (2*m) x
  rw [classicalNLSHierarchyCoupling_eq_integral a b ha hb hpa hpb (2*m) x,
    classicalNLSHierarchyCoupling_zero_of_midpointReflection ε hε a b hpa hpb hTa hTb,
    zero_add] at he
  convert! he using 1
  apply Prod.ext <;> dsimp only <;> ring

end NLS.ZakharovShabat
