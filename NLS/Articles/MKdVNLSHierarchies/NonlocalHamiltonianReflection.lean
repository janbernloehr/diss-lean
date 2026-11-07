import NLS.ZakharovShabat.NLSHierarchyReflectionNonlocal

/-! # The corrected all-order smooth clause of Proposition 11(iii)

The gradients are the actual physical Hamiltonian gradients certified by
independent periodic variations. The original sharp H^(2m-1) extension is
not asserted by this smooth interface.
-/
noncomputable section
open Complex MeasureTheory NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.Articles.MKdVNLSHierarchies

/-- On either reflected smooth subspace the nonlocal term is
+2*i*(J*phi)*integral(R*phi dot grad S_(2m-1)). -/
theorem proposition11_iii_smooth_corrected (m : ℕ) (hm : 1 ≤ m)
    (ε : ℂ) (hε : ε=1 ∨ ε = -1) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hTa : ∀ x, ε*a (1-x)=a x) (hTb : ∀ x, ε*b (1-x)=b x) (x : ℝ) :
    (I*(classicalNLSHierarchyGradient a b (2*m) x).1,
     -I*(classicalNLSHierarchyGradient a b (2*m) x).2) =
      (deriv (fun y => (classicalNLSHierarchyGradient a b (2*m-1) y).1) x+
        2*I*b x*(∫ y in (0:ℝ)..x, classicalNLSHierarchyRPairing a b (2*m-1) y),
       deriv (fun y => (classicalNLSHierarchyGradient a b (2*m-1) y).2) x-
        2*I*a x*(∫ y in (0:ℝ)..x, classicalNLSHierarchyRPairing a b (2*m-1) y)) := by
  have he := classicalNLSHierarchyGradient_reflection_nonlocal ε hε a b ha hb hpa hpb hTa hTb (m-1) x
  simpa only [show 2*(m-1)+2=2*m by omega,show 2*(m-1)+1=2*m-1 by omega] using he

end NLS.Articles.MKdVNLSHierarchies
