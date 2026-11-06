import NLS.KdV.HillGlobalDifferentialReality
import NLS.KdV.HillFiniteAbelianPolynomials

/-! # Closed non-own Dirichlet gaps contribute zero to the normalized numerator -/
noncomputable section
open Set Complex
open NLS.ZakharovShabat
namespace NLS.KdV

theorem hillAbelianSelectedGlobalPsi_closed_Dirichlet_eq_zero
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hkn : k+1 ≠ n)
    (hc : hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) = 0) :
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn (hillDirichletEnergies q k) = 0 := by
  apply (hillAbelianSelectedGlobalPsi_zero_iff q.val q.property.1 q.property.2 n hn _).mpr
  refine ⟨k,hkn,?_⟩
  exact congrArg (fun x : ℝ => (x : ℂ)) (hillGapRoot_eq_Dirichlet_of_closed q _
    (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).property k hc)

end NLS.KdV
