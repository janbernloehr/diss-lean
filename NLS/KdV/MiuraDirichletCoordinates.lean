import NLS.KdV.HillHminusAuxiliaryDirichlet
import NLS.ZakharovShabat.AuxiliaryPeriodOneBoundaryInterlacing
import NLS.ZakharovShabat.SourceLemma9_1Auxiliary
import NLS.KdV.HminusOneMiuraHighPairs

/-! Literal auxiliary Dirichlet coordinates, their scalar energies and
full signed L2 displacements, with exact characteristic-root transport. -/
noncomputable section
open Set Complex Metric NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- The actual canonical auxiliary Dirichlet coordinate of the original
unit-period diagonal source. -/
def hillMiuraDiracDirichlet (u : Coeff 2) (n : ℤ) : ℂ :=
  canonicalAuxiliaryPeriodOneRoots (by simp) (by norm_num) .dirichlet (hillMiuraDiagonal u) n

/-- Its scalar energy with the literal constant Miura translation. -/
def hillMiuraDirichletEnergy (u : Coeff 2) (c : ℂ) (n : ℤ) : ℂ :=
  (hillMiuraDiracDirichlet u n)^2-c

theorem hillMiuraDiracDirichlet_im_eq_zero (u : PeriodOneRealL2) (n : ℤ) :
    (hillMiuraDiracDirichlet u.val n).im = 0 :=
  canonicalAuxiliaryPeriodOneRoots_im_eq_zero (by simp) (by norm_num) .dirichlet
    (hillMiuraDiagonal u.val) (isRealType_hillMiuraDiagonal u) n

/-- Each actual auxiliary Dirichlet root lies in the corresponding
original diagonal periodic gap, with no change of signed index. -/
theorem hillMiuraDiracDirichlet_mem_gap (u : PeriodOneRealL2) (n : ℤ) :
    (hillMiuraDiracLeft u.val n).re ≤ (hillMiuraDiracDirichlet u.val n).re ∧
      (hillMiuraDiracDirichlet u.val n).re ≤ (hillMiuraDiracRight u.val n).re :=
  canonicalAuxiliaryPeriodOneRoots_mem_gap (by simp) (by norm_num) .dirichlet
    (hillMiuraDiagonal u.val) (isRealType_hillMiuraDiagonal u) n

/-- At every nonzero auxiliary coordinate, the squared and translated
energy is a zero of the independent full scalar Dirichlet characteristic. -/
theorem hillHminusDirichlet_miuraDirichletEnergy_eq_zero
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (n : ℤ) (hn : hillMiuraDiracDirichlet u n ≠ 0) :
    hillHminusDirichlet q (hillMiuraDirichletEnergy u c n) = 0 := by
  have hs := (canonicalAuxiliaryPeriodOneRoots_exhaustive (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u) _).mpr ⟨n,rfl⟩
  have hz := (auxiliaryPeriodOneCharacteristic_eq_zero_iff (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u) _).mpr hs
  rw [auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u c _ hi] at hz
  exact (mul_eq_zero.mp hz).resolve_left hn

/-- The full signed canonical auxiliary displacement has the original L2 norm. -/
def hillMiuraDirichletDisplacement (u : Coeff 2) : Coeff 2 :=
  sourceAuxiliaryBoundaryDisplacement (by simp) (by norm_num) .dirichlet (hillMiuraDiagonal u)

theorem hillMiuraDirichletDisplacement_apply (u : Coeff 2) (n : ℤ) :
    hillMiuraDirichletDisplacement u n = hillMiuraDiracDirichlet u n-(Real.pi:ℂ)*n :=
  sourceAuxiliaryBoundaryDisplacement_apply (by simp) (by norm_num) .dirichlet
    (hillMiuraDiagonal u) n

end NLS.KdV
