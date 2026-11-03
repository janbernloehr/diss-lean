import NLS.KdV.HminusOneDirichletOrder
import NLS.KdV.HminusOneMiuraHighPairs

/-! Canonical auxiliary branches of the actual rough scalar Dirichlet
characteristic. These give scalar roots and multiplicities at the SAME
signed index outside a finite central block, without relabeling that block. -/
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
  apply (hillHminusDirichlet_eq_zero_iff_auxiliarySpectrum q u c
    (hillMiuraDirichletEnergy u c n) (hillMiuraDiracDirichlet u n) hi
      (by simp [hillMiuraDirichletEnergy]) hn).mpr
  exact (canonicalAuxiliaryPeriodOneRoots_exhaustive (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u) _).mpr ⟨n,rfl⟩

/-- The full signed canonical auxiliary displacement has the original L2 norm. -/
def hillMiuraDirichletDisplacement (u : Coeff 2) : Coeff 2 :=
  sourceAuxiliaryBoundaryDisplacement (by simp) (by norm_num) .dirichlet (hillMiuraDiagonal u)

theorem hillMiuraDirichletDisplacement_apply (u : Coeff 2) (n : ℤ) :
    hillMiuraDirichletDisplacement u n = hillMiuraDiracDirichlet u n-(Real.pi:ℂ)*n :=
  sourceAuxiliaryBoundaryDisplacement_apply (by simp) (by norm_num) .dirichlet
    (hillMiuraDiagonal u) n

/-- For every complex lift, one cutoff gives nonzero canonical auxiliary
coordinates and simple scalar Dirichlet zeros on both signed tails. -/
theorem exists_simple_hillMiuraDirichletEnergy_tail
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      hillMiuraDiracDirichlet u n ≠ 0 ∧
      hillHminusDirichlet q (hillMiuraDirichletEnergy u c n) = 0 ∧
      analyticOrderNatAt (hillHminusDirichlet q) (hillMiuraDirichletEnergy u c n) = 1 := by
  let P := auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num) (hillMiuraDiagonal u)
  let K := BoundaryCondition.canonicalRootCutoff .dirichlet (by simp) (by norm_num) P.val P.property
  have hs := (BoundaryCondition.canonicalRoots_spec .dirichlet (by simp) (by norm_num)
    P.val P.property).1
  refine ⟨max 2 (K+1),le_max_left _ _,fun n hn => ?_⟩
  have hnK : K < n.natAbs := by have := (le_max_right 2 (K+1)).trans hn; omega
  have hn2 : 2 ≤ n.natAbs := (le_max_left _ _).trans hn
  have hd := hs.distant_spec n hnK
  change hillMiuraDiracDirichlet u n ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4) ∧ _ at hd
  have hne : hillMiuraDiracDirichlet u n ≠ 0 := by
    intro hz
    have hh := hd.1
    rw [hz,mem_ball,dist_eq_norm,zero_sub,norm_neg,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast,
      ← Int.cast_abs,← Int.natCast_natAbs] at hh
    simp only [Int.cast_natCast] at hh
    have hnr : (1:ℝ) ≤ n.natAbs := by exact_mod_cast (show 1 ≤ n.natAbs by omega)
    nlinarith [Real.pi_pos]
  refine ⟨hne,hillHminusDirichlet_miuraDirichletEnergy_eq_zero q u c hi n hne,?_⟩
  rw [hillMiuraDirichletEnergy,
    analyticOrderNatAt_hillHminusDirichlet_shifted_miura q u c _ hi hne,
    BoundaryCondition.auxiliaryAlgebraicMultiplicity_eq]
  exact hd.2

end NLS.KdV
