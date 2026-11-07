import NLS.KdV.HminusOneMiuraDirichlet
import NLS.MKdV.QuasiHillL2DirichletEigenstate

/-! The full complex H-minus-one Dirichlet characteristic detects the
independently defined physical quasi-derivative boundary problem for ANY
literal shifted Miura lift. Existence is intrinsic to the potential, since
every potential has a lift and all lifts give the same zero criterion.
Matching this regularized equation to a native distributional Dirichlet
operator domain, and algebraic multiplicities, remain separate steps. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.MKdV NLS.ZakharovShabat
namespace NLS.KdV

/-- Any literal complex L2 shifted Miura lift gives the nontrivial scalar
Dirichlet zero criterion, including at zero energy. -/
theorem hillHminusDirichlet_eq_zero_iff_eigenstate_of_shifted_image
    (q : PeriodOneHminusOne) (u : Coeff 2) (c lambda : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillHminusDirichlet q lambda = 0 ↔ ∃ w : Curve (ℂ × ℂ),
      IsQuasiHillL2DirichletState u (lambda+c) w ∧
        ∃ t : Icc (0:ℝ) 1, (w t).1 ≠ 0 := by
  rw [hillHminusDirichlet_eq_miura_of_shifted_image q u c lambda hi]
  exact quasiHillL2Dirichlet_eq_zero_iff_exists_eigenstate u (lambda+c)

/-- Every full complex H-minus-one potential admits the physical scalar
Dirichlet criterion. The lift and energy translation are witnessed, not
supplied as additional hypotheses on the potential. -/
theorem hillHminusDirichlet_eq_zero_iff_exists_eigenstate
    (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusDirichlet q lambda = 0 ↔
      ∃ (u : Coeff 2) (c : ℂ) (w : Curve (ℂ × ℂ)),
        periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c) ∧
        IsQuasiHillL2DirichletState u (lambda+c) w ∧
        ∃ t : Icc (0:ℝ) 1, (w t).1 ≠ 0 := by
  constructor
  · intro h
    let C := hillHminusMiuraChartAt q
    have hi := C.image q (mem_hillHminusMiuraChartAt q)
    obtain ⟨w,hw,hn⟩ :=
      (hillHminusDirichlet_eq_zero_iff_eigenstate_of_shifted_image q (C.lift q)
        C.energyShift lambda hi).mp h
    exact ⟨C.lift q,C.energyShift,w,hi,hw,hn⟩
  · rintro ⟨u,c,w,hi,hw,hn⟩
    exact (hillHminusDirichlet_eq_zero_iff_eigenstate_of_shifted_image q u c lambda hi).mpr
      ⟨w,hw,hn⟩

/-- Nontrivial scalar Dirichlet solvability is independent of the choice
of the actual L2 Miura lift and constant energy translation. -/
theorem exists_dirichlet_eigenstate_iff_other_shifted_image
    (q : PeriodOneHminusOne) (u v : Coeff 2) (c d lambda : ℂ)
    (hu : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hv : periodOneMiura v = q+periodOneL2Inclusion (lp.single 2 0 d)) :
    (∃ w : Curve (ℂ × ℂ), IsQuasiHillL2DirichletState u (lambda+c) w ∧
      ∃ t : Icc (0:ℝ) 1, (w t).1 ≠ 0) ↔
    (∃ w : Curve (ℂ × ℂ), IsQuasiHillL2DirichletState v (lambda+d) w ∧
      ∃ t : Icc (0:ℝ) 1, (w t).1 ≠ 0) :=
  (hillHminusDirichlet_eq_zero_iff_eigenstate_of_shifted_image q u c lambda hu).symm.trans
    (hillHminusDirichlet_eq_zero_iff_eigenstate_of_shifted_image q v d lambda hv)

end NLS.KdV
