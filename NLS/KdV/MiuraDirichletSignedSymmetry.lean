import NLS.KdV.MiuraDirichletCoordinates
import NLS.KdV.MiuraL2DirichletAuxiliary
import NLS.ZakharovShabat.CanonicalPeriodOneBoundaryAnalytic
import NLS.SequenceSpaces.OrderedSignedSimpleEnumeration

/-! The exact central index of the actual real diagonal auxiliary
Dirichlet spectrum. Oddness and the original L2 displacement prove full
signed reflection and the zero coordinate, rather than assuming a tail offset. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- The actual auxiliary Dirichlet characteristic of a diagonal source
is odd, including the zero-frequency normalization. -/
theorem auxiliaryDirichlet_hillMiuraDiagonal_neg (u : Coeff 2) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u) (-z) =
      -auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
        (hillMiuraDiagonal u) z := by
  rw [auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet,
    auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet,neg_sq,neg_mul]


/-- Canonical real diagonal auxiliary roots are strictly ordered at
EVERY signed index, including the finite central block. -/
theorem strictMono_hillMiuraDiracDirichlet_re (u : PeriodOneRealL2) :
    StrictMono (fun n : ℤ => (hillMiuraDiracDirichlet u.val n).re) := by
  simpa only [hillMiuraDiracDirichlet,canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase] using
    strictMono_canonicalPeriodOneBoundaryRoots_re_of_realType (by simp) (by norm_num)
      .dirichlet (sourcePhase (hillMiuraDiagonal u.val))
        (isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal u))

/-- The actual auxiliary characteristic's zeros are exactly the range
of its canonical diagonal sequence on the whole complex L2 domain. -/
theorem mem_range_hillMiuraDiracDirichlet_iff (u : Coeff 2) (z : ℂ) :
    z ∈ range (hillMiuraDiracDirichlet u) ↔
      auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
        (hillMiuraDiagonal u) z = 0 :=
  (canonicalAuxiliaryPeriodOneRoots_exhaustive (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u) z).symm.trans
      (auxiliaryPeriodOneCharacteristic_eq_zero_iff (by simp) (by norm_num)
        .dirichlet (hillMiuraDiagonal u) z).symm

/-- Oddness of the independently normalized characteristic and L2
asymptotics fix full signed reflection, including every central index. -/
theorem hillMiuraDiracDirichlet_neg (u : PeriodOneRealL2) (n : ℤ) :
    hillMiuraDiracDirichlet u.val (-n) = -hillMiuraDiracDirichlet u.val n := by
  let f := hillMiuraDiracDirichlet u.val
  let g : ℤ → ℂ := fun k => -f (-k)
  have hf : Memℓp (fun k => f k-(Real.pi:ℂ)*k) 2 := by
    have h := lp.memℓp (hillMiuraDirichletDisplacement u.val)
    convert! h using 1
    funext k
    exact (hillMiuraDirichletDisplacement_apply u.val k).symm
  have hg : Memℓp (fun k => g k-(Real.pi:ℂ)*k) 2 := by
    have h := lp.memℓp (-(Coeff.reflection (hillMiuraDirichletDisplacement u.val)))
    convert! h using 1
    funext k
    simp only [lp.coeFn_neg,Pi.neg_apply,Coeff.reflection_apply,
      hillMiuraDirichletDisplacement_apply,Int.cast_neg]
    dsimp [g,f]
    ring
  have hfm := strictMono_hillMiuraDiracDirichlet_re u
  have hgm : StrictMono (fun k => (g k).re) := by
    intro i j hij
    have h := hfm (neg_lt_neg hij)
    simpa only [g,Complex.neg_re] using neg_lt_neg h
  have hroot (k : ℤ) : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num)
      .dirichlet (hillMiuraDiagonal u.val) (f k) = 0 :=
    (mem_range_hillMiuraDiracDirichlet_iff u.val _).mp ⟨k,rfl⟩
  have hneg (k : ℤ) : -f k ∈ range f := by
    apply (mem_range_hillMiuraDiracDirichlet_iff u.val _).mpr
    rw [auxiliaryDirichlet_hillMiuraDiagonal_neg,hroot,neg_zero]
  have he : range f = range g := by
    ext z
    constructor
    · rintro ⟨k,rfl⟩
      obtain ⟨j,hj⟩ := hneg k
      refine ⟨-j,?_⟩
      simp only [g,neg_neg,hj]
    · rintro ⟨k,rfl⟩
      exact hneg (-k)
  have heq := ordered_signed_simple_unique_of_l2 f g hf hg hfm hgm he
  simpa only [g,neg_neg] using congrFun heq (-n)

/-- The original zero auxiliary coordinate is exactly zero, fixing
the scalar positive-index offset without any central root assumption. -/
theorem hillMiuraDiracDirichlet_zero (u : PeriodOneRealL2) :
    hillMiuraDiracDirichlet u.val 0 = 0 := by
  have he := hillMiuraDiracDirichlet_neg u 0
  simp only [neg_zero] at he
  linear_combination (1/2:ℂ)*he

/-- Positive signed indices are exactly positive real frequencies. -/
theorem hillMiuraDiracDirichlet_re_pos_iff (u : PeriodOneRealL2) (n : ℤ) :
    0 < (hillMiuraDiracDirichlet u.val n).re ↔ 0 < n := by
  have he : (hillMiuraDiracDirichlet u.val 0).re <
      (hillMiuraDiracDirichlet u.val n).re ↔ (0:ℤ) < n :=
    (strictMono_hillMiuraDiracDirichlet_re u).lt_iff_lt
  simpa only [hillMiuraDiracDirichlet_zero,Complex.zero_re] using he

end NLS.KdV
