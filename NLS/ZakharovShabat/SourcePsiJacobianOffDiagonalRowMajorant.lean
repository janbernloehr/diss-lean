import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalAllGaps
import NLS.SequenceSpaces.FiniteExponentTail
import NLS.SequenceSpaces.Truncation

/-!
# An ℓᵖ row majorant for the off-diagonal psi Jacobian

The numerator in the all-real-gap off-diagonal estimate is the sum
of three ℓᵖ displacement magnitudes, multiplied by one plus a
bounded ℓᵖ quotient majorant. It therefore defines an ℓᵖ
sequence, as required by the matrix estimate in Lemma 12.5.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The positive real coefficient sequence appearing in the
off-diagonal inverse lattice-distance estimate. -/
def sourcePsiOffDiagonalRowMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (B : Coeff p) : Coeff p := by
  let D : ℤ → ℝ := fun m =>
    ‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2
  let M : ℝ := (8/Real.pi)*(1+‖B‖)
  have hD : Memℓp D p := by
    have ha : Memℓp (fun m : ℤ => ‖a m‖) p := (lp.memℓp a).norm
    have hm : Memℓp (fun m : ℤ =>
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖) p :=
      (lp.memℓp (sourcePeriodicMidpointDisplacement hp hp1 ψ)).norm
    have hg : Memℓp (fun m : ℤ =>
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) p := by
      simpa only [div_eq_mul_inv,one_mul,mul_comm] using
        ((lp.memℓp (sourcePeriodicGapDisplacement hp hp1 ψ)).norm.const_mul
          (1/2:ℝ))
    exact (ha.add hm).add hg
  have hmajor : Memℓp (fun m : ℤ => M*D m) p :=
    hD.const_mul M
  refine ⟨fun m => (((8/Real.pi)*D m*(1+‖B m‖) : ℝ) : ℂ),?_⟩
  apply hmajor.mono
  intro m
  have hDm : 0 ≤ D m := by dsimp [D]; positivity
  have hfactor : 0 ≤ (8/Real.pi)*D m := by positivity
  have hBcoord : ‖B m‖ ≤ ‖B‖ :=
    lp.norm_apply_le_norm
      (ne_of_gt (zero_lt_one.trans_le Fact.out)) B m
  have hweight : 1+‖B m‖ ≤ 1+‖B‖ := by linarith
  have hvalue : 0 ≤ (8/Real.pi)*D m*(1+‖B m‖) := by positivity
  calc
    ‖(((8/Real.pi)*D m*(1+‖B m‖) : ℝ) : ℂ)‖ =
        (8/Real.pi)*D m*(1+‖B m‖) := by
          rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hvalue]
    _ ≤ (8/Real.pi)*D m*(1+‖B‖) :=
      mul_le_mul_of_nonneg_left hweight hfactor
    _ = M*D m := by dsimp [M]; ring

/-- The row majorant's coordinate norm is the exact nonnegative
numerator from the off-diagonal Jacobian bound. -/
theorem norm_sourcePsiOffDiagonalRowMajorant_apply
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (B : Coeff p) (m : ℤ) :
    ‖sourcePsiOffDiagonalRowMajorant hp hp1 a ψ B m‖ =
      (8/Real.pi)*
        (‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
        (1+‖B m‖) := by
  have hnonneg : 0 ≤ (8/Real.pi)*
      (‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
      (1+‖B m‖) := by positivity
  simp only [sourcePsiOffDiagonalRowMajorant,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hnonneg]

/-- A fixed `ℓᵖ` sequence dominates every off-diagonal row majorant
whose root displacement is coordinatewise bounded by `a` and whose
quotient majorant has norm at most `M`. In particular, this applies
to the deleted-coordinate inputs as the deleted index escapes. -/
def sourcePsiOffDiagonalUniformRowMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (M : ℝ) : Coeff p :=
  ((1+M : ℝ) : ℂ) • sourcePsiOffDiagonalRowMajorant hp hp1 a ψ 0

/-- The uniform majorant controls the whole norm-bounded family of
quotient corrections, including deleted-coordinate root inputs. -/
theorem norm_sourcePsiOffDiagonalRowMajorant_le_uniform
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a a' : Coeff p) (ψ : CoeffPair p) (B : Coeff p)
    (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ m : ℤ, ‖a' m‖ ≤ ‖a m‖)
    (hB : ‖B‖ ≤ M) (m : ℤ) :
    ‖sourcePsiOffDiagonalRowMajorant hp hp1 a' ψ B m‖ ≤
      ‖sourcePsiOffDiagonalUniformRowMajorant hp hp1 a ψ M m‖ := by
  rw [norm_sourcePsiOffDiagonalRowMajorant_apply]
  have hfixed :
      ‖sourcePsiOffDiagonalUniformRowMajorant hp hp1 a ψ M m‖ =
        (1+M) * (8/Real.pi) *
          (‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) := by
    simp only [sourcePsiOffDiagonalUniformRowMajorant,
      lp.coeFn_smul, Pi.smul_apply, norm_smul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1+M),
      norm_sourcePsiOffDiagonalRowMajorant_apply, lp.coeFn_zero,
      Pi.zero_apply, norm_zero, add_zero, mul_one]
    ring
  rw [hfixed]
  have hBcoord : ‖B m‖ ≤ M :=
    (lp.norm_apply_le_norm
      (ne_of_gt (zero_lt_one.trans_le Fact.out)) B m).trans hB
  have hfactor : 0 ≤ 8/Real.pi := by positivity
  have hroot : 0 ≤ ‖a m‖ +
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by positivity
  have hroot' : ‖a' m‖ +
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤
      ‖a m‖ +
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
    linarith [ha m]
  have hweight : 1+‖B m‖ ≤ 1+M := by linarith
  calc
    (8/Real.pi) *
        (‖a' m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
          (1+‖B m‖) ≤
        (8/Real.pi) *
        (‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
          (1+M) := by
            gcongr
    _ = _ := by ring

/-- One majorant works for every deleted coordinate of a fixed root
sequence, uniformly over quotient corrections with bounded norm. -/
theorem norm_sourcePsiOffDiagonalRowMajorant_delete_le_uniform
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (B : Coeff p)
    (M : ℝ) (hM : 0 ≤ M) (hB : ‖B‖ ≤ M)
    (n m : ℤ) :
    ‖sourcePsiOffDiagonalRowMajorant hp hp1
      (Coeff.deleteCoordinate n a) ψ B m‖ ≤
      ‖sourcePsiOffDiagonalUniformRowMajorant hp hp1 a ψ M m‖ := by
  apply norm_sourcePsiOffDiagonalRowMajorant_le_uniform
    hp hp1 a (Coeff.deleteCoordinate n a) ψ B M hM _ hB m
  intro j
  by_cases hj : j = n
  · subst j
    simp
  · rw [Coeff.deleteCoordinate_apply_other n j hj]

/-- Every deleted-index off-diagonal row majorant is uniformly small
on sufficiently distant output rows, provided the quotient-correction
norms share one bound. -/
theorem exists_sourcePsiOffDiagonalRowMajorant_delete_uniformTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p)
    (M : ℝ) (hM : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n m : ℤ, K ≤ m.natAbs →
      ∀ B : Coeff p, ‖B‖ ≤ M →
        ‖sourcePsiOffDiagonalRowMajorant hp hp1
          (Coeff.deleteCoordinate n a) ψ B m‖ < ε := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  obtain ⟨K,hK⟩ := Coeff.exists_natAbs_norm_lt hpr
    (sourcePsiOffDiagonalUniformRowMajorant hp hp1 a ψ M) hε
  refine ⟨K,?_⟩
  intro n m hm B hB
  exact (norm_sourcePsiOffDiagonalRowMajorant_delete_le_uniform
    hp hp1 a ψ B M hM hB n m).trans_lt (hK m hm)

/-- The off-diagonal row majorants of all deleted-index inputs have
one common `ℓᵖ` tail cutoff when their quotient corrections are norm
bounded. This is stronger than uniform decay of individual rows. -/
theorem exists_sourcePsiOffDiagonalRowMajorant_delete_uniformNormTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p)
    (M : ℝ) (hM : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∀ n : ℤ, ∀ B : Coeff p, ‖B‖ ≤ M →
      ‖Coeff.truncate s
          (sourcePsiOffDiagonalRowMajorant hp hp1
            (Coeff.deleteCoordinate n a) ψ B) -
        sourcePsiOffDiagonalRowMajorant hp hp1
          (Coeff.deleteCoordinate n a) ψ B‖ < ε := by
  let b := sourcePsiOffDiagonalUniformRowMajorant hp hp1 a ψ M
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp
    (Coeff.tendsto_truncate hp b) ε hε
  refine ⟨s,?_⟩
  intro n B hB
  let bₙ := sourcePsiOffDiagonalRowMajorant hp hp1
    (Coeff.deleteCoordinate n a) ψ B
  have hpoint (m : ℤ) :
      ‖(Coeff.truncate s bₙ - bₙ) m‖ ≤
        ‖(Coeff.truncate s b - b) m‖ := by
    by_cases hm : m ∈ s
    · simp [Coeff.truncate_apply, hm]
    · simpa [Coeff.truncate_apply, hm] using
        norm_sourcePsiOffDiagonalRowMajorant_delete_le_uniform
          hp hp1 a ψ B M hM hB n m
  have hnorm : ‖Coeff.truncate s bₙ - bₙ‖ ≤
      ‖Coeff.truncate s b - b‖ :=
    lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out)) hpoint
  have hb : ‖Coeff.truncate s b - b‖ < ε := by
    simpa only [dist_eq_norm] using hs s le_rfl
  exact hnorm.trans_lt hb

/-- Both real gap types satisfy the dissertation's off-diagonal
matrix-entry pattern with an actual `ℓᵖ` row majorant. -/
theorem norm_sourcePsi_offDiagonalJacobian_le_rowMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n) (hmk : m ≠ k)
    (a : DeletedCoeff p n)
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      Metric.ball ((Real.pi : ℂ)*m) R)
    (hdom : Metric.closedBall ((Real.pi : ℂ)*m) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : Metric.sphere ((Real.pi : ℂ)*m) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ Metric.sphere ((Real.pi : ℂ)*m) R,
      z ≠ displacedRoots (a : Coeff p) n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (Metric.closedBall ((Real.pi : ℂ)*m) R))
    (B : Coeff p)
    (hroot : ‖(a : Coeff p) k‖ ≤ Real.pi/4)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤ Real.pi/4)
    (hQ : ∀ z ∈ Metric.closedBall ((Real.pi : ℂ)*m) R,
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n k hkn t) ψ
        ((Real.pi : ℂ)*m) R) 0‖ ≤
      ‖sourcePsiOffDiagonalRowMajorant hp hp1 (a : Coeff p) ψ B m‖ /
        ‖((m-k : ℤ) : ℂ)‖ := by
  rw [norm_sourcePsiOffDiagonalRowMajorant_apply]
  exact norm_sourcePsi_offDiagonalJacobian_all_realGaps_le
    hp hp1 ψ hreal n m k hmn hkn hmk a hroots R hR hRquarter
      hseg hdom hcircle havoidn hreg B hroot hsmall hQ

end NLS.ZakharovShabat
