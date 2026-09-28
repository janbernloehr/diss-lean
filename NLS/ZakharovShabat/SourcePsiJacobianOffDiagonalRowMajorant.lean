import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalAllGaps

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
