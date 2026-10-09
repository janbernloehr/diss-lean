import NLS.ZakharovShabat.L2HermitianFirstBorn
import NLS.ZakharovShabat.L2SolutionDifferentialEquation
import NLS.FunctionalAnalysis.ContinuousCurveIntegral

/-! # Lemma G.1 for arbitrary physical L2 potentials

Pass the actual continuous-potential operator estimate to the original L2
space. Both the operator curve and its square integral converge in the
required norms. The coefficient is exactly ||u|| exp(||u||).
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The fundamental matrix built from the two actual L2 solution columns. -/
def l2FundamentalMatrix (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(l2SolutionCurve u z (1,0) t).1,(l2SolutionCurve u z (0,1) t).1;
     (l2SolutionCurve u z (1,0) t).2,(l2SolutionCurve u z (0,1) t).2]

/-- The actual fundamental-solution remainder in the Hermitian operator norm. -/
def l2HermitianRemainderOperator (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    HermitianPair →L[ℂ] HermitianPair :=
  hermitianColumns (l2SolutionCurve u z (1,0) t-classicalFreeVector z (1,0) t)
    (l2SolutionCurve u z (0,1) t-classicalFreeVector z (0,1) t)

/-- The operator is exactly M-E for the actual L2 fundamental matrix. -/
theorem l2HermitianRemainderOperator_eq_matrix (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2HermitianRemainderOperator u z t =
      classicalHermitianMatrixOperator (l2FundamentalMatrix u z t-classicalFreeMatrix z t) := by
  unfold l2HermitianRemainderOperator classicalHermitianMatrixOperator
  congr 1 <;> ext <;> simp [l2FundamentalMatrix,classicalFreeMatrix,classicalFreeVector]

/-- The source's exponentially weighted remainder operator norm. -/
def l2NormalizedHermitianRemainder (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) : ℝ :=
  Real.exp (-(|z.im| *t.val))*‖l2HermitianRemainderOperator u z t‖

/-- The actual continuous-potential remainder converges to the actual L2 remainder. -/
theorem tendsto_classicalNormalizedHermitianRemainder_L2 (u : IntervalPairL2) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    Tendsto (fun φ => classicalNormalizedHermitianRemainder φ z t) (continuousPotentialL2Filter u)
      (𝓝 (l2NormalizedHermitianRemainder u z t)) := by
  have h₁ := ((continuous_eval_const t).tendsto (l2SolutionCurve u z (1,0))).comp
    (tendsto_classicalSolutionCurve_L2 u z (1,0))
  have h₂ := ((continuous_eval_const t).tendsto (l2SolutionCurve u z (0,1))).comp
    (tendsto_classicalSolutionCurve_L2 u z (0,1))
  have hr₁ := h₁.sub (tendsto_const_nhds (x := classicalFreeVector z (1,0) t))
  have hr₂ := h₂.sub (tendsto_const_nhds (x := classicalFreeVector z (0,1) t))
  have h := (continuous_hermitianColumns.continuousAt.tendsto.comp (hr₁.prodMk_nhds hr₂)).norm
  simpa only [Function.comp_def,classicalSolutionCurve_apply,classicalNormalizedHermitianRemainder,
    classicalHermitianRemainderOperator,classicalSolutionRemainder,l2NormalizedHermitianRemainder,
    l2HermitianRemainderOperator] using h.const_mul (Real.exp (-(|z.im| *t.val)))

/-- Exact classical recovery of the square integral appearing on the right of G.1. -/
theorem integral_l2NormalizedHermitianFirstBorn_sq_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..t.val, (extend (l2NormalizedHermitianFirstBorn (continuousPotentialL2Class φ) z) s)^2) =
      ∫ s in (0:ℝ)..t.val, (classicalNormalizedHermitianFirstBorn φ z s)^2 := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
  have he := l2NormalizedHermitianFirstBorn_of_continuous φ z ⟨s,hs'⟩
  simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs'] using congrArg (fun x : ℝ => x^2) he

/-- G.1 with the literal coefficient and genuine Hermitian operator norm for
all original physical L2 potentials, complex frequencies, and times in [0,1]. -/
theorem l2HermitianOperator_le_L2_firstBorn (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2NormalizedHermitianRemainder u z t ≤ l2NormalizedHermitianFirstBorn u z t+
      ‖u‖*Real.exp ‖u‖*Real.sqrt (∫ s in (0:ℝ)..t.val,
        (extend (l2NormalizedHermitianFirstBorn u z) s)^2) := by
  let : NeBot (continuousPotentialL2Filter u) := continuousPotentialL2Filter_neBot u
  have hp : Tendsto continuousPotentialL2Class (continuousPotentialL2Filter u) (𝓝 u) := tendsto_comap
  have hF := ((continuous_l2NormalizedHermitianFirstBorn z).tendsto u).comp hp
  have hv := ((continuous_eval_const t).tendsto (l2NormalizedHermitianFirstBorn u z)).comp hF
  have hS := ((continuous_curve_squareIntegral t).tendsto (l2NormalizedHermitianFirstBorn u z)).comp hF
  simp only [Function.comp_def,l2NormalizedHermitianFirstBorn_of_continuous] at hv
  simp only [Function.comp_def,integral_l2NormalizedHermitianFirstBorn_sq_of_continuous] at hS
  have hA := hp.norm
  simp only [norm_continuousPotentialL2Class] at hA
  have hR := hv.add ((hA.mul (Real.continuous_exp.continuousAt.tendsto.comp hA)).mul
    (Real.continuous_sqrt.continuousAt.tendsto.comp hS))
  exact le_of_tendsto_of_tendsto (tendsto_classicalNormalizedHermitianRemainder_L2 u z t) hR
    (Eventually.of_forall (fun φ => classicalHermitianOperator_le_L2_firstBorn φ z t))

/-- Exact recovery of the existing classical fundamental matrix. -/
theorem l2FundamentalMatrix_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2FundamentalMatrix (continuousPotentialL2Class φ) z t = classicalFundamentalMatrix φ z t := by
  simp only [l2FundamentalMatrix,l2SolutionCurve_of_continuous,classicalSolutionCurve_apply,
    classicalFundamentalMatrix]

/-- The fundamental matrix has its original identity initial value. -/
@[simp] theorem l2FundamentalMatrix_zero (u : IntervalPairL2) (z : ℂ) :
    l2FundamentalMatrix u z ⟨0,by constructor <;> norm_num⟩ = 1 := by
  simp [l2FundamentalMatrix,Matrix.one_fin_two]

/-- The remainder normalization recovers the exact classical definition. -/
theorem l2NormalizedHermitianRemainder_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    l2NormalizedHermitianRemainder (continuousPotentialL2Class φ) z t =
      classicalNormalizedHermitianRemainder φ z t := by
  simp only [l2NormalizedHermitianRemainder,l2HermitianRemainderOperator,l2SolutionCurve_of_continuous,
    classicalSolutionCurve_apply,classicalNormalizedHermitianRemainder,classicalHermitianRemainderOperator,
    classicalSolutionRemainder]

end NLS.ZakharovShabat
