import NLS.ZakharovShabat.SourcePsiGeneralVariation
import NLS.ZakharovShabat.SourcePsiContourAnalytic

/-!
# Scalar psi-equation variation at arbitrary root data

Moving a retained root changes the contour integrand by a Cauchy
kernel. On a contour that avoids that root and the canonical-root
branch cuts, the scalar equation is exactly affine in this direction.
The resulting integral is the corresponding nonfree Jacobian matrix
entry in Lemma 12.5.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The kernel obtained by differentiating a retained numerator root. -/
def sourcePsiRootVariationKernel (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) /
    (displacedRoots a k-z)

/-- Pointwise variation of the contour integrand away from the
original moved root. -/
theorem sourcePsiContourIntegrandJoint_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a : Coeff p) (ψ : CoeffPair p)
    (z t : ℂ) (hzk : z ≠ displacedRoots a k) :
    sourcePsiContourIntegrandJoint hp hp1 n
      (z,(a+lp.single p k t,ψ)) =
      sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) +
        t * sourcePsiRootVariationKernel hp hp1 n k a ψ z := by
  unfold sourcePsiContourIntegrandJoint sourcePsiRootVariationKernel
  rw [sourcePsiCandidate_variation hp hp1 n k hkn a z t hzk]
  dsimp only [sourcePsiContourIntegrandJoint]
  ring

/-- For a real-type source, the fixed-data psi integrand is
continuous on every circle contained in the canonical-root domain. -/
theorem continuousOn_sourcePsiContourIntegrandJoint_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (r : ℝ)
    (hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    ContinuousOn
      (fun z : ℂ => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)))
      (sphere c r) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  intro z hz
  have hinc : AnalyticAt ℂ (fun w : ℂ => (w,(a,ψ))) z :=
    analyticAt_id.prod (analyticAt_const)
  have hval : AnalyticAt ℂ
      (fun w : ℂ => sourcePsiContourIntegrandJoint hp hp1 n (w,(a,ψ))) z :=
    ((hdata n).2 (z,(a,ψ)) ⟨hreal hψ,hcircle hz⟩).comp
      (f := fun w : ℂ => (w,(a,ψ))) hinc
  exact hval.continuousAt.continuousWithinAt

/-- The root-variation kernel is continuous on a contour avoiding the
moved root and lying in the canonical-root domain. -/
theorem continuousOn_sourcePsiRootVariationKernel_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ)
    (a : Coeff p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (r : ℝ)
    (hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c r, z ≠ displacedRoots a k) :
    ContinuousOn
      (sourcePsiRootVariationKernel hp hp1 n k a ψ)
      (sphere c r) := by
  have hbase := continuousOn_sourcePsiContourIntegrandJoint_circle
    hp hp1 n a ψ hψ c r hcircle
  have hden : ContinuousOn
      (fun z : ℂ => (displacedRoots a k-z)⁻¹) (sphere c r) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_const.sub continuousOn_id
    · intro z hz
      exact sub_ne_zero.mpr (Ne.symm (havoid z hz))
  change ContinuousOn
    (fun z : ℂ => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) *
      (displacedRoots a k-z)⁻¹) (sphere c r)
  exact hbase.mul hden

/-- On a contour avoiding the moved root, every scalar equation is
exactly affine along that root coordinate. Its slope is the weighted
Cauchy-kernel integral from Lemma 12.5. -/
theorem sourcePsiEquationCoordinate_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hkn : k ≠ n)
    (a : Coeff p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c r, z ≠ displacedRoots a k)
    (t : ℂ) :
    sourcePsiEquationCoordinate hp hp1 n m (a+lp.single p k t) ψ c r =
      sourcePsiEquationCoordinate hp hp1 n m a ψ c r +
        t * (((n-m : ℤ) : ℂ) *
          (∮ z in C(c,r), sourcePsiRootVariationKernel hp hp1 n k a ψ z)) := by
  let F : ℂ → ℂ := fun z => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))
  let K : ℂ → ℂ := sourcePsiRootVariationKernel hp hp1 n k a ψ
  have hFcont : ContinuousOn F (sphere c r) :=
    continuousOn_sourcePsiContourIntegrandJoint_circle
      hp hp1 n a ψ hψ c r hcircle
  have hKcont : ContinuousOn K (sphere c r) :=
    continuousOn_sourcePsiRootVariationKernel_circle
      hp hp1 n k a ψ hψ c r hcircle havoid
  have hFint : CircleIntegrable F c r := hFcont.circleIntegrable hr
  have htKint : CircleIntegrable (fun z => t*K z) c r :=
    (continuousOn_const.mul hKcont).circleIntegrable hr
  have hInt :
      (∮ z in C(c,r), sourcePsiContourIntegrandJoint hp hp1 n
        (z,(a+lp.single p k t,ψ))) =
      ∮ z in C(c,r), F z+t*K z := by
    apply circleIntegral.integral_congr hr
    intro z hz
    exact sourcePsiContourIntegrandJoint_variation
      hp hp1 n k hkn a ψ z t (havoid z hz)
  rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral,
    sourcePsiEquationCoordinate_eq_raw_circleIntegral,
    hInt, circleIntegral.integral_add hFint htKint,
    circleIntegral.integral_const_mul]
  ring

/-- The nonfree scalar Jacobian entry is the weighted integral of the
root-variation kernel, whenever the selected contour avoids that root. -/
theorem hasDerivAt_sourcePsiEquationCoordinate_rootVariation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hkn : k ≠ n)
    (a : Coeff p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c r, z ≠ displacedRoots a k) :
    HasDerivAt
      (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        (a+lp.single p k t) ψ c r)
      (((n-m : ℤ) : ℂ) *
        (∮ z in C(c,r), sourcePsiRootVariationKernel hp hp1 n k a ψ z))
      0 := by
  let slope : ℂ := ((n-m : ℤ) : ℂ) *
    (∮ z in C(c,r), sourcePsiRootVariationKernel hp hp1 n k a ψ z)
  let base : ℂ := sourcePsiEquationCoordinate hp hp1 n m a ψ c r
  have heq : (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
      (a+lp.single p k t) ψ c r) =
      (fun t : ℂ => base+t*slope) := by
    funext t
    exact sourcePsiEquationCoordinate_variation
      hp hp1 n m k hkn a ψ hψ c r hr hcircle havoid t
  rw [heq]
  change HasDerivAt (fun t : ℂ => base+t*slope) slope 0
  simpa using (((hasDerivAt_id (0 : ℂ)).mul_const slope).const_add base)

/-- The same matrix entry in the dissertation's omitted-coordinate
Banach parameter space. -/
theorem hasDerivAt_sourcePsiDeletedEquationCoordinate_rootVariation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hkn : k ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c r, z ≠ displacedRoots (a : Coeff p) k) :
    HasDerivAt
      (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n k hkn t) ψ c r)
      (((n-m : ℤ) : ℂ) *
        (∮ z in C(c,r), sourcePsiRootVariationKernel hp hp1 n k
          (a : Coeff p) ψ z)) 0 := by
  have hcoe (t : ℂ) :
      ((a+Coeff.deletedSingleCLM n k hkn t : DeletedCoeff p n) : Coeff p) =
      (a : Coeff p)+lp.single p k t := by
    rw [Submodule.coe_add, Coeff.deletedSingleCLM_coe]
  have heq : (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n k hkn t) ψ c r) =
      (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        ((a : Coeff p)+lp.single p k t) ψ c r) := by
    funext t
    exact congrArg (fun b : Coeff p =>
      sourcePsiEquationCoordinate hp hp1 n m b ψ c r) (hcoe t)
  rw [heq]
  exact hasDerivAt_sourcePsiEquationCoordinate_rootVariation
    hp hp1 n m k hkn (a : Coeff p) ψ hψ c r hr hcircle havoid

end NLS.ZakharovShabat
