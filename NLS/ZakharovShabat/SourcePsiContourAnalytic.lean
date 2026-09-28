import NLS.ZakharovShabat.SourcePsiCandidate
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic
import NLS.ComplexAnalysis.ParametricCircleIntegral
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-!
# Scalar contour equations for the psi-functions

The function in (2.23) is divided by the canonical spectral root on
the moving-gap complement. For each fixed contour, the resulting
scalar functional is holomorphic in both the root displacement sequence
and the potential. This is the coordinatewise analytic part of the
contour map in Lemma 12.4; estimates placing all coordinates in one
`ℓᵖ` space are separate.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The spectral/root-displacement/source domain on which the
canonical root in the denominator does not vanish. -/
def sourcePsiContourJointDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) : Set (ℂ × (Coeff p × CoeffPair p)) :=
  {t | (t.1,t.2.2) ∈ sourceCanonicalRootJointDomain hp hp1 W}

/-- The integrand of (2.21), before choosing a contour. -/
def sourcePsiContourIntegrandJoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) : ℂ × (Coeff p × CoeffPair p) → ℂ :=
  fun t => sourcePsiCandidate n (t.1,t.2.1) /
    sourceCanonicalRoot hp hp1 t.2.2 t.1

/-- Joint analyticity of the psi contour integrand on the natural
gap complement, assuming a domain for the canonical root. -/
theorem sourcePsiContourIntegrandJoint_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (W : Set (CoeffPair p))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)) :
    AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
      (sourcePsiContourJointDomain hp hp1 W) := by
  intro t ht
  have hnumProj : AnalyticAt ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.1)) t :=
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hrootProj : AnalyticAt ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.2)) t :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hnum : AnalyticAt ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) =>
        sourcePsiCandidate n (q.1,q.2.1)) t :=
    ((analyticOnNhd_sourcePsiCandidate hp hp1 n)
      (t.1,t.2.1) (mem_univ _)).comp
        (f := fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.1)) hnumProj
  have hden : AnalyticAt ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) =>
        sourceCanonicalRoot hp hp1 q.2.2 q.1) t :=
    (hroot (t.1,t.2.2) ht).comp
      (f := fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.2)) hrootProj
  exact hnum.div hden
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 t.2.2 t.1 ht.2)

/-- One almost-real source neighborhood supports every indexed psi
integrand, jointly analytic in the spectral variable and both Banach
parameters. -/
theorem exists_global_sourcePsiContourIntegrand_jointAnalytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ n : ℤ,
        IsOpen (sourcePsiContourJointDomain hp hp1 W) ∧
        AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
          (sourcePsiContourJointDomain hp hp1 W) := by
  obtain ⟨W,hWopen,hWconn,hreal,hDopen,hroot⟩ :=
    exists_global_source_analytic_canonicalRoot hp hp1
  refine ⟨W,hWopen,hWconn,hreal,fun n => ⟨?_,?_⟩⟩
  · have hproj : Continuous
        (fun t : ℂ × (Coeff p × CoeffPair p) => (t.1,t.2.2)) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    exact hDopen.preimage hproj
  · exact sourcePsiContourIntegrandJoint_analyticOnNhd hp hp1 n W hroot

/-- The normalized psi contour functional, with the factor `1/(2π)`
from (2.21). -/
def sourcePsiContour (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  (2*Real.pi : ℂ)⁻¹ *
    ∮ z in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))

/-- If a fixed circle avoids the gaps at a real-type base source,
the normalized contour is Fréchet-holomorphic in the numerator roots
and source potential on a common neighborhood of that base point. -/
theorem exists_local_sourcePsiContour_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    ∃ V : Set (Coeff p × CoeffPair p), IsOpen V ∧ (a,φ) ∈ V ∧
      (∀ b ∈ V, sphere c R ⊆ sourceCanonicalRootDomain hp hp1 b.2) ∧
      DifferentiableOn ℂ
        (fun b : Coeff p × CoeffPair p =>
          sourcePsiContour hp hp1 n b.1 b.2 c R) V := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let D := sourcePsiContourJointDomain hp hp1 W
  let F := sourcePsiContourIntegrandJoint hp hp1 n
  have hbase (z : ℂ) (hz : z ∈ sphere c R) : (z,(a,φ)) ∈ D :=
    ⟨hreal hφ,hcircle hz⟩
  obtain ⟨V,hVopen,hbaseV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D (hdata n).1 (hdata n).2 c R (a,φ) hbase
  refine ⟨V,hVopen,hbaseV,?_,?_⟩
  · intro b hb z hz
    exact (hbound z hz b hb).1.2
  · intro b hb
    have hdiff :=
      NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
        F D (hdata n).1 (hdata n).2 c R hR V hVopen b hb M
        (fun q hq θ =>
          (hbound (circleMap c R θ) (circleMap_mem_sphere c hR θ) q hq).1)
        (fun q hq θ =>
          (hbound (circleMap c R θ) (circleMap_mem_sphere c hR θ) q hq).2)
    change DifferentiableWithinAt ℂ
      (fun q : Coeff p × CoeffPair p =>
        (2*Real.pi : ℂ)⁻¹ * ∮ z in C(c,R), F (z,q)) V b
    exact (hdiff.const_mul (2*Real.pi : ℂ)⁻¹).differentiableWithinAt

/-- The fixed psi contour functional has a joint Banach power series
in the deleted numerator roots and the complex source potential near
every real-type base source for which the circle avoids the gaps. -/
theorem exists_local_sourcePsiContour_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    ∃ V : Set (Coeff p × CoeffPair p), IsOpen V ∧ (a,φ) ∈ V ∧
      (∀ b ∈ V, sphere c R ⊆ sourceCanonicalRootDomain hp hp1 b.2) ∧
      AnalyticOnNhd ℂ
        (fun b : Coeff p × CoeffPair p =>
          sourcePsiContour hp hp1 n b.1 b.2 c R) V := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let D := sourcePsiContourJointDomain hp hp1 W
  let F := sourcePsiContourIntegrandJoint hp hp1 n
  have hbase (z : ℂ) (hz : z ∈ sphere c R) : (z,(a,φ)) ∈ D :=
    ⟨hreal hφ,hcircle hz⟩
  obtain ⟨V,hVopen,hbaseV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D (hdata n).1 (hdata n).2 c R (a,φ) hbase
  have hcircleV (b : Coeff p × CoeffPair p) (hb : b ∈ V) :
      sphere c R ⊆ sourceCanonicalRootDomain hp hp1 b.2 := by
    intro z hz
    exact (hbound z hz b hb).1.2
  have hanalytic :=
    NLS.ComplexAnalysis.analyticOnNhd_circleIntegral_of_jointAnalytic
      F (hdata n).1 (hdata n).2 c R hR hVopen
        (fun b hb z hz => (hbound z hz b hb).1)
  refine ⟨V,hVopen,hbaseV,hcircleV,?_⟩
  have hfun :
      ((2*Real.pi : ℂ)⁻¹ •
        (fun b : Coeff p × CoeffPair p => ∮ z in C(c,R), F (z,b))) =
      (fun b : Coeff p × CoeffPair p =>
        sourcePsiContour hp hp1 n b.1 b.2 c R) := by
    funext b
    simp [sourcePsiContour,F]
  rw [← hfun]
  exact hanalytic.const_smul

/-- At the free potential and free roots, the new contour functional
is exactly the free contour used in the orthogonality theorem. -/
theorem sourcePsiContour_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) :
    sourcePsiContour hp hp1 n (0 : Coeff p) (0 : CoeffPair p) c R =
      sourcePsiFreeContour hp hp1 n c R := by
  unfold sourcePsiContour sourcePsiFreeContour
  congr 1
  apply circleIntegral.integral_congr hR
  intro z _
  simp only [sourcePsiContourIntegrandJoint, sourcePsiCandidate_zero hp hp1 n z]

/-- The analytically varying contour functional recovers the free
Kronecker normalization on every sufficiently small free circle. -/
theorem sourcePsiContour_zero_orthogonality
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m n : ℤ) (R : ℝ)
    (hR : 0 < R) (hRπ : R < Real.pi) :
    sourcePsiContour hp hp1 n (0 : Coeff p) (0 : CoeffPair p)
      ((Real.pi : ℂ)*m) R = if m = n then 1 else 0 := by
  rw [sourcePsiContour_zero hp hp1 n _ R hR.le]
  exact sourcePsiFreeContour_orthogonality hp hp1 m n R hR hRπ

/-- The scalar `F_m^n` coordinate in (2.22). Unlike the orthogonality
functional (2.21), equation (2.22) has no `1/(2π)` factor. The full
sequence-valued map requires a separate `ℓᵖ` bound. -/
def sourcePsiEquationCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  ((n-m : ℤ) : ℂ) * (2*Real.pi : ℂ) *
    sourcePsiContour hp hp1 n a ψ c R

/-- Equation (2.22) has exactly the unnormalized circle integral. -/
theorem sourcePsiEquationCoordinate_eq_raw_circleIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) :
    sourcePsiEquationCoordinate hp hp1 n m a ψ c R =
      ((n-m : ℤ) : ℂ) *
        (∮ z in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))) := by
  unfold sourcePsiEquationCoordinate sourcePsiContour
  have hπ : (2*Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  field_simp

/-- Every free coordinate of the contour equation vanishes on its
own free-centered circle. -/
theorem sourcePsiEquationCoordinate_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m n : ℤ) (R : ℝ)
    (hR : 0 < R) (hRπ : R < Real.pi) :
    sourcePsiEquationCoordinate hp hp1 n m
      (0 : Coeff p) (0 : CoeffPair p) ((Real.pi : ℂ)*m) R = 0 := by
  rw [sourcePsiEquationCoordinate,
    sourcePsiContour_zero_orthogonality hp hp1 m n R hR hRπ]
  by_cases hmn : m = n
  · subst n
    simp
  · simp [hmn]

/-- Each weighted scalar equation coordinate is holomorphic in both
Banach parameters near a real-type base source. -/
theorem exists_local_sourcePsiEquationCoordinate_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    ∃ V : Set (Coeff p × CoeffPair p), IsOpen V ∧ (a,φ) ∈ V ∧
      (∀ b ∈ V, sphere c R ⊆ sourceCanonicalRootDomain hp hp1 b.2) ∧
      DifferentiableOn ℂ
        (fun b : Coeff p × CoeffPair p =>
          sourcePsiEquationCoordinate hp hp1 n m b.1 b.2 c R) V := by
  obtain ⟨V,hVopen,hbase,hcircleV,hdiff⟩ :=
    exists_local_sourcePsiContour_differentiableOn
      hp hp1 n a φ hφ c R hR hcircle
  refine ⟨V,hVopen,hbase,hcircleV,?_⟩
  change DifferentiableOn ℂ
    (fun b : Coeff p × CoeffPair p =>
      (((n-m : ℤ) : ℂ) * (2*Real.pi : ℂ)) *
        sourcePsiContour hp hp1 n b.1 b.2 c R) V
  exact hdiff.const_mul _

/-- Each fixed-circle scalar psi equation coordinate has a joint
Banach power series in the root displacement sequence and source
potential near a real-type base source. -/
theorem exists_local_sourcePsiEquationCoordinate_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    ∃ V : Set (Coeff p × CoeffPair p), IsOpen V ∧ (a,φ) ∈ V ∧
      (∀ b ∈ V, sphere c R ⊆ sourceCanonicalRootDomain hp hp1 b.2) ∧
      AnalyticOnNhd ℂ
        (fun b : Coeff p × CoeffPair p =>
          sourcePsiEquationCoordinate hp hp1 n m b.1 b.2 c R) V := by
  obtain ⟨V,hVopen,hbase,hcircleV,hanalytic⟩ :=
    exists_local_sourcePsiContour_analyticOnNhd
      hp hp1 n a φ hφ c R hR hcircle
  refine ⟨V,hVopen,hbase,hcircleV,?_⟩
  have hfun :
      ((((n-m : ℤ) : ℂ) * (2*Real.pi : ℂ)) •
        (fun b : Coeff p × CoeffPair p =>
          sourcePsiContour hp hp1 n b.1 b.2 c R)) =
      (fun b : Coeff p × CoeffPair p =>
        sourcePsiEquationCoordinate hp hp1 n m b.1 b.2 c R) := by
    funext b
    simp [sourcePsiEquationCoordinate]
  rw [← hfun]
  exact hanalytic.const_smul

/-- Around every real-type source and every gap, one enclosing circle
works for nearby potentials and makes the corresponding scalar psi
equation holomorphic in the displacement sequence and potential. -/
theorem exists_local_sourcePsiEquationCoordinate_enclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (Coeff p × CoeffPair p), IsOpen V ∧ (a,φ) ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ b ∈ V,
          sourcePeriodicSegment hp hp1 b.2 m ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 b.2 m) ∧
        DifferentiableOn ℂ
          (fun b : Coeff p × CoeffPair p =>
            sourcePsiEquationCoordinate hp hp1 n m b.1 b.2 c R) V := by
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle hp hp1 φ hφ m
  obtain ⟨V₁,hV₁open,hbaseV₁,_,hdiff⟩ :=
    exists_local_sourcePsiEquationCoordinate_differentiableOn
      hp hp1 n m a φ hφ c R hR.le (hgeom φ hφV₀).2.2
  let V : Set (Coeff p × CoeffPair p) := V₁ ∩ {b | b.2 ∈ V₀}
  have hVopen : IsOpen V :=
    hV₁open.inter (hV₀open.preimage continuous_snd)
  have hbase : (a,φ) ∈ V := ⟨hbaseV₁,hφV₀⟩
  refine ⟨V,hVopen,hbase,c,R,hR,?_,hdiff.mono inter_subset_left⟩
  intro b hb
  exact ⟨(hgeom b.2 hb.2).1,(hgeom b.2 hb.2).2.1⟩

end NLS.ZakharovShabat
