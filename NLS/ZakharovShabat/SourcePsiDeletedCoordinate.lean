import NLS.SequenceSpaces.DeletedCoordinate
import NLS.ZakharovShabat.SourcePsiContourAnalytic

/-!
# Psi equations on the deleted-coordinate Banach space

Section 12 uses `ℓᵖ(ℤ \ {n})` for the unknown roots. We use its
closed zero-at-`n` realization inside the ambient integer-indexed
`ℓᵖ` space. The numerator and each scalar contour equation descend
through the continuous coordinate-deletion projection.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The numerator in (2.23) with its actual omitted-coordinate
Banach-space parameter. -/
def sourcePsiDeletedCandidate (n : ℤ) : ℂ × DeletedCoeff p n → ℂ :=
  fun t => sourcePsiCandidate n (t.1,(t.2 : Coeff p))

/-- The deleted-coordinate numerator is jointly entire in the
spectral parameter and its Banach parameter. -/
theorem analyticOnNhd_sourcePsiDeletedCandidate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℂ (sourcePsiDeletedCandidate (p := p) n) univ := by
  intro t _
  have hinc : AnalyticAt ℂ
      (fun q : ℂ × DeletedCoeff p n => (q.1,(q.2 : Coeff p))) t :=
    analyticAt_fst.prod
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.analyticAt t.2).comp
        analyticAt_snd)
  exact ((analyticOnNhd_sourcePsiCandidate hp hp1 n)
    (t.1,(t.2 : Coeff p)) (mem_univ _)).comp
      (f := fun q : ℂ × DeletedCoeff p n => (q.1,(q.2 : Coeff p))) hinc

/-- Deleting the unused ambient coordinate before evaluating the
numerator does not change its value. -/
theorem sourcePsiCandidate_eq_deletedCandidate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ) (a : Coeff p) :
    sourcePsiCandidate n (z,a) =
      sourcePsiDeletedCandidate n (z,Coeff.deleteCoordinateTo n a) := by
  change sourcePsiCandidate n (z,a) =
    sourcePsiCandidate n (z,Coeff.deleteCoordinate n a)
  exact sourcePsiCandidate_eq_of_off_index hp hp1 n z a _
    (fun m hm => (Coeff.deleteCoordinate_apply_other n m hm a).symm)

/-- The normalized contour functional on the omitted-coordinate
Banach space. -/
def sourcePsiDeletedContour (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  sourcePsiContour hp hp1 n (a : Coeff p) ψ c R

/-- The scalar equation in (2.22) on the omitted-coordinate Banach
space. -/
def sourcePsiDeletedEquationCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) : ℂ :=
  sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ c R

/-- The free data solve each scalar equation on the deleted-coordinate
space. -/
theorem sourcePsiDeletedEquationCoordinate_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m n : ℤ) (R : ℝ)
    (hR : 0 < R) (hRπ : R < Real.pi) :
    sourcePsiDeletedEquationCoordinate hp hp1 n m
      (0 : DeletedCoeff p n) (0 : CoeffPair p)
      ((Real.pi : ℂ)*m) R = 0 := by
  change sourcePsiEquationCoordinate hp hp1 n m
    (0 : Coeff p) (0 : CoeffPair p) ((Real.pi : ℂ)*m) R = 0
  exact sourcePsiEquationCoordinate_zero hp hp1 m n R hR hRπ

/-- The ambient contour equation factors through coordinate deletion
on every circle of nonnegative radius. -/
theorem sourcePsiEquationCoordinate_eq_deletedCoordinate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    sourcePsiEquationCoordinate hp hp1 n m a ψ c R =
      sourcePsiDeletedEquationCoordinate hp hp1 n m
        (Coeff.deleteCoordinateTo n a) ψ c R := by
  have hnum (z : ℂ) :
      sourcePsiCandidate n (z,a) =
        sourcePsiCandidate n (z,Coeff.deleteCoordinate n a) :=
    sourcePsiCandidate_eq_of_off_index hp hp1 n z a _
      (fun k hk => (Coeff.deleteCoordinate_apply_other n k hk a).symm)
  have hInt :
      (∮ z in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))) =
      (∮ z in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n
        (z,(Coeff.deleteCoordinate n a,ψ))) := by
    apply circleIntegral.integral_congr hR
    intro z _
    exact congrArg (fun v : ℂ => v / sourceCanonicalRoot hp hp1 ψ z) (hnum z)
  change ((n-m : ℤ) : ℂ) * ((2*Real.pi : ℂ)⁻¹ *
      (∮ z in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)))) =
    ((n-m : ℤ) : ℂ) * ((2*Real.pi : ℂ)⁻¹ *
      (∮ z in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n
        (z,(Coeff.deleteCoordinate n a,ψ))))
  rw [hInt]

/-- Near a real-type source, every scalar equation is holomorphic in
the actual omitted-coordinate Banach parameter and the potential. -/
theorem exists_local_sourcePsiDeletedEquationCoordinate_enclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (a : DeletedCoeff p n) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (DeletedCoeff p n × CoeffPair p),
      IsOpen V ∧ (a,φ) ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ b ∈ V,
          sourcePeriodicSegment hp hp1 b.2 m ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 b.2 m) ∧
        DifferentiableOn ℂ
          (fun b : DeletedCoeff p n × CoeffPair p =>
            sourcePsiDeletedEquationCoordinate hp hp1 n m b.1 b.2 c R) V := by
  obtain ⟨U,hUopen,hbaseU,c,R,hR,hgeom,hdiff⟩ :=
    exists_local_sourcePsiEquationCoordinate_enclosingCircle
      hp hp1 n m (a : Coeff p) φ hφ
  let ι : DeletedCoeff p n × CoeffPair p → Coeff p × CoeffPair p :=
    fun b => ((b.1 : Coeff p),b.2)
  have hι : Differentiable ℂ ι := by
    intro b
    exact ((((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.analyticAt b.1).comp
      analyticAt_fst).prod analyticAt_snd).differentiableAt
  let V := ι ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage hι.continuous
  have hbase : (a,φ) ∈ V := hbaseU
  refine ⟨V,hVopen,hbase,c,R,hR,?_,?_⟩
  · intro b hb
    exact hgeom (ι b) hb
  · intro b hb
    have hsection := (hdiff (ι b) hb).differentiableAt
      (hUopen.mem_nhds hb)
    exact (hsection.comp b (hι b)).differentiableWithinAt

end NLS.ZakharovShabat
