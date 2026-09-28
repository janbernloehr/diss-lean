import NLS.ZakharovShabat.SourcePsiLimitIntegrandUniform
import NLS.ZakharovShabat.SourcePsiJacobianGapFactorization
import NLS.ZakharovShabat.SourcePsiJacobianFullMatrix

/-!
# Scalar selected-Jacobian entries at an escaping deleted index

The contour limit for the full retained integrand is converted into a
limit of the actual scalar directional derivative. The normalization
by `π` is kept explicit so the candidate `Q*` matrix entry can later
be used in finite-block operator convergence.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A scalar retained-root Jacobian entry for the full coefficient
sequence with coordinate `n` deleted. The undefined retained direction
at `k = n` is assigned zero; this case disappears as `|n| → ∞` for
every fixed `k`. -/
def sourcePsiDeletedScalarMatrixEntry
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) : ℂ :=
  if hkn : k ≠ n then
    deriv (fun t : ℂ =>
      sourcePsiDeletedEquationCoordinate hp hp1 n m
        (Coeff.deleteCoordinateTo n a +
          Coeff.deletedSingleCLM n k hkn t) ψ c R) 0
  else 0

/-- The candidate nonfree scalar `Q*` matrix entry on one fixed
contour, with the normalization from equation (2.28). -/
def sourcePsiLimitMatrixEntry
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) : ℂ :=
  (∮ z in C(c,R), sourcePsiLimitMatrixIntegrand hp hp1 m k a ψ z) /
    (Real.pi : ℂ)

/-- On a fixed valid contour, every fixed retained scalar Jacobian
entry converges to the corresponding candidate `Q*` entry when the
deleted index escapes in either direction. -/
theorem tendsto_sourcePsiDeletedScalarMatrixEntry_at_natAbs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hk : ∀ z ∈ sphere c R, displacedRoots a k - z ≠ 0) :
    Tendsto (fun n : ℤ =>
      sourcePsiDeletedScalarMatrixEntry hp hp1 n m k a ψ c R)
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a ψ c R)) := by
  have hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m :=
    fun z hz => hcircle hz m
  have hlim := tendsto_circleIntegral_sourcePsi_fullJacobianIntegrand_deletedIndex
    hp hp1 m k a ψ hψ c R hR hdisc hk hm
  have hπ : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hconv := hlim.div_const (Real.pi : ℂ)
  have hfar := (tendsto_norm_freeCenter_sub_at_natAbs c).eventually_ge_atTop
    (R + 1)
  have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      k ≠ n := by
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨k.natAbs + 1,?_⟩
    intro j hj n hn hnk
    subst n
    omega
  have heq : (fun n : ℤ =>
      (∮ z in C(c,R),
        (Real.pi : ℂ) *
          (((displacedRoots (Coeff.deleteCoordinate n a) m-z) /
              (displacedRoots (Coeff.deleteCoordinate n a) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (Coeff.deleteCoordinate n a) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z))) /
        (Real.pi : ℂ)) =ᶠ[Filter.comap Int.natAbs Filter.atTop]
      (fun n => sourcePsiDeletedScalarMatrixEntry hp hp1 n m k a ψ c R) := by
    filter_upwards [hfar,hne] with n hnfar hkn
    let b : DeletedCoeff p n := Coeff.deleteCoordinateTo n a
    have hcoeb : (b : Coeff p) = Coeff.deleteCoordinate n a := rfl
    have hnroot : displacedRoots (b : Coeff p) n = (Real.pi : ℂ) * n := by
      rw [hcoeb]
      simp [displacedRoots,Coeff.deleteCoordinate_apply_same]
    have havoidn : ∀ z ∈ sphere c R,
        z ≠ displacedRoots (b : Coeff p) n := by
      intro z hz
      have hzR : ‖z-c‖ ≤ R := by
        simpa only [mem_sphere, dist_eq_norm] using le_of_eq hz
      have htri : ‖(Real.pi : ℂ) * n-c‖ ≤
          ‖(Real.pi : ℂ) * n-z‖ + ‖z-c‖ := by
        calc
          ‖(Real.pi : ℂ) * n-c‖ =
              ‖((Real.pi : ℂ) * n-z)+(z-c)‖ := by
                congr 1
                ring
          _ ≤ _ := norm_add_le _ _
      have hdenpos : 0 < ‖(Real.pi : ℂ) * n-z‖ := by linarith
      have hden : (Real.pi : ℂ) * n-z ≠ 0 :=
        norm_ne_zero_iff.mp (ne_of_gt hdenpos)
      rw [hnroot]
      exact (sub_ne_zero.mp hden).symm
    have hkroot : displacedRoots (b : Coeff p) k = displacedRoots a k := by
      rw [hcoeb]
      simp [displacedRoots,Coeff.deleteCoordinate_apply_other n k hkn]
    have havoidk : ∀ z ∈ sphere c R,
        z ≠ displacedRoots (b : Coeff p) k := by
      intro z hz
      rw [hkroot]
      exact (sub_ne_zero.mp (hk z hz)).symm
    have hder := deriv_sourcePsiDeletedEquationCoordinate_eq_gap_factor_circleIntegral
      hp hp1 n m k hkn b ψ hψ c R hR hcircle havoidn havoidk
    have hscaled := congrArg (fun w : ℂ => (Real.pi : ℂ) * w) hder
    rw [← circleIntegral.integral_const_mul] at hscaled
    dsimp only [sourcePsiDeletedScalarMatrixEntry]
    rw [dif_pos hkn]
    rw [hcoeb] at hscaled
    rw [← hscaled]
    exact mul_div_cancel_left₀ _ hπ
  change Tendsto (fun n : ℤ =>
      (∮ z in C(c,R),
        (Real.pi : ℂ) *
          (((displacedRoots (Coeff.deleteCoordinate n a) m-z) /
              (displacedRoots (Coeff.deleteCoordinate n a) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (Coeff.deleteCoordinate n a) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z))) /
        (Real.pi : ℂ))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a ψ c R)) at hconv
  exact hconv.congr' heq

/-- On any valid selected chart, a retained entry of the bounded
full-space Jacobian is the scalar derivative whose limit was just
computed. -/
theorem sourcePsiFullRootJacobian_retained_entry_eq_scalarMatrixEntry
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ j : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) j =
        sourcePsiEquationCoordinate hp hp1 n j
          (t.1 : Coeff p) t.2 (c j) (R j))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (hpair : (Coeff.deleteCoordinateTo n a,ψ) ∈ U)
    (hmn : m ≠ n) (hkn : k ≠ n) :
    (sourcePsiFullRootJacobian hp hp1 n c R
      (Coeff.deleteCoordinateTo n a) ψ (lp.single p k 1)) m =
      sourcePsiDeletedScalarMatrixEntry hp hp1 n m k a ψ (c m) (R m) := by
  rw [sourcePsiFullRootJacobian_retained_entry_eq_deriv
    hp hp1 n c R U hUopen hcoord hdiff
      (Coeff.deleteCoordinateTo n a) ψ hpair m k hmn hkn]
  simp only [sourcePsiDeletedScalarMatrixEntry, dif_pos hkn]

end NLS.ZakharovShabat
