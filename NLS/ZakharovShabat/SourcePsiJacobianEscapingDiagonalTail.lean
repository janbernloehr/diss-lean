import NLS.ZakharovShabat.SourcePsiQuotientUniformRootVariation
import NLS.ZakharovShabat.SourcePsiJacobianUniformDiagonalTail
import NLS.ZakharovShabat.SourcePsiGapProductCompact

/-!
# Uniform diagonal correction as the deleted index escapes

A fixed quotient majorant controls the undeleted root sequence. Uniform
holomorphic root variation contributes a scalar error that tends to
zero under deletion of a distant coordinate. Together with the fixed
midpoint and gap tails this makes every distant diagonal correction
small, eventually uniformly in the deleted index.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The diagonal scalar Jacobians on free tail circles tend to two
in the output tail, uniformly for all sufficiently distant deleted
copies of a fixed gap-contained root sequence. -/
theorem exists_sourcePsi_escaping_diagonal_scalarUniformTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ m : ℤ, K ≤ m.natAbs → ∀ hmn : m ≠ n,
          ‖deriv (fun t : ℂ =>
            sourcePsiDeletedEquationCoordinate hp hp1 n m
              (Coeff.deleteCoordinateTo n a +
                Coeff.deletedSingleCLM n m hmn t) φ
              ((Real.pi : ℂ)*m) (Real.pi/8)) 0-2‖ < ε := by
  obtain ⟨Kfree,c,R,hfree,hgeom,B,L,r,hL,hr,hvariation⟩ :=
    exists_sourcePsiQuotient_uniformRootVariation hp hp1 a φ hφ
  obtain ⟨W,hWopen,_,hrealW,hQanalytic⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hφW : φ ∈ W := hrealW hφ
  have hnear : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      Coeff.deleteCoordinate n a ∈ ball a r :=
    (Coeff.tendsto_deleteCoordinate_at_natAbs hp a).eventually
      (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hvarlim : Tendsto
      (fun n : ℤ => 4*L*‖Coeff.deleteCoordinate n a-a‖)
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 0) := by
    simpa using ((Coeff.tendsto_deleteCoordinate_at_natAbs hp a).sub_const a).norm.const_mul (4*L)
  intro ε hε
  obtain ⟨Kerr,herr⟩ :=
    exists_sourcePsi_diagonal_lp_uniform_error_tail hp hp1 φ B (ε/2) (half_pos hε)
  have hsmall : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      4*L*‖Coeff.deleteCoordinate n a-a‖ < ε/2 :=
    hvarlim.eventually (Iio_mem_nhds (half_pos hε))
  refine ⟨max (Kfree+1) Kerr,?_⟩
  filter_upwards [hnear,hsmall] with n hn hsmalln
  let aₙ : DeletedCoeff p n := Coeff.deleteCoordinateTo n a
  have hdel : (aₙ : Coeff p) n = 0 := aₙ.property
  have hroots (j : ℤ) : (displacedRoots (aₙ : Coeff p) j).im = 0 := by
    by_cases hj : j = n
    · subst j
      simp [displacedRoots,hdel]
    · have heq : displacedRoots (aₙ : Coeff p) j = displacedRoots a j := by
        simp [aₙ,displacedRoots,Coeff.deleteCoordinateTo,
          Coeff.deleteCoordinate_apply_other n j hj]
      rw [heq]
      exact sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ hφ j _ (ha j)
  intro m hm hmn
  have hmFree : Kfree < m.natAbs := by omega
  have hmErr : Kerr ≤ m.natAbs := by omega
  obtain ⟨hc,hR⟩ := hfree m hmFree
  have hgeomM := hgeom m
  have hseg : sourcePeriodicSegment hp hp1 φ m ⊆
      ball ((Real.pi : ℂ)*m) (Real.pi/8) := by
    simpa only [hc,hR] using hgeomM.2.1
  have hdom : closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 φ m := by
    simpa only [hc,hR] using hgeomM.2.2.1
  have hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 φ := by
    simpa only [hc,hR] using hgeomM.2.2.2
  have hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (aₙ : Coeff p) φ z))
      (closedBall ((Real.pi : ℂ)*m) (Real.pi/8)) :=
    analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
      hp hp1 n m hmn.symm aₙ φ W hφW (hQanalytic m).2
        (Real.pi/8) (by nlinarith [Real.pi_pos]) hdom
  have havoidn : ∀ z ∈ sphere ((Real.pi : ℂ)*m) (Real.pi/8),
      z ≠ displacedRoots (aₙ : Coeff p) n := by
    intro z hz
    rw [show displacedRoots (aₙ : Coeff p) n =
      (Real.pi : ℂ)*n by simp [displacedRoots,hdel]]
    exact freeCircle_point_ne_freeCenter m n (Real.pi/8)
      (by positivity) (by nlinarith [Real.pi_pos]) z hz
  let E : ℝ := ‖B m‖+L*‖Coeff.deleteCoordinate n a-a‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let Bm : Coeff p := lp.single p m (E : ℂ)
  have hBm : ‖Bm m‖ = E := by
    simp [Bm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE]
  have hQ : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((aₙ : Coeff p),φ))-1‖ ≤ ‖Bm m‖ := by
    intro z hz
    rw [hBm]
    exact hvariation (Coeff.deleteCoordinate n a) hn m z
      (by simpa only [hc,hR] using hz)
  have hcenter : ((Real.pi*(m:ℝ) : ℝ) : ℂ) = (Real.pi : ℂ)*m := by
    push_cast
    rfl
  have hbound := norm_sourcePsi_diagonalJacobian_sub_two_le_all_real_gaps
    hp hp1 φ hφ n m hmn aₙ hroots
      (Real.pi*(m:ℝ)) (Real.pi/8) (by positivity)
      (by simpa only [hcenter] using hseg)
      (by simpa only [hcenter] using hdom)
      (by simpa only [hcenter] using hcircle)
      (by simpa only [hcenter] using havoidn)
      (by simpa only [hcenter] using hreg)
      Bm (herr m hmErr).1 (by simpa only [hcenter] using hQ)
  rw [hBm] at hbound
  have hbaseerr := (herr m hmErr).2 n hmn
  have hfinal :
      4*E + 4*(‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 φ m‖/2) /
          ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ < ε := by
    dsimp only [E]
    linarith
  simpa only [hcenter,aₙ] using hbound.trans_lt hfinal

end NLS.ZakharovShabat
