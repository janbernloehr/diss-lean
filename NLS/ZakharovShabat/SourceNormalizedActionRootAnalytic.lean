import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Banach analyticity of all normalized-action roots on one domain

The rationalized contour integrand gives a genuine Banach power series,
including at collapsed gaps. Fixed tail circles and a finite head
intersection give one source neighborhood for every action factor.
The principal square root is then analytic on the positive-real-part domain.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem analyticAt_sourceNormalizedActionCircleCandidate_of_jointAnalytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (ψ : CoeffPair p)
    (hcircle : ∀ z ∈ sphere c R,
      AnalyticAt ℂ (sourceNormalizedActionCircleIntegrandJoint hp hp1 n) (z,ψ)) :
    AnalyticAt ℂ (sourceNormalizedActionCircleCandidate hp hp1 n c R) ψ := by
  let F := sourceNormalizedActionCircleIntegrandJoint hp hp1 n
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hD : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  obtain ⟨V,hV,hψV,_,_,hbound⟩ :=
    exists_uniform_joint_fderiv_bound_on_circle F D hD hF c R ψ hcircle
  have hA := analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF c R hR.le hV
    (fun χ hχ z hz => (hbound z hz χ hχ).1)
  exact analyticAt_const.mul (hA ψ hψV)

theorem exists_local_sourceNormalizedAction_analytic_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      AnalyticOnNhd ℂ (sourceNormalizedActionComplexExtension hp hp1 n) V ∧
      ∀ ψ ∈ V, sourceComplexAction hp hp1 n ψ =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  obtain ⟨U,hU,hφU,c,R,hR,hgeom,_,heq⟩ :=
    exists_local_sourceNormalizedActionCircleCandidate_eq_realExtension hp hp1 φ hreal n
  have hA : AnalyticAt ℂ (sourceNormalizedActionCircleCandidate hp hp1 n c R) φ :=
    analyticAt_sourceNormalizedActionCircleCandidate_of_jointAnalytic hp hp1 n c R hR φ
      (fun z hz => analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_realType hp hp1 n φ hreal z
        (sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n c R
          (hgeom φ hφU).1 (hgeom φ hφU).2 hz))
  let A := {ψ | AnalyticAt ℂ (sourceNormalizedActionCircleCandidate hp hp1 n c R) ψ}
  refine ⟨U ∩ A,hU.inter (isOpen_analyticAt _ _),⟨hφU,hA⟩,?_,?_⟩
  · intro ψ hψ
    apply hψ.2.congr
    filter_upwards [hU.mem_nhds hψ.1] with χ hχ
    exact (heq χ hχ).2.2
  · intro ψ hψ
    exact (heq ψ hψ.1).1.trans
      (congrArg ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * ·) (heq ψ hψ.1).2.2)

/-- A single open neighborhood carries analytic action factors and
exact action factorization at every index, including collapsed gaps. -/
theorem exists_local_sourceNormalizedAction_allIndices_analytic_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (sourceNormalizedActionComplexExtension hp hp1 n) V) ∧
      ∀ ψ ∈ V, ∀ n : ℤ, sourceComplexAction hp hp1 n ψ =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  classical
  obtain ⟨Kc,Vc,hVc,hφc,hjoint⟩ :=
    exists_local_source_distantNormalizedActionCircleIntegrand_jointAnalytic hp hp1 φ hreal
  obtain ⟨Ka,r,hr,hagree⟩ := exists_local_sourceNormalizedAction_uniform_circle_complex_agreement hp hp1 φ hreal
  let K := max Kc Ka
  have hlocal (n : ℤ) := exists_local_sourceNormalizedAction_analytic_factor hp hp1 φ hreal n
  choose Un hUn hφUn hAn hFn using hlocal
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let H := ⋂ n ∈ S, Un n
  have hH : IsOpen H := isOpen_biInter_finset (fun n _ => hUn n)
  have hφH : φ ∈ H := by simp only [H,mem_iInter]; exact fun n _ => hφUn n
  let V := (Vc ∩ ball φ r) ∩ H
  have hV : IsOpen V := (hVc.inter isOpen_ball).inter hH
  have hhead (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hn : ¬K < n.natAbs) : ψ ∈ Un n := by
    have hnS : n ∈ S := by simp only [S,Finset.mem_Icc]; omega
    exact mem_iInter.mp (mem_iInter.mp hψ.2 n) hnS
  refine ⟨V,hV,⟨⟨hφc,mem_ball_self hr⟩,hφH⟩,?_,?_⟩
  · intro n ψ hψ
    by_cases hn : K < n.natAbs
    · have hnC : Kc < n.natAbs := (le_max_left Kc Ka).trans_lt hn
      have hnA : Ka ≤ n.natAbs := (le_max_right Kc Ka).trans hn.le
      have hA := analyticAt_sourceNormalizedActionCircleCandidate_of_jointAnalytic hp hp1 n
        ((Real.pi:ℂ)*n) (Real.pi/8) (by positivity) ψ (hjoint ψ hψ.1.1 n hnC)
      apply hA.congr
      filter_upwards [hV.mem_nhds hψ] with χ hχ
      exact (hagree χ hχ.1.2 n hnA).1
    · exact hAn n ψ (hhead ψ hψ n hn)
  · intro ψ hψ n
    by_cases hn : K < n.natAbs
    · have hd := hagree ψ hψ.1.2 n ((le_max_right Kc Ka).trans hn.le)
      exact hd.2.trans (congrArg ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * ·) hd.1)
    · exact hFn n ψ (hhead ψ hψ n hn)

/-- The principal roots are analytic in the full complex Banach source
space on one neighborhood, with exact squares and action factorization. -/
theorem exists_local_sourceNormalizedActionRoot_allIndices_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (sourceNormalizedActionRoot hp hp1 n) V) ∧
      ∀ ψ ∈ V, ∀ n : ℤ,
        (sourceNormalizedActionRoot hp hp1 n ψ)^2 = 4*sourceNormalizedActionComplexExtension hp hp1 n ψ ∧
        sourceComplexAction hp hp1 n ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨Vr,hVr,hφr,c,hc,hpos,_,hsq⟩ :=
    exists_local_sourceNormalizedActionRoot_allCoordinates (q := p) hp hp1 hp1 hp hhalf φ hreal
  obtain ⟨Va,hVa,hφa,hA,hfactor⟩ :=
    exists_local_sourceNormalizedAction_allIndices_analytic_factor hp hp1 φ hreal
  refine ⟨Vr ∩ Va,hVr.inter hVa,⟨hφr,hφa⟩,?_,?_⟩
  · intro n ψ hψ
    have hslit : 4*sourceNormalizedActionComplexExtension hp hp1 n ψ ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      exact Or.inl (lt_of_lt_of_le hc (hpos ψ hψ.1 n))
    exact (Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds hslit)).comp
      (f := fun χ : CoeffPair p => 4*sourceNormalizedActionComplexExtension hp hp1 n χ)
      (analyticAt_const.mul (hA n ψ hψ.2))
  · intro ψ hψ n
    exact ⟨(hsq ψ hψ.1 n).2,hfactor ψ hψ.2 n⟩

end NLS.ZakharovShabat
