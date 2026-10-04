import NLS.ComplexAnalysis.ParametricCosineMeanLocal
import NLS.ZakharovShabat.SourceAbelianMomentEvenNumeratorJoint
import NLS.ZakharovShabat.SourceAbelianMomentRealGapIntegral

/-! # Analytic cosine means of the actual source gaps

Only the canonical midpoint and squared half-gap enter analyticity.
A real-centered isolating contour supplies the compact disc needed by
the square-descent construction, including when the selected gap is closed.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The regular cosine integral along the actual canonical source gap. -/
def sourceGapCosineMean (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ)
    (g : ℂ × CoeffPair p → ℂ) (ψ : CoeffPair p) : ℂ :=
  parametricCosineMean g (fun χ => sourceStandardRootMidpoint hp hp1 χ k)
    (sourceStandardRootHalfGap hp hp1 ψ k,ψ)

/-- Source analyticity of the mean needs no nonzero-gap hypothesis and
no analytic choice of the two periodic endpoints. -/
theorem analyticAt_sourceGapCosineMean_of_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ)
    (g : ℂ × CoeffPair p → ℂ) (D : Set (ℂ × CoeffPair p)) (hD : IsOpen D)
    (hg : AnalyticOnNhd ℂ g D) (φ : realTypeSourceSubmodule p)
    (S : ℝ) (hS : ‖sourceStandardRootHalfGap hp hp1 φ.val k‖ < S)
    (hdisc : ∀ z ∈ closedBall (sourceStandardRootMidpoint hp hp1 φ.val k) S, (z,φ.val) ∈ D) :
    AnalyticAt ℂ (sourceGapCosineMean hp hp1 k g) φ.val := by
  obtain ⟨V,_,_,hreal,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hhalf : AnalyticAt ℂ (fun ψ => (sourceStandardRootHalfGap hp hp1 ψ k)^2) φ.val := by
    have he : (fun ψ => (sourceStandardRootHalfGap hp hp1 ψ k)^2) =
        fun ψ => (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2/4 := by
      funext ψ
      unfold sourceStandardRootHalfGap
      ring
    rw [he]
    exact (hcoord φ.val (hreal φ.property) k).2.div_const
  exact analyticAt_parametricCosineMean_of_analytic_square g
    (fun ψ => sourceStandardRootMidpoint hp hp1 ψ k)
    (fun ψ => sourceStandardRootHalfGap hp hp1 ψ k) D hD hg φ.val
    (hcoord φ.val (hreal φ.property) k).1 hhalf S hS hdisc

/-- A real-centered enclosing circle provides enough room for square
descent inside the omitted-root domain. -/
theorem analyticAt_sourceGapCosineMean_of_realCenteredCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ)
    (g : ℂ × CoeffPair p → ℂ) (U : Set (CoeffPair p))
    (hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (hg : AnalyticOnNhd ℂ g (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ U)
    (c : ℂ) (R : ℝ) (hc : c.im = 0)
    (hseg : sourcePeriodicSegment hp hp1 φ.val k ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val k) :
    AnalyticAt ℂ (sourceGapCosineMean hp hp1 k g) φ.val := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k
  have hc' : (c.re:ℂ) = c := Complex.ext rfl (by simpa only [ofReal_im] using hc.symm)
  obtain ⟨S,hS,hnest⟩ := exists_sourceStandardRoot_innerMidpointDisc_of_realCenteredCircle
    hp hp1 φ.val φ.property k c.re R (by simpa only [hc'] using hseg)
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) k
  have hl : (l.re:ℂ) = l := Complex.ext rfl (by simpa only [ofReal_im] using him.1.symm)
  have hr : (r.re:ℂ) = r := Complex.ext rfl (by simpa only [ofReal_im] using him.2.symm)
  have ht : (((l.re+r.re)/2:ℝ):ℂ) = sourceStandardRootMidpoint hp hp1 φ.val k := by
    push_cast
    rw [hl,hr]
    rfl
  have hδ := sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property k
  have hd : 0 ≤ (r.re-l.re)/2 := by
    have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)).2.1 k)
    dsimp only [l,r]
    linarith
  have hnorm : ‖sourceStandardRootHalfGap hp hp1 φ.val k‖ < S := by
    rw [hδ,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd]
    exact hS
  apply analyticAt_sourceGapCosineMean_of_disc hp hp1 k g _ hD hg φ S hnorm
  intro z hz
  refine ⟨hφ,hother (ball_subset_closedBall ?_)⟩
  change closedBall (((l.re+r.re)/2:ℝ):ℂ) S ⊆ ball (c.re:ℂ) R at hnest
  rw [ht,hc'] at hnest
  exact hnest hz

/-- The actual normalized even-moment cosine numerator has an analytic
mean near every real source, including every collapsed selected gap. -/
theorem SourcePsiNormalizedComplexExtension.analyticAt_evenMomentCosineMean
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (A : SourceAbelianMomentAtlas hp hp1 W s) (U : Set (CoeffPair p)) (hUV : U ⊆ V)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ U) (n k : ℤ) (m : ℕ)
    (hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 k)
      (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (hS : AnalyticOnNhd ℂ (sourceFullAbelianSquare hp hp1 W k)
      (sourceStandardRootOmittedJointDomain hp hp1 U k)) :
    AnalyticAt ℂ (sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
      sourceAbelianMomentEvenNumerator hp hp1 W n k m (s n t.2 : Coeff p) t.2 t.1)) φ.val := by
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  have hfamily := (A.localChart φ₀).family φ.val (mem_ball_self (A.localChart φ₀).radius_pos)
  exact analyticAt_sourceGapCosineMean_of_realCenteredCircle hp hp1 k _ U hD
    (hs.evenNumerator_joint_analytic W U hUV n k m hO hS) φ hφ
    ((A.localChart φ₀).center k) ((A.localChart φ₀).contourRadius k)
    (hfamily.1 k) (hfamily.2 k).2.1 (hfamily.2 k).2.2.1

end NLS.ZakharovShabat
