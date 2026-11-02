import NLS.ZakharovShabat.Section7EntirePeriodUniqueness
import NLS.ZakharovShabat.SourceSection7PsiProduct
import NLS.ZakharovShabat.SourcePsiRealNormalization
import NLS.ZakharovShabat.SourcePsiGlobalContourFamily
import NLS.ZakharovShabat.SourcePsiPiecewiseContour

/-! # Unrestricted period uniqueness of the Section 7 psi products

Arbitrary complex lp root displacements give sub-sine growth for the
deleted product. Its full gap-period family therefore determines the
entire function, without assuming reality or assigned-disc root placement.
-/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every deleted lp product has sub-sine growth on the expanding
half-integer circles, with no root placement assumption. -/
theorem section7_psi_sub_sine_growth
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
        ‖sourcePsiCandidate n (z,a)/(-2*sin z)‖ ≤ ε := by
  obtain ⟨K₀,hK₀⟩ := eventually_centralCircle_entireSingleSpectralProduct_div_free_close
    hp (displacedRoots a) (memℓp_displacedRoots a) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨K₁,hK₁⟩ := exists_nat_gt ((‖displacedRoots a n‖+2/ε)/Real.pi)
  refine ⟨max K₀ K₁,?_⟩
  intro k hk z hz
  have hj : ‖jointSingleSpectralProduct (z,a)/(-2*sin z)‖ ≤ 2 := by
    have hb := hK₀ k ((le_max_left _ _).trans hk) z hz
    have ht := norm_add_le (jointSingleSpectralProduct (z,a)/(-2*sin z)-1) (1 : ℂ)
    rw [sub_add_cancel,norm_one] at ht
    change ‖jointSingleSpectralProduct (z,a)/(-2*sin z)-1‖ ≤ 1 at hb
    linarith
  have hnorm : ‖z‖ = centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hK : ‖displacedRoots a n‖+2/ε < (K₁ : ℝ)*Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK₁)
  have hkk : (K₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_max_right K₀ K₁).trans hk
  have hdist : 2/ε ≤ ‖displacedRoots a n-z‖ := by
    have ht := norm_sub_le (displacedRoots a n) (displacedRoots a n-z)
    rw [sub_sub_cancel] at ht
    unfold centralCircleRadius at hnorm
    nlinarith [Real.pi_pos]
  have hdistpos : 0 < ‖displacedRoots a n-z‖ :=
    (div_pos (by norm_num) hε).trans_le hdist
  have hfactor : (displacedRoots a n-z)*sourcePsiCandidate n (z,a) =
      -jointSingleSpectralProduct (z,a) := by
    rw [jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)]
    dsimp only [sourcePsiCandidate]
    ring
  have hprod : ‖displacedRoots a n-z‖*‖sourcePsiCandidate n (z,a)/(-2*sin z)‖ ≤ 2 := by
    rw [← norm_mul,← mul_div_assoc,hfactor,neg_div,norm_neg]
    exact hj
  have hbudget : 2 ≤ ε*‖displacedRoots a n-z‖ := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hdist
  apply le_of_mul_le_mul_left (a := ‖displacedRoots a n-z‖) _ hdistpos
  nlinarith

/-- Equal periods determine the entire deleted product, even for
arbitrary complex lp root sequences with no assigned-disc placement. -/
theorem section7_psi_eq_of_periods
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a b : Coeff p)
    (c R : ℤ → ℝ)
    (hgeom : ∀ m : ℤ, 0 < R m ∧
      sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m : ℂ) (R m) ∧
      closedBall (c m : ℂ) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
      sphere (c m : ℂ) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (hperiod : ∀ m : ℤ,
      (∮ z in C((c m : ℂ),R m), sourcePsiCandidate n (z,a)/sourceCanonicalRoot hp hp1 φ z) =
      (∮ z in C((c m : ℂ),R m), sourcePsiCandidate n (z,b)/sourceCanonicalRoot hp hp1 φ z)) :
    (fun z => sourcePsiCandidate n (z,a)) = (fun z => sourcePsiCandidate n (z,b)) := by
  let A : ℂ → ℂ := fun z => sourcePsiCandidate n (z,a)
  let B : ℂ → ℂ := fun z => sourcePsiCandidate n (z,b)
  have hA : AnalyticOnNhd ℂ A univ := by
    intro z _
    exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,a) (mem_univ _)).comp
      (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  have hB : AnalyticOnNhd ℂ B univ := by
    intro z _
    exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,b) (mem_univ _)).comp
      (f := fun w : ℂ => (w,b)) (analyticAt_id.prod analyticAt_const)
  have hz := section7_entire_zero_of_periods hp hp1 φ hφ (fun z => A z-B z)
    (hA.sub hB) c R hgeom ?_ ?_
  · funext z
    exact sub_eq_zero.mp (congrFun hz z)
  · intro m
    have hint (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ) :
        CircleIntegrable (fun z => F z/sourceCanonicalRoot hp hp1 φ z) (c m : ℂ) (R m) := by
      apply ContinuousOn.circleIntegrable (hgeom m).1.le
      exact (hF.continuousOn.mono (subset_univ _)).div
        ((sourceCanonicalRoot_analyticOnNhd hp hp1 φ).continuousOn.mono (hgeom m).2.2.2)
        (fun z hz => sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z ((hgeom m).2.2.2 hz))
    simp_rw [sub_div]
    rw [circleIntegral.integral_sub (hint A hA) (hint B hB),hperiod m,sub_self]
  · intro ε hε
    obtain ⟨KA,hKA⟩ := section7_psi_sub_sine_growth hp hp1 n a (ε/2) (by positivity)
    obtain ⟨KB,hKB⟩ := section7_psi_sub_sine_growth hp hp1 n b (ε/2) (by positivity)
    refine ⟨max KA KB,?_⟩
    intro k hk z hz
    rw [sub_div]
    exact (norm_sub_le _ _).trans (by
      have ha := hKA k ((le_max_left _ _).trans hk) z hz
      have hb := hKB k ((le_max_right _ _).trans hk) z hz
      change ‖A z/(-2*sin z)‖ ≤ ε/2 at ha
      change ‖B z/(-2*sin z)‖ ≤ ε/2 at hb
      linarith)

/-- Unrestricted complex root data with the normalized Kronecker periods
produce the canonical psi function at every real source. -/
theorem section7_psi_eq_gapRoot_of_normalized_periods
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (n : ℤ) (a : Coeff p) (c R : ℤ → ℝ)
    (hgeom : ∀ m : ℤ, 0 < R m ∧
      sourcePeriodicSegment hp hp1 φ.val m ⊆ ball (c m : ℂ) (R m) ∧
      closedBall (c m : ℂ) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val m ∧
      sphere (c m : ℂ) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ.val)
    (hperiod : ∀ m : ℤ, sourcePsiContour hp hp1 n a φ.val (c m : ℂ) (R m) =
      if m = n then 1 else 0) :
    (fun z => sourcePsiCandidate n (z,a)) =
      (fun z => sourcePsiCandidate n (z,(sourcePsiGapRoot hp hp1 n φ : Coeff p))) := by
  apply section7_psi_eq_of_periods hp hp1 φ.val φ.property n a _ c R hgeom
  intro m
  have hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ.val (fun m => (c m : ℂ)) R :=
    ⟨fun m => ofReal_im (c m),hgeom⟩
  have he := (hperiod m).trans
    (sourcePsiGapRoot_contour_orthogonality hp hp1 n φ _ R hfamily m).symm
  have hπ : (2*Real.pi : ℂ)⁻¹ ≠ 0 := inv_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
  exact mul_left_cancel₀ hπ he

/-- The corrected literal product and exact periods characterize one
entire function on one constructed contour family before every n.
The competing products may have arbitrary complex lp root displacements. -/
theorem section7_existsUnique_psi_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) :
    ∃ c R : ℤ → ℝ,
      (∀ m : ℤ, 0 < R m ∧
        sourcePeriodicSegment hp hp1 φ.val m ⊆ ball (c m : ℂ) (R m) ∧
        closedBall (c m : ℂ) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val m ∧
        sphere (c m : ℂ) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ.val) ∧
      ∀ n : ℤ, ∃! F : ℂ → ℂ,
        (∃ a : Coeff p, ∀ z : ℂ, Tendsto (fun N : ℕ =>
          (-2/singleSpectralDenominator n)*
            ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
              (displacedRoots a m-z)/singleSpectralDenominator m)
          atTop (𝓝 (F z))) ∧
        ∀ m : ℤ, (2*Real.pi : ℂ)⁻¹*
          (∮ z in C((c m : ℂ),R m), F z/sourceCanonicalRoot hp hp1 φ.val z) =
            if m = n then 1 else 0 := by
  obtain ⟨_,V,_,hφV,c₀,R,hc,_,hG⟩ :=
    exists_local_sourcePsi_allGap_realCenteredContourFamily hp hp1 φ.val φ.property
  let c : ℤ → ℝ := fun m => (c₀ m).re
  have hcoe (m : ℤ) : (c m : ℂ) = c₀ m := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using (hc m).symm
  have hgeom : ∀ m : ℤ, 0 < R m ∧
      sourcePeriodicSegment hp hp1 φ.val m ⊆ ball (c m : ℂ) (R m) ∧
      closedBall (c m : ℂ) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val m ∧
      sphere (c m : ℂ) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ.val := by
    intro m
    simpa only [hcoe] using hG φ.val hφV m
  refine ⟨c,R,hgeom,?_⟩
  intro n
  let b : Coeff p := sourcePsiGapRoot hp hp1 n φ
  refine ⟨(fun z => sourcePsiCandidate n (z,b)),?_,?_⟩
  · refine ⟨⟨b,sourceSection7_psi_product hp hp1 n b⟩,?_⟩
    intro m
    exact sourcePsiGapRoot_contour_orthogonality hp hp1 n φ (fun m => (c m : ℂ)) R
      ⟨fun m => ofReal_im (c m),hgeom⟩ m
  · intro F hF
    obtain ⟨a,ha⟩ := hF.1
    have heq : F = fun z => sourcePsiCandidate n (z,a) := by
      funext z
      exact tendsto_nhds_unique (ha z) (sourceSection7_psi_product hp hp1 n a z)
    rw [heq]
    apply section7_psi_eq_gapRoot_of_normalized_periods hp hp1 φ n a c R hgeom
    intro m
    simpa only [heq,sourcePsiContour,sourcePsiContourIntegrandJoint] using hF.2 m

/-- The characterization uses any admissible original winding-one
piecewise C1 circuits, retaining their exact normalized periods. -/
theorem section7_psi_eq_gapRoot_of_original_circuit_periods
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D C) (hφ : φ.val ∈ V)
    (n : ℤ) (a : Coeff p) (Γ : ℤ → NLS.ComplexAnalysis.PiecewiseC1Loop)
    (hΓ : ∀ m : ℤ, (Γ m).Inside (D m \ sourcePeriodicSegment hp hp1 φ.val m))
    (hw : ∀ m : ℤ, (Γ m).windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m) = 1)
    (hperiod : ∀ m : ℤ, sourcePsiCircuit hp hp1 n a φ.val (Γ m) =
      if m = n then 1 else 0) :
    (fun z => sourcePsiCandidate n (z,a)) =
      (fun z => sourcePsiCandidate n (z,(sourcePsiGapRoot hp hp1 n φ : Coeff p))) := by
  classical
  choose c R hR hdisc using hD.discs
  let P (m : ℤ) := hD.periodCircle φ.val hφ m (c m) (R m) (hR m) (hdisc m)
  have hgeom : ∀ m : ℤ, 0 < R m ∧
      sourcePeriodicSegment hp hp1 φ.val m ⊆ ball (c m : ℂ) (R m) ∧
      closedBall (c m : ℂ) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val m ∧
      sphere (c m : ℂ) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ.val := by
    intro m
    exact ⟨(P m).radius_pos,(P m).gap,(P m).closedBall_subset_omittedDomain,
      (P m).sphere_subset_rootDomain⟩
  apply section7_psi_eq_gapRoot_of_normalized_periods hp hp1 φ n a c R hgeom
  intro m
  have hinside : (Γ m).Inside (ball ((P m).center : ℂ) (P m).radius \
      sourcePeriodicSegment hp hp1 φ.val m) := by
    change (Γ m).Inside (ball (c m : ℂ) (R m) \ sourcePeriodicSegment hp hp1 φ.val m)
    rw [← hdisc m]
    exact hΓ m
  have he := (P m).psiCircuit_eq_mul_winding n a (Γ m) hinside
  rw [hw m,mul_one] at he
  exact he.symm.trans (hperiod m)

end NLS.ZakharovShabat
