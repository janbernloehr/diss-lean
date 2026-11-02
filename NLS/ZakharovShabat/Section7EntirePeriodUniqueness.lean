import NLS.ZakharovShabat.SourceEntireGapContourZeros
import NLS.ZakharovShabat.SourcePsiFullProductInterpolation
import NLS.ZakharovShabat.SourcePsiContourConjugation
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Entire numerator uniqueness from all gap periods

An entire numerator real on the real axis, with vanishing gap periods
and sub-sine growth on the expanding spectral circles, vanishes.
This interpolation argument imposes no placement condition on its roots.
-/
noncomputable section
open Set Filter Topology Metric Complex ComplexConjugate
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Sub-sine growth and one zero in every actual gap force an entire
function to vanish. No information about any other zeros is needed. -/
theorem section7_entire_zero_of_gap_zeros
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (hzeros : ∀ m : ℤ, ∃ z ∈ sourcePeriodicSegment hp hp1 φ m, F z = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k), ‖F z/(-2*sin z)‖ ≤ ε) :
    F = 0 := by
  classical
  choose ρ hρ using hzeros
  have hρlp := memℓp_sourcePeriodicSegment_samples hp hp1 φ ρ (fun m => (hρ m).1)
  let a : Coeff p := ⟨fun m => ρ m-(Real.pi : ℂ)*m,hρlp⟩
  have ha (m : ℤ) : displacedRoots a m = ρ m := by dsimp [a,displacedRoots]; ring
  have hgap : a ∈ sourcePeriodicGapRootSet hp hp1 φ := by
    intro m
    rw [ha]
    exact (hρ m).1
  have hinj : Function.Injective ρ := by
    intro i j he
    apply displacedRoots_injective_of_periodicGapRootSet hp hp1 a φ hφ hgap
    simpa only [ha] using he
  let G := entireSingleSpectralProduct ρ
  have hG := analyticOnNhd_entireSingleSpectralProduct hp ρ hρlp
  have hsimple := entireSingleSpectralProduct_simple_zeros_of_injective hp hp1 ρ hρlp hinj
  have hcommon (z : ℂ) (hz : G z = 0) : F z = 0 := by
    obtain ⟨m,hm⟩ := (entireSingleSpectralProduct_eq_zero_iff_of_lp hp ρ hρlp z).mp hz
    rw [← hm]
    exact (hρ m).2
  obtain ⟨K₀,hK₀⟩ := eventually_centralCircle_entireSingleSpectralProduct_ne_zero hp ρ hρlp
  let R : ℕ → ℝ := fun j => centralCircleRadius (j+K₀)
  have hR : Tendsto R atTop atTop := by
    have ht : Tendsto (fun j : ℕ => (j : ℝ)*Real.pi) atTop atTop :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos).congr'
        (Eventually.of_forall (fun j => by ring))
    have hbase : Tendsto centralCircleRadius atTop atTop :=
      ht.atTop_add tendsto_const_nhds
    exact hbase.comp (tendsto_add_atTop_nat K₀)
  apply NLS.ComplexAnalysis.entire_eq_zero_of_simple_zero_interpolation hF hG
    hcommon hsimple R hR (fun j z hz => hK₀ (j+K₀) (by omega) z hz)
  intro ε hε
  obtain ⟨KF,hKF⟩ := hsmall (ε/2) (by positivity)
  obtain ⟨KG,hKG⟩ := eventually_centralCircle_entireSingleSpectralProduct_div_free_close
    hp ρ hρlp (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [eventually_ge_atTop (max KF KG)] with j hj
  intro z hz
  have hfs := hKF (j+K₀) (by omega) z hz
  have hgs := hKG (j+K₀) (by omega) z hz
  have hd : -2*sin z ≠ (0 : ℂ) := by
    intro he
    rw [he,div_zero,zero_sub,norm_neg,norm_one] at hgs
    norm_num at hgs
  have hlow : (1 : ℝ)/2 ≤ ‖G z/(-2*sin z)‖ := by
    have ht := norm_add_le (G z/(-2*sin z)) (1-G z/(-2*sin z))
    rw [add_sub_cancel,norm_one,norm_sub_rev] at ht
    change ‖G z/(-2*sin z)-1‖ ≤ 1/2 at hgs
    linarith
  have hratio : F z/G z = (F z/(-2*sin z))/(G z/(-2*sin z)) := by
    exact (div_div_div_cancel_right₀ hd (F z) (G z)).symm
  rw [hratio,norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖G z/(-2*sin z)‖)).mpr
  nlinarith

/-- A real entire numerator with zero periods on every actual gap and
sub-sine growth is zero, without a prescribed root placement. -/
theorem section7_real_entire_zero_of_periods
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (hreal : ∀ x : ℝ, (F (x : ℂ)).im = 0)
    (c R : ℤ → ℝ)
    (hgeom : ∀ m : ℤ, 0 < R m ∧
      sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m : ℂ) (R m) ∧
      closedBall (c m : ℂ) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
      sphere (c m : ℂ) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (hperiod : ∀ m : ℤ, (∮ z in C((c m : ℂ),R m), F z/sourceCanonicalRoot hp hp1 φ z) = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k), ‖F z/(-2*sin z)‖ ≤ ε) :
    F = 0 := by
  apply section7_entire_zero_of_gap_zeros hp hp1 φ hφ F hF ?_ hsmall
  intro m
  rcases sourcePeriodicGap_eq_zero_or_open hp hp1 φ hφ m with hclosed | hopen
  · have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 φ m
    refine ⟨sourceStandardRootMidpoint hp hp1 φ m,hmid,?_⟩
    exact sourceEntireNumerator_zero_at_collapsedGap hp hp1 φ hφ m F hF
      hclosed (c m : ℂ) (R m) (hgeom m).1 ((hgeom m).2.1 hmid)
      (hgeom m).2.2.1 (hgeom m).2.2.2 (hperiod m)
  · obtain ⟨z,hz,hzero⟩ := exists_sourceEntireNumerator_zero_on_openGap
      hp hp1 φ hφ m F hF hreal hopen (c m) (R m) (hgeom m).1
      (hgeom m).2.1 (hgeom m).2.2.1 (hgeom m).2.2.2 (hperiod m)
    exact ⟨z,sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 φ m hz,hzero⟩

/-- Complex entire numerators are determined by all actual gap periods
in the sub-sine growth class. Reflection reduces to the real interpolation
argument, so neither real nor localized roots are assumed. -/
theorem section7_entire_zero_of_periods
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (c R : ℤ → ℝ)
    (hgeom : ∀ m : ℤ, 0 < R m ∧
      sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m : ℂ) (R m) ∧
      closedBall (c m : ℂ) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
      sphere (c m : ℂ) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (hperiod : ∀ m : ℤ, (∮ z in C((c m : ℂ),R m), F z/sourceCanonicalRoot hp hp1 φ z) = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k), ‖F z/(-2*sin z)‖ ≤ ε) :
    F = 0 := by
  have hprojection (a : ℂ) (ha : ‖a‖ = 1) :
      (fun z => a*F z+conj (a*F (conj z))) = 0 := by
    let A : ℂ → ℂ := fun z => a*F z
    let B : ℂ → ℂ := fun z => conj (A (conj z))
    have hA : AnalyticOnNhd ℂ A univ := analyticOnNhd_const.mul hF
    have hB : AnalyticOnNhd ℂ B univ := by
      apply analyticOnNhd_univ_iff_differentiable.mpr
      intro z
      simpa only [Function.comp_def,conj_conj] using
        (hA (conj z) (mem_univ _)).differentiableAt.conj_conj
    apply section7_real_entire_zero_of_periods hp hp1 φ hφ
      (fun z => A z+B z) (hA.add hB) ?_ c R hgeom ?_ ?_
    · intro x
      dsimp only [B]
      rw [conj_ofReal,add_im,conj_im]
      ring
    · intro m
      let Q := sourceCanonicalRoot hp hp1 φ
      have hAQ : CircleIntegrable (fun z => A z/Q z) (c m : ℂ) (R m) := by
        apply ContinuousOn.circleIntegrable (hgeom m).1.le
        exact (hA.continuousOn.mono (subset_univ _)).div
          ((sourceCanonicalRoot_analyticOnNhd hp hp1 φ).continuousOn.mono (hgeom m).2.2.2)
          (fun z hz => sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z ((hgeom m).2.2.2 hz))
      have hBQ : CircleIntegrable (fun z => B z/Q z) (c m : ℂ) (R m) := by
        apply ContinuousOn.circleIntegrable (hgeom m).1.le
        exact (hB.continuousOn.mono (subset_univ _)).div
          ((sourceCanonicalRoot_analyticOnNhd hp hp1 φ).continuousOn.mono (hgeom m).2.2.2)
          (fun z hz => sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z ((hgeom m).2.2.2 hz))
      have hJA : (∮ z in C((c m : ℂ),R m), A z/Q z) = 0 := by
        simp only [A,mul_div_assoc]
        rw [circleIntegral.integral_const_mul,hperiod m,mul_zero]
      have hJB : (∮ z in C((c m : ℂ),R m), B z/Q z) = 0 := by
        rw [NLS.ComplexAnalysis.circleIntegral_eq_conj_of_anti_conj
          (fun z => A z/Q z) (fun z => B z/Q z) (c m) (R m) (hgeom m).1 ?_,hJA,map_zero]
        intro z hz
        dsimp only [B,Q]
        rw [conj_conj,sourceCanonicalRoot_conj_of_realType hp hp1 φ hφ z ((hgeom m).2.2.2 hz)]
        simp only [map_div₀,div_neg]
      simp_rw [add_div]
      rw [circleIntegral.integral_add hAQ hBQ,hJA,hJB,add_zero]
    · intro ε hε
      obtain ⟨K,hK⟩ := hsmall (ε/2) (by positivity)
      refine ⟨K,?_⟩
      intro k hk z hz
      have hcz : conj z ∈ sphere (0 : ℂ) (centralCircleRadius k) := by
        simpa only [mem_sphere,dist_zero_right,norm_conj] using hz
      have hfirst : ‖A z/(-2*sin z)‖ ≤ ε/2 := by
        simpa only [A,mul_div_assoc,norm_mul,ha,one_mul] using hK k hk z hz
      have hsecond : ‖B z/(-2*sin z)‖ ≤ ε/2 := by
        have he : B z/(-2*sin z) = conj (A (conj z)/(-2*sin (conj z))) := by
          simp only [B,map_div₀,map_mul,map_neg,map_ofNat,sin_conj,conj_conj]
        rw [he,norm_conj]
        simpa only [A,mul_div_assoc,norm_mul,ha,one_mul] using hK k hk (conj z) hcz
      rw [add_div]
      exact (norm_add_le _ _).trans (by linarith)
  have hone := hprojection 1 norm_one
  have hi := hprojection I norm_I
  funext z
  have h1 := congrFun hone z
  have h2 := congrFun hi z
  simp only [one_mul,Pi.zero_apply] at h1
  simp only [map_mul,conj_I,Pi.zero_apply] at h2
  calc
    F z = (F z+conj (F (conj z)))/2-I*(I*F z+(-I)*conj (F (conj z)))/2 := by
      ring_nf
      rw [I_sq]
      ring
    _ = 0 := by rw [h1,h2]; ring

end NLS.ZakharovShabat
