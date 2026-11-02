import NLS.ZakharovShabat.SourceAbelianEndpointIntegrals
import NLS.ZakharovShabat.SourceActionChi
import NLS.ZakharovShabat.AppendixFUniformShortPiece
import NLS.ZakharovShabat.AppendixFSourceLimits
import NLS.ZakharovShabat.AppendixFSourceDomination
import NLS.ZakharovShabat.AppendixFOriginalCollapsed

/-!
# The actual midpoint-spoke decomposition in Appendix F

The integral of the actual differential along an integrable midpoint
spoke is the endpoint average minus the approached midpoint boundary
value. The latter is the short-piece term, with the full -i coefficient.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The corrected majorant proves integrability of each actual admissible spoke.
Only the half-gap estimate, normalized-gap smallness and a regular-factor bound are used. -/
theorem SourceCorollary10_6Data.appendixF_source_spoke_intervalIntegrable
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (ν : ℂ)
    (hz : ν-sourceStandardRootMidpoint hp hp1 ψ n ≠ 0)
    (ha : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      sourceStandardRootMidpoint hp hp1 ψ n‖ ≤
        ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖/2)
    (he : ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n /
      (2*(ν-sourceStandardRootMidpoint hp hp1 ψ n))‖ ≤ 1)
    (M : ℝ)
    (hχ : ∀ t ∈ Ioc (0:ℝ) 1, ‖sourceActionChi hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n))‖ ≤ M)
    (hpath : ∀ t ∈ Ioc (0:ℝ) 1,
      sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n) ∈
        sourceCanonicalRootDomain hp hp1 ψ) :
    let τ := sourceStandardRootMidpoint hp hp1 ψ n
    let Z := fun t : ℝ => τ+(t:ℂ)*(ν-τ)
    IntervalIntegrable (fun t : ℝ => -Complex.I*(ν-τ)*
      ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-Z t)/
        sourceStandardRoot hp hp1 ψ n (Z t))*sourceActionChi hp hp1 n ψ (Z t)) volume 0 1 := by
  dsimp only
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let z := ν-τ
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let e := ‖γ/(2*z)‖
  let g := fun t : ℝ => Real.sqrt (t+e)/Real.sqrt |t-e|
  have hg : Integrable g (volume.restrict (Ioc (0:ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (appendixF_positive_majorant_integrable e (norm_nonneg _) he)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  apply (hg.const_mul (‖z‖*M)).mono'
    (H.appendixF_spoke_integrand_measurable hW ψ hψ n ν hpath)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    (volume.restrict (Ioc (0:ℝ) 1)).ae_ne e] with t ht hne
  have hq := appendixF_standard_root_quotient_majorant τ γ
    (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    z hz ha t ht.1 hne
  have hgn : 0 ≤ g t := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  simp only [norm_mul,norm_neg,norm_I,one_mul]
  change ‖z‖*‖(_-(_+(t:ℂ)*z))/normalizedStandardRoot τ (γ^2) (τ+(t:ℂ)*z)‖*
    ‖sourceActionChi hp hp1 n ψ (τ+(t:ℂ)*z)‖ ≤ ‖z‖*M*g t
  calc
    _ ≤ (‖z‖*g t)*M := mul_le_mul
      (mul_le_mul_of_nonneg_left hq (norm_nonneg _)) (hχ t ht)
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) hgn)
    _ = _ := by ring

/-- Actual source analyticity supplies all integrability bounds on a tail of a
collapsing sequence; only admissibility of the selected spokes is assumed. -/
theorem SourceLemma10_10Data.appendixF_source_spoke_eventually_intervalIntegrable
    (H : SourceLemma10_10Data hp hp1 W) (hW : IsOpen W)
    {V : Set (CoeffPair p)} (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (ψ : ℕ → CoeffPair p) (hψ : Tendsto ψ atTop (𝓝 φ))
    (ν : ℂ) (hν : ν ∈ frontier (D n))
    (hpath : ∀ k, ∀ t ∈ Ioc (0:ℝ) 1,
      sourceStandardRootMidpoint hp hp1 (ψ k) n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 (ψ k) n) ∈
        sourceCanonicalRootDomain hp hp1 (ψ k)) :
    let τ := fun k => sourceStandardRootMidpoint hp hp1 (ψ k) n
    let Z := fun k (t : ℝ) => τ k+(t:ℂ)*(ν-τ k)
    ∀ᶠ k in atTop, IntervalIntegrable (fun t : ℝ => -Complex.I*(ν-τ k)*
      ((canonicalCriticalPoints hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n-Z k t)/
        sourceStandardRoot hp hp1 (ψ k) n (Z k t))*sourceActionChi hp hp1 n (ψ k) (Z k t)) volume 0 1 := by
  dsimp only
  let Q := H.previous.previous.previous
  let A := Q.roots.roots.symmetric
  let τ := fun χ : CoeffPair p => sourceStandardRootMidpoint hp hp1 χ n
  obtain ⟨U,hU,hφU,hUV,M,_,hbound⟩ := Q.appendixF_chi_uniform_closedDisk_bound hW hV hVW hD φ hφ n
  obtain ⟨a,R,hR,he⟩ := hD.discs n
  have hνnot : ν ∉ D n := by
    rw [he,frontier_ball _ hR.ne'] at hν
    rw [he]
    exact fun hz => (not_lt_of_ge (mem_sphere.mp hν).ge) (mem_ball.mp hz)
  have hzne (χ : CoeffPair p) (hχ : χ ∈ V) : ν-τ χ ≠ 0 := by
    intro heq
    exact hνnot (sub_eq_zero.mp heq ▸ hD.gap χ hχ n (sourcePeriodicMidpoint_mem_segment hp hp1 χ n))
  have hτ := (A.midpoint n φ (hVW hφ)).continuousAt.tendsto.comp hψ
  have hg := A.appendixF_gap_tendsto_zero φ (hVW hφ) n hgap ψ hψ
  have heps : Tendsto (fun k => ‖canonicalPeriodicGap hp hp1
      (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n / (2*(ν-τ (ψ k)))‖) atTop (𝓝 (0:ℝ)) := by
    simpa only [τ,sourceStandardRootMidpoint,Function.comp_def,Pi.div_apply,zero_div,norm_zero] using
      (hg.div (tendsto_const_nhds.mul (tendsto_const_nhds.sub hτ))
        (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (hzne φ hφ))).norm
  have hhalf := hψ.eventually (H.appendixF_eventually_half_gap hW φ (hVW hφ) n hgap)
  filter_upwards [hψ (hU.mem_nhds hφU),hhalf,
    heps.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with k hk hh hepsk
  apply Q.appendixF_source_spoke_intervalIntegrable hW (ψ k) (hVW (hUV hk)) n ν
    (hzne (ψ k) (hUV hk)) hh hepsk.le M ?_ (hpath k)
  intro t ht
  apply hbound (ψ k) hk
  have hτD := hD.gap (ψ k) (hUV hk) n (sourcePeriodicMidpoint_mem_segment hp hp1 (ψ k) n)
  have hνcl := frontier_subset_closure hν
  rw [he] at hτD
  rw [he,closure_ball _ hR.ne'] at hνcl ⊢
  have h := (convex_closedBall (a:ℂ) R).lineMap_mem (ball_subset_closedBall hτD) hνcl
    (Ioc_subset_Icc_self ht)
  simpa only [AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using h

/-- A straight ray from the midpoint stays on the terminal point's chosen gap side. -/
theorem appendixF_midpoint_spoke_mem_side (ψ : CoeffPair p) (n : ℤ)
    (ν : ℂ) (upper : Bool) (hν : ν ∈ sourceAbelianGapSide hp hp1 ψ n upper)
    (t : ℝ) (ht : 0 < t) :
    sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n) ∈
      sourceAbelianGapSide hp hp1 ψ n upper := by
  have hi : ((sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*
      (ν-sourceStandardRootMidpoint hp hp1 ψ n)-sourceStandardRootMidpoint hp hp1 ψ n) /
      sourceStandardRootHalfGap hp hp1 ψ n).im =
      t*((ν-sourceStandardRootMidpoint hp hp1 ψ n)/sourceStandardRootHalfGap hp hp1 ψ n).im := by
    rw [add_sub_cancel_left,mul_div_assoc,Complex.mul_im]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  cases upper
  · change ((ν-sourceStandardRootMidpoint hp hp1 ψ n)/sourceStandardRootHalfGap hp hp1 ψ n).im < 0 at hν
    change ((_-sourceStandardRootMidpoint hp hp1 ψ n)/sourceStandardRootHalfGap hp hp1 ψ n).im < 0
    rw [hi]
    exact mul_neg_of_pos_of_neg ht hν
  · change 0 < ((ν-sourceStandardRootMidpoint hp hp1 ψ n)/sourceStandardRootHalfGap hp hp1 ψ n).im at hν
    change 0 < ((_-sourceStandardRootMidpoint hp hp1 ψ n)/sourceStandardRootHalfGap hp hp1 ψ n).im
    rw [hi]
    exact mul_pos ht hν

/-- For a countable family of open gaps, one original boundary point supplies
admissible midpoint spokes and a well-defined side for each source. -/
theorem SourceIsolatingNeighborhoods.appendixF_exists_common_sided_spokes
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : ℕ → CoeffPair p) (hψ : ∀ k, ψ k ∈ V) (n : ℤ)
    (hgap : ∀ k, canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n ≠ 0) :
    ∃ ν ∈ frontier (D n), ∃ upper : ℕ → Bool, ∀ k,
      ν ∈ sourceCanonicalRootDomain hp hp1 (ψ k) ∧
      ν ∈ sourceAbelianGapSide hp hp1 (ψ k) n (upper k) ∧
      ∀ t ∈ Ioc (0:ℝ) 1,
        sourceStandardRootMidpoint hp hp1 (ψ k) n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 (ψ k) n) ∈
          sourceCanonicalRootDomain hp hp1 (ψ k) := by
  classical
  let τ := fun k => sourceStandardRootMidpoint hp hp1 (ψ k) n
  let g := fun k => sourceStandardRootHalfGap hp hp1 (ψ k) n
  obtain ⟨a,R,hR,he⟩ := hD.discs n
  obtain ⟨ν,hν,hlines⟩ := appendixF_exists_common_boundary_point (a:ℂ) R hR τ g
  have hgne k : g k ≠ 0 := div_ne_zero (hgap k) (by norm_num)
  have hi k : ((ν-τ k)/g k).im ≠ 0 := by
    intro him
    apply hlines k
    refine ⟨((ν-τ k)/g k).re,?_⟩
    have hre : (((ν-τ k)/g k).re:ℂ) = (ν-τ k)/g k := by
      simpa only [him,Complex.ofReal_zero,zero_mul,add_zero] using (Complex.re_add_im ((ν-τ k)/g k))
    dsimp only
    rw [Complex.real_smul,hre,div_mul_cancel₀ _ (hgne k),sub_add_cancel]
  have hsides k : ∃ upper : Bool, ν ∈ sourceAbelianGapSide hp hp1 (ψ k) n upper := by
    rcases (hi k).lt_or_gt with hneg | hpos
    · exact ⟨false,hneg⟩
    · exact ⟨true,hpos⟩
  choose upper hside using hsides
  refine ⟨ν,by simpa only [he,frontier_ball _ hR.ne'] using hν,upper,?_⟩
  intro k
  have hτD := hD.gap (ψ k) (hψ k) n (sourcePeriodicMidpoint_mem_segment hp hp1 (ψ k) n)
  rw [he] at hτD
  have hpath (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      τ k+(t:ℂ)*(ν-τ k) ∈ sourceCanonicalRootDomain hp hp1 (ψ k) := by
    have hcl : τ k+(t:ℂ)*(ν-τ k) ∈ closure (D n) := by
      rw [he,closure_ball _ hR.ne']
      have h := (convex_closedBall (a:ℂ) R).lineMap_mem (ball_subset_closedBall hτD)
        (sphere_subset_closedBall hν) (Ioc_subset_Icc_self ht)
      simpa only [τ,AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using h
    exact hD.closedCutDisk_subset_rootDomain (ψ k) (hψ k) n
      ⟨hcl,sourceAbelianGapSide_avoids_segment hp hp1 (ψ k) n (upper k) _
        (appendixF_midpoint_spoke_mem_side (ψ k) n ν (upper k) (hside k) t ht.1)⟩
  have hroot : ν ∈ sourceCanonicalRootDomain hp hp1 (ψ k) := by
    simpa only [Complex.ofReal_one,one_mul,add_sub_cancel] using hpath 1 (by norm_num)
  exact ⟨hroot,hside k,hpath⟩

/-- The actual improper endpoint average equals the midpoint-spoke integral plus its
one-sided short-piece boundary value, retaining the full differential coefficient. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_midpoint_integral_identity
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (ν : ℂ) (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (upper : Bool) (hside : ν ∈ sourceAbelianGapSide hp hp1 ψ n upper)
    (hpath : ∀ t ∈ Ioc (0:ℝ) 1,
      sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n) ∈
        sourceCanonicalRootDomain hp hp1 ψ)
    (hint : IntervalIntegrable (fun t : ℝ =>
      -Complex.I*(ν-sourceStandardRootMidpoint hp hp1 ψ n)*
        ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
          (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n)))/
            sourceStandardRoot hp hp1 ψ n
              (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n)))*
        sourceActionChi hp hp1 n ψ
          (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n))) volume 0 1) :
    sourceAbelianEndpointAverage hp hp1 n ν ψ = C.gapBoundary n ψ (Real.pi/2) upper+
      ∫ t in (0:ℝ)..1, -Complex.I*(ν-sourceStandardRootMidpoint hp hp1 ψ n)*
        ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
          (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n)))/
            sourceStandardRoot hp hp1 ψ n
              (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n)))*
        sourceActionChi hp hp1 n ψ
          (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let Z := fun t : ℝ => τ+(t:ℂ)*(ν-τ)
  let F := fun z : ℂ => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)
  have hZ : Continuous Z := by dsimp only [Z]; fun_prop
  obtain ⟨E⟩ := C.charts ψ hψ
  have hstart : Tendsto Z (𝓝[>] (0:ℝ)) (𝓝[sourceAbelianGapSide hp hp1 ψ n upper] τ) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Z,Complex.ofReal_zero,zero_mul,add_zero] using
        (hZ.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact appendixF_midpoint_spoke_mem_side ψ n ν upper hside t ht
  have hboundary := C.fullPrimitive_tendsto_gapBoundary n ψ hψ hgap (Real.pi/2)
    ⟨by positivity,by linarith [Real.pi_pos]⟩ upper
  simp only [Real.cos_pi_div_two,Complex.ofReal_zero,mul_zero,add_zero] at hboundary
  have hleft : Tendsto (F ∘ Z) (𝓝[>] (0:ℝ)) (𝓝 (C.gapBoundary n ψ (Real.pi/2) upper)) :=
    hboundary.comp hstart
  have hright : Tendsto (F ∘ Z) (𝓝[<] (1:ℝ)) (𝓝 (F ν)) := by
    have hz1 : Tendsto Z (𝓝[<] (1:ℝ)) (𝓝 ν) := by
      simpa only [Z,Complex.ofReal_one,one_mul,add_sub_cancel] using
        ((hZ.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (1:ℝ))))
    have hcomp := (sourceFullAbelianPrimitive_hasDerivAt E n ν hν).continuousAt.tendsto.comp
      hz1
    exact hcomp
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (F ∘ Z)
        (-Complex.I*(ν-τ)*((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-Z t)/
          sourceStandardRoot hp hp1 ψ n (Z t))*sourceActionChi hp hp1 n ψ (Z t)) t := by
    have hZ' : HasDerivAt Z (ν-τ) t := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using
        (Complex.ofRealCLM.hasDerivAt (x := t) |>.mul_const (ν-τ)).const_add τ
    have hf := (sourceFullAbelianPrimitive_hasDerivAt E n (Z t)
      (hpath t (Ioo_subset_Ioc_self ht))).scomp t hZ'
    rw [sourceCriticalRootRatio_eq_selectedFactor_mul_chi hp hp1 ψ n (Z t)
      (hpath t (Ioo_subset_Ioc_self ht))] at hf
    exact hf.congr_deriv (by simp only [smul_eq_mul]; ring)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0:ℝ) < 1) hderiv hint hleft hright
  rw [C.endpointAverage_eq ψ hψ n ν hν]
  change F ν = _
  change (∫ t in (0:ℝ)..1, -Complex.I*(ν-τ)*
    ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-Z t)/
      sourceStandardRoot hp hp1 ψ n (Z t))*sourceActionChi hp hp1 n ψ (Z t)) =
        F ν-C.gapBoundary n ψ (Real.pi/2) upper at hi
  rw [hi]
  ring

/-- The exact midpoint-spoke identity gives the vanishing remainder in corrected F.3.
The side may vary with the source; integrability of each spoke is explicit. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_midpoint_remainder_tendsto_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    {S : Set (CoeffPair p)} (H : SourceLemma10_2Data hp hp1 S)
    (φ : CoeffPair p) (hφS : φ ∈ S)
    (hφC : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (ψ : ℕ → CoeffPair p) (hψ : Tendsto ψ atTop (𝓝 φ))
    (hψC : ∀ k, ψ k ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hopen : ∀ k, canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n ≠ 0)
    (ν : ℂ) (hν : ∀ k, ν ∈ sourceCanonicalRootDomain hp hp1 (ψ k))
    (upper : ℕ → Bool) (hside : ∀ k, ν ∈ sourceAbelianGapSide hp hp1 (ψ k) n (upper k))
    (hpath : ∀ k, ∀ t ∈ Ioc (0:ℝ) 1,
      sourceStandardRootMidpoint hp hp1 (ψ k) n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 (ψ k) n) ∈
        sourceCanonicalRootDomain hp hp1 (ψ k)) :
    let τ := fun k => sourceStandardRootMidpoint hp hp1 (ψ k) n
    let Z := fun k (t : ℝ) => τ k+(t:ℂ)*(ν-τ k)
    let J := fun k (t : ℝ) => -Complex.I*(ν-τ k)*
      ((canonicalCriticalPoints hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n-Z k t)/
        sourceStandardRoot hp hp1 (ψ k) n (Z k t))*sourceActionChi hp hp1 n (ψ k) (Z k t)
    (∀ k, IntervalIntegrable (J k) volume 0 1) →
      Tendsto (fun k => sourceAbelianEndpointAverage hp hp1 n ν (ψ k)-∫ t in (0:ℝ)..1, J k t)
        atTop (𝓝 0) := by
  dsimp only
  intro hint
  have hg : Tendsto (fun k => ‖sourcePeriodicGapDisplacement hp hp1 (ψ k) n‖) atTop (𝓝 0) := by
    simpa only [sourcePeriodicGapDisplacement_apply,norm_zero] using
      (H.appendixF_gap_tendsto_zero φ hφS n hgap ψ hψ).norm
  have hlim := C.appendixF_gapBoundary_tendsto_zero_locally φ hφC ψ hψ n hg (fun _ => Real.pi/2) upper
  apply hlim.congr'
  filter_upwards [] with k
  rw [C.appendixF_midpoint_integral_identity (ψ k) (hψC k) n (hopen k) ν (hν k)
    (upper k) (hside k) (hpath k) (hint k)]
  ring

/-- The original source sequence has a common boundary point where its actual
improper endpoint averages converge, by the corrected spoke argument and short-piece identity. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_exists_endpointAverage_limit
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    {S V : Set (CoeffPair p)} (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S)
    (hV : IsOpen V) (hVS : V ⊆ S)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hφC : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (ψ : ℕ → CoeffPair p) (hψV : ∀ k, ψ k ∈ V) (hψ : Tendsto ψ atTop (𝓝 φ))
    (hopen : ∀ k, canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n ≠ 0) :
    ∃ ν ∈ frontier (D n),
      Tendsto (fun k => sourceAbelianEndpointAverage hp hp1 n ν (ψ k)) atTop
        (𝓝 (sourceAbelianEndpointAverage hp hp1 n ν φ)) := by
  obtain ⟨ν,hν,upper,hpaths⟩ := hD.appendixF_exists_common_sided_spokes ψ hψV n hopen
  refine ⟨ν,hν,?_⟩
  obtain ⟨U,hU,hφU,_,hlim⟩ := H.appendixF_source_spoke_integral_tendsto_locally hS hV hVS hD φ hφ n hgap
  have hint := H.appendixF_source_spoke_eventually_intervalIntegrable hS hV hVS hD φ hφ n hgap ψ hψ ν hν
    (fun k => (hpaths k).2.2)
  have hsmall : ∀ᶠ k in atTop, ψ k ∈ U ∧ ψ k ∈ ball C.discs.source.val C.discs.sourceRadius := by
    filter_upwards [hψ (hU.mem_nhds hφU),hψ (isOpen_ball.mem_nhds hφC)] with k hk hc
    exact ⟨hk,hc⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hint.and hsmall)
  let θ := fun k => ψ (k+N)
  have hθ : Tendsto θ atTop (𝓝 φ) := hψ.comp (tendsto_add_atTop_nat N)
  have hθC k : θ k ∈ ball C.discs.source.val C.discs.sourceRadius :=
    (hN (k+N) (Nat.le_add_left N k)).2.2
  have hθU k : θ k ∈ U := (hN (k+N) (Nat.le_add_left N k)).2.1
  have hi := hlim θ hθU hθ ν hν (fun k => (hpaths (k+N)).2.2)
  have hr := C.appendixF_midpoint_remainder_tendsto_zero H.previous.previous.previous.roots.roots.symmetric
    φ (hVS hφ) hφC n hgap θ hθ hθC (fun k => hopen (k+N)) ν (fun k => (hpaths (k+N)).1)
    (fun k => upper (k+N)) (fun k => (hpaths (k+N)).2.1) (fun k => (hpaths (k+N)).2.2)
    (fun k => (hN (k+N) (Nat.le_add_left N k)).1)
  have hνroot : ν ∈ sourceCanonicalRootDomain hp hp1 φ := by
    have hopenD : IsOpen (D n) := by
      obtain ⟨a,R,_,he⟩ := hD.discs n
      rw [he]
      exact isOpen_ball
    have hνnot : ν ∉ D n := by simpa only [hopenD.interior_eq] using hν.2
    exact hD.closedCutDisk_subset_rootDomain φ hφ n
      ⟨frontier_subset_closure hν,fun hs => hνnot (hD.gap φ hφ n hs)⟩
  let τ := fun χ : CoeffPair p => sourceStandardRootMidpoint hp hp1 χ n
  let J := fun (χ : CoeffPair p) (t : ℝ) => -Complex.I*(ν-τ χ)*
    ((canonicalCriticalPoints hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n-
      (τ χ+(t:ℂ)*(ν-τ χ)))/sourceStandardRoot hp hp1 χ n (τ χ+(t:ℂ)*(ν-τ χ)))*
    sourceActionChi hp hp1 n χ (τ χ+(t:ℂ)*(ν-τ χ))
  let L := ∫ t in (0:ℝ)..1, -Complex.I*(ν-τ φ)*sourceActionChi hp hp1 n φ (τ φ+(t:ℂ)*(ν-τ φ))
  change Tendsto (fun k => ∫ t in (0:ℝ)..1, J (θ k) t) atTop (𝓝 L) at hi
  change Tendsto (fun k => sourceAbelianEndpointAverage hp hp1 n ν (θ k)-∫ t in (0:ℝ)..1, J (θ k) t)
    atTop (𝓝 0) at hr
  have htotal : Tendsto (fun k => sourceAbelianEndpointAverage hp hp1 n ν (θ k)) atTop (𝓝 L) := by
    convert hi.add hr using 1
    · funext k
      ring
    · rw [add_zero]
  have heq : L = sourceAbelianEndpointAverage hp hp1 n ν φ := by
    dsimp only [L]
    rw [intervalIntegral.integral_const_mul]
    exact (C.appendixF_collapsed_original_segment H hVS hD φ hφ hφC n hgap ν hνroot
      (frontier_subset_closure hν)).symm
  rw [heq] at htotal
  exact (tendsto_add_atTop_iff_nat N).mp htotal

end NLS.ZakharovShabat
