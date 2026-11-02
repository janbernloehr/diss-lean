import NLS.ZakharovShabat.AppendixFEndpointAnalytic
import NLS.ZakharovShabat.AppendixFOpenGapSpokes
import NLS.ZakharovShabat.AppendixFSourceSpokes
import NLS.ZakharovShabat.SourceAbelianEndpointIntegrals
import NLS.ZakharovShabat.SourceActionChi
import Mathlib.Analysis.Convex.Hull

/-!
# Actual source endpoint integrals in the open-gap argument of Appendix F

Unordered analytic endpoint branches give the actual standard root.
The integrable normalized-root parameter integral computes the literal
improper endpoint integral, retaining its full -i displacement coefficient.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W S V : Set (CoeffPair p)}
variable {D : ℤ → Set ℂ} {c : ℝ}

/-- Unordered endpoint branches determine the literal source standard root. -/
theorem appendixF_source_root_eq_of_endpoint_pair (ψ : CoeffPair p) (n : ℤ) (ρ₁ ρ₂ z : ℂ)
    (hpair : ({ρ₁,ρ₂} : Set ℂ) =
      {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
       canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n}) :
    sourceStandardRoot hp hp1 ψ n z = normalizedStandardRoot ((ρ₁+ρ₂)/2) ((ρ₂-ρ₁)^2) z := by
  rcases pair_eq_pair_iff.mp hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · unfold sourceStandardRoot
    congr 1 <;> dsimp only [canonicalPeriodicMidpoint,canonicalPeriodicGap] <;> ring

/-- The actual improper endpoint integral equals its integrable straight-spoke parameter integral. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_endpoint_parameter_identity
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hpath : ∀ t ∈ Ioc (0:ℝ) 1, a+(t:ℂ)*(ν-a) ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hint : IntervalIntegrable (fun t : ℝ =>
      ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        (a+(t:ℂ)*(ν-a)))/sourceStandardRoot hp hp1 ψ n (a+(t:ℂ)*(ν-a)))*
          sourceActionChi hp hp1 n ψ (a+(t:ℂ)*(ν-a))) volume 0 1) :
    sourceAbelianEndpointIntegral hp hp1 ψ a ν = -Complex.I*(ν-a)*∫ t in (0:ℝ)..1,
      ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        (a+(t:ℂ)*(ν-a)))/sourceStandardRoot hp hp1 ψ n (a+(t:ℂ)*(ν-a)))*
          sourceActionChi hp hp1 n ψ (a+(t:ℂ)*(ν-a)) := by
  let Z := fun t : ℝ => a+(t:ℂ)*(ν-a)
  let F := fun z : ℂ => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)
  let J := fun t : ℝ =>
    ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-Z t)/
      sourceStandardRoot hp hp1 ψ n (Z t))*sourceActionChi hp hp1 n ψ (Z t)
  have hZ : Continuous Z := by dsimp only [Z]; fun_prop
  obtain ⟨E⟩ := C.charts ψ hψ
  have hstart : Tendsto Z (𝓝[>] (0:ℝ)) (𝓝[sourceCanonicalRootDomain hp hp1 ψ] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Z,Complex.ofReal_zero,zero_mul,add_zero] using
        (hZ.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
        nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [self_mem_nhdsWithin,hsmall] with t ht ht1
      exact hpath t ⟨ht,ht1.le⟩
  have hleft0 : Tendsto F (𝓝[sourceCanonicalRootDomain hp hp1 ψ] a) (𝓝 0) := by
    simpa only [sub_self,mul_zero,F] using
      (C.fullPrimitive_endpoint_limit_openGap n n ψ hψ a ha).mono_left
        (nhdsWithin_mono a (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))
  have hleft : Tendsto (F ∘ Z) (𝓝[>] (0:ℝ)) (𝓝 0) := hleft0.comp hstart
  have hright : Tendsto (F ∘ Z) (𝓝[<] (1:ℝ)) (𝓝 (F ν)) := by
    have hz1 : Tendsto Z (𝓝[<] (1:ℝ)) (𝓝 ν) := by
      simpa only [Z,Complex.ofReal_one,one_mul,add_sub_cancel] using
        (hZ.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (1:ℝ)))
    exact (sourceFullAbelianPrimitive_hasDerivAt E n ν hν).continuousAt.tendsto.comp hz1
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (F ∘ Z) (-Complex.I*(ν-a)*J t) t := by
    have hZ' : HasDerivAt Z (ν-a) t := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using
        (Complex.ofRealCLM.hasDerivAt (x := t) |>.mul_const (ν-a)).const_add a
    have hf := (sourceFullAbelianPrimitive_hasDerivAt E n (Z t)
      (hpath t (Ioo_subset_Ioc_self ht))).scomp t hZ'
    rw [sourceCriticalRootRatio_eq_selectedFactor_mul_chi hp hp1 ψ n (Z t)
      (hpath t (Ioo_subset_Ioc_self ht))] at hf
    exact hf.congr_deriv (by dsimp only [J]; simp only [smul_eq_mul]; ring)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0:ℝ) < 1) hderiv (hint.const_mul (-Complex.I*(ν-a))) hleft hright
  rw [intervalIntegral.integral_const_mul,sub_zero] at hi
  rw [C.endpointIntegral_eq ψ hψ n a ν ha hν]
  exact hi.symm

/-- The actual source data supplies the regular-factor analyticity and identifies the
analytic singular parameter integral with the literal improper endpoint integral. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_source_endpoint_integral_analytic
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (H : SourceCorollary10_6Data hp hp1 S) (hS : IsOpen S)
    (hV : IsOpen V) (hVS : V ⊆ S)
    (hVC : V ⊆ ball C.discs.source.val C.discs.sourceRadius)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (ρ₁ ρ₂ : CoeffPair p → ℂ) (hA₁ : AnalyticOnNhd ℂ ρ₁ V) (hA₂ : AnalyticOnNhd ℂ ρ₂ V)
    (hpair : ∀ ψ ∈ V, ({ρ₁ ψ,ρ₂ ψ} : Set ℂ) =
      {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
       canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n})
    (hgap : ρ₂ φ-ρ₁ φ ≠ 0) (σ : ℝ) (hσ : 0 < σ)
    (hν : ρ₁ φ-(σ:ℂ)*(ρ₂ φ-ρ₁ φ) ∈ frontier (D n))
    (hpath : ∀ ψ ∈ V, segment ℝ (ρ₁ ψ) (ρ₁ φ-(σ:ℂ)*(ρ₂ φ-ρ₁ φ)) \ {ρ₁ ψ} ⊆
      closure (D n) ∩ sourceCanonicalRootDomain hp hp1 ψ) :
    let ν := ρ₁ φ-(σ:ℂ)*(ρ₂ φ-ρ₁ φ)
    let Z := fun (ψ : CoeffPair p) (t : ℝ) => ρ₁ ψ+(t:ℂ)*(ν-ρ₁ ψ)
    let J := fun (ψ : CoeffPair p) (t : ℝ) =>
      ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-Z ψ t)/
        sourceStandardRoot hp hp1 ψ n (Z ψ t))*sourceActionChi hp hp1 n ψ (Z ψ t)
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      (∀ ψ ∈ U, IntervalIntegrable (J ψ) volume 0 1) ∧
      (∀ ψ ∈ U, sourceAbelianEndpointIntegral hp hp1 ψ (ρ₁ ψ) ν =
        -Complex.I*(ν-ρ₁ ψ)*∫ t in (0:ℝ)..1, J ψ t) ∧
      AnalyticOnNhd ℂ (fun ψ => sourceAbelianEndpointIntegral hp hp1 ψ (ρ₁ ψ) ν) U := by
  dsimp only
  let ν := ρ₁ φ-(σ:ℂ)*(ρ₂ φ-ρ₁ φ)
  let Z := fun (ψ : CoeffPair p) (t : ℝ) => ρ₁ ψ+(t:ℂ)*(ν-ρ₁ ψ)
  let a := fun ψ : CoeffPair p => canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let χ := fun q : ℂ × CoeffPair p => sourceActionChi hp hp1 n q.2 q.1
  let J := fun (ψ : CoeffPair p) (t : ℝ) =>
    ((a ψ-Z ψ t)/sourceStandardRoot hp hp1 ψ n (Z ψ t))*χ (Z ψ t,ψ)
  let K := fun (ψ : CoeffPair p) (t : ℝ) =>
    ((a ψ-Z ψ t)/normalizedStandardRoot ((ρ₁ ψ+ρ₂ ψ)/2) ((ρ₂ ψ-ρ₁ ψ)^2) (Z ψ t))*χ (Z ψ t,ψ)
  obtain ⟨center,R,hR,hDb⟩ := hD.discs n
  have hρD (ψ : CoeffPair p) (hψ : ψ ∈ V) : ρ₁ ψ ∈ D n := by
    have hseg : segment ℝ (ρ₁ ψ) (ρ₂ ψ) = sourcePeriodicSegment hp hp1 ψ n := by
      rw [sourcePeriodicSegment,← convexHull_pair,← convexHull_pair,hpair ψ hψ]
    exact hD.gap ψ hψ n (by rw [← hseg]; exact left_mem_segment ℝ _ _)
  have hνnot : ν ∉ D n := by
    have hopen : IsOpen (D n) := by rw [hDb]; exact isOpen_ball
    simpa only [hopen.interior_eq] using hν.2
  have hνne (ψ : CoeffPair p) (hψ : ψ ∈ V) : ν-ρ₁ ψ ≠ 0 := by
    intro he
    exact hνnot (sub_eq_zero.mp he ▸ hρD ψ hψ)
  have hZcl (ψ : CoeffPair p) (hψ : ψ ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      Z ψ t ∈ closure (D n) := by
    have hconv : Convex ℝ (closure (D n)) := by
      rw [hDb,closure_ball _ hR.ne']
      exact convex_closedBall _ _
    have hh := hconv.lineMap_mem (subset_closure (hρD ψ hψ)) (frontier_subset_closure hν) ht
    simpa only [Z,AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using hh
  have hZroot (ψ : CoeffPair p) (hψ : ψ ∈ V) (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      Z ψ t ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    apply (hpath ψ hψ ?_).2
    constructor
    · have hh := lineMap_mem_segment ℝ (ρ₁ ψ) ν (Ioc_subset_Icc_self ht)
      simpa only [Z,AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using hh
    · intro he
      have he' : ρ₁ ψ+(t:ℂ)*(ν-ρ₁ ψ) = ρ₁ ψ := he
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.1.ne') (hνne ψ hψ) (add_eq_left.mp he')
  have hχ (ψ : CoeffPair p) (hψ : ψ ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      AnalyticAt ℂ χ (Z ψ t,ψ) := H.chi_joint hS n (Z ψ t,ψ)
        ⟨hVS hψ,hD.closedDisk_subset_omittedDomain ψ hψ n (hZcl ψ hψ t ht)⟩
  have ha : AnalyticOnNhd ℂ a V := fun ψ hψ =>
    (H.roots.roots.symmetric.simplicity.critical ψ (hVS hψ) n).1
  obtain ⟨U,hU,hφU,hUV,hI,hA⟩ := appendixF_endpoint_integral_analytic
    ρ₁ ρ₂ a χ V hV φ hφ hA₁ hA₂ ha hgap σ hσ hχ
  have hJK (ψ : CoeffPair p) (hψ : ψ ∈ V) : J ψ = K ψ := by
    funext t
    dsimp only [J,K]
    rw [appendixF_source_root_eq_of_endpoint_pair ψ n (ρ₁ ψ) (ρ₂ ψ) (Z ψ t) (hpair ψ hψ)]
  have hint (ψ : CoeffPair p) (hψ : ψ ∈ U) : IntervalIntegrable (J ψ) volume 0 1 := by
    rw [hJK ψ (hUV hψ)]
    exact hI ψ hψ
  have hidentity (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      sourceAbelianEndpointIntegral hp hp1 ψ (ρ₁ ψ) ν =
        -Complex.I*(ν-ρ₁ ψ)*∫ t in (0:ℝ)..1, J ψ t := by
    have hψV := hUV hψ
    have hρ : ρ₁ ψ ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ) := by
      rw [← hpair ψ hψV]
      simp
    have hνroot : ν ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      simpa only [Z,Complex.ofReal_one,one_mul,add_sub_cancel] using hZroot ψ hψV 1 (by norm_num)
    exact C.appendixF_endpoint_parameter_identity ψ (hVC hψV) n (ρ₁ ψ) ν hρ hνroot
      (hZroot ψ hψV) (hint ψ hψ)
  refine ⟨U,hU,hφU,hUV,hint,hidentity,?_⟩
  intro ψ hψ
  apply (hA ψ hψ).congr
  filter_upwards [hU.mem_nhds hψ] with ξ hξ
  have hh := hidentity ξ hξ
  rw [hJK ξ (hUV hξ)] at hh
  exact hh.symm

/-- At an open gap, the actual source data produces both analytic improper endpoint
integrals on one neighborhood, with terminal points on the original disc boundary. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_open_endpoint_integrals_analytic
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (H : SourceCorollary10_6Data hp hp1 S) (hS : IsOpen S)
    (hV : IsOpen V) (hVS : V ⊆ S)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hφC : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    ∃ ν₁ ν₂ : ℂ, ν₁ ∈ frontier (D n) ∧ ν₂ ∈ frontier (D n) ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
        ∃ ρ₁ ρ₂ : CoeffPair p → ℂ,
          AnalyticOnNhd ℂ ρ₁ U ∧ AnalyticOnNhd ℂ ρ₂ U ∧
          ρ₁ φ = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∧
          ρ₂ φ = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∧
          (∀ ψ ∈ U, ({ρ₁ ψ,ρ₂ ψ} : Set ℂ) =
            {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
             canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n}) ∧
          AnalyticOnNhd ℂ (fun ψ => sourceAbelianEndpointIntegral hp hp1 ψ (ρ₁ ψ) ν₁) U ∧
          AnalyticOnNhd ℂ (fun ψ => sourceAbelianEndpointIntegral hp hp1 ψ (ρ₂ ψ) ν₂) U := by
  obtain ⟨σ₁,σ₂,ν₁,ν₂,hσ₁,hσ₂,heq₁,heq₂,hν₁,hν₂,
      U₀,hU₀,hφU₀,hU₀V,ρ₁,ρ₂,hA₁,hA₂,hbase₁,hbase₂,hbranches⟩ :=
    H.roots.roots.symmetric.appendixF_common_open_gap_spokes hV hVS hD φ hφ n hgap
  let B := U₀ ∩ ball C.discs.source.val C.discs.sourceRadius
  have hB : IsOpen B := hU₀.inter isOpen_ball
  have hφB : φ ∈ B := ⟨hφU₀,hφC⟩
  have hBV : B ⊆ V := fun _ hψ => hU₀V hψ.1
  have hBA₁ : AnalyticOnNhd ℂ ρ₁ B := hA₁.mono inter_subset_left
  have hBA₂ : AnalyticOnNhd ℂ ρ₂ B := hA₂.mono inter_subset_left
  have hg : ρ₂ φ-ρ₁ φ ≠ 0 := by rw [hbase₁,hbase₂]; exact hgap
  have hg' : ρ₁ φ-ρ₂ φ ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hg).symm
  have he₁ : ρ₁ φ-(σ₁:ℂ)*(ρ₂ φ-ρ₁ φ) = ν₁ := by rw [hbase₁,hbase₂]; exact heq₁.symm
  have he₂ : ρ₂ φ-(σ₂:ℂ)*(ρ₁ φ-ρ₂ φ) = ν₂ := by
    rw [hbase₁,hbase₂,heq₂]
    ring
  have hpair := fun ψ (hψ : ψ ∈ B) => (hbranches ψ hψ.1).1
  have hpair' (ψ : CoeffPair p) (hψ : ψ ∈ B) :
      ({ρ₂ ψ,ρ₁ ψ} : Set ℂ) =
        {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
         canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} := by
    rw [pair_comm (ρ₂ ψ) (ρ₁ ψ)]
    exact hpair ψ hψ
  obtain ⟨U₁,hU₁,hφU₁,hU₁B,_,_,hI₁⟩ := C.appendixF_source_endpoint_integral_analytic
    H hS hB (hBV.trans hVS) inter_subset_right (hD.mono hBV) φ hφB n ρ₁ ρ₂ hBA₁ hBA₂ hpair
    hg σ₁ hσ₁ (by rw [he₁]; exact hν₁)
    (by intro ψ hψ; rw [he₁]; exact (hbranches ψ hψ.1).2.2.2.2.1)
  obtain ⟨U₂,hU₂,hφU₂,hU₂B,_,_,hI₂⟩ := C.appendixF_source_endpoint_integral_analytic
    H hS hB (hBV.trans hVS) inter_subset_right (hD.mono hBV) φ hφB n ρ₂ ρ₁ hBA₂ hBA₁ hpair'
    hg' σ₂ hσ₂ (by rw [he₂]; exact hν₂)
    (by intro ψ hψ; rw [he₂]; exact (hbranches ψ hψ.1).2.2.2.2.2)
  rw [he₁] at hI₁
  rw [he₂] at hI₂
  refine ⟨ν₁,ν₂,hν₁,hν₂,U₁ ∩ U₂,hU₁.inter hU₂,⟨hφU₁,hφU₂⟩,
    fun _ hψ => hBV (hU₁B hψ.1),ρ₁,ρ₂,
    hBA₁.mono (fun _ hψ => hU₁B hψ.1),hBA₂.mono (fun _ hψ => hU₁B hψ.1),
    hbase₁,hbase₂,fun ψ hψ => hpair ψ (hU₁B hψ.1),
    hI₁.mono inter_subset_left,hI₂.mono inter_subset_right⟩

end NLS.ZakharovShabat
