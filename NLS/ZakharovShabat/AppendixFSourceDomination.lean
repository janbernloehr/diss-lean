import NLS.ZakharovShabat.AppendixFSourceSpokes
import NLS.ZakharovShabat.SourceActionChi
import NLS.ZakharovShabat.AppendixFSourceLimits
import NLS.ZakharovShabat.AppendixFPositiveIntegral
import NLS.ComplexAnalysis.CompactParameterBounds
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Source bounds and measurability for the Appendix F majorant

Joint analyticity gives a common bound for the actual chi_n product on
the whole original closed disc. Along any admissible midpoint spoke,
the actual standard-root quotient is measurable on the punctured interval.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- One source neighborhood bounds the literal chi_n product on the original closed disc. -/
theorem SourceCorollary10_6Data.appendixF_chi_uniform_closedDisk_bound
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    {V : Set (CoeffPair p)} (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ U, ∀ z ∈ closure (D n),
        ‖sourceActionChi hp hp1 n ψ z‖ ≤ M := by
  have hK : IsCompact (closure (D n)) := by
    obtain ⟨a,R,hR,he⟩ := hD.discs n
    rw [he,closure_ball _ hR.ne']
    exact isCompact_closedBall _ _
  obtain ⟨U,hU,hφU,M,hM,hb⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    (fun q : ℂ × CoeffPair p => sourceActionChi hp hp1 n q.2 q.1)
    (sourceStandardRootOmittedJointDomain hp hp1 W n) (H.roots.joint n).1
    (H.chi_joint hW n).continuousOn (closure (D n)) hK φ
    (fun z hz => ⟨hVW hφ,hD.closedDisk_subset_omittedDomain φ hφ n hz⟩)
  exact ⟨U ∩ V,hU.inter hV,⟨hφU,hφ⟩,inter_subset_right,M+1,by positivity,
    fun ψ hψ z hz => (hb ψ hψ.1 z hz).2.trans (by linarith)⟩

/-- Actual admissible midpoint spokes give measurable spectral integrands with the full coefficient. -/
theorem SourceCorollary10_6Data.appendixF_spoke_integrand_measurable
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (ν : ℂ)
    (hpath : ∀ t ∈ Ioc (0:ℝ) 1,
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n+
        (t:ℂ)*(ν-canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n) ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let Z := fun t : ℝ => τ+(t:ℂ)*(ν-τ)
    AEStronglyMeasurable (fun t => -I*(ν-τ)*
      ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-Z t) /
        sourceStandardRoot hp hp1 ψ n (Z t))*sourceActionChi hp hp1 n ψ (Z t))
      (volume.restrict (Ioc (0:ℝ) 1)) := by
  dsimp only
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let Z := fun t : ℝ => τ+(t:ℂ)*(ν-τ)
  have hZ : Continuous Z := by dsimp only [Z]; fun_prop
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
  intro t ht
  have hz := hpath t ht
  have hr : ContinuousAt (fun u : ℝ => sourceStandardRoot hp hp1 ψ n (Z u)) t :=
    ((H.roots.roots.spectral ψ n (Z t) (hz n)).continuousAt).comp (f := Z) hZ.continuousAt
  have hx : ContinuousAt (fun u : ℝ => sourceActionChi hp hp1 n ψ (Z u)) t :=
    ((H.chi_joint hW n (Z t,ψ) ⟨hψ,fun m _ => hz m⟩).continuousAt).comp
      (f := fun u : ℝ => (Z u,ψ)) (hZ.continuousAt.prodMk continuousAt_const)
  exact ((continuousAt_const.mul ((continuousAt_const.sub hZ.continuousAt).div hr
    (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n (Z t) (hz n)))).mul hx).continuousWithinAt

/-- A common source neighborhood supplies the domination and measurability needed for
convergence of the actual rescaled integrals along admissible midpoint spokes. -/
theorem SourceLemma10_10Data.appendixF_source_spoke_integral_tendsto_locally
    (H : SourceLemma10_10Data hp hp1 W) (hW : IsOpen W)
    {V : Set (CoeffPair p)} (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∀ ψ : ℕ → CoeffPair p, (∀ k, ψ k ∈ U) → Tendsto ψ atTop (𝓝 φ) →
        ∀ ν ∈ frontier (D n),
          let τ := fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
            (periodOnePotential χ) (periodOnePotential_mem χ) n
          let Z := fun (χ : CoeffPair p) (t : ℝ) => τ χ+(t:ℂ)*(ν-τ χ)
          (∀ k, ∀ t ∈ Ioc (0:ℝ) 1, Z (ψ k) t ∈ sourceCanonicalRootDomain hp hp1 (ψ k)) →
          Tendsto (fun k => ∫ t in (0:ℝ)..1, -I*(ν-τ (ψ k))*
            ((canonicalCriticalPoints hp hp1 (periodOnePotential (ψ k))
              (periodOnePotential_mem (ψ k)) n-Z (ψ k) t)/
                sourceStandardRoot hp hp1 (ψ k) n (Z (ψ k) t))*sourceActionChi hp hp1 n (ψ k) (Z (ψ k) t))
            atTop (𝓝 (∫ t in (0:ℝ)..1, -I*(ν-τ φ)*sourceActionChi hp hp1 n φ (Z φ t))) := by
  let Q := H.previous.previous.previous
  let A := Q.roots.roots.symmetric
  obtain ⟨U,hU,hφU,hUV,M,hM,hbound⟩ :=
    Q.appendixF_chi_uniform_closedDisk_bound hW hV hVW hD φ hφ n
  obtain ⟨T,hTsub,hT,hφT⟩ := _root_.mem_nhds_iff.mp
    (H.appendixF_eventually_half_gap hW φ (hVW hφ) n hgap)
  refine ⟨U ∩ T,hU.inter hT,⟨hφU,hφT⟩,inter_subset_left.trans hUV,?_⟩
  intro ψ hψU hψ ν hν
  dsimp only
  intro hpath
  let τ := fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  let γ := fun k => canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n
  let a := fun k => canonicalCriticalPoints hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n
  let z := fun k => ν-τ (ψ k)
  let Z := fun (χ : CoeffPair p) (t : ℝ) => τ χ+(t:ℂ)*(ν-τ χ)
  have hψV k : ψ k ∈ V := hUV (hψU k).1
  obtain ⟨center,R,hR,hDball⟩ := hD.discs n
  have hνsphere : ν ∈ sphere (center:ℂ) R := by
    simpa only [hDball,frontier_ball _ hR.ne'] using hν
  have hτball (χ : CoeffPair p) (hχ : χ ∈ V) : τ χ ∈ ball (center:ℂ) R := by
    rw [← hDball]
    exact hD.gap χ hχ n (sourcePeriodicMidpoint_mem_segment hp hp1 χ n)
  have hzne (χ : CoeffPair p) (hχ : χ ∈ V) : ν-τ χ ≠ 0 := by
    intro he
    have hlt := mem_ball.mp (hτball χ hχ)
    rw [← sub_eq_zero.mp he,mem_sphere.mp hνsphere] at hlt
    exact lt_irrefl _ hlt
  have hZcl (χ : CoeffPair p) (hχ : χ ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      Z χ t ∈ closure (D n) := by
    rw [hDball,closure_ball _ hR.ne']
    have h := (convex_closedBall (center:ℂ) R).lineMap_mem
      (ball_subset_closedBall (hτball χ hχ)) (sphere_subset_closedBall hνsphere) ht
    simpa only [Z,AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using h
  have hzbound (χ : CoeffPair p) (hχ : χ ∈ V) : ‖ν-τ χ‖ ≤ 2*R := by
    rw [← dist_eq_norm]
    calc
      dist ν (τ χ) ≤ dist ν (center:ℂ)+dist (center:ℂ) (τ χ) := dist_triangle _ _ _
      _ ≤ R+R := add_le_add (mem_sphere.mp hνsphere).le
        (by simpa only [dist_comm] using (mem_ball.mp (hτball χ hχ)).le)
      _ = 2*R := by ring
  have hτ := (A.midpoint n φ (hVW hφ)).continuousAt.tendsto.comp hψ
  have hz : Tendsto z atTop (𝓝 (ν-τ φ)) := tendsto_const_nhds.sub hτ
  have hg : Tendsto γ atTop (𝓝 0) := A.appendixF_gap_tendsto_zero φ (hVW hφ) n hgap ψ hψ
  have hχlim (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      Tendsto (fun k => sourceActionChi hp hp1 n (ψ k) (Z (ψ k) t)) atTop
        (𝓝 (sourceActionChi hp hp1 n φ (Z φ t))) := by
    have hx := (Q.chi_joint hW n (Z φ t,φ)
      ⟨hVW hφ,hD.closedDisk_subset_omittedDomain φ hφ n (hZcl φ hφ t (Ioc_subset_Icc_self ht))⟩).continuousAt
    have hpoint : Tendsto (fun k => (Z (ψ k) t,ψ k)) atTop (𝓝 (Z φ t,φ)) :=
      (hτ.add (hz.const_mul (t:ℂ))).prodMk_nhds hψ
    have hcomp := hx.tendsto.comp hpoint
    simpa only [Function.comp_def] using hcomp
  have hmajor (k : ℕ) (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      ‖z k‖*‖sourceActionChi hp hp1 n (ψ k) (Z (ψ k) t)‖ ≤ 2*R*M :=
    mul_le_mul (hzbound (ψ k) (hψV k))
      (hbound (ψ k) (hψU k).1 (Z (ψ k) t) (hZcl (ψ k) (hψV k) t (Ioc_subset_Icc_self ht)))
      (norm_nonneg _) (by positivity)
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun t : ℝ => z k*((a k-(τ (ψ k)+(t:ℂ)*z k))/
        normalizedStandardRoot (τ (ψ k)) ((γ k)^2) (τ (ψ k)+(t:ℂ)*z k))*
          sourceActionChi hp hp1 n (ψ k) (Z (ψ k) t)) (volume.restrict (Ioc (0:ℝ) 1)) := by
    have h := (Q.appendixF_spoke_integrand_measurable hW (ψ k) (hVW (hψV k)) n ν
      (hpath k)).const_mul I
    simpa only [τ,γ,a,z,Z,sourceStandardRoot,← mul_assoc,mul_neg,I_mul_I,neg_neg,one_mul] using h
  have hlim := appendixF_collapsing_spoke_integral_tendsto_of_gap_zero
    (fun k => τ (ψ k)) γ a z (ν-τ φ) (hzne φ hφ) hg hz
    (fun k => hzne (ψ k) (hψV k)) (fun k => hTsub (hψU k).2)
    (fun k t => sourceActionChi hp hp1 n (ψ k) (Z (ψ k) t))
    (fun t => sourceActionChi hp hp1 n φ (Z φ t)) hχlim
    (2*R*M) (by positivity) hmajor hmeas
  simpa only [← intervalIntegral.integral_const_mul,sourceStandardRoot,τ,γ,a,z,Z,mul_assoc] using
    hlim.const_mul (-I)

/-- Every convergent nearby source sequence has a single original boundary point and
admissible spokes whose actual differential integrals converge to the collapsed formula. -/
theorem SourceLemma10_10Data.appendixF_exists_common_convergent_spokes
    (H : SourceLemma10_10Data hp hp1 W) (hW : IsOpen W)
    {V : Set (CoeffPair p)} (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (ψ : ℕ → CoeffPair p) (hψV : ∀ k, ψ k ∈ V) (hψ : Tendsto ψ atTop (𝓝 φ)) :
        ∃ ν ∈ frontier (D n),
          let τ := fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
            (periodOnePotential χ) (periodOnePotential_mem χ) n
          let Z := fun (χ : CoeffPair p) (t : ℝ) => τ χ+(t:ℂ)*(ν-τ χ)
          (∀ k, ν ∈ sourceCanonicalRootDomain hp hp1 (ψ k) ∧
            ∀ t ∈ Ioc (0:ℝ) 1, Z (ψ k) t ∈ sourceCanonicalRootDomain hp hp1 (ψ k)) ∧
          Tendsto (fun k => ∫ t in (0:ℝ)..1, -I*(ν-τ (ψ k))*
            ((canonicalCriticalPoints hp hp1 (periodOnePotential (ψ k))
              (periodOnePotential_mem (ψ k)) n-Z (ψ k) t)/
                sourceStandardRoot hp hp1 (ψ k) n (Z (ψ k) t))*sourceActionChi hp hp1 n (ψ k) (Z (ψ k) t))
            atTop (𝓝 (∫ t in (0:ℝ)..1, -I*(ν-τ φ)*sourceActionChi hp hp1 n φ (Z φ t))) := by
  obtain ⟨U,hU,hφU,_,hlim⟩ := H.appendixF_source_spoke_integral_tendsto_locally hW hV hVW hD φ hφ n hgap
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hψ (hU.mem_nhds hφU))
  obtain ⟨ν,hν,hspokes⟩ := hD.exists_common_source_midpoint_spokes ψ hψV n
  refine ⟨ν,hν,?_⟩
  dsimp only
  let τ := fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  have hpath (k : ℕ) (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      τ (ψ k)+(t:ℂ)*(ν-τ (ψ k)) ∈ sourceCanonicalRootDomain hp hp1 (ψ k) := by
    have hzne : ν-τ (ψ k) ≠ 0 := by
      intro he
      have hm := sourcePeriodicMidpoint_mem_segment hp hp1 (ψ k) n
      apply (hspokes k).1 n
      rwa [sub_eq_zero.mp he]
    apply ((hspokes k).2 ?_).2
    constructor
    · have h := lineMap_mem_segment ℝ (τ (ψ k)) ν (Ioc_subset_Icc_self ht)
      simpa only [AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using h
    · intro he
      have he' : τ (ψ k)+(t:ℂ)*(ν-τ (ψ k)) = τ (ψ k) := he
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.1.ne') hzne (add_eq_left.mp he')
  refine ⟨fun k => ⟨(hspokes k).1,hpath k⟩,?_⟩
  apply (tendsto_add_atTop_iff_nat N).mp
  exact hlim (fun k => ψ (k+N)) (fun k => hN (k+N) (Nat.le_add_left N k))
    (hψ.comp (tendsto_add_atTop_nat N)) ν hν (fun k => hpath (k+N))

end NLS.ZakharovShabat
