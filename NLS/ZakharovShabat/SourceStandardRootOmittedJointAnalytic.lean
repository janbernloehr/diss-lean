import NLS.ZakharovShabat.SourceStandardRootOmittedProduct
import NLS.ComplexAnalysis.LocalAnalyticApproximationOn
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-!
# Joint analyticity of arbitrary-index omitted standard-root products

The uniform paired-factor tail estimate is unchanged beyond the one pair
containing the omitted root. A bounded literal finite prefix therefore
gives local uniform convergence of the actual arbitrary-index cutoffs.
The local Banach-space Taylor theorem then proves joint analyticity.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The arbitrary-index product as a joint spectral/source function. -/
def sourceStandardRootOmittedJointProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) : ℂ × CoeffPair p → ℂ :=
  fun t => sourceStandardRootOmittedProduct hp hp1 n t.2 t.1

@[simp] theorem sourceStandardRootOmittedJointProduct_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourceStandardRootOmittedJointProduct hp hp1 0 =
      sourceStandardRootPairedJointProduct hp hp1 := by
  funext t
  exact sourceStandardRootOmittedProduct_zero hp hp1 t.2 t.1

/-- Continuity of the finite literal cutoffs at one point and uniform
paired-factor tails yield local uniform convergence of the omitted product. -/
theorem exists_local_uniform_sourceStandardRootOmittedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (z : ℂ)
    (hcont : ∀ N : ℕ, ContinuousAt
      (sourceStandardRootOmittedPartialProduct hp hp1 n N) (z,φ)) :
    ∃ U : Set (ℂ × CoeffPair p), IsOpen U ∧ (z,φ) ∈ U ∧
      TendstoUniformlyOn (sourceStandardRootOmittedPartialProduct hp hp1 n)
        (sourceStandardRootOmittedJointProduct hp hp1 n) atTop U := by
  let R : ℝ := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨V, hVopen, hφV, Ntail, D, hD, htail⟩ :=
    exists_uniform_absolute_sourceStandardRootPairedFactor_tails hp hp1 φ R hR
  let N₀ := max Ntail n.natAbs
  let F : ℂ × CoeffPair p → ℂ := sourceStandardRootOmittedPartialProduct hp hp1 n N₀
  have hFcont : ContinuousAt F (z,φ) := hcont N₀
  let P : ℝ := ‖F (z,φ)‖+1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hFP : ‖F (z,φ)‖ < P := by dsimp [P]; linarith
  have hnear : {t : ℂ × CoeffPair p | ‖F t‖ < P} ∈ 𝓝 (z,φ) :=
    hFcont.norm (gt_mem_nhds hFP)
  obtain ⟨U₁, hU₁sub, hU₁open, hbaseU₁⟩ := _root_.mem_nhds_iff.mp hnear
  let U : Set (ℂ × CoeffPair p) :=
    U₁ ∩ {t | t.2 ∈ V} ∩ {t | ‖t.1‖ < R}
  have hUopen : IsOpen U := by
    exact (hU₁open.inter (hVopen.preimage continuous_snd)).inter
      (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)
  have hbaseU : (z,φ) ∈ U := by
    refine ⟨⟨hbaseU₁, hφV⟩, ?_⟩
    dsimp [R]
    linarith
  let a (t : ℂ × CoeffPair p) : ℂ :=
    (if n = 0 then 1 else sourceStandardRoot hp hp1 t.2 0 t.1) /
      singleSpectralDenominator n
  let u (t : ℂ × CoeffPair p) (j : ℕ) : ℂ :=
    sourceStandardRootOmittedPairedFactor hp hp1 t.2 t.1 n j - 1
  have hfinite (t : ℂ × CoeffPair p) (N : ℕ) :
      a t * ∏ j ∈ Finset.range N, (1+u t j) =
        sourceStandardRootOmittedPartialProduct hp hp1 n N t := by
    rw [sourceStandardRootOmittedPartialProduct_eq_paired]
    dsimp only [a, u]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    ring
  have hprod := NLS.ComplexAnalysis.tendstoUniformlyOn_prefactor_prod_one_add_nat_of_tail
    a u U N₀ P hP
    (fun t ht => by
      have hpre : ‖F t‖ < P := hU₁sub ht.1.1
      rw [hfinite]
      exact hpre.le)
    D hD
    (fun N hN t ht s hs => by
      have hNtail : Ntail ≤ N := (le_max_left _ _).trans hN
      have hNn : n.natAbs ≤ N := (le_max_right _ _).trans hN
      have heq : (∑ j ∈ s, ‖u t j‖) =
          ∑ j ∈ s, ‖sourceStandardRootPairedFactor hp hp1 t.2 t.1 j - 1‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [u]
        rw [sourceStandardRootOmittedPairedFactor_eq_of_ne hp hp1 t.2 t.1 n j
          (by have := hs j hj; omega)]
      rw [heq]
      exact htail N hNtail t.2 ht.1.2 t.1 ht.2.le s hs)
    (sourceStandardRootOmittedJointProduct hp hp1 n)
    (fun t _ => by
      have h := tendsto_sourceStandardRootOmittedPartialProduct hp hp1 n t.2 t.1
      change Tendsto (fun N => a t * ∏ j ∈ Finset.range N, (1+u t j)) atTop
        (𝓝 (sourceStandardRootOmittedJointProduct hp hp1 n t))
      have heq : (fun N => a t * ∏ j ∈ Finset.range N, (1+u t j)) =
          (fun N => sourceStandardRootOmittedPartialProduct hp hp1 n N t) := by
        funext N
        exact hfinite t N
      rw [heq]
      exact h)
  refine ⟨U, hUopen, hbaseU, ?_⟩
  have hfun : (fun N t => a t * ∏ j ∈ Finset.range N, (1+u t j)) =
      sourceStandardRootOmittedPartialProduct hp hp1 n := by
    funext N t
    exact hfinite t N
  rw [hfun] at hprod
  exact hprod

/-- One connected almost-real source domain works for every omitted index:
the actual infinite products are jointly analytic and nonzero on their
open moving-gap complements, with locally uniform literal cutoffs. -/
theorem exists_global_source_analytic_omittedJointProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ n : ℤ,
        IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
        AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
          (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
        TendstoLocallyUniformlyOn
          (sourceStandardRootOmittedPartialProduct hp hp1 n)
          (sourceStandardRootOmittedJointProduct hp hp1 n) atTop
          (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
        ∀ t ∈ sourceStandardRootOmittedJointDomain hp hp1 W n,
          sourceStandardRootOmittedJointProduct hp hp1 n t ≠ 0 := by
  obtain ⟨W, hWopen, hWconnected, hreal, hdata⟩ :=
    exists_global_source_open_analytic_omittedPartialProduct hp hp1
  refine ⟨W, hWopen, hWconnected, hreal, ?_⟩
  intro n
  let D := sourceStandardRootOmittedJointDomain hp hp1 W n
  have hDopen : IsOpen D := (hdata n).1
  have hfinite (N : ℕ) : AnalyticOnNhd ℂ
      (sourceStandardRootOmittedPartialProduct hp hp1 n N) D := (hdata n).2 N
  have huniform (t : ℂ × CoeffPair p) (ht : t ∈ D) :
      ∃ U : Set (ℂ × CoeffPair p), IsOpen U ∧ t ∈ U ∧
        TendstoUniformlyOn (sourceStandardRootOmittedPartialProduct hp hp1 n)
          (sourceStandardRootOmittedJointProduct hp hp1 n) atTop U :=
    exists_local_uniform_sourceStandardRootOmittedProduct hp hp1 n t.2 t.1
      (fun N => (hfinite N t ht).continuousAt)
  have happrox : NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximationOn
      (sourceStandardRootOmittedPartialProduct hp hp1 n)
      (sourceStandardRootOmittedJointProduct hp hp1 n) D :=
    NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximationOn.of_open_local_uniform
      hDopen hfinite huniform
  have hanalytic : AnalyticOnNhd ℂ
      (sourceStandardRootOmittedJointProduct hp hp1 n) D :=
    NLS.ComplexAnalysis.analyticOnNhd_of_complexSmoothOn _ hDopen happrox.contDiffOn
  have hlocal : TendstoLocallyUniformlyOn
      (sourceStandardRootOmittedPartialProduct hp hp1 n)
      (sourceStandardRootOmittedJointProduct hp hp1 n) atTop D := by
    intro u hu t ht
    obtain ⟨U, hUopen, htU, hconv⟩ := huniform t ht
    exact ⟨U, mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds htU), hconv u hu⟩
  refine ⟨hDopen, hanalytic, hlocal, ?_⟩
  intro t ht
  exact sourceStandardRootOmittedProduct_ne_zero hp hp1 t.2 t.1 n ht.2

/-- Joint analyticity restricts to spectral analyticity at each fixed
source potential, as in the first clause of Lemma 10.5. -/
theorem sourceStandardRootOmittedProduct_analyticOnNhd_spectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (W : Set (CoeffPair p))
    (hjoint : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n))
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    AnalyticOnNhd ℂ (fun z => sourceStandardRootOmittedProduct hp hp1 n ψ z)
      (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  intro z hz
  have h := hjoint (z,ψ) ⟨hψ,hz⟩
  have hpair : AnalyticAt ℂ (fun w : ℂ => (w,ψ)) z :=
    analyticAt_id.prod analyticAt_const
  simpa only [sourceStandardRootOmittedJointProduct, Function.comp_def] using
    h.comp (f := fun w : ℂ => (w,ψ)) hpair

end NLS.ZakharovShabat
