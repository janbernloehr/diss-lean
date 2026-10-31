import NLS.ZakharovShabat.AppendixFEndpointRoot
import NLS.ComplexAnalysis.AppendixFProofEstimates
import Mathlib.Topology.Compactness.Compact

/-! # Uniform endpoint-spoke radicand bounds in F.2

The positive base radicand persists uniformly for all path parameters
after restricting the source to one open neighborhood.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- A strict lower bound on a compact reference slice persists on one parameter neighborhood. -/
theorem appendixF_local_uniform_lower_bound
    {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
    (K : Set T) (hK : IsCompact K) (x : X) (f : X × T → ℝ) (c : ℝ)
    (hf : ∀ t ∈ K, ContinuousAt f (x,t)) (hc : ∀ t ∈ K, c < f (x,t)) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, ∀ t ∈ K, c < f (y,t) := by
  have hn : ∀ᶠ y in 𝓝 x, ∀ t ∈ K, c < f (y,t) :=
    hK.eventually_forall_of_forall_eventually fun t ht =>
      (hf t ht).eventually (lt_mem_nhds (hc t ht))
  obtain ⟨V,hVsub,hV,hxV⟩ := _root_.mem_nhds_iff.mp hn
  exact ⟨V,hV,hxV,fun y hy => hVsub hy⟩

/-- A positive lower bound for the real part bounds the principal root away from zero. -/
theorem appendixF_sqrt_norm_lower (z : ℂ) (c : ℝ) (hc : 0 ≤ c) (hz : c ≤ z.re) :
    Real.sqrt c ≤ ‖Complex.sqrt z‖ := by
  have hs : Complex.sqrt z ^ 2 = z := by
    have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hn : ‖Complex.sqrt z‖^2 = ‖z‖ := by rw [← norm_pow,hs]
  have hle := hz.trans (Complex.re_le_norm z)
  nlinarith [Real.sq_sqrt hc,Real.sqrt_nonneg c,norm_nonneg (Complex.sqrt z)]

end NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The endpoint-path denominator and the real part of its radicand have explicit
positive uniform bounds near any noncollapsed complex base pair. -/
theorem appendixF_endpoint_uniform_radicand
    {X : Type*} [TopologicalSpace X] (ρ₁ ρ₂ : X → ℂ) (x : X)
    (h₁ : ContinuousAt ρ₁ x) (h₂ : ContinuousAt ρ₂ x)
    (hgap : ρ₂ x-ρ₁ x ≠ 0) (σ : ℝ) (hσ : 0 < σ) :
    let ν := ρ₁ x-(σ:ℂ)*(ρ₂ x-ρ₁ x)
    let z := fun (y : X) (t : ℝ) => ρ₁ y+(t:ℂ)*(ν-ρ₁ y)
    let D := fun (y : X) (t : ℝ) => (ρ₁ y+ρ₂ y)/2-z y t
    let R := fun (y : X) (t : ℝ) => (ρ₁ y-ν)*(ρ₂ y-z y t)/(D y t)^2
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, ∀ t ∈ Icc (0:ℝ) 1,
      ‖ρ₂ x-ρ₁ x‖/4 < ‖D y t‖ ∧ (σ/(1/2+σ))/2 < (R y t).re := by
  dsimp only
  let ν := ρ₁ x-(σ:ℂ)*(ρ₂ x-ρ₁ x)
  let z := fun (y : X) (t : ℝ) => ρ₁ y+(t:ℂ)*(ν-ρ₁ y)
  let D := fun (y : X) (t : ℝ) => (ρ₁ y+ρ₂ y)/2-z y t
  let R := fun (y : X) (t : ℝ) => (ρ₁ y-ν)*(ρ₂ y-z y t)/(D y t)^2
  change ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, ∀ t ∈ Icc (0:ℝ) 1,
    ‖ρ₂ x-ρ₁ x‖/4 < ‖D y t‖ ∧ (σ/(1/2+σ))/2 < (R y t).re
  have hg : 0 < ‖ρ₂ x-ρ₁ x‖ := norm_pos_iff.mpr hgap
  have hDbase (t : ℝ) : D x t = (((1/2:ℝ)+t*σ:ℝ):ℂ)*(ρ₂ x-ρ₁ x) := by
    dsimp [D,z,ν]
    push_cast
    ring
  have hDlower (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖ρ₂ x-ρ₁ x‖/4 < ‖D x t‖ := by
    have ht0 := ht.1
    rw [hDbase,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (1/2:ℝ)+t*σ)]
    nlinarith [mul_nonneg ht.1 hσ.le]
  have hDne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : D x t ≠ 0 := by
    apply norm_pos_iff.mp
    exact (by positivity : 0 < ‖ρ₂ x-ρ₁ x‖/4).trans (hDlower t ht)
  have hRbase (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      R x t = ((σ*(1+t*σ)/(1/2+t*σ)^2:ℝ):ℂ) :=
    appendixF_endpoint_base_radicand (ρ₁ x) (ρ₂ x) hgap σ t hσ ht.1
  have hRlower (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (σ/(1/2+σ))/2 < (R x t).re := by
    rw [hRbase t ht,Complex.ofReal_re]
    have h := NLS.ComplexAnalysis.appendixF_endpoint_radicand_lower σ t hσ ht
    linarith
  have hDcont (t : ℝ) : ContinuousAt (fun p : X × ℝ => D p.1 p.2) (x,t) := by
    have ha : ContinuousAt (fun p : X × ℝ => ρ₁ p.1) (x,t) := h₁.comp continuousAt_fst
    have hb : ContinuousAt (fun p : X × ℝ => ρ₂ p.1) (x,t) := h₂.comp continuousAt_fst
    have htC : ContinuousAt (fun p : X × ℝ => (p.2:ℂ)) (x,t) :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    exact ((ha.add hb).div_const 2).sub (ha.add (htC.mul (continuousAt_const.sub ha)))
  have hRcont (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ContinuousAt (fun p : X × ℝ => R p.1 p.2) (x,t) := by
    have ha : ContinuousAt (fun p : X × ℝ => ρ₁ p.1) (x,t) := h₁.comp continuousAt_fst
    have hb : ContinuousAt (fun p : X × ℝ => ρ₂ p.1) (x,t) := h₂.comp continuousAt_fst
    have htC : ContinuousAt (fun p : X × ℝ => (p.2:ℂ)) (x,t) :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    exact ((ha.sub continuousAt_const).mul
      (hb.sub (ha.add (htC.mul (continuousAt_const.sub ha))))).div
        ((hDcont t).pow 2) (pow_ne_zero 2 (hDne t ht))
  obtain ⟨V₁,hV₁,hx₁,h₁V⟩ := NLS.ComplexAnalysis.appendixF_local_uniform_lower_bound
    (Icc (0:ℝ) 1) isCompact_Icc x (fun p : X × ℝ => ‖D p.1 p.2‖)
    (‖ρ₂ x-ρ₁ x‖/4) (fun t _ => (hDcont t).norm) hDlower
  obtain ⟨V₂,hV₂,hx₂,h₂V⟩ := NLS.ComplexAnalysis.appendixF_local_uniform_lower_bound
    (Icc (0:ℝ) 1) isCompact_Icc x (fun p : X × ℝ => (R p.1 p.2).re)
    ((σ/(1/2+σ))/2) (fun t ht => Complex.continuous_re.continuousAt.comp (hRcont t ht)) hRlower
  exact ⟨V₁ ∩ V₂,hV₁.inter hV₂,⟨hx₁,hx₂⟩,
    fun y hy t ht => ⟨h₁V y hy.1 t ht,h₂V y hy.2 t ht⟩⟩

/-- On one source neighborhood the denominator and principal-root factor are jointly
continuous, analytic in the source, and bounded away from zero uniformly in t. -/
theorem appendixF_endpoint_uniform_branches
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ₁ ρ₂ : X → ℂ) (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U)
    (h₁ : AnalyticOnNhd ℂ ρ₁ U) (h₂ : AnalyticOnNhd ℂ ρ₂ U)
    (hgap : ρ₂ x-ρ₁ x ≠ 0) (σ : ℝ) (hσ : 0 < σ) :
    let ν := ρ₁ x-(σ:ℂ)*(ρ₂ x-ρ₁ x)
    let z := fun (y : X) (t : ℝ) => ρ₁ y+(t:ℂ)*(ν-ρ₁ y)
    let D := fun (y : X) (t : ℝ) => (ρ₁ y+ρ₂ y)/2-z y t
    let R := fun (y : X) (t : ℝ) => (ρ₁ y-ν)*(ρ₂ y-z y t)/(D y t)^2
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ c : ℝ, 0 < c ∧
      ContinuousOn (fun p : X × ℝ => D p.1 p.2) (V ×ˢ Icc (0:ℝ) 1) ∧
      ContinuousOn (fun p : X × ℝ => Complex.sqrt (R p.1 p.2)) (V ×ˢ Icc (0:ℝ) 1) ∧
      ∀ t ∈ Icc (0:ℝ) 1,
        AnalyticOnNhd ℂ (fun y => D y t) V ∧
        AnalyticOnNhd ℂ (fun y => Complex.sqrt (R y t)) V ∧
        ∀ y ∈ V, c ≤ ‖D y t‖ ∧ c ≤ ‖Complex.sqrt (R y t)‖ := by
  dsimp only
  let ν := ρ₁ x-(σ:ℂ)*(ρ₂ x-ρ₁ x)
  let z := fun (y : X) (t : ℝ) => ρ₁ y+(t:ℂ)*(ν-ρ₁ y)
  let D := fun (y : X) (t : ℝ) => (ρ₁ y+ρ₂ y)/2-z y t
  let R := fun (y : X) (t : ℝ) => (ρ₁ y-ν)*(ρ₂ y-z y t)/(D y t)^2
  obtain ⟨W,hW,hxW,hbound⟩ := appendixF_endpoint_uniform_radicand ρ₁ ρ₂ x
    (h₁ x hx).continuousAt (h₂ x hx).continuousAt hgap σ hσ
  let V := U ∩ W
  let d₀ := ‖ρ₂ x-ρ₁ x‖/4
  let r₀ := (σ/(1/2+σ))/2
  have hd₀ : 0 < d₀ := div_pos (norm_pos_iff.mpr hgap) (by norm_num)
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hB (y : X) (hy : y ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      d₀ < ‖D y t‖ ∧ r₀ < (R y t).re := hbound y hy.2 t ht
  have hDne (y : X) (hy : y ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : D y t ≠ 0 :=
    norm_pos_iff.mp (hd₀.trans (hB y hy t ht).1)
  have hslit (y : X) (hy : y ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      R y t ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (hr₀.trans (hB y hy t ht).2))
  have hDC (y : X) (hy : y ∈ V) (t : ℝ) :
      ContinuousAt (fun p : X × ℝ => D p.1 p.2) (y,t) := by
    have ha : ContinuousAt (fun p : X × ℝ => ρ₁ p.1) (y,t) :=
      (h₁ y hy.1).continuousAt.comp continuousAt_fst
    have hb : ContinuousAt (fun p : X × ℝ => ρ₂ p.1) (y,t) :=
      (h₂ y hy.1).continuousAt.comp continuousAt_fst
    have htC : ContinuousAt (fun p : X × ℝ => (p.2:ℂ)) (y,t) :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    exact ((ha.add hb).div_const 2).sub (ha.add (htC.mul (continuousAt_const.sub ha)))
  have hRC (y : X) (hy : y ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ContinuousAt (fun p : X × ℝ => R p.1 p.2) (y,t) := by
    have ha : ContinuousAt (fun p : X × ℝ => ρ₁ p.1) (y,t) :=
      (h₁ y hy.1).continuousAt.comp continuousAt_fst
    have hb : ContinuousAt (fun p : X × ℝ => ρ₂ p.1) (y,t) :=
      (h₂ y hy.1).continuousAt.comp continuousAt_fst
    have htC : ContinuousAt (fun p : X × ℝ => (p.2:ℂ)) (y,t) :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    exact ((ha.sub continuousAt_const).mul
      (hb.sub (ha.add (htC.mul (continuousAt_const.sub ha))))).div
        ((hDC y hy t).pow 2) (pow_ne_zero 2 (hDne y hy t ht))
  have hDA (y : X) (hy : y ∈ V) (t : ℝ) : AnalyticAt ℂ (fun a => D a t) y :=
    ((h₁ y hy.1).add (h₂ y hy.1)).div_const.sub
      ((h₁ y hy.1).add (analyticAt_const.mul (analyticAt_const.sub (h₁ y hy.1))))
  have hRA (y : X) (hy : y ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      AnalyticAt ℂ (fun a => R a t) y :=
    (((h₁ y hy.1).sub analyticAt_const).mul ((h₂ y hy.1).sub
      ((h₁ y hy.1).add (analyticAt_const.mul (analyticAt_const.sub (h₁ y hy.1)))))).div
        ((hDA y hy t).pow 2) (pow_ne_zero 2 (hDne y hy t ht))
  refine ⟨V,hU.inter hW,⟨hx,hxW⟩,inter_subset_left,
    min d₀ (Real.sqrt r₀),lt_min hd₀ (Real.sqrt_pos.mpr hr₀),?_,?_,?_⟩
  · rintro ⟨y,t⟩ ⟨hy,ht⟩
    exact (hDC y hy t).continuousWithinAt
  · rintro ⟨y,t⟩ ⟨hy,ht⟩
    exact ((Complex.differentiableAt_sqrt (hslit y hy t ht)).continuousAt.comp (f := fun p : X × ℝ => R p.1 p.2)
      (hRC y hy t ht)).continuousWithinAt
  · intro t ht
    refine ⟨fun y hy => hDA y hy t,?_,?_⟩
    · intro y hy
      have hs : AnalyticAt ℂ Complex.sqrt (R y t) :=
        Complex.differentiableOn_sqrt.analyticAt
          (Complex.isOpen_slitPlane.mem_nhds (hslit y hy t ht))
      exact hs.comp (f := fun a => R a t) (hRA y hy t ht)
    · intro y hy
      exact ⟨(min_le_left _ _).trans (hB y hy t ht).1.le,
        (min_le_right _ _).trans (NLS.ComplexAnalysis.appendixF_sqrt_norm_lower
          (R y t) r₀ hr₀.le (hB y hy t ht).2.le)⟩

end NLS.ZakharovShabat
