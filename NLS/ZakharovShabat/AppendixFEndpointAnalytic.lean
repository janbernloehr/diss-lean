import NLS.ZakharovShabat.AppendixFUniformRadicand
import NLS.ComplexAnalysis.AppendixFWeightedIntegral

/-! # Analyticity of the literal endpoint-spoke integral in F.2

Analytic endpoint branches and a regular factor analytic along the path
give analyticity of the normalized-root integral on one source neighborhood.
-/
noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace NLS.ZakharovShabat

/-- The endpoint-spoke integrand is the regular factor times the inverse-square-root
weight, with the actual normalized-root branch retained. -/
theorem appendixF_endpoint_integrand_weight (ρ₁ ρ₂ ν a χ : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    let τ := (ρ₁+ρ₂)/2
    let z := ρ₁+(t:ℂ)*(ν-ρ₁)
    (a-z)/normalizedStandardRoot τ ((ρ₂-ρ₁)^2) z*χ =
      ((a-z)/(τ-z)*χ/Complex.sqrt ((ρ₁-ν)*(ρ₂-z)/(τ-z)^2))/(Real.sqrt t:ℂ) := by
  dsimp only
  rw [appendixF_normalized_root_on_endpoint_spoke ρ₁ ρ₂ ν t ht]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The literal normalized-root endpoint-spoke integral is analytic near a noncollapsed
complex source. Regular-factor analyticity is required only along the actual paths. -/
theorem appendixF_endpoint_integral_analytic
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ₁ ρ₂ a : X → ℂ) (χ : ℂ × X → ℂ)
    (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U)
    (h₁ : AnalyticOnNhd ℂ ρ₁ U) (h₂ : AnalyticOnNhd ℂ ρ₂ U)
    (ha : AnalyticOnNhd ℂ a U) (hgap : ρ₂ x-ρ₁ x ≠ 0) (σ : ℝ) (hσ : 0 < σ)
    (hχ : ∀ y ∈ U, ∀ t ∈ Icc (0:ℝ) 1,
      AnalyticAt ℂ χ (ρ₁ y+(t:ℂ)*(ρ₁ x-(σ:ℂ)*(ρ₂ x-ρ₁ x)-ρ₁ y),y)) :
    let ν := ρ₁ x-(σ:ℂ)*(ρ₂ x-ρ₁ x)
    let z := fun (y : X) (t : ℝ) => ρ₁ y+(t:ℂ)*(ν-ρ₁ y)
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      (∀ y ∈ V, IntervalIntegrable (fun t => (a y-z y t)/
        normalizedStandardRoot ((ρ₁ y+ρ₂ y)/2) ((ρ₂ y-ρ₁ y)^2) (z y t)*χ (z y t,y)) volume 0 1) ∧
      AnalyticOnNhd ℂ (fun y => -Complex.I*(ν-ρ₁ y)*
        (∫ t in (0:ℝ)..1, (a y-z y t)/
          normalizedStandardRoot ((ρ₁ y+ρ₂ y)/2) ((ρ₂ y-ρ₁ y)^2) (z y t)*χ (z y t,y))) V := by
  dsimp only
  let ν := ρ₁ x-(σ:ℂ)*(ρ₂ x-ρ₁ x)
  let Z : ℂ × X → ℂ := fun p => ρ₁ p.2+p.1*(ν-ρ₁ p.2)
  let D : ℂ × X → ℂ := fun p => (ρ₁ p.2+ρ₂ p.2)/2-Z p
  let R : ℂ × X → ℂ := fun p => (ρ₁ p.2-ν)*(ρ₂ p.2-Z p)/(D p)^2
  let G : ℂ × X → ℂ := fun p => (a p.2-Z p)/D p*χ (Z p,p.2)/Complex.sqrt (R p)
  obtain ⟨W,hW,hxW,hbound⟩ := appendixF_endpoint_uniform_radicand ρ₁ ρ₂ x
    (h₁ x hx).continuousAt (h₂ x hx).continuousAt hgap σ hσ
  let V := U ∩ W
  have hV : IsOpen V := hU.inter hW
  have hGA (y : X) (hy : y ∈ V) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      AnalyticAt ℂ G ((t:ℂ),y) := by
    have hB := hbound y hy.2 t ht
    have hd : D ((t:ℂ),y) ≠ 0 := norm_pos_iff.mp
      ((div_pos (norm_pos_iff.mpr hgap) (by norm_num : (0:ℝ)<4)).trans hB.1)
    have hr : 0 < (R ((t:ℂ),y)).re :=
      (by positivity : 0 < (σ/(1/2+σ))/2).trans hB.2
    have hslit : R ((t:ℂ),y) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl hr)
    have hsne : Complex.sqrt (R ((t:ℂ),y)) ≠ 0 := by
      apply norm_pos_iff.mp
      exact (Real.sqrt_pos.mpr hr).trans_le
        (NLS.ComplexAnalysis.appendixF_sqrt_norm_lower _ _ hr.le le_rfl)
    have hA₁ : AnalyticAt ℂ (fun p : ℂ × X => ρ₁ p.2) ((t:ℂ),y) :=
      (h₁ y hy.1).comp analyticAt_snd
    have hA₂ : AnalyticAt ℂ (fun p : ℂ × X => ρ₂ p.2) ((t:ℂ),y) :=
      (h₂ y hy.1).comp analyticAt_snd
    have hAZ : AnalyticAt ℂ Z ((t:ℂ),y) :=
      hA₁.add (analyticAt_fst.mul (analyticAt_const.sub hA₁))
    have hAD : AnalyticAt ℂ D ((t:ℂ),y) := (hA₁.add hA₂).div_const.sub hAZ
    have hAR : AnalyticAt ℂ R ((t:ℂ),y) :=
      ((hA₁.sub analyticAt_const).mul (hA₂.sub hAZ)).div (hAD.pow 2) (pow_ne_zero 2 hd)
    have hAS : AnalyticAt ℂ (fun p => Complex.sqrt (R p)) ((t:ℂ),y) :=
      (Complex.differentiableOn_sqrt.analyticAt
        (Complex.isOpen_slitPlane.mem_nhds hslit)).comp (f := R) hAR
    have hAX : AnalyticAt ℂ (fun p : ℂ × X => χ (Z p,p.2)) ((t:ℂ),y) :=
      (hχ y hy.1 t ht).comp (f := fun p : ℂ × X => (Z p,p.2))
        (hAZ.prod analyticAt_snd)
    have hAa : AnalyticAt ℂ (fun p : ℂ × X => a p.2) ((t:ℂ),y) :=
      (ha y hy.1).comp analyticAt_snd
    exact (((hAa.sub hAZ).div hAD hd).mul hAX).div hAS hsne
  have hI := NLS.ComplexAnalysis.appendixF_inverse_sqrt_integral_analytic G
    {p | AnalyticAt ℂ G p} (isOpen_analyticAt ℂ G) (fun _ hp => hp) V hV hGA
  have hpoint (y : X) (t : ℝ) (ht : 0 ≤ t) :
      (a y-Z ((t:ℂ),y))/normalizedStandardRoot ((ρ₁ y+ρ₂ y)/2)
          ((ρ₂ y-ρ₁ y)^2) (Z ((t:ℂ),y))*χ (Z ((t:ℂ),y),y) =
        G ((t:ℂ),y)/(Real.sqrt t:ℂ) :=
    appendixF_endpoint_integrand_weight (ρ₁ y) (ρ₂ y) ν (a y) (χ (Z ((t:ℂ),y),y)) t ht
  have hint (y : X) (hy : y ∈ V) : IntervalIntegrable (fun t =>
      (a y-Z ((t:ℂ),y))/normalizedStandardRoot ((ρ₁ y+ρ₂ y)/2)
        ((ρ₂ y-ρ₁ y)^2) (Z ((t:ℂ),y))*χ (Z ((t:ℂ),y),y)) volume 0 1 := by
    have hcont : ContinuousOn (fun t : ℝ => G ((t:ℂ),y)) (Icc (0:ℝ) 1) := by
      intro t ht
      exact ((hGA y hy t ht).continuousAt.comp (f := fun s : ℝ => ((s:ℂ),y))
        (Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const)).continuousWithinAt
    apply (NLS.ComplexAnalysis.appendixF_inverse_sqrt_intervalIntegrable _ hcont).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Ioc (0:ℝ) 1 := by simpa using ht
    exact (hpoint y t ht'.1.le).symm
  refine ⟨V,hV,⟨hx,hxW⟩,inter_subset_left,hint,?_⟩
  have heq (y : X) : (∫ t in (0:ℝ)..1, (a y-Z ((t:ℂ),y))/
      normalizedStandardRoot ((ρ₁ y+ρ₂ y)/2) ((ρ₂ y-ρ₁ y)^2) (Z ((t:ℂ),y))*χ (Z ((t:ℂ),y),y)) =
      ∫ t in (0:ℝ)..1, G ((t:ℂ),y)/(Real.sqrt t:ℂ) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall fun t ht => hpoint y t
        (by
          have ht' : t ∈ Ioc (0:ℝ) 1 := by simpa using ht
          exact ht'.1.le)
  intro y hy
  apply ((analyticAt_const.mul (analyticAt_const.sub (h₁ y hy.1))).mul (hI y hy)).congr
  exact Filter.Eventually.of_forall fun b => congrArg (fun v => -Complex.I*(ν-ρ₁ b)*v) (heq b).symm

end NLS.ZakharovShabat
