import NLS.ZakharovShabat.SourceDirichletSpectralVectorBound

/-! # Finite endpoint limits of actual Hilbert spectral curves

Uniform speed makes an actual real spectral curve uniformly continuous
in the original complete source space. It therefore has a source-space
limit at both finite endpoints. Closedness of the real form and
continuity of the norm and actual discriminant preserve the conserved
data at these limits. Joining a new local ODE solution to such a limit
is a subsequent continuation step.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- Every point of the closed finite time interval, in particular either
endpoint, has a genuine real Hilbert source limit with the original norm
and every original discriminant value. The assigned values of `γ` at the
endpoints are not assumed to agree with these limits. -/
theorem exists_sourceDirichletSpectral_limit_of_mem_closedInterval
    (k : ℤ) (γ : ℝ → CoeffPair 2) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax 2 (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t)
    (u c : ℝ) (hu : u ∈ Ioo a b) (hc : c ∈ Icc a b) :
    ∃ ψ : CoeffPair 2, Tendsto γ (𝓝[Ioo a b] c) (𝓝 ψ) ∧
      IsRealType (CoeffPair.toMax 2 ψ) ∧ ‖ψ‖ = ‖γ u‖ ∧
      ∀ w : ℂ, canonicalDiscriminant (by simp) (periodOnePotential ψ) w =
        canonicalDiscriminant (by simp) (periodOnePotential (γ u)) w := by
  obtain ⟨C,_,hLip⟩ := exists_lipschitzOnWith_sourceDirichletSpectral_integralCurve
    k γ a b hreal hγ u hu
  have hcl : c ∈ closure (Ioo a b) := by
    rw [closure_Ioo (hu.1.trans hu.2).ne]
    exact hc
  let : NeBot (𝓝[Ioo a b] c) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hCauchy : Cauchy (𝓝[Ioo a b] c) := cauchy_nhds.mono nhdsWithin_le_nhds
  have hmap := hCauchy.map_of_le hLip.uniformContinuousOn
    (le_principal_iff.mpr self_mem_nhdsWithin)
  obtain ⟨ψ,hψ⟩ := cauchy_map_iff_exists_tendsto.mp hmap
  have hrealLimit : IsRealType (CoeffPair.toMax 2 ψ) := by
    apply (isClosed_realTypeSourceLocus (p := 2)).mem_of_tendsto hψ
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t ht
  have hnorm : Tendsto (fun t => ‖γ t‖) (𝓝[Ioo a b] c) (𝓝 ‖γ u‖) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (norm_eq_on_sourceDirichletSpectral_integralCurve k γ a b hreal hγ t u ht hu).symm
  refine ⟨ψ,hψ,hrealLimit,tendsto_nhds_unique hψ.norm hnorm,?_⟩
  intro w
  have hF : ContinuousAt (fun χ : CoeffPair 2 =>
      canonicalDiscriminant (by simp) (periodOnePotential χ) w) ψ :=
    ((analyticOnNhd_canonicalDiscriminant_periodOne (p := 2) (by simp) (by norm_num)
      (w,ψ) (mem_univ _)).comp (f := fun χ : CoeffPair 2 => (w,χ))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  have hconst : Tendsto (fun t => canonicalDiscriminant (by simp) (periodOnePotential (γ t)) w)
      (𝓝[Ioo a b] c) (𝓝 (canonicalDiscriminant (by simp) (periodOnePotential (γ u)) w)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (canonicalDiscriminant_eq_on_sourceDirichletSpectral_integralCurve
      (by simp) (by norm_num) (by norm_num) k γ a b hγ t u ht hu w).symm
  exact tendsto_nhds_unique (hF.tendsto.comp hψ) hconst

end NLS.ZakharovShabat
