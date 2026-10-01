import NLS.FunctionalAnalysis.IntegralCurveJoin
import NLS.ZakharovShabat.SourceDirichletSpectralEndpointLimit

/-! # Actual continuation past finite Hilbert spectral endpoints

The source-space endpoint limit is real. Picard-Lindelof constructs a
new local actual solution through it, and the boundary differentiability
argument joins this solution to the old curve. The resulting curve agrees
with the old one throughout its original interval and solves the actual
indexed source equation at the joining time as well.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.Poisson NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- An actual real local Hilbert spectral curve can be started at any
real time, using the already constructed local solution through its source. -/
theorem exists_sourceDirichletSpectral_integralCurve_at_time
    (k : ℤ) (φ : realTypeSourceLocus 2) (c : ℝ) :
    ∃ η : ℝ → CoeffPair 2, η c = φ.val ∧
      (∀ t : ℝ, IsRealType (CoeffPair.toMax 2 (η t))) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (c-ε) (c+ε), HasDerivAt η
        (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (η t)) t := by
  obtain ⟨γ,h0,hreal,ε,hε,hder,_,_⟩ :=
    exists_sourceDirichletSpectral_norm_conserved_integralCurve k φ
  let η : ℝ → CoeffPair 2 := fun t => γ (t-c)
  refine ⟨η,by simpa [η] using h0,fun t => hreal (t-c),ε,hε,?_⟩
  intro t ht
  have ht' : t-c ∈ Ioo (-ε) ε := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hshift : HasDerivAt (fun s : ℝ => s-c) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const c
  have h := HasDerivAt.scomp (h := fun s : ℝ => s-c) t (hder (t-c) ht') hshift
  simpa only [Function.comp_def,one_smul] using h

/-- Every real actual indexed Hilbert curve on a nonempty finite interval
extends past its right endpoint, agreeing with the original curve at every
original interior time. Its ODE holds at the old endpoint too. -/
theorem exists_sourceDirichletSpectral_rightContinuation
    (k : ℤ) (γ : ℝ → CoeffPair 2) (a b : ℝ) (hab : a < b)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax 2 (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Γ : ℝ → CoeffPair 2,
      EqOn Γ γ (Ioo a b) ∧
      (∀ t ∈ Ioo a (b+ε), IsRealType (CoeffPair.toMax 2 (Γ t))) ∧
      ∀ t ∈ Ioo a (b+ε), HasDerivAt Γ
        (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (Γ t)) t := by
  let u : ℝ := (a+b)/2
  have hu : u ∈ Ioo a b := ⟨by dsimp [u]; linarith,by dsimp [u]; linarith⟩
  obtain ⟨ψ,hlim,hψ,_,_⟩ := exists_sourceDirichletSpectral_limit_of_mem_closedInterval
    k γ a b hreal hγ u b hu ⟨hab.le,le_rfl⟩
  obtain ⟨η,hηb,hηreal,ε,hε,hηder⟩ :=
    exists_sourceDirichletSpectral_integralCurve_at_time k ⟨ψ,hψ⟩ b
  let Γ := joinIntegralCurve b ψ γ η
  have hηlim : Tendsto η (𝓝[Ioo b (b+ε)] b) (𝓝 ψ) := by
    have h := (hηder b ⟨by linarith,by linarith⟩).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Ioo b (b+ε)] b ≤ 𝓝 b)
    simpa only [hηb] using h
  have hV : ContinuousAt
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k) ψ :=
    (analyticAt_sourceDirichletSpectralVector_of_realType
      (by simp) (by norm_num) (by norm_num) k ⟨ψ,hψ⟩).continuousAt
  have hder : ∀ t ∈ Ioo a (b+ε), HasDerivAt Γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (Γ t)) t := by
    apply hasDerivAt_joinIntegralCurve _ γ η ψ a b (b+ε) hab (by linarith) hγ
      (fun t ht => hηder t ⟨by linarith [ht.1],ht.2⟩) hlim hηlim hV
  refine ⟨ε,hε,Γ,?_,?_,hder⟩
  · intro t ht
    exact joinIntegralCurve_of_lt b ψ γ η ht.2
  · intro t ht
    rcases lt_trichotomy t b with htb | rfl | hbt
    · rw [show Γ t = γ t from joinIntegralCurve_of_lt b ψ γ η htb]
      exact hreal t ⟨ht.1,htb⟩
    · simpa only [Γ,joinIntegralCurve_at] using hψ
    · rw [show Γ t = η t from joinIntegralCurve_of_gt b ψ γ η hbt]
      exact hηreal t

/-- Every real actual indexed Hilbert curve extends past its left
endpoint as well, with the actual ODE valid at the old endpoint. -/
theorem exists_sourceDirichletSpectral_leftContinuation
    (k : ℤ) (γ : ℝ → CoeffPair 2) (a b : ℝ) (hab : a < b)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax 2 (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Γ : ℝ → CoeffPair 2,
      EqOn Γ γ (Ioo a b) ∧
      (∀ t ∈ Ioo (a-ε) b, IsRealType (CoeffPair.toMax 2 (Γ t))) ∧
      ∀ t ∈ Ioo (a-ε) b, HasDerivAt Γ
        (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (Γ t)) t := by
  let u : ℝ := (a+b)/2
  have hu : u ∈ Ioo a b := ⟨by dsimp [u]; linarith,by dsimp [u]; linarith⟩
  obtain ⟨ψ,hlim,hψ,_,_⟩ := exists_sourceDirichletSpectral_limit_of_mem_closedInterval
    k γ a b hreal hγ u a hu ⟨le_rfl,hab.le⟩
  obtain ⟨η,hηa,hηreal,ε,hε,hηder⟩ :=
    exists_sourceDirichletSpectral_integralCurve_at_time k ⟨ψ,hψ⟩ a
  let Γ := joinIntegralCurve a ψ η γ
  have hηlim : Tendsto η (𝓝[Ioo (a-ε) a] a) (𝓝 ψ) := by
    have h := (hηder a ⟨by linarith,by linarith⟩).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Ioo (a-ε) a] a ≤ 𝓝 a)
    simpa only [hηa] using h
  have hV : ContinuousAt
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k) ψ :=
    (analyticAt_sourceDirichletSpectralVector_of_realType
      (by simp) (by norm_num) (by norm_num) k ⟨ψ,hψ⟩).continuousAt
  have hder : ∀ t ∈ Ioo (a-ε) b, HasDerivAt Γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (Γ t)) t := by
    apply hasDerivAt_joinIntegralCurve _ η γ ψ (a-ε) a b (by linarith) hab
      (fun t ht => hηder t ⟨ht.1,by linarith [ht.2]⟩) hγ hηlim hlim hV
  refine ⟨ε,hε,Γ,?_,?_,hder⟩
  · intro t ht
    exact joinIntegralCurve_of_gt a ψ η γ ht.1
  · intro t ht
    rcases lt_trichotomy t a with hta | rfl | hat
    · rw [show Γ t = η t from joinIntegralCurve_of_lt a ψ η γ hta]
      exact hηreal t
    · simpa only [Γ,joinIntegralCurve_at] using hψ
    · rw [show Γ t = γ t from joinIntegralCurve_of_gt a ψ η γ hat]
      exact hreal t ⟨hat,ht.2⟩

/-- Both finite endpoints can be passed in one actual real extension.
The new curve agrees on the entire old interval and preserves the
original source norm and every discriminant value throughout the larger
interval, including at both joining times. -/
theorem exists_sourceDirichletSpectral_twoSidedContinuation
    (k : ℤ) (γ : ℝ → CoeffPair 2) (a b : ℝ) (hab : a < b)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax 2 (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Γ : ℝ → CoeffPair 2,
      EqOn Γ γ (Ioo a b) ∧
      (∀ t ∈ Ioo (a-δ) (b+ε), IsRealType (CoeffPair.toMax 2 (Γ t))) ∧
      (∀ t ∈ Ioo (a-δ) (b+ε), HasDerivAt Γ
        (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (Γ t)) t) ∧
      ∀ u ∈ Ioo a b, ∀ t ∈ Ioo (a-δ) (b+ε), ‖Γ t‖ = ‖γ u‖ ∧
        ∀ w : ℂ, canonicalDiscriminant (by simp) (periodOnePotential (Γ t)) w =
          canonicalDiscriminant (by simp) (periodOnePotential (γ u)) w := by
  obtain ⟨ε,hε,Γ₁,hEq₁,hreal₁,hder₁⟩ :=
    exists_sourceDirichletSpectral_rightContinuation k γ a b hab hreal hγ
  obtain ⟨δ,hδ,Γ,hEq₂,hreal₂,hder₂⟩ :=
    exists_sourceDirichletSpectral_leftContinuation k Γ₁ a (b+ε)
      (by linarith) hreal₁ hder₁
  have hEq : EqOn Γ γ (Ioo a b) := by
    intro t ht
    exact (hEq₂ ⟨ht.1,by linarith [ht.2]⟩).trans (hEq₁ ht)
  refine ⟨δ,hδ,ε,hε,Γ,hEq,hreal₂,hder₂,?_⟩
  intro u hu t ht
  have hu' : u ∈ Ioo (a-δ) (b+ε) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  constructor
  · simpa only [hEq hu] using norm_eq_on_sourceDirichletSpectral_integralCurve
      k Γ (a-δ) (b+ε) hreal₂ hder₂ t u ht hu'
  · intro w
    simpa only [hEq hu] using canonicalDiscriminant_eq_on_sourceDirichletSpectral_integralCurve
      (by simp) (by norm_num) (by norm_num) k Γ (a-δ) (b+ε) hder₂ t u ht hu' w

end NLS.ZakharovShabat
