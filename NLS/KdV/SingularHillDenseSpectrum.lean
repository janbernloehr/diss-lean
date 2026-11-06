import NLS.KdV.SingularHillSpectralProjection

/-! # Spectral persistence and dense parameter comparison for the full operator

Arbitrarily small physical resolvent circles exist by spectral discreteness.
Their nonzero finite projection ranks persist in the full H^-1 potential
norm. A continuous scalar constraint valid on spectra at a dense set of
parameters therefore holds on every actual full-domain spectrum.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem exists_singularHillResolventCircle_small
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (z : ℂ) (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ sphere z r ⊆ singularHillResolventSet q := by
  let A : Set ℂ := {w | w ∈ singularHillSpectrum q ∧ ‖w‖ ≤ ‖z‖+R} \ {z}
  have hA : A.Finite := (finite_singularHillSpectrum_norm_le q (‖z‖+R)).sdiff
  have hz : z ∈ Aᶜ := by simp [A]
  obtain ⟨d,hd,hball⟩ := Metric.isOpen_iff.mp hA.isClosed.isOpen_compl z hz
  let r := min R d/2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : r < R := by have := min_le_left R d; dsimp only [r]; linarith
  have hrd : r < d := by have := min_le_right R d; dsimp only [r]; linarith
  refine ⟨r,hr,hrR,?_⟩
  intro w hw
  by_contra hres
  have hwz : w ≠ z := by
    intro he
    have hh := mem_sphere.mp hw
    rw [he,dist_self] at hh
    linarith
  have hb : ‖w‖ ≤ ‖z‖+R := by
    calc
      ‖w‖ = ‖(w-z)+z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w-z‖+‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖+R := by rw [← dist_eq_norm,mem_sphere.mp hw]; linarith
  have hwA : w ∈ A := ⟨⟨hres,hb⟩,by simpa only [mem_singleton_iff] using hwz⟩
  exact hball (show w ∈ ball z d from (mem_sphere.mp hw).trans_lt hrd) hwA

theorem singularHillRieszProjection_eq_zero_of_closedBall_resolvent
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hball : closedBall c r ⊆ singularHillResolventSet q) : singularHillRieszProjection q c r = 0 := by
  have ha : AnalyticOnNhd ℂ (fun z => -singularHillBaseResolvent q z) (closedBall c r) :=
    fun z hz => (analyticAt_singularHillBaseResolvent q z (hball hz)).neg
  unfold singularHillRieszProjection NLS.CircleIntegral.normalized
  rw [Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
    ha.continuousOn (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt),smul_zero]

theorem singularHillRieszProjection_rank_pos_of_spectrum
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere z r ⊆ singularHillResolventSet q) (hz : z ∈ singularHillSpectrum q) :
    0 < Module.finrank ℂ (singularHillRieszProjection q z r).range := by
  let := finiteDimensional_singularHillRieszProjection_range q z r hr hc
  obtain ⟨f,hf0,hf⟩ := (mem_singularHillSpectrum_iff q z).mp hz
  have hfix := singularHillRieszProjection_eigenvector_inside q z r hr hc z (mem_ball_self hr) f hf
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨singularHillDomainInclusion f,⟨singularHillDomainInclusion f,hfix⟩⟩,?_⟩
  intro he
  apply hf0
  apply singularHillDomainInclusion_injective
  have hh := congrArg Subtype.val he
  simpa only [map_zero,Submodule.coe_zero] using! hh

theorem singularHillSpectrum_constraint_of_dense_parameters
    {T : Type*} [PseudoMetricSpace T]
    (Q : T → FourierLebesgueSpace (2 : ℝ) (-1) 2) (hQ : Continuous Q)
    (F : T → ℂ → ℂ) (hF : Continuous F.uncurry)
    (S : Set T) (hS : Dense S)
    (hzeros : ∀ s ∈ S, ∀ z ∈ singularHillSpectrum (Q s), F s z = 0)
    (t : T) (z : ℂ) (hz : z ∈ singularHillSpectrum (Q t)) : F t z = 0 := by
  by_contra hne
  have hopen : IsOpen {p : T × ℂ | F p.1 p.2 ≠ 0} := isOpen_ne.preimage hF
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hopen (t,z) hne
  obtain ⟨r,hr,hrR,hcircle⟩ := exists_singularHillResolventCircle_small (Q t) z R hR
  have hpos := singularHillRieszProjection_rank_pos_of_spectrum (Q t) z r hr hcircle hz
  have he := hQ.continuousAt.preimage_mem_nhds
    (eventually_singularHillRieszProjection_rank_eq (Q t) z r hr hcircle)
  have hfreq : ∃ᶠ s in 𝓝 t, s ∈ S := mem_closure_iff_frequently.mp (hS t)
  obtain ⟨s,hs,hsR,hscircle,hsrank⟩ :=
    (hfreq.and_eventually ((show ∀ᶠ s in 𝓝 t, s ∈ ball t R from ball_mem_nhds t hR).and he)).exists
  have hres : closedBall z r ⊆ singularHillResolventSet (Q s) := by
    intro w hw
    by_contra hwres
    have hzero := hzeros s hs w hwres
    have hp : (s,w) ∈ ball (t,z) R := by
      rw [mem_ball,Prod.dist_eq,max_lt_iff]
      exact ⟨hsR,(mem_closedBall.mp hw).trans_lt hrR⟩
    exact hball hp hzero
  have hzero := singularHillRieszProjection_eq_zero_of_closedBall_resolvent (Q s) z r hr.le hres
  rw [hzero] at hsrank
  have hleft : Module.finrank ℂ
      ((0 : FourierLebesgueSpace (2 : ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2 : ℝ) (-1) 2).range) = 0 := by
    change Module.finrank ℂ (LinearMap.range
      (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2 →ₗ[ℂ] FourierLebesgueSpace (2 : ℝ) (-1) 2)) = 0
    rw [LinearMap.range_zero,finrank_bot]
  rw [hleft] at hsrank
  omega

end NLS.KdV
