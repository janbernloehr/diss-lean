import NLS.Dynamics.PhaseContinuityChoice
import NLS.SequenceSpaces.UniformPhaseExponential
import NLS.ZakharovShabat.SourceSection22PhaseEstimate
import NLS.ZakharovShabat.SourceFrequencyMixedIntroduction
import NLS.ZakharovShabat.SourceBirkhoffInverseChart

/-! # Uniform Section 22 estimates for the original Birkhoff family

The cutoff and time increment retain the original frequencies and pair
norm. One complex source neighborhood carries a mixed exponential bound.
An actual complex inverse chart transports the frequency and exponential
bounds, together with full trajectory analyticity, to one coordinate
neighborhood chosen before every compact time horizon.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- On one complex neighborhood containing all real sources, every point
has a source neighborhood independent of the time horizon. The exponential
error admits a fixed p/2 plus OnePlus decomposition on each compact interval. -/
theorem exists_phase_error_mixed_neighborhood :
    ∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ U ∧
      ∀ φ ∈ Y, ∃ V' : Set (CoeffPair p), IsOpen V' ∧ φ ∈ V' ∧ V' ⊆ Y ∧
        ∀ R : ℝ, 0 ≤ R →
          ∃ g : ℝ × CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)),
          ∃ h : ℝ × CoeffPair p → CoeffOnePlus,
            (∀ x ∈ Icc (-R) R ×ˢ V', ∀ n,
              Complex.exp ((x.1 : ℂ)*Complex.I*A.renormalizedFrequency n x.2)-1 =
                g x n+(h x).1 n) ∧
            (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-R) R ×ˢ V', ‖g x‖ ≤ C) ∧
            ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
              ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-R) R ×ˢ V',
                ‖CoeffOnePlus.toCoeff q hq1 hq (h x)‖ ≤ C := by
  obtain ⟨Y₀,hY₀,_,hreal,_,_,hlocal⟩ :=
    A.exists_frequencySequence_neighborhood Q.roots D.roots_open D.roots_real_subset
  let Y := Y₀ ∩ U
  have hY : IsOpen Y := hY₀.inter Q.source_open
  refine ⟨Y,hY,fun φ hφ => ⟨hreal hφ,Q.real_subset hφ⟩,inter_subset_right,?_⟩
  intro φ hφ
  obtain ⟨V',hV,hφV,_,hb⟩ := hlocal φ hφ.1
  refine ⟨V' ∩ Y,hV.inter hY,⟨hφV,hφ⟩,inter_subset_right,?_⟩
  intro R hR
  apply Coeff.exists_uniform_phase_error_onePlus_decomposition (V' ∩ Y)
    (fun ψ n => A.renormalizedFrequency n ψ) ENNReal.ofReal_ne_top ?_ R hR
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨C,hC,hb⟩ := hb r hr hr1 hpr
  exact ⟨C,hC,fun ψ hψ => ⟨A.frequencySequence r ψ,(hb ψ hψ.1).1,(hb ψ hψ.1).2⟩⟩

end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The original coordinate trajectory has one symmetric cutoff and one
positive time increment before all compact horizons and all time origins.
This is a coordinate estimate and does not assert global source inversion. -/
theorem exists_hamiltonian_phase_continuity_cutoff (φ : realTypeSourceSubmodule p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ δ : ℝ, 0 < δ ∧
      ((2 : ℝ) ^ p.toReal * ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) N},
        (‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 n.val‖ ^ p.toReal+
          ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).2 n.val‖ ^ p.toReal) ≤ ε ^ p.toReal) ∧
      ∀ T : ℝ, ∀ t u : Icc (-T) T, |t.val-u.val| < δ →
        (∀ n ∈ Finset.Icc (-(N : ℤ)) N,
          ‖Complex.exp ((((t.val-u.val)*A.phaseFrequency φ n : ℝ) : ℂ)*Complex.I)-1‖ *
            ‖(CoeffPair.toMax p).symm (sourceComplexBirkhoffMap hp hp1 s φ.val)‖ ≤ ε) ∧
        ‖(CoeffPair.toMax p).symm (A.hamiltonianComplexPhaseTrajectoryOn T φ.val t-
          A.hamiltonianComplexPhaseTrajectoryOn T φ.val u)‖ ≤ 2*ε := by
  obtain ⟨N,hN,δ,hδ,htail,hbound⟩ := Birkhoff.exists_symmetric_phase_continuity_estimate hp
    (A.phaseFrequency φ) (sourceComplexBirkhoffMap hp hp1 s φ.val) ε hε
  refine ⟨N,hN,δ,hδ,htail,?_⟩
  intro T t u htu
  rw [Q.hamiltonian_phase_real T φ t,Q.hamiltonian_phase_real T φ u]
  exact hbound t.val u.val htu

end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The original full trajectory is bounded by its initial amplitude and the
bounded frequency correction; no estimate uses the unbounded free lattice. -/
theorem norm_hamiltonian_phase_trajectory_le (R C : ℝ) (hR : 0 ≤ R)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hb : ∀ n, ‖A.renormalizedFrequency n ψ‖ ≤ C) :
    ‖A.hamiltonianComplexPhaseTrajectoryOn R ψ‖ ≤
      Real.exp (R*C)*‖sourceComplexBirkhoffMap hp hp1 s ψ‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro t
  apply Coeff.norm_pair_le_of_apply_le _ _ _ (Real.exp_pos _).le
  intro n
  obtain ⟨he₁,he₂⟩ := Q.hamiltonian_phase_coordinates R ψ hψ t n
  rw [he₁,he₂]
  have hfreq : (((2*Real.pi*n)^2 : ℝ) : ℂ) = (2*(Real.pi : ℂ)*n)^2 := by
    simp only [Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_intCast]
  have ht : |t.val| ≤ R := abs_le.mpr t.property
  constructor
  · rw [← hfreq,← Complex.ofReal_neg]
    exact Coeff.norm_complex_phase_mul_le
      ((2*Real.pi*n)^2) (-t.val) R C (A.renormalizedFrequency n ψ)
      ((sourceComplexBirkhoffMap hp hp1 s ψ).1 n) hR (by simpa only [abs_neg] using ht) (hb n)
  · rw [← hfreq]
    exact Coeff.norm_complex_phase_mul_le
      ((2*Real.pi*n)^2) t.val R C (A.renormalizedFrequency n ψ)
      ((sourceComplexBirkhoffMap hp hp1 s ψ).2 n) hR ht (hb n)

end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.ZakharovShabat.SourceSection20Data
open Filter Topology
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- One actual complex coordinate neighborhood carries the original inverse,
the uniform mixed frequency and exponential bounds, and full trajectory
analyticity, before choosing the compact time horizon. -/
theorem exists_complex_coordinate_phase_neighborhood (φ : realTypeSourceSubmodule p) :
    ∃ V' : Set (Coeff p × Coeff p), IsOpen V' ∧
      sourceComplexBirkhoffMap hp hp1 s φ.val ∈ V' ∧
      ∃ χ : (Coeff p × Coeff p) → CoeffPair p,
        AnalyticOnNhd ℂ χ V' ∧ MapsTo χ V' U ∧
        χ (sourceComplexBirkhoffMap hp hp1 s φ.val) = φ.val ∧
        (∀ z ∈ V', sourceComplexBirkhoffMap hp hp1 s (χ z) = z) ∧
        (∀ T : ℝ, AnalyticOnNhd ℂ
          (fun z => A.hamiltonianComplexPhaseTrajectoryOn T (χ z)) V') ∧
        (∃ a : (Coeff p × Coeff p) → Coeff (ENNReal.ofReal (p.toReal/2)),
          ∃ b : (Coeff p × Coeff p) → CoeffOnePlus,
            (∀ z ∈ V', ∀ n, A.renormalizedFrequency n (χ z) = a z n+(b z).1 n) ∧
            (∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ V', ‖a z‖ ≤ C) ∧
            ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
              ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ V', ‖CoeffOnePlus.toCoeff q hq1 hq (b z)‖ ≤ C) ∧
        (∀ R : ℝ, 0 ≤ R →
          ∃ g : ℝ × (Coeff p × Coeff p) → Coeff (ENNReal.ofReal (p.toReal/2)),
          ∃ h : ℝ × (Coeff p × Coeff p) → CoeffOnePlus,
            (∀ x ∈ Icc (-R) R ×ˢ V', ∀ n,
              Complex.exp ((x.1 : ℂ)*Complex.I*A.renormalizedFrequency n (χ x.2))-1 =
                g x n+(h x).1 n) ∧
            (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-R) R ×ˢ V', ‖g x‖ ≤ C) ∧
            ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
              ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-R) R ×ˢ V',
                ‖CoeffOnePlus.toCoeff q hq1 hq (h x)‖ ≤ C) ∧
        ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ R : ℝ, 0 ≤ R → ∀ z ∈ V',
          ‖A.hamiltonianComplexPhaseTrajectoryOn R (χ z)‖ ≤ Real.exp (R*C)*M := by
  obtain ⟨Y,_,hr,_,he⟩ := Q.exists_phase_error_mixed_neighborhood
  obtain ⟨Ve,hVe,hφe,_,he⟩ := he φ.val (hr φ.property)
  obtain ⟨Vf,hVf,hφf,hfU,a,b,hab,ha,hb⟩ := Q.frequency_mixed_at_real φ
  let K := ‖A.boundedPhaseCorrection φ.val‖+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbnd : ∀ᶠ ψ in 𝓝 φ.val, ‖A.boundedPhaseCorrection ψ‖ < K :=
    ((Q.bounded_phase_correction.1 φ.val (Q.real_subset φ.property)).continuousAt.norm).eventually
      (gt_mem_nhds (by dsimp [K]; linarith))
  obtain ⟨Vb,hbnd,hVb,hφb⟩ := mem_nhds_iff.mp hbnd
  obtain ⟨C⟩ := D.complex.exists_inverseChart φ ((Vf ∩ Ve) ∩ Vb)
    ((hVf.inter hVe).inter hVb) ⟨⟨hφf,hφe⟩,hφb⟩
  let L := Birkhoff.rectangularToComplex (p := p)
  let z₀ := sourceComplexBirkhoffMap hp hp1 s φ.val
  let V' := (L.symm ⁻¹' C.target) ∩ Metric.ball z₀ 1
  let χ := fun z => C.inverse (L.symm z)
  have hχf (z) (hz : z ∈ V') : χ z ∈ Vf := (C.image_subset hz.1).2.1.1
  have hχe (z) (hz : z ∈ V') : χ z ∈ Ve := (C.image_subset hz.1).2.1.2
  have hχU : MapsTo χ V' U := fun z hz => hfU (hχf z hz)
  have hχa : AnalyticOnNhd ℂ χ V' := fun z hz =>
    (C.analytic _ hz.1).comp (L.symm.toContinuousLinearMap.analyticAt z)
  refine ⟨V',(C.target_open.preimage L.symm.continuous).inter Metric.isOpen_ball,
    ?_,χ,hχa,hχU,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,Metric.mem_ball_self (by norm_num)⟩
    change L.symm (L (sourceBirkhoffMap hp hp1 s φ.val)) ∈ C.target
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using C.center_mem
  · change C.inverse (L.symm (L (sourceBirkhoffMap hp hp1 s φ.val))) = φ.val
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using C.base_eq
  · intro z hz
    change L (sourceBirkhoffMap hp hp1 s (C.inverse (L.symm z))) = z
    rw [C.right_inverse _ hz.1,L.apply_symm_apply]
  · intro T z hz
    exact (Q.hamiltonian_phase_analytic T _ (hχU hz)).comp (hχa z hz)
  · refine ⟨fun z => a (χ z),fun z => b (χ z),fun z hz n => hab _ (hχf z hz) n,?_,?_⟩
    · obtain ⟨K,hK,hbound⟩ := ha
      exact ⟨K,hK,fun z hz => hbound _ (hχf z hz)⟩
    · intro q hq1 hq
      obtain ⟨K,hK,hbound⟩ := hb q hq1 hq
      exact ⟨K,hK,fun z hz => hbound _ (hχf z hz)⟩
  · intro R hR
    obtain ⟨g,h,hgh,hg,hh⟩ := he R hR
    let F : ℝ × (Coeff p × Coeff p) → ℝ × CoeffPair p := fun x => (x.1,χ x.2)
    have hF : MapsTo F (Icc (-R) R ×ˢ V') (Icc (-R) R ×ˢ Ve) :=
      fun x hx => ⟨hx.1,hχe _ hx.2⟩
    refine ⟨g ∘ F,h ∘ F,?_,?_,?_⟩
    · intro x hx n
      exact hgh (F x) (hF hx) n
    · obtain ⟨K,hK,hbound⟩ := hg
      exact ⟨K,hK,fun x hx => hbound (F x) (hF hx)⟩
    · intro q hq1 hq
      obtain ⟨K,hK,hbound⟩ := hh q hq1 hq
      exact ⟨K,hK,fun x hx => hbound (F x) (hF hx)⟩

  · refine ⟨K,‖z₀‖+1,hK,by positivity,?_⟩
    intro R hR z hz
    have hχbound : ∀ n, ‖A.renormalizedFrequency n (χ z)‖ ≤ K := by
      intro n
      rw [← Q.bounded_phase_correction.2 (χ z) (hχU hz) n]
      exact (lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0)
        (A.boundedPhaseCorrection (χ z)) n).trans (hbnd (C.image_subset hz.1).2.2).le
    have hinit : sourceComplexBirkhoffMap hp hp1 s (χ z) = z := by
      change L (sourceBirkhoffMap hp hp1 s (C.inverse (L.symm z))) = z
      rw [C.right_inverse _ hz.1,L.apply_symm_apply]
    have hzbound : ‖z‖ ≤ ‖z₀‖+1 := by
      have hd : ‖z-z₀‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz.2
      calc
        ‖z‖ = ‖(z-z₀)+z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖z-z₀‖+‖z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖+1 := by linarith
    calc
      _ ≤ Real.exp (R*K)*‖sourceComplexBirkhoffMap hp hp1 s (χ z)‖ :=
        Q.norm_hamiltonian_phase_trajectory_le R K hR (χ z) (hχU hz) hχbound
      _ ≤ Real.exp (R*K)*(‖z₀‖+1) := by
        rw [hinit]
        exact mul_le_mul_of_nonneg_left hzbound (Real.exp_pos _).le

end NLS.ZakharovShabat.SourceSection20Data
