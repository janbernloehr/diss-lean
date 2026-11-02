import NLS.KdV.ClassicalHighCriticalPoints
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Banach analytic actual Hill critical displacement tails

The high frequency critical displacements form an actual ℓ² map, analytic
on a single complex potential neighborhood. At zero the tail is zero, so
its whole ℓ² norm is uniformly small on a common neighborhood of zero.
This is a norm assertion about the infinite sequence, not just separate
continuity or analyticity of its coordinates.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

private def classicalHillCriticalDisplacement (q : NLS.LinearVolterra.Curve ℂ) : Coeff 2 :=
  canonicalCriticalDisplacement (by simp) (by norm_num) (classicalHillCoefficientPotential q)
    (classicalHillCoefficientPotential_even q)

/-- Positive high-frequency critical displacement, with the finite head zeroed. -/
def classicalHillCriticalFrequencyTail (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) : Coeff 2 :=
  ⟨fun k : ℤ => if (N : ℤ) < k then classicalHillCriticalDisplacement q k else 0,
    (lp.memℓp (classicalHillCriticalDisplacement q)).mono' (fun k => by
      split_ifs
      · exact le_refl _
      · simpa only [norm_zero] using norm_nonneg (classicalHillCriticalDisplacement q k))⟩

theorem classicalHillCriticalFrequencyTail_apply (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) (k : ℤ) :
    classicalHillCriticalFrequencyTail N q k = if (N : ℤ) < k then
      canonicalCriticalPoints (by simp) (by norm_num) (classicalHillCoefficientPotential q)
        (classicalHillCoefficientPotential_even q) k-(Real.pi : ℂ)*k else 0 := rfl

private theorem norm_classicalHillCriticalFrequencyTail_le (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) :
    ‖classicalHillCriticalFrequencyTail N q‖ ≤ ‖classicalHillCriticalDisplacement q‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro k
  change ‖if (N : ℤ) < k then classicalHillCriticalDisplacement q k else 0‖ ≤ _
  split_ifs
  · exact le_refl _
  · simpa only [norm_zero] using norm_nonneg (classicalHillCriticalDisplacement q k)

/-- On one neighborhood of every complex continuous potential, the actual
infinite tail is Banach analytic and norm bounded, with a common valid labeling. -/
theorem exists_analytic_classicalHillCriticalFrequencyTail (q0 : NLS.LinearVolterra.Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), ∃ R : ℝ,
      0 < N ∧ IsOpen V ∧ q0 ∈ V ∧ 0 ≤ R ∧
      AnalyticOnNhd ℂ (classicalHillCriticalFrequencyTail N) V ∧
      ∀ q ∈ V, ‖classicalHillCriticalFrequencyTail N q‖ ≤ R ∧
        CriticalPointLabeling (by simp) (by norm_num) (classicalHillCoefficientPotential q)
          (classicalHillCoefficientPotential_even q) N
          (canonicalCriticalPoints (by simp) (by norm_num) (classicalHillCoefficientPotential q)
            (classicalHillCoefficientPotential_even q)) := by
  obtain ⟨Nh,Wh,hNh,hWh,hqh,hhigh⟩ := exists_analytic_classicalHillHighCriticalPoints q0
  obtain ⟨Nl,hNl,Ul,hUl,_,hql,_,R,hR,hlabel⟩ :=
    exists_uniform_canonicalCriticalPoints (by simp) (by norm_num) (classicalHillCoefficientPotential q0)
  let N := max Nh Nl
  let V := Wh ∩ (classicalHillCoefficientPotential ⁻¹' Ul)
  have hV : IsOpen V := hWh.inter (hUl.preimage continuous_classicalHillCoefficientPotential)
  have hb (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
      ‖classicalHillCriticalFrequencyTail N q‖ ≤ R :=
    (norm_classicalHillCriticalFrequencyTail_le N q).trans (hlabel _ hq.2
      (classicalHillCoefficientPotential_even q)).2
  have hcoord (k : ℤ) : AnalyticOnNhd ℂ (fun q => classicalHillCriticalFrequencyTail N q k) V := by
    by_cases hk : (N : ℤ) < k
    · have hk0 : 0 < k := by omega
      let n : ℕ+ := ⟨k.toNat, by omega⟩
      have hnk : (n : ℤ) = k := Int.toNat_of_nonneg hk0.le
      have hnN : N < (n : ℕ) := by
        have h : (N : ℤ) < (n : ℤ) := by rwa [hnk]
        exact_mod_cast h
      have hnh : Nh < (n : ℕ) := (le_max_left _ _).trans_lt hnN
      have he : (fun q => classicalHillCriticalFrequencyTail N q k) =
          (fun q => classicalHillFrequencyCritical q n-(Real.pi : ℂ)*k) := by
        funext q
        rw [classicalHillCriticalFrequencyTail_apply, if_pos hk]
        dsimp only [classicalHillFrequencyCritical]
        rw [hnk]
      rw [he]
      exact ((hhigh n hnh).1.mono inter_subset_left).sub analyticOnNhd_const
    · have he : (fun q => classicalHillCriticalFrequencyTail N q k) = (fun _ => (0 : ℂ)) := by
        funext q
        rw [classicalHillCriticalFrequencyTail_apply, if_neg hk]
      rw [he]
      exact analyticOnNhd_const
  refine ⟨N,V,R,hNh.trans_le (le_max_left _ _),hV,⟨hqh,hql⟩,hR,
    Coeff.analyticOnNhd_of_bounded_coordinatewise _ hV hcoord R hb,?_⟩
  intro q hq
  exact ⟨hb q hq,(hlabel _ hq.2 (classicalHillCoefficientPotential_even q)).1.enlarge N
    (le_max_right _ _)⟩

/-- A valid distant free labeling identifies every retained coordinate
with its free center, so the entire displacement tail vanishes. -/
theorem classicalHillCriticalFrequencyTail_free (N : ℕ)
    (hlabel : CriticalPointLabeling (by simp) (by norm_num) (classicalHillCoefficientPotential 0)
      (classicalHillCoefficientPotential_even 0) N
      (canonicalCriticalPoints (by simp) (by norm_num) (classicalHillCoefficientPotential 0)
        (classicalHillCoefficientPotential_even 0))) :
    classicalHillCriticalFrequencyTail N 0 = 0 := by
  ext k
  rw [classicalHillCriticalFrequencyTail_apply]
  by_cases hk : (N : ℤ) < k
  · rw [if_pos hk]
    have hk0 : 0 < k := by omega
    let n : ℕ+ := ⟨k.toNat, by omega⟩
    have hnk : (n : ℤ) = k := Int.toNat_of_nonneg hk0.le
    have hnN : N < k.natAbs := by omega
    have hl := hlabel.distant k hnN
    have henergy : ((Real.pi : ℂ)*k)^2 = freeHillEnergy n := by
      rw [← hnk]
      dsimp only [freeHillEnergy]
      push_cast
      ring
    have hz : deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential 0))
        ((Real.pi : ℂ)*k) = 0 := by
      rw [classicalHill_frequency_derivative_eq,henergy,deriv_classicalHillDiscriminant_free_energy,mul_zero]
    have he := (hl.2.2.2 _ (mem_closedBall_self (by positivity))).mp hz
    rw [← he,sub_self]
    rfl
  · rw [if_neg hk]
    rfl

/-- The whole actual ℓ² displacement tail can be made uniformly small on
one complex neighborhood of zero, for an arbitrary prescribed epsilon. -/
theorem exists_small_analytic_classicalHillCriticalFrequencyTail (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ 0 ∈ V ∧
      AnalyticOnNhd ℂ (classicalHillCriticalFrequencyTail N) V ∧
      ∀ q ∈ V, ‖classicalHillCriticalFrequencyTail N q‖ < ε := by
  obtain ⟨N,W,R,hN,hW,h0W,_,ha,hb⟩ := exists_analytic_classicalHillCriticalFrequencyTail 0
  have hzero := classicalHillCriticalFrequencyTail_free N (hb 0 h0W).2
  have hlim := (ha 0 h0W).continuousAt.norm
  have hsmall : ∀ᶠ q in 𝓝 (0 : NLS.LinearVolterra.Curve ℂ),
      ‖classicalHillCriticalFrequencyTail N q‖ < ε :=
    hlim.eventually (gt_mem_nhds (by simpa only [hzero,norm_zero] using hε))
  obtain ⟨U,hUsub,hU,h0U⟩ := _root_.mem_nhds_iff.mp hsmall
  exact ⟨N,W ∩ U,hN,hW.inter hU,⟨h0W,h0U⟩,ha.mono inter_subset_left,
    fun q hq => hUsub hq.2⟩

/-- At any continuous complex source, every sufficiently high actual
critical frequency is uniformly as close to its free center as prescribed.
The neighborhood and cutoff are chosen before the high index. -/
theorem exists_classicalHill_small_critical_frequency_neighborhood
    (q0 : NLS.LinearVolterra.Curve ℂ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ M : ℕ, ∃ U : Set (NLS.LinearVolterra.Curve ℂ), 0 < M ∧ IsOpen U ∧ q0 ∈ U ∧
      ∀ q ∈ U, ∀ n : ℕ+, M ≤ (n : ℕ) →
        ‖classicalHillFrequencyCritical q n-(Real.pi : ℂ)*(n : ℕ)‖ < epsilon := by
  obtain ⟨N,V,R,hN,hV,hq0,_,ha,_⟩ := exists_analytic_classicalHillCriticalFrequencyTail q0
  let f := classicalHillCriticalFrequencyTail N
  have hs : Summable (fun j : ℤ => ‖f q0 j‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (f q0)).summable
  have hi : Function.Injective (fun j : ℕ => (j : ℤ)) := by
    intro i j hij
    exact Int.ofNat_inj.mp hij
  have hnat := hs.comp_injective hi
  have hlim := hnat.tendsto_atTop_zero
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (epsilon/2)^2)))
  have hc : ContinuousAt (fun q => f q-f q0) q0 :=
    (ha q0 hq0).continuousAt.sub continuousAt_const
  have hcont : ∀ᶠ q in 𝓝 q0, ‖f q-f q0‖ < epsilon/2 :=
    hc.norm.eventually (gt_mem_nhds (by simpa only [sub_self,norm_zero] using (half_pos hepsilon)))
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp hcont
  refine ⟨max (N+1) M,V ∩ W,by omega,hV.inter hW,⟨hq0,hqW⟩,?_⟩
  intro q hq n hn
  have hnN : N < (n : ℕ) := by have := (le_max_left (N+1) M).trans hn;omega
  have hnM : M ≤ (n : ℕ) := (le_max_right (N+1) M).trans hn
  have he : f q (n : ℤ) = classicalHillFrequencyCritical q n-(Real.pi : ℂ)*(n : ℕ) := by
    rw [classicalHillCriticalFrequencyTail_apply,if_pos (by exact_mod_cast hnN)]
    rfl
  have hbase : ‖f q0 (n : ℤ)‖ < epsilon/2 := by
    have hb := hM (n : ℕ) hnM
    change ‖f q0 (n : ℤ)‖^2 < (epsilon/2)^2 at hb
    nlinarith [norm_nonneg (f q0 (n : ℤ))]
  have hdiff := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (f q-f q0) (n : ℤ)
  have ht := norm_le_norm_sub_add (f q (n : ℤ)) (f q0 (n : ℤ))
  rw [← he]
  change ‖f q (n : ℤ)-f q0 (n : ℤ)‖ ≤ ‖f q-f q0‖ at hdiff
  have hsmall : ‖f q-f q0‖ < epsilon/2 := hWsub hq.2
  linarith

end NLS.KdV
