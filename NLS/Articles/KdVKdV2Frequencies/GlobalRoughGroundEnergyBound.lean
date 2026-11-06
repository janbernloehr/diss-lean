import NLS.Articles.KdVKdV2Frequencies.GlobalRoughGroundEnergyFiniteGap
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianInjective
import NLS.KdV.HillHminusOneLabelContinuity

/-! # The actual ground-energy bound at every real mean-zero rough source

One actual local weak inverse supplies physical finite-gap source
approximants from finite target truncations. The intrinsic lowest energy
and the SAME global positive forward map are continuous in H-minus-one,
so the proved bound passes to every real rough source.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem physical_gap_closed_of_signed_zero (D : GlobalRoughAbelianForwardData)
    (p : RealPeriodOneHillPotential) (n : ℕ) (hn : 0 < n)
    (hz : (D.signed (hillOriginalHminusSource p.val)).val (n : ℤ) = 0) :
    hillRealLabels p.val p.property.1 p.property.2 (2*n) =
      hillRealLabels p.val p.property.1 p.property.2 (2*n-1) := by
  have hs := D.signed_positive_real (hillOriginalHminusSource p.val)
    (hillOriginalHminusSource_real p.val p.property.2) (n : ℤ) (by exact_mod_cast hn)
  rw [hz] at hs
  have hp : D.positive (hillOriginalHminusSource p.val) (n : ℤ) = 0 :=
    (div_eq_zero_iff.mp hs.symm).resolve_right (Weight.complex_ne_zero _ _)
  have hI := D.positive_physical_action_norm p n hn
  rw [hp,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero] at hI
  have ho := monotone_hillRealLabels p.val p.property.1 p.property.2 (show 2*n-1 ≤ 2*n by omega)
  apply le_antisymm ?_ ho
  by_contra hlt
  have hpos := (hillRealGapIntegral_pos_iff p.val p.property.1 p.property.2 n (by omega)).mpr (lt_of_not_ge hlt)
  rw [hI] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- EVERY actual real mean-zero rough source has its exact intrinsic
ground energy bounded by the SAME actual weak positive target norm.
No L2 membership, spectral finite-gap or source-size premise remains. -/
theorem ground_energy_le_positive_norm (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    -hillHminusLowestRealRoot q hr ≤ (2/Real.pi)*‖D.positive q‖^2 := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let a := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q
  have hLa : L a = q := WeightedCoeff.meanZeroWeightedLift_projection _ q hm
  have hreal : IsRealPeriodOneHminusOne (L a) := by rwa [hLa]
  let z := D.meanZeroForward a
  have hJa : deletedL2Conjugation a = a :=
    (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a).mp hreal
  have hJz : deletedL2Conjugation z = z := by
    change deletedL2Conjugation (D.meanZeroForward a) = D.meanZeroForward a
    rw [←D.meanZeroForward_conjugation,hJa]
  obtain ⟨U,hU,hzU,G,hG,hGa,hdata⟩ := D.exists_real_weak_inverse_germ a hreal
  have hGz : G z = a := hGa
  let c := fun S : ℕ => deletedSymmetricTruncate S z
  have ht : Tendsto c atTop (𝓝 z) := tendsto_deletedSymmetricTruncate z
  obtain ⟨S0,hS0⟩ := eventually_atTop.mp (ht.eventually (hU.mem_nhds hzU))
  have hnear (k : ℕ) : c (k+S0) ∈ U := hS0 _ (by omega)
  let Q : ℕ → PeriodOneHminusOne := fun k => L (G (c (k+S0)))
  have hraw (k : ℕ) : D.signed (Q k) =
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) (c (k+S0)) :=
    (hdata _ (hnear k)).2.2.1
  have hQr (k : ℕ) : IsRealPeriodOneHminusOne (Q k) :=
    (hdata _ (hnear k)).2.2.2 (deletedSymmetricTruncate_real _ z hJz)
  have hQm (k : ℕ) : (Q k).val 0 = 0 := WeightedCoeff.meanZeroWeightedLift_zero _ _
  have hreg (k : ℕ) : Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*(D.signed (Q k)).val j) 2 := by
    rw [hraw k]
    exact deletedSymmetricTruncate_weighted_mem _ z _ _
  choose p hp using fun k => D.exists_physical_of_signed_half_mem (Q k) (hQr k) (hreg k)
  change ∀ k, hillOriginalHminusSource (p k).val = Q k at hp
  have hclosed (k n : ℕ) (hn : k+S0+1 ≤ n) :
      hillRealLabels (p k).val (p k).property.1 (p k).property.2 (2*n) =
        hillRealLabels (p k).val (p k).property.1 (p k).property.2 (2*n-1) := by
    apply D.physical_gap_closed_of_signed_zero (p k) n (by omega)
    rw [hp k,hraw k,WeightedCoeff.meanZeroWeightedLift_apply,deletedSymmetricTruncate_apply,
      if_neg (by simp only [Finset.mem_Icc]; omega),zero_div]
  have hb (k : ℕ) : -hillHminusLowestRealRoot (Q k) (hQr k) ≤ (2/Real.pi)*‖D.positive (Q k)‖^2 := by
    have hmp : (hillOriginalHminusSource (p k).val).val 0 = 0 := by rw [hp k]; exact hQm k
    have h := D.ground_energy_le_positive_norm_of_physical_finiteGap (p k) hmp (k+S0+1) (by omega)
      (hclosed k)
    simpa only [hp k] using h
  have hshift : StrictMono (fun k : ℕ => k+S0) := fun _ _ h => Nat.add_lt_add_right h S0
  have hQ : Tendsto Q atTop (𝓝 q) := by
    have h := L.continuous.continuousAt.tendsto.comp
      (((hG z hzU).continuousAt.tendsto).comp (ht.comp hshift.tendsto_atTop))
    simpa only [Q,hGz,hLa,Function.comp_def] using h
  have hsource : Tendsto (fun k => (⟨Q k,hQr k⟩ : PeriodOneRealHminusOne)) atTop (𝓝 ⟨q,hr⟩) :=
    tendsto_subtype_rng.mpr hQ
  have hleft := (continuous_hillHminusLowestRealRoot.continuousAt.tendsto.comp hsource).neg
  have hright := ((D.positive_analytic q (D.real_mem_domain q hr)).continuousAt.tendsto.comp hQ).norm.pow 2 |>.const_mul (2/Real.pi)
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hb)

/-- A universal source bound in the norm of the SAME actual global weak
positive target, valid for every real mean-zero H-minus-one source. -/
theorem norm_source_le_positive_norm (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    ‖q‖ ≤ (‖periodOneMassOperator 0‖+‖periodOneL2Inclusion‖)*
        Real.sqrt ((2/Real.pi)*‖D.positive q‖^2)+
      (‖periodOneMiuraProduct‖+‖periodOneL2Inclusion‖)*((2/Real.pi)*‖D.positive q‖^2) := by
  obtain ⟨u,_hu,hi,_hn,_ht,_hl,_hr,_ha⟩ := exists_periodOneMiura_ground_factor q hr hm
  have h := norm_source_le_of_realMiura_energy q hm _ u hi
  have he := D.ground_energy_le_positive_norm q hr hm
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by positivity))
    (mul_le_mul_of_nonneg_left he (by positivity)))

/-- Positive normalization is bounded by the native norm of the SAME
actual signed weak target; this uses its literal positive coefficients. -/
theorem positive_norm_le_signed_norm (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ‖D.positive q‖ ≤ ‖D.signed q‖ := by
  let b := WeightedCoeff.weightIsometry (Weight.sobolev (-1/2)) 2 (D.signed q)
  have h : ‖D.positive q‖ ≤ ‖b‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro j
    by_cases hj : 0 < j
    · change ‖D.positive q j‖ ≤ ‖(Weight.sobolev (-1/2) j : ℂ)*(D.signed q).val j‖
      rw [D.signed_positive_real q hr j hj]
      have he : (Weight.sobolev (-1/2) j : ℂ)*
          (D.positive q j/(Weight.sobolev (-1/2) j : ℂ)) = D.positive q j := by
        rw [←mul_div_assoc]
        exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev (-1/2)) j)
      rw [he]
    · rw [D.positive_zero q (D.real_mem_domain q hr) j (by omega),norm_zero]
      exact norm_nonneg _
  simpa only [b,LinearIsometryEquiv.norm_map] using h

/-- Exact intrinsic energy bound in the native h^(-1/2) norm of the
SAME full signed weak map, at EVERY real mean-zero rough source. -/
theorem ground_energy_le_signed_norm (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    -hillHminusLowestRealRoot q hr ≤ (2/Real.pi)*‖D.signed q‖^2 :=
  (D.ground_energy_le_positive_norm q hr hm).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (D.positive_norm_le_signed_norm q hr) 2) (by positivity))

/-- EVERY actual normalized real factor has the global weak target L2
bound. Neither a factor norm bound nor a no-loss premise is assumed. -/
theorem ground_factor_norm_sq_le_signed_norm (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0)
    (u : PeriodOneRealL2) (hu : u.val 0 = 0) (e : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) :
    ‖u.val‖^2 ≤ (2/Real.pi)*‖D.signed q‖^2 := by
  have he := periodOneRealMiura_energy_eq_norm_sq q hm e u hi
  have hg := neg_miura_energy_eq_hillHminusLowestRealRoot q hr u e hu hi
  have h := D.ground_energy_le_signed_norm q hr hm
  rwa [←hg,neg_neg,he] at h

/-- A universal H-minus-one source bound by the SAME actual signed weak
target norm, without a spectral finite-gap or initial L2 restriction. -/
theorem norm_source_le_signed_norm (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    ‖q‖ ≤ (‖periodOneMassOperator 0‖+‖periodOneL2Inclusion‖)*
        Real.sqrt ((2/Real.pi)*‖D.signed q‖^2)+
      (‖periodOneMiuraProduct‖+‖periodOneL2Inclusion‖)*((2/Real.pi)*‖D.signed q‖^2) := by
  obtain ⟨u,_hu,hi,_hn,_ht,_hl,_hr,_ha⟩ := exists_periodOneMiura_ground_factor q hr hm
  have h := norm_source_le_of_realMiura_energy q hm _ u hi
  have he := D.ground_energy_le_signed_norm q hr hm
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by positivity))
    (mul_le_mul_of_nonneg_left he (by positivity)))

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
