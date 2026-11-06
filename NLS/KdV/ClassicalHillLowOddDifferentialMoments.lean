import NLS.KdV.ClassicalHillOddDifferentialMoments
import NLS.KdV.FreeHighContourPeriods
import NLS.KdV.ClassicalHighContourMoments

/-! # Odd differential moments at each fixed contour near the free source

Compact source tubes supply the finite-head counterpart of high-gap
asymptotics. No simplicity of the nearby periodic roots is assumed.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

private theorem exists_source_tube (S : Set ℂ) (hS : IsCompact S)
    (O : Set (ℂ × Curve ℂ)) (hO : IsOpen O) (hbase : ∀ z ∈ S, (z,0) ∈ O) :
    ∃ U : Set (Curve ℂ), IsOpen U ∧ 0 ∈ U ∧ S ×ˢ U ⊆ O := by
  have hs : S ×ˢ {(0 : Curve ℂ)} ⊆ O := by
    rintro ⟨z,a⟩ ⟨hz,ha⟩
    obtain rfl := mem_singleton_iff.mp ha
    exact hbase z hz
  obtain ⟨W,U,_,hU,hSW,h0,hsub⟩ := generalized_tube_lemma hS isCompact_singleton hO hs
  exact ⟨U,hU,h0 (mem_singleton _),fun t ht => hsub ⟨hSW ht.1,ht.2⟩⟩

theorem classicalHill_free_frequency_annulus_coverage (k : ℕ+) (r : ℝ) (hr : 0 < r)
    (z : ℂ) (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
    (hfar : r ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖) :
    (z^2,(0 : Curve ℂ)) ∈ classicalHillContinuationDomain := by
  have hsin : sin z ≠ 0 := by
    intro he
    have hc := free_derivative_zero_eq_center (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi)
      (k : ℤ) (by simpa only [Int.cast_natCast] using hz) (by rw [he,mul_zero])
    have hc' : z = (Real.pi : ℂ)*(k : ℕ) := by simpa only [Int.cast_natCast] using hc
    rw [hc',sub_self,norm_zero] at hfar
    linarith
  have hroot : classicalHillFreeRoot (z^2) ≠ 0 := by
    rw [classicalHillFreeRoot_eq_sin,sqrt_sq_of_re_pos z (re_pos_of_high_closedBall _ k.property z hz)]
    exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hsin
  have hrad : classicalHillRadicand (z^2,(0 : Curve ℂ)) ≠ 0 := by
    rw [← classicalHillFreeRoot_sq]
    exact pow_ne_zero _ hroot
  intro s _
  simpa only [sourceSegmentMap,zero_add,sub_zero,smul_zero] using
    (show (z^2,(0 : Curve ℂ)) ∈ classicalHillRootDomain from ⟨sq_mem_slitPlane_of_high_closedBall _ k.property z hz,hrad⟩)

/-- At each fixed positive contour, a constructed source neighborhood of
zero cancels every odd moment before any entire numerator is chosen. -/
theorem exists_classicalHill_fixed_odd_differential_moments (k : ℕ+) :
    ∃ U : Set (Curve ℂ), IsOpen U ∧ 0 ∈ U ∧
      ∀ a ∈ U, ∀ P : ℂ → ℂ, AnalyticOnNhd ℂ P univ → ∀ l : ℕ,
        (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          (classicalHillContinuedPrimitive (z^2,a)+I*(k : ℂ)*Real.pi)^(2*l+1)*
            (P (z^2)/classicalHillContinuedRoot (z^2,a))*(2*z)) = 0 := by
  let c : ℂ := (Real.pi : ℂ)*(k : ℕ)
  let sigma : ℂ := (-1 : ℂ)^(k : ℕ)
  have hsigma : sigma^2 = 1 := by dsimp only [sigma];rw [← pow_mul,Nat.mul_comm (k : ℕ) 2,pow_mul];norm_num
  have hc2 : c^2 = freeHillEnergy k := by dsimp only [c,freeHillEnergy];push_cast;ring
  have hbase : classicalHillDiscriminant 0 (freeHillEnergy k) = 2*sigma := by
    rw [classicalHillDiscriminant_zero,cos_sqrt_freeHillEnergy]
  obtain ⟨O,hO,hpO,W,hW,h0W,K,H,hK,hH,_,_,_,_,hmatch⟩ :=
    exists_classicalHill_primitive_ratio_continuation (freeHillEnergy k,0) sigma hsigma hbase
  let S : Set ℂ := {z | (z^2,(0 : Curve ℂ)) ∈ O ∧ (-I*(z-c))^2 ∈ W}
  have hS : IsOpen S := (hO.preimage (by fun_prop : Continuous (fun z : ℂ => (z^2,(0 : Curve ℂ))))).inter
    (hW.preimage (by fun_prop : Continuous (fun z : ℂ => (-I*(z-c))^2)))
  have hcS : c ∈ S := ⟨by rw [hc2];exact hpO,by simpa only [sub_self,mul_zero,zero_pow (by decide : 2 ≠ 0)] using h0W⟩
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hcS)
  let r := min (eps/2) (Real.pi/8)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hreps : r < eps := (min_le_left _ _).trans_lt (by linarith)
  have hrpi : r ≤ Real.pi/4 := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  have hsmall (z : ℂ) (hz : z ∈ closedBall c r) :
      (z^2,(0 : Curve ℂ)) ∈ O ∧ (-I*(z-c))^2 ∈ W := hball (closedBall_subset_ball hreps hz)
  let E : Set (ℂ × Curve ℂ) := (fun t : ℂ × Curve ℂ => (t.1^2,t.2)) ⁻¹' O
  obtain ⟨U1,hU1,h01,hchart⟩ := exists_source_tube (closedBall c r) (isCompact_closedBall c r)
    E (hO.preimage (by fun_prop)) (fun z hz => (hsmall z hz).1)
  let F (t : ℂ × Curve ℂ) : ℂ := classicalHillFrequencyPrimitive t+I*(k : ℂ)*Real.pi
  let T : Set (ℂ × Curve ℂ) := classicalHillFrequencyDomain ∩ (fun t => (F t)^2) ⁻¹' W
  have hT : IsOpen T := ((analyticOnNhd_classicalHillFrequencyPrimitive.add analyticOnNhd_const).pow 2).continuousOn.isOpen_inter_preimage
    isOpen_classicalHillFrequencyDomain hW
  have hT0 (z : ℂ) (hz : z ∈ sphere c r) : (z,(0 : Curve ℂ)) ∈ T := by
    have hzbig : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := closedBall_subset_closedBall hrpi (sphere_subset_closedBall hz)
    refine ⟨classicalHill_free_frequency_annulus_coverage k r hr z hzbig (mem_sphere_iff_norm.mp hz).ge,?_⟩
    have he : F (z,0) = -I*(z-c) := by
      dsimp only [F,classicalHillFrequencyPrimitive]
      rw [classicalHillContinuedPrimitive_base,classicalHillFreePrimitive,sqrt_sq_of_re_pos z (re_pos_of_high_closedBall _ k.property z hzbig)]
      dsimp only [c]
      ring
    change (F (z,0))^2 ∈ W
    rw [he]
    exact (hsmall z (sphere_subset_closedBall hz)).2
  obtain ⟨U2,hU2,h02,hbranch⟩ := exists_source_tube (sphere c r) (isCompact_sphere c r) T hT hT0
  let A : Set ℂ := closedBall c (Real.pi/4) \ ball c r
  have hA : IsCompact A := (isCompact_closedBall c (Real.pi/4)).diff isOpen_ball
  have hA0 (z : ℂ) (hz : z ∈ A) : (z,(0 : Curve ℂ)) ∈ classicalHillFrequencyDomain :=
    classicalHill_free_frequency_annulus_coverage k r hr z hz.1 (by simpa only [mem_ball,dist_eq_norm,not_lt] using hz.2)
  obtain ⟨U3,hU3,h03,hannulus⟩ := exists_source_tube A hA classicalHillFrequencyDomain isOpen_classicalHillFrequencyDomain hA0
  refine ⟨U1 ∩ (U2 ∩ U3),hU1.inter (hU2.inter hU3),⟨h01,h02,h03⟩,?_⟩
  intro a ha P hP l
  have hcover : ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      r ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖ → (z^2,a) ∈ classicalHillContinuationDomain := by
    intro z hz hfar
    have hh : (z,a) ∈ A ×ˢ U3 :=
      ⟨⟨hz,by simpa only [c,mem_ball,dist_eq_norm,not_lt] using hfar⟩,ha.2.2⟩
    exact hannulus hh
  rw [classicalHill_frequency_differential_radius_independence P hP k (2*l+1) a r hr hrpi hcover]
  have hchart' (z : ℂ) (hz : z ∈ closedBall c r) : (z^2,a) ∈ O :=
    hchart (show (z,a) ∈ closedBall c r ×ˢ U1 from ⟨hz,ha.1⟩)
  let G (z : ℂ) : ℂ := (P (z^2)/classicalHillContinuedRoot (z^2,a))*(2*z)
  have hKz : AnalyticOnNhd ℂ (fun z => K (z^2,a)) (closedBall c r) := by
    intro z hz
    exact (hK (z^2,a) (hchart' z hz)).comp (f := fun z : ℂ => (z^2,a)) ((analyticAt_id.pow 2).prod analyticAt_const)
  have hHz : AnalyticOnNhd ℂ (fun z => H (z^2,a)*P (z^2)*(2*z)) (closedBall c r) := by
    intro z hz
    have hh := (hH (z^2,a) (hchart' z hz)).comp (f := fun z : ℂ => (z^2,a)) ((analyticAt_id.pow 2).prod analyticAt_const)
    exact (hh.mul ((hP (z^2) (mem_univ _)).comp (f := fun z : ℂ => z^2) (analyticAt_id.pow 2))).mul (analyticAt_const.mul analyticAt_id)
  have hcircle (z : ℂ) (hz : z ∈ sphere c r) :
      K (z^2,a) = (F (z,a))^2 ∧ H (z^2,a)*P (z^2)*(2*z) = F (z,a)*G z := by
    have ht : (z,a) ∈ T := hbranch (show (z,a) ∈ sphere c r ×ˢ U2 from ⟨hz,ha.2.1⟩)
    have hcosh : 2*cosh (F (z,a)) = sigma*classicalHillDiscriminant a (z^2) := by
      dsimp only [F,classicalHillFrequencyPrimitive]
      rw [cosh_add_hill_index]
      linear_combination sigma*(classicalHillContinuedPrimitive_trace (z^2,a) ht.1).1
    obtain ⟨hk,hh⟩ := hmatch (z^2,a) (hchart' z (sphere_subset_closedBall hz))
      (F (z,a)) (classicalHillContinuedRoot (z^2,a)) ht.2 hcosh
      (classicalHill_shifted_primitive_sheet k (z^2,a) ht.1) (classicalHillContinuedRoot_ne_zero _ ht.1)
    refine ⟨hk,?_⟩
    rw [hh]
    dsimp only [G]
    ring
  have hz := frequencyMoment_odd_eq_zero_of_continuations (fun z => F (z,a)) G
    (fun z => K (z^2,a)) (fun z => H (z^2,a)*P (z^2)*(2*z)) c r hr.le hKz hHz hcircle l
  simpa only [frequencyMoment,F,G,classicalHillFrequencyPrimitive,mul_assoc] using! hz

/-- Finite-head compact tubes and the uniform high tail give one source
neighborhood before every positive contour and every entire numerator. -/
theorem exists_classicalHill_all_odd_differential_moments :
    ∃ U : Set (Curve ℂ), IsOpen U ∧ 0 ∈ U ∧
      ∀ a ∈ U, ∀ k : ℕ+, ∀ P : ℂ → ℂ, AnalyticOnNhd ℂ P univ → ∀ l : ℕ,
        (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          (classicalHillContinuedPrimitive (z^2,a)+I*(k : ℂ)*Real.pi)^(2*l+1)*
            (P (z^2)/classicalHillContinuedRoot (z^2,a))*(2*z)) = 0 := by
  classical
  obtain ⟨M,W,hM,hW,h0W,hhigh⟩ := exists_classicalHill_high_odd_differential_moments (0 : Curve ℂ)
  have hlow (j : ℕ) := exists_classicalHill_fixed_odd_differential_moments (⟨j+1,by omega⟩ : ℕ+)
  choose V hV h0V hlocal using hlow
  let U : Set (Curve ℂ) := W ∩ ⋂ j ∈ Finset.range M, V j
  have hU : IsOpen U := hW.inter (isOpen_biInter_finset (fun j _ => hV j))
  have h0U : (0 : Curve ℂ) ∈ U := ⟨h0W,mem_iInter₂.mpr (fun j _ => h0V j)⟩
  refine ⟨U,hU,h0U,?_⟩
  intro a ha k P hP l
  by_cases hk : M ≤ (k : ℕ)
  · exact hhigh a ha.1 k hk P hP l
  · let j := (k : ℕ)-1
    have hi : j ∈ Finset.range M := Finset.mem_range.mpr (by dsimp only [j];omega)
    have hkidx : (⟨j+1,by omega⟩ : ℕ+) = k := Subtype.ext (Nat.sub_add_cancel k.property)
    have haV : a ∈ V j := mem_iInter₂.mp ha.2 j hi
    simpa only [hkidx] using! hlocal j a haV P hP l

end NLS.KdV
