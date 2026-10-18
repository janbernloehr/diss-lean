import NLS.ZakharovShabat.PhysicalAngularValues

/-! # Reality and convergence of the physical angles

The intrinsic physical beta terms are real and absolutely summable. Every
admissible eta value is real at an open gap, and the selected theta is real
there. These conclusions require no supplied normalized source family.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Physical gap noncollapse is exactly the nonzero original gap condition. -/
theorem physicalPeriodicGap_ne_iff (u : IntervalPairL2) (n : ℤ) :
    physicalPeriodicLeft u n ≠ physicalPeriodicRight u n ↔
      sourcePeriodicGapDisplacement (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) n ≠ 0 := by
  rw [(physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2,
    sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,sub_ne_zero]
  exact ne_comm

/-- Every selected off-diagonal beta is an actual physical integral value. -/
theorem physicalBeta_mem (n m : ℤ) (hm : m ≠ n) (u : physicalRealSubmodule) :
    physicalBeta n m u ∈ physicalAngularIntegralValues n m u := by
  rw [physicalBeta,dif_neg hm]
  exact (existsUnique_physicalBeta_value n m hm u).choose_spec.1

/-- Every physical off-diagonal integral equals the selected beta value. -/
theorem physicalBeta_unique (n m : ℤ) (hm : m ≠ n) (u : physicalRealSubmodule)
    {v : ℂ} (hv : v ∈ physicalAngularIntegralValues n m u) : v = physicalBeta n m u := by
  rw [physicalBeta,dif_neg hm]
  exact (existsUnique_physicalBeta_value n m hm u).choose_spec.2 v hv

/-- The diagonal is omitted exactly, even at collapsed gaps. -/
@[simp] theorem physicalBeta_self (n : ℤ) (u : physicalRealSubmodule) : physicalBeta n n u = 0 := by
  simp [physicalBeta]

/-- Physical eta values have exactly the same class modulo 2pi at an open gap. -/
theorem physicalEta_values_period (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n ≠ physicalPeriodicRight u.val n)
    {v w : ℂ} (hv : v ∈ physicalAngularIntegralValues n n u)
    (hw : w ∈ physicalAngularIntegralValues n n u) : ∃ k : ℤ, v-w = (k:ℂ)*(2*Real.pi) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  exact D.toSourceSection14OriginalData.physicalEta_values_period n u hg hv hw

/-- Every beta term at a collapsed real physical gap is zero, including the omitted diagonal. -/
theorem physicalBeta_eq_zero_of_collapsed (n m : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val m = physicalPeriodicRight u.val m) : physicalBeta n m u = 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  rw [A.physicalBeta_eq_source]
  by_cases hm : m = n
  · simp only [sourceAngularBetaSeriesTerm,if_pos hm]
  · rw [sourceAngularBetaSeriesTerm,if_neg hm]
    apply sourceAngularBeta_eq_zero_of_real_collapsed_gap (by simp) (by norm_num) n m s
      (sourcePhysicalL2Equiv.symm u.val) u.property
    by_contra hne
    exact ((physicalPeriodicGap_ne_iff u.val m).mpr hne) hg

/-- Every physical beta value is real, including at collapsed gaps. -/
theorem physicalBeta_im_eq_zero (n m : ℤ) (u : physicalRealSubmodule) : (physicalBeta n m u).im = 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  rw [A.physicalBeta_eq_source]
  by_cases hm : m = n
  · simp only [sourceAngularBetaSeriesTerm,if_pos hm,Complex.zero_im]
  · rw [sourceAngularBetaSeriesTerm,if_neg hm]
    exact A.previous.beta_original_im_eq_zero _ (A.complex.source_subset (A.complex.real_subset u.property))
      u.property n m hm

/-- The actual physical correction series is absolutely convergent. -/
theorem summable_norm_physicalBeta (n : ℤ) (u : physicalRealSubmodule) :
    Summable (fun m => ‖physicalBeta n m u‖) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  exact D.toSourceSection14OriginalData.summable_norm_physicalBeta n u

/-- Every admissible physical eta value is real at an open gap. -/
theorem physicalEta_value_im_eq_zero (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n ≠ physicalPeriodicRight u.val n)
    {v : ℂ} (hv : v ∈ physicalAngularIntegralValues n n u) : v.im = 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  obtain ⟨P,hμ,Q,γ,hQ,hγ,hnorm,hi,hm,rfl⟩ := A.physicalEta_value_toSource n u hv
  exact A.previous.eta_original_pathIntegral_im_eq_zero (sourcePhysicalL2Equiv.symm u.val)
    (A.complex.source_subset (A.complex.real_subset u.property)) u.property n
    (by simpa only [sourcePeriodicGapDisplacement_apply] using (physicalPeriodicGap_ne_iff u.val n).mp hg) P hμ Q γ hQ hnorm hγ hi hm

/-- The selected physical eta is real on its open-gap domain. -/
theorem physicalEta_im_eq_zero (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n ≠ physicalPeriodicRight u.val n) : (physicalEta n u).im = 0 :=
  physicalEta_value_im_eq_zero n u hg (physicalEta_mem n u hg)

/-- Every selected physical theta is real at its open gap. -/
theorem physicalTheta_im_eq_zero (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n ≠ physicalPeriodicRight u.val n) : (physicalTheta n u).im = 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  obtain ⟨k,hk⟩ := A.physicalTheta_sub_source n u hg
  have hθ := A.previous.theta_original_im_eq_zero (sourcePhysicalL2Equiv.symm u.val)
    (A.complex.source_subset (A.complex.real_subset u.property)) u.property n
    (by simpa only [sourcePeriodicGapDisplacement_apply] using (physicalPeriodicGap_ne_iff u.val n).mp hg)
  have hi := congrArg Complex.im hk
  simpa [hθ] using hi

end NLS.ZakharovShabat
