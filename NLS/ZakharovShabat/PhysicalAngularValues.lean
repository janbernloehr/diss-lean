import NLS.ZakharovShabat.PhysicalAngularComparison

/-! # Intrinsic physical beta, eta, and theta values

Physical integrals determine beta uniquely and eta modulo 2pi. Their
selections use no supplied source family. The correction is absolutely
summable, and the resulting angles give the original physical coordinates.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical unitInterval
namespace NLS.ZakharovShabat

/-- A physical beta value exists uniquely without a supplied normalized family. -/
theorem existsUnique_physicalBeta_value (n m : ℤ) (hm : m ≠ n) (u : physicalRealSubmodule) :
    ∃! v : ℂ, v ∈ physicalAngularIntegralValues n m u := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  exact D.toSourceSection14OriginalData.existsUnique_physicalBeta_value n m hm u

/-- The independent physical beta summand, with the diagonal omitted. -/
def physicalBeta (n m : ℤ) (u : physicalRealSubmodule) : ℂ :=
  if h : m = n then 0 else (existsUnique_physicalBeta_value n m h u).choose

/-- The actual sum of physical off-diagonal beta values; absolute convergence is proved below. -/
def physicalBetaCorrection (n : ℤ) (u : physicalRealSubmodule) : ℂ := ∑' m, physicalBeta n m u

/-- A physical eta value exists at every real open gap without a supplied family. -/
theorem physicalEta_values_nonempty (m : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val m ≠ physicalPeriodicRight u.val m) :
    (physicalAngularIntegralValues m m u).Nonempty := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  exact D.toSourceSection14OriginalData.physicalEta_values_nonempty m u hg

/-- Choose a physical eta integral; outside the proved open-gap domain a zero fallback is allowed. -/
def physicalEta (n : ℤ) (u : physicalRealSubmodule) : ℂ :=
  if h : (physicalAngularIntegralValues n n u).Nonempty then h.choose else 0

/-- At an open gap the selected eta is an actual integrable physical path value. -/
theorem physicalEta_mem (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n ≠ physicalPeriodicRight u.val n) :
    physicalEta n u ∈ physicalAngularIntegralValues n n u := by
  rw [physicalEta,dif_pos (physicalEta_values_nonempty n u hg)]
  exact (physicalEta_values_nonempty n u hg).choose_spec

/-- The physical angle is the actual diagonal integral plus the off-diagonal correction. -/
def physicalTheta (n : ℤ) (u : physicalRealSubmodule) : ℂ := physicalEta n u + physicalBetaCorrection n u

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- The independently selected beta value agrees with every source family, including the zero diagonal. -/
theorem physicalBeta_eq_source (n m : ℤ) (u : physicalRealSubmodule) :
    physicalBeta n m u = sourceAngularBetaSeriesTerm (by simp) (by norm_num) n s
      (sourcePhysicalL2Equiv.symm u.val) m := by
  by_cases hm : m = n
  · simp only [physicalBeta,sourceAngularBetaSeriesTerm,dif_pos hm,if_pos hm]
  · rw [physicalBeta,dif_neg hm,sourceAngularBetaSeriesTerm,if_neg hm]
    exact D.physicalAngularIntegralValues_beta n m hm u (NLS.ZakharovShabat.existsUnique_physicalBeta_value n m hm u).choose_spec.1

/-- The intrinsic physical correction is the original absolutely convergent correction. -/
theorem physicalBetaCorrection_eq_source (n : ℤ) (u : physicalRealSubmodule) :
    physicalBetaCorrection n u = sourceAngularBetaCorrection (by simp) (by norm_num) n s
      (sourcePhysicalL2Equiv.symm u.val) := by
  simp only [physicalBetaCorrection,sourceAngularBetaCorrection,D.physicalBeta_eq_source]

/-- The intrinsic and original angles have exactly the same class modulo 2pi on open gaps. -/
theorem physicalTheta_sub_source (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n ≠ physicalPeriodicRight u.val n) :
    ∃ k : ℤ, physicalTheta n u-sourceAngularOriginalTheta (by simp) (by norm_num) n s
      (sourcePhysicalL2Equiv.symm u.val) = (k:ℂ)*(2*Real.pi) := by
  have hg' : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sourcePhysicalL2Equiv.symm u.val)) (periodOnePotential_mem _) n ≠ 0 := by
    rw [canonicalPeriodicGap,sub_ne_zero]
    simpa only [(physicalPeriodicEndpoints_eq_source u.val).1,(physicalPeriodicEndpoints_eq_source u.val).2] using hg.symm
  have hφ : sourcePhysicalL2Equiv.symm u.val ∈ W := D.complex.source_subset (D.complex.real_subset u.property)
  obtain ⟨k,hk⟩ := D.previous.eta_original_integral_values_period (sourcePhysicalL2Equiv.symm u.val) hφ n hg'
    (D.physicalEta_value_toSource n u (physicalEta_mem n u hg))
    (D.previous.eta_original_integral_mem _ hφ n hg')
  refine ⟨k,?_⟩
  rw [physicalTheta,D.physicalBetaCorrection_eq_source,sourceAngularOriginalTheta]
  simpa only [add_sub_add_right_eq_sub] using hk

/-- The original physical homeomorphism has coordinates from independently specified physical integrals. -/
theorem physicalRealActionAngleHomeomorph_intrinsic_formula (u : physicalRealSubmodule) (n : ℤ) :
    (D.physicalRealActionAngleHomeomorph u).fst n = Real.sqrt (2*(physicalIndexedAction n u.val).re)*
      Real.cos (physicalTheta n u).re ∧
    (D.physicalRealActionAngleHomeomorph u).snd n = Real.sqrt (2*(physicalIndexedAction n u.val).re)*
      Real.sin (physicalTheta n u).re := by
  have h := D.physicalRealActionAngleHomeomorph_formula_of_eta u n (physicalEta n u) (by
    intro hg
    apply D.physicalEta_value_toSource
    apply physicalEta_mem
    intro he
    apply hg
    rw [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
    have he' : canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (sourcePhysicalL2Equiv.symm u.val))
        (periodOnePotential_mem _) n = canonicalPeriodicRight (by simp) (by norm_num)
          (periodOnePotential (sourcePhysicalL2Equiv.symm u.val)) (periodOnePotential_mem _) n := by
      simpa only [(physicalPeriodicEndpoints_eq_source u.val).1,(physicalPeriodicEndpoints_eq_source u.val).2] using he
    rw [he',sub_self])
  simpa only [physicalTheta,D.physicalBetaCorrection_eq_source] using h

/-- The intrinsic physical beta series converges absolutely at every real Hilbert input. -/
theorem summable_norm_physicalBeta (n : ℤ) (u : physicalRealSubmodule) :
    Summable (fun m => ‖physicalBeta n m u‖) := by
  simp only [D.physicalBeta_eq_source]
  exact D.complex.angular.beta_series.summable_norm _
    (D.complex.source_subset (D.complex.real_subset u.property)) n

end SourceSection14OriginalData

end NLS.ZakharovShabat
