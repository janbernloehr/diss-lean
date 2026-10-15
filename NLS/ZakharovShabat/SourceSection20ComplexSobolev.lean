import NLS.ZakharovShabat.SourceSection20SobolevDomain

/-! # Physical Section 20 brackets on the full original complex H¹ domain

Connectedness of the original H¹ open-gap domain extends the proved real
momentum and energy germs to every complex point. The original angle
vector therefore has its actual analytic H¹ lift throughout that domain.
The source domain and original family are chosen before every index.
-/
noncomputable section
open Set Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat.SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection20Data D A B U)
include Q

/-- Real open-gap germs determine analytic maps on the whole original complex H¹ domain. -/
theorem eqOn_sobolev_openGapDomain_of_real_germs
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (n : ℤ) (f g : (ScalarDomain 2 × ScalarDomain 2) → F)
    (hf : AnalyticOnNhd ℂ f (sourceSobolevOpenGapDomain U n))
    (hg : AnalyticOnNhd ℂ g (sourceSobolevOpenGapDomain U n))
    (hreal : ∀ a : realTypeSobolevSourceLocus, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0 →
        f =ᶠ[𝓝 a.val] g) : EqOn f g (sourceSobolevOpenGapDomain U n) := by
  obtain ⟨a,hn⟩ := exists_realSobolev_open_gap n
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (Q.isConnected_sobolev_openGapDomain n).isPreconnected
    (show a.val ∈ sourceSobolevOpenGapDomain U n from ⟨Q.real_subset a.property,hn⟩) (hreal a hn)

/-- The actual physical momentum bracket is `2πn` at every original complex H¹ open-gap source. -/
theorem sobolev_momentum_bracket_complex (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion a ∈ U) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n s a = 2*(Real.pi : ℂ)*n := by
  apply Q.eqOn_sobolev_openGapDomain_of_real_germs n _ (fun _ => 2*(Real.pi : ℂ)*n)
    ?_ analyticOnNhd_const (fun b hb => Q.sobolev_momentum_bracket_complex_germ b n hb) ⟨ha,hn⟩
  exact (D.previous.original_theta_common_domain.analyticOnNhd_sobolevThetaMomentumBracket n).mono
    (fun b hb => ⟨D.complex.source_subset (Q.original_subset hb.1),hb.2⟩)

/-- The full complex-domain momentum identity is locally constant in the H¹ topology. -/
theorem sobolev_momentum_bracket_complex_eventually (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion a ∈ U) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n s =ᶠ[𝓝 a] (fun _ => 2*(Real.pi : ℂ)*n) := by
  filter_upwards [(Q.isOpen_sobolev_openGapDomain n).mem_nhds ⟨ha,hn⟩] with b hb
  exact Q.sobolev_momentum_bracket_complex b hb.1 n hb.2

/-- The analytic H¹ recovery equals the actual original angle vector on the full complex domain. -/
theorem sobolevThetaVector_inclusion_complex (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion a ∈ U) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    sobolevSourceInclusion (sourceSobolevThetaVector n s a) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a) :=
  D.previous.original_theta_common_domain.sobolevThetaVector_inclusion_of_momentum_germ n a
    (D.complex.source_subset (Q.original_subset ha)) hn (2*(Real.pi : ℂ)*n)
    (Q.sobolev_momentum_bracket_complex_eventually a ha n hn)

/-- Every original complex H¹ open-gap source has a unique actual H¹ angle-vector lift. -/
theorem existsUnique_sobolevThetaVector_complex (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion a ∈ U) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    ∃! v : ScalarDomain 2 × ScalarDomain 2, sobolevSourceInclusion v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a) :=
  ⟨sourceSobolevThetaVector n s a,Q.sobolevThetaVector_inclusion_complex a ha n hn,
    fun _v hv => sobolevSourceInclusion_injective
      (hv.trans (Q.sobolevThetaVector_inclusion_complex a ha n hn).symm)⟩

/-- The actual spatial derivative formula holds at every complex H¹ open-gap source. -/
theorem sobolevThetaVector_spatial_complex (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion a ∈ U) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevSpatialDerivative (sourceSobolevThetaVector n s a) =
      sourceHamiltonianDirection le_rfl
        (fderiv ℂ (sourceAngularThetaDifferential (by simp) (by norm_num) n s)
          (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative a)) :=
  D.previous.original_theta_common_domain.sobolevThetaVector_spatial_of_momentum_germ n a
    (D.complex.source_subset (Q.original_subset ha)) hn (2*(Real.pi : ℂ)*n)
    (Q.sobolev_momentum_bracket_complex_eventually a ha n hn)

/-- The physical H¹ energy bracket equals the restored original frequency
on the full original complex domain with the selected collapsed-gap locus removed. -/
theorem sobolev_energy_bracket_complex (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion a ∈ U) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaEnergyBracket n s a = A.renormalizedFrequency n (sobolevSourceInclusion a)+
      4*periodOneSobolevMass a+(2*(n : ℂ)*Real.pi)^2 := by
  apply Q.eqOn_sobolev_openGapDomain_of_real_germs n _ _ ?_ ?_
    (fun b hb => Q.sobolev_energy_bracket_complex_germ b n hb) ⟨ha,hn⟩
  · intro b hb
    exact analyticAt_sourceSobolevThetaEnergyBracket D.previous.original_theta_common_domain n b
      (D.complex.source_subset (Q.original_subset hb.1)) hb.2
  · intro b hb
    exact Q.analyticAt_sobolev_restored_frequency n b hb.1

/-- Every Hilbert cotangent representing the full physical H¹ energy
derivative gives the same original Poisson bivector throughout the complex domain. -/
theorem sobolev_energy_bivector_complex (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion a ∈ U) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0)
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : fderiv ℂ periodOneSobolevHamiltonian a = L.comp sobolevSourceInclusion) :
    sourceBivector le_rfl
      (sourceAngularThetaDifferential (by simp) (by norm_num) n s (sobolevSourceInclusion a)) L =
        A.renormalizedFrequency n (sobolevSourceInclusion a)+
          4*periodOneSobolevMass a+(2*(n : ℂ)*Real.pi)^2 := by
  rw [← sourceSobolevThetaEnergyBracket_eq_sourceBivector n s a
    (Q.sobolevThetaVector_inclusion_complex a ha n hn) L hL]
  exact Q.sobolev_energy_bracket_complex a ha n hn

end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.ZakharovShabat
/-- One original family and one connected source domain support every
physical complex H¹ angle bracket, with no further index-dependent shrinking. -/
theorem sourceSection20_original_complex_sobolev :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
    ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
    ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
    ∃ B U : Set (CoeffPair 2), ∃ _Q : SourceSection20Data D A B U,
      ∀ a : ScalarDomain 2 × ScalarDomain 2, sobolevSourceInclusion a ∈ U → ∀ n : ℤ,
        canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0 →
        sourceSobolevThetaMomentumBracket n s a = 2*(Real.pi : ℂ)*n ∧
        sobolevSourceInclusion (sourceSobolevThetaVector n s a) =
          sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a) ∧
        sourceSobolevThetaEnergyBracket n s a =
          A.renormalizedFrequency n (sobolevSourceInclusion a)+
            4*periodOneSobolevMass a+(2*(n : ℂ)*Real.pi)^2 := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q,fun a ha n hn =>
    ⟨Q.sobolev_momentum_bracket_complex a ha n hn,
      Q.sobolevThetaVector_inclusion_complex a ha n hn,Q.sobolev_energy_bracket_complex a ha n hn⟩⟩
end NLS.ZakharovShabat
