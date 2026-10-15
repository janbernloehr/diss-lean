import NLS.ZakharovShabat.SourceSection20AngleSobolev
import NLS.ZakharovShabat.SourceSobolevAngleEnergy
import NLS.ZakharovShabat.SourceSection20EnergyBracket

/-! # The original physical energy bracket on real H¹ and complex germs

The actual full H¹ energy derivative acts on the constructed H¹ angle
vector. H¹ finite-gap density identifies this physical bracket with the
original moment frequency, with mass and dispersion restored. Analytic
uniqueness extends the identity to a complex germ at each real open-gap
source. These results retain the original family and primitive.
-/
noncomputable section
open Set Filter Topology Complex NLS.Poisson
namespace NLS.ZakharovShabat.SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection20Data D A B U)
include Q

/-- The restored original frequency is analytic in the physical H¹ topology. -/
theorem analyticAt_sobolev_restored_frequency (n : ℤ) (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion a ∈ U) :
    AnalyticAt ℂ (fun b => A.renormalizedFrequency n (sobolevSourceInclusion b) +
      4*periodOneSobolevMass b+(2*(n : ℂ)*Real.pi)^2) a :=
  (((Q.frequency_analytic n _ ha).comp (sobolevSourceInclusion.analyticAt a)).add
    (analyticAt_const.mul (analyticAt_periodOneSobolevMass a))).add analyticAt_const

/-- The actual physical H¹ bracket agrees with the original frequency at finite gaps. -/
theorem sobolev_energy_bracket_finiteGap
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaEnergyBracket n s (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) =
      A.renormalizedFrequency n φ.val +
        4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1+(2*(n : ℂ)*Real.pi)^2 := by
  rw [sourceSobolevThetaEnergyBracket,Q.sobolevThetaVector_eq_finiteGap φ hf n hn]
  exact Q.finiteGap_energy_bracket φ hf n hn

/-- The physical energy bracket now holds for every real H¹ source with the selected gap open. -/
theorem sobolev_energy_bracket (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaEnergyBracket n s a.val =
      A.renormalizedFrequency n (sobolevSourceInclusion a.val) +
        4*periodOneSobolevMass a.val+(2*(n : ℂ)*Real.pi)^2 := by
  let q : realTypeSobolevSourceLocus → realTypeSourceSubmodule 2 :=
    fun b => ⟨sobolevSourceInclusion b.val,b.property⟩
  have hq : Continuous q := (sobolevSourceInclusion.continuous.comp continuous_subtype_val).subtype_mk _
  let G := q ⁻¹' sourceOpenGapRealLocus (by simp) (by norm_num) n
  have hG : IsOpen G := (isOpen_sourceOpenGapRealLocus (by simp) (by norm_num) n).preimage hq
  let F := fun b : ScalarDomain 2 × ScalarDomain 2 =>
    A.renormalizedFrequency n (sobolevSourceInclusion b)+4*periodOneSobolevMass b+(2*(n : ℂ)*Real.pi)^2
  have hzero : sourceSobolevThetaEnergyBracket n s a.val-F a.val = 0 := by
    apply eq_of_continuousOn_of_sourceSobolevFiniteGap hG
      (H := fun b => sourceSobolevThetaEnergyBracket n s b.val-F b.val) (c := 0) ?_ ?_ a hn
    · intro b hb
      have hE := analyticAt_sourceSobolevThetaEnergyBracket D.previous.original_theta_common_domain n b.val
        (D.previous.original_theta_common_domain.real_subset b.property) hb
      have hF := Q.analyticAt_sobolev_restored_frequency n b.val (Q.real_subset b.property)
      exact ((hE.sub hF).continuousAt.comp continuous_subtype_val.continuousAt).continuousWithinAt
    · intro b hb hbf
      have he := Q.sobolev_energy_bracket_finiteGap (q b) hbf n hb
      have hm := periodOneSobolevMass_sourceFiniteGapSobolevPair (by simp) (by norm_num) (q b) hbf
      rw [sourceFiniteGapSobolevPair_sobolevSource] at he hm
      change sourceSobolevThetaEnergyBracket n s b.val-F b.val = 0
      dsimp only [F]
      rw [he,hm]
      exact sub_self _
  exact sub_eq_zero.mp hzero

/-- Analytic uniqueness preserves the actual physical bracket on a complex H¹ germ. -/
theorem sobolev_energy_bracket_complex_germ (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaEnergyBracket n s =ᶠ[𝓝 a.val]
      (fun b => A.renormalizedFrequency n (sobolevSourceInclusion b)+
        4*periodOneSobolevMass b+(2*(n : ℂ)*Real.pi)^2) := by
  classical
  let gap := fun b : ScalarDomain 2 × ScalarDomain 2 => canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (sobolevSourceInclusion b)) (periodOnePotential_mem _) n
  let F := fun b : ScalarDomain 2 × ScalarDomain 2 => A.renormalizedFrequency n (sobolevSourceInclusion b)+
    4*periodOneSobolevMass b+(2*(n : ℂ)*Real.pi)^2
  have hg : ContinuousAt gap a.val :=
    ((continuousAt_canonicalPeriodicRight_periodOne_of_realType (by simp) (by norm_num)
      (sobolevSourceInclusion a.val) a.property n).sub
      (continuousAt_canonicalPeriodicLeft_periodOne_of_realType (by simp) (by norm_num)
        (sobolevSourceInclusion a.val) a.property n)).comp sobolevSourceInclusion.continuous.continuousAt
  have hopen : ∀ᶠ b in 𝓝 a.val, gap b ≠ 0 := hg.eventually (isOpen_compl_singleton.mem_nhds hn)
  let f := fun b => if gap b ≠ 0 then sourceSobolevThetaEnergyBracket n s b else F b
  have he : sourceSobolevThetaEnergyBracket n s =ᶠ[𝓝 a.val] f := by
    filter_upwards [hopen] with b hb
    simp only [f,if_pos hb]
  have hf : AnalyticAt ℂ f a.val :=
    (analyticAt_sourceSobolevThetaEnergyBracket D.previous.original_theta_common_domain n a.val
      (D.previous.original_theta_common_domain.real_subset a.property) hn).congr he
  have hreal (b : realTypeSobolevSourceLocus) : f b.val = F b.val := by
    dsimp only [f]
    split_ifs with hb
    · exact Q.sobolev_energy_bracket b n hb
    · rfl
  exact he.trans (eventuallyEq_sobolev_of_analyticAt_of_real_agreement a f F hf
    (Q.analyticAt_sobolev_restored_frequency n a.val (Q.real_subset a.property)) hreal)

/-- Every Hilbert cotangent representing the actual H¹ energy derivative
recovers the original physical frequency on every real open-gap H¹ source. -/
theorem sobolev_energy_bivector (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0)
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : fderiv ℂ periodOneSobolevHamiltonian a.val = L.comp sobolevSourceInclusion) :
    sourceBivector le_rfl
      (sourceAngularThetaDifferential (by simp) (by norm_num) n s (sobolevSourceInclusion a.val)) L =
      A.renormalizedFrequency n (sobolevSourceInclusion a.val)+
        4*periodOneSobolevMass a.val+(2*(n : ℂ)*Real.pi)^2 := by
  rw [← sourceSobolevThetaEnergyBracket_eq_sourceBivector n s a.val
    (Q.sobolevThetaVector_inclusion a n hn) L hL]
  exact Q.sobolev_energy_bracket a n hn

/-- The energy bracket also recovers any previously constructed original
Hilbert action frequency, with its mass and free dispersion restored. -/
theorem sobolev_energy_bracket_original_frequency
    {T : Set (Coeff 1)} {F : Coeff 1 → ℤ → ℂ} (E : SourceOriginalHilbertFrequencyData D T F)
    (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaEnergyBracket n s a.val =
      F (sourceActionSequence (q := 1) (by simp) (by norm_num) s (sobolevSourceInclusion a.val)) n+
        4*periodOneSobolevMass a.val+(2*(n : ℂ)*Real.pi)^2 := by
  rw [Q.hilbert_action_frequency E ⟨sobolevSourceInclusion a.val,a.property⟩ n]
  exact Q.sobolev_energy_bracket a n hn

/-- Each selected index has one open complex H¹ domain containing all its
real open-gap sources, with the actual analytic angle vector and physical energy bracket. -/
theorem exists_sobolev_energy_domain (n : ℤ) :
    ∃ T : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen T ∧
      (∀ a : realTypeSobolevSourceLocus, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0 → a.val ∈ T) ∧
      T ⊆ {a | sobolevSourceInclusion a ∈ U ∧ canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0} ∧
      AnalyticOnNhd ℂ (sourceSobolevThetaVector n s) T ∧
      ∀ a ∈ T,
        sobolevSourceInclusion (sourceSobolevThetaVector n s a) =
          sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a) ∧
        sourceSobolevThetaEnergyBracket n s a =
          A.renormalizedFrequency n (sobolevSourceInclusion a)+
            4*periodOneSobolevMass a+(2*(n : ℂ)*Real.pi)^2 := by
  obtain ⟨M,hM,hrM,hsubM,_⟩ := Q.exists_sobolev_momentum_domain n
  let G := {a : ScalarDomain 2 × ScalarDomain 2 | a ∈ M ∧
    sobolevSourceInclusion (sourceSobolevThetaVector n s a) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a) ∧
    sourceSobolevThetaEnergyBracket n s a =
      A.renormalizedFrequency n (sobolevSourceInclusion a)+4*periodOneSobolevMass a+(2*(n : ℂ)*Real.pi)^2}
  have hsub : interior G ⊆ {a | sobolevSourceInclusion a ∈ U ∧ canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0} :=
    fun a ha => hsubM (interior_subset ha).1
  refine ⟨interior G,isOpen_interior,?_,hsub,(Q.analyticOnNhd_sobolevThetaVector n).mono hsub,?_⟩
  · intro a hn
    apply mem_interior_iff_mem_nhds.mpr
    have hM' : ∀ᶠ b in 𝓝 a.val, b ∈ M := hM.mem_nhds (hrM a hn)
    exact hM'.and ((Q.sobolevThetaVector_inclusion_complex_germ a n hn).and
      (Q.sobolev_energy_bracket_complex_germ a n hn))
  · intro a ha
    exact (interior_subset ha).2

end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.ZakharovShabat
/-- The original constructor supplies the actual H¹ angle vector and energy
identity, simultaneously for all real H¹ sources and all selected open gaps. -/
theorem sourceSection20_original_sobolev_energy :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
    ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
    ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
    ∃ B U : Set (CoeffPair 2), ∃ _Q : SourceSection20Data D A B U,
      ∀ a : realTypeSobolevSourceLocus, ∀ n : ℤ, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0 →
        sobolevSourceInclusion (sourceSobolevThetaVector n s a.val) =
          sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a.val) ∧
        sourceSobolevThetaEnergyBracket n s a.val =
          A.renormalizedFrequency n (sobolevSourceInclusion a.val)+
            4*periodOneSobolevMass a.val+(2*(n : ℂ)*Real.pi)^2 := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q,fun a n hn =>
    ⟨Q.sobolevThetaVector_inclusion a n hn,Q.sobolev_energy_bracket a n hn⟩⟩
end NLS.ZakharovShabat
