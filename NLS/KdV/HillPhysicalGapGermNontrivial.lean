import NLS.KdV.HillFreeAbelianDifferential
import NLS.KdV.HillHminusLocalGapMoments
import NLS.KdV.HillUnitRealSourceUnembed

/-! # Every selected physical gap opens arbitrarily near zero

The exact free Fourier derivative rules out an identically collapsed
physical gap germ. This also proves nontriviality of the actual analytic
squared-gap germ in native L2 coordinates.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem frequently_hillRealGapHalfLength_ne_zero (n : ℕ+) :
    ∃ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ)≠0 := by
  intro hc
  obtain ⟨Z,hZ,_hZ0,hDZ,hmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_free_differential h0q h0r (n : ℕ) n.property
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      Z (SpectralWeight.one.toCoeff p.val)=(0 : ℂ) := by
    filter_upwards [hc,hmatch] with p hp hpZ
    exact hpZ.trans (hillDirichletAbelianCoordinate_closed p.val p.property.1 p.property.2
      (n : ℕ) n.property (not_ne_iff.mp hp))
  let v : Coeff 2 := lp.single 2 (2*(n : ℤ)) 1
  have hv : v ∈ Coeff.paritySubspace 0 := by
    rw [Coeff.mem_paritySubspace]
    intro k hk
    have hkn : k≠2*(n : ℤ) := by omega
    simp only [v,lp.single_apply,Pi.single_apply,hkn,ite_false]
  have hv0 : v 0=0 := by
    simp [v,lp.single_apply]
  have hd := fderiv_eq_on_parity_of_eventuallyEq_realPotentials 0 h0q h0r Z
    (fun _ => (0 : ℂ)) (by simpa only [map_zero] using hZ.differentiableAt)
    (differentiableAt_const _) he v hv
  simp only [map_zero,hDZ v hv hv0,fderiv_const_apply,zero_apply,
    v,lp.single_apply,Pi.single_apply,ite_true,mul_one] at hd
  have hs : (Real.sqrt (2*((n : ℕ) : ℝ)*Real.pi) : ℂ)≠0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  exact (inv_ne_zero hs) hd

theorem hillLocalGapSquare_native_germ_nontrivial (n : ℕ+) :
    ¬ ∀ᶠ u : Coeff 2 in 𝓝 0,
      hillLocalGapSquare 0 h0q h0r (n : ℕ) (Coeff.periodDouble u)=0 := by
  intro hz
  obtain ⟨W,hW,h0W,hmatch⟩ :=
    exists_hillLocalGapSymmetricData_physical_neighborhood 0 h0q h0r (n : ℕ) n.property
  have ht : Tendsto (fun p : RealPeriodOneHillPotential =>
      Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))
      (𝓝 ⟨0,h0q,h0r⟩) (𝓝 (0 : Coeff 2)) := by
    simpa only [Function.comp_def,map_zero] using
      ((Fourier.paritySample (p := 2) 0).continuous.comp
        (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)).tendsto
          (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  have hc : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ)=0 := by
    filter_upwards [ht.eventually hz,hW.mem_nhds h0W] with p hp hpW
    rw [hillPeriodDouble_unitSample _ p.property.1,(hmatch p hpW).2] at hp
    have hh : (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)=0 := by
      have h := sq_eq_zero_iff.mp hp
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    exact ofReal_injective hh
  exact (frequently_hillRealGapHalfLength_ne_zero h0q h0r n) (hc.mono (fun _ h hn => hn h))

theorem hillHminusLocalGapSquare_l2_germ_nontrivial (n : ℕ+) :
    ¬ ∀ᶠ u : Coeff 2 in 𝓝 0,
      hillHminusLocalGapSquare h0q h0r n (periodOneL2Inclusion u)=0 := by
  simpa only [hillHminusLocalGapSquare_l2] using
    hillLocalGapSquare_native_germ_nontrivial h0q h0r n

end NLS.KdV
