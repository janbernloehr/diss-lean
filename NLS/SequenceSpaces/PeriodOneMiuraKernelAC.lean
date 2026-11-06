import NLS.SequenceSpaces.PeriodOneMiuraMinimalCritical
import NLS.Fourier.UnitIntervalL2ProductCoefficients

/-! # An actual Miura kernel gives a nonzero periodic AC solution

The actual unit Fourier synthesis of the kernel has an absolutely
continuous representative solving F-prime=-2*u*F almost everywhere.
Neither continuity nor differentiability of the L2 kernel is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ENNReal
namespace NLS
open Fourier

theorem exists_periodOneMiura_kernel_AC (u v : Coeff 2) (hv : v ≠ 0)
    (he : ∀ j : ℤ, 2*I*(Real.pi : ℂ)*j*v j+2*(periodOneMiuraProduct u v).val j = 0) :
    ∃ F : ℝ → ℂ, Continuous F ∧ AbsolutelyContinuousOnInterval F 0 1 ∧
      (unitL2SynthesisEquiv v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 1)] F ∧
      F 1 = F 0 ∧ (∃ x ∈ Icc (0 : ℝ) 1, F x ≠ 0) ∧
      ∀ᵐ x ∂volume.restrict (Ioc 0 1),
        HasDerivAt F ((-2 : ℂ)*(unitL2SynthesisEquiv u : ℝ → ℂ) x*F x) x := by
  let U := unitL2SynthesisEquiv u
  let V := unitL2SynthesisEquiv v
  let g : ℝ → ℂ := fun x => (-2 : ℂ)*(U x*V x)
  have hU (j : ℤ) : unitFourierCoefficient U j = u j := by
    rw [unitFourierCoefficient_eq_intervalFourierCoefficient,←unitL2SynthesisEquiv_symm_coefficient]
    exact congrArg (fun a : Coeff 2 => a j) (unitL2SynthesisEquiv.symm_apply_apply u)
  have hV (j : ℤ) : unitFourierCoefficient V j = v j := by
    rw [unitFourierCoefficient_eq_intervalFourierCoefficient,←unitL2SynthesisEquiv_symm_coefficient]
    exact congrArg (fun a : Coeff 2 => a j) (unitL2SynthesisEquiv.symm_apply_apply v)
  have hprod : MemLp (fun x => U x*V x) 1 (volume.restrict (Ioc 0 1)) := (Lp.memLp V).mul (Lp.memLp U)
  have hg : IntervalIntegrable g volume 0 1 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hprod.integrable le_rfl)).const_mul (-2 : ℂ)
  have hfourier (j : ℤ) : 2*I*(Real.pi : ℂ)*j*unitFourierCoefficient V j = unitFourierCoefficient g j+0 := by
    rw [hV,unitFourierCoefficient_const_mul,unitFourierCoefficient_mul_of_memLp U V (Lp.memLp U) (Lp.memLp V)]
    simp_rw [hU,hV]
    have h := he j
    rw [periodOneMiuraProduct_apply] at h
    linear_combination h
  obtain ⟨F,hFc,hFa,hrep,hFd,hjump⟩ := exists_ac_unitInterval_representative_of_fourier_equation
    V g (Lp.memLp V) hg 0 hfourier
  have hnon : ∃ x ∈ Icc (0 : ℝ) 1, F x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : V = 0 := by
      apply Lp.ext
      filter_upwards [hrep,ae_restrict_mem measurableSet_Ioc,
        Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))] with x hx hxi hz
      rw [hx,h x ⟨hxi.1.le,hxi.2⟩]
      exact hz.symm
    apply hv
    apply unitL2SynthesisEquiv.injective
    exact hz.trans (map_zero _).symm
  refine ⟨F,hFc,hFa,hrep,sub_eq_zero.mp (by simpa using hjump),hnon,?_⟩
  filter_upwards [hFd,hrep] with x hd hx
  simpa only [g,hx,mul_assoc] using hd

/-- Every actual least-energy factor of EVERY real mean-zero rough
source has an actual nonzero periodic AC kernel representative. -/
theorem exists_periodOneMiura_minimal_energy_AC_kernel (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    ∃ e : ℝ, 0 ≤ e ∧ ∃ u : PeriodOneRealL2,
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) ∧
      ‖u.val‖^2 = e ∧
      (∀ (f : ℝ) (w : PeriodOneRealL2),
        periodOneMiura w.val = q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)) → e ≤ f) ∧
      ∃ v : Coeff 2, v ≠ 0 ∧ ∃ F : ℝ → ℂ,
        Continuous F ∧ AbsolutelyContinuousOnInterval F 0 1 ∧
        (unitL2SynthesisEquiv v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 1)] F ∧
        F 1 = F 0 ∧ (∃ x ∈ Icc (0 : ℝ) 1, F x ≠ 0) ∧
        ∀ᵐ x ∂volume.restrict (Ioc 0 1),
          HasDerivAt F ((-2 : ℂ)*(unitL2SynthesisEquiv u.val : ℝ → ℂ) x*F x) x := by
  obtain ⟨e,he,u,hu,hnorm,hmin⟩ := exists_periodOneMiura_minimal_energy q hr hm
  obtain ⟨v,hv,hker⟩ := exists_periodOneMiura_kernel_of_minimal q hr e u hu hmin
  exact ⟨e,he,u,hu,hnorm,hmin,v,hv,exists_periodOneMiura_kernel_AC u.val v hv hker⟩

end NLS
