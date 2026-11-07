import NLS.KdV.MiuraFractionalDirichletComparison
import NLS.KdV.HillMiuraFractionalLiftBound

/-! # Local fractional estimates for actual native Dirichlet eigenfunctions

A fixed H-minus-one Miura chart supplies a uniform power bound for every
potential in a bounded H^(-r) slice of one open native neighborhood.
-/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.ZakharovShabat NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier
local instance fractionalDirichletH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance fractionalDirichletH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

theorem HillHminusMiuraChart.exists_uniform_fractional_dirichletEigenfunction_bound
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, ∃ B : ℝ,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ 0 ≤ B ∧
      ∀ b : WeightedCoeff (Weight.sobolev (-r)) 2, ‖b‖ ≤ M →
        sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b ∈ V →
        ∀ n : ℕ+, N < (n:ℕ) → ∃ g : UnitDirichletH1, g ≠ 0 ∧
          singularDirichletOperator
              (periodOneOriginal (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b)) g =
            hillHminusDirichletComplexLabels (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b) n •
              singularDirichletDomainInclusion g ∧
          ‖unitDirichletContinuousInclusion g-dirichletFreeSineCurve n‖ ≤ B*(n:ℝ)^(-(1-r)) := by
  obtain ⟨Vb,R,L,hVb,hqVb,hVbd,hR,hL,hbound⟩ :=
    C.exists_local_fractional_lift_bound q hq r hr hr1 M hM
  let Taux := auxiliaryPeriodOneDirichletPotential (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2:ℝ≥0∞))
  let Fa : PeriodOneHminusOne → dirichletSubspace (p := 2) :=
    fun a => Taux (hillMiuraDiagonal (C.lift a))
  have hFa : AnalyticOnNhd ℂ Fa C.domain := by
    intro a ha
    exact (Taux.analyticAt _).comp ((hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha))
  obtain ⟨N₀,V₀,hN₀,hV₀,hq₀,_,hcontrol,_⟩ := C.exists_uniform_analytic_dirichletControl q hq
  obtain ⟨N₁,U₁,_,hU₁,_,hq₁,_,hsmall⟩ :=
    exists_uniform_small_canonicalBoundaryDisks (by simp) (by norm_num) (Fa q)
      (show 0 < Real.pi/4 by positivity) le_rfl
  let V := V₀ ∩ (Vb ∩ Fa ⁻¹' U₁)
  have hV : IsOpen V := by
    have he : Vb ∩ Fa ⁻¹' U₁ = Vb ∩ (C.domain ∩ Fa ⁻¹' U₁) := by
      ext a
      simp only [mem_inter_iff,mem_preimage]
      exact ⟨fun h => ⟨h.1,hVbd h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩
    apply hV₀.inter
    rw [he]
    exact hVb.inter (hFa.continuousOn.isOpen_inter_preimage C.domain_open hU₁)
  obtain ⟨D,hD,hcompare⟩ := exists_miura_fractional_dirichlet_comparison_constant
  let B := D*miuraFractionalFreeConstant R 1*L
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hD (miuraFractionalFreeConstant_nonneg _ _ hR)) hL
  refine ⟨max N₀ N₁,V,B,hN₀.trans_le (le_max_left _ _),hV,⟨hq₀,hqVb,hq₁⟩,hB,?_⟩
  intro b hb ha n hn
  let a : PeriodOneHminusOne := sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b
  have had : a ∈ C.domain := hVbd ha.2.1
  obtain ⟨U,hU,hlift,hUL⟩ := hbound b hb ha.2.1
  have hs : 0 ≤ 1-r := by linarith
  have hs1 : 1-r ≤ 1 := by linarith
  have hraw := sobolevToL2_eq_of_raw_coefficients (1-r) hs U (C.lift a) hU
  let z := hillMiuraDiracDirichlet (C.lift a) (n:ℕ)
  have hn₀ : N₀ < (n:ℕ) := (le_max_left _ _).trans_lt hn
  have hn₁ : N₁ < (n:ℕ) := (le_max_right _ _).trans_lt hn
  have hdisk := hsmall (Fa a) ha.2.2 .dirichlet ((n:ℕ):ℤ) (by simpa using hn₁)
  have hfreq : ‖z-(Real.pi:ℂ)*(n:ℕ)‖ ≤ Real.pi/4 := by
    have hh : ‖z-(Real.pi:ℂ)*(n:ℕ)‖ < Real.pi/4 := by
      simpa only [Fa,Taux,z,hillMiuraDiracDirichlet,canonicalAuxiliaryPeriodOneRoots,
        Int.cast_natCast,mem_ball,dist_eq_norm] using hdisk
    exact hh.le
  have hz : z ≠ 0 := by
    intro he
    rw [he,zero_sub,norm_neg] at hfreq
    have hc : ‖(Real.pi:ℂ)*(n:ℕ)‖ = Real.pi*(n:ℝ) := by simp [Real.pi_pos.le]
    rw [hc] at hfreq
    have hnp : (1:ℝ) ≤ n := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  have hroot : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal (C.lift a)) z = 0 :=
    (auxiliaryPeriodOneCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet _ z).mpr
      ((canonicalAuxiliaryPeriodOneRoots_exhaustive (by simp) (by norm_num) .dirichlet _ z).mpr
        ⟨((n:ℕ):ℤ),rfl⟩)
  obtain ⟨g,hg0,hg,hpos⟩ := exists_native_Miura_eigen_with_sineCurve (C.lift a) z hz hroot
  have he : singularDirichletOperator (periodOneOriginal a) g =
      hillHminusDirichletComplexLabels a n • singularDirichletDomainInclusion g := by
    rw [hillHminusDirichletComplexLabels_eq_tail_of_control a (C.lift a) C.energyShift N₀
      (hcontrol a ha.1) n hn₀]
    apply (singularDirichlet_source_eigen_add_constant_iff a (hillMiuraDirichletEnergy (C.lift a) C.energyShift (n:ℕ))
      C.energyShift g).mp
    rw [← C.image a had]
    simpa only [hillMiuraDirichletEnergy,sub_add_cancel] using hg
  refine ⟨g,hg0,he,?_⟩
  rw [hpos]
  have hcomp := hcompare (1-r) hs hs1 U R (by rw [hraw]; exact hlift) n z hfreq (by rw [hraw]; exact hroot)
  rw [hraw] at hcomp
  apply hcomp.trans
  have hcoef : 0 ≤ D*miuraFractionalFreeConstant R 1*(n:ℝ)^(-(1-r)) := by
    exact mul_nonneg (mul_nonneg hD (miuraFractionalFreeConstant_nonneg _ _ hR)) (Real.rpow_nonneg (by positivity) _)
  exact (mul_le_mul_of_nonneg_left hUL hcoef).trans_eq (by dsimp only [B]; ring)

end NLS.KdV
