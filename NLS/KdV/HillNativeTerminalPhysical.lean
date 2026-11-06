import NLS.KdV.HillNativeRegularTerminal
import NLS.KdV.HillPhysicalRegularQuadraticTerminal
import NLS.KdV.HillUniformDirichletPhysical
import NLS.KdV.HillUniformRealGapLocalization
import NLS.KdV.HillFilledFreeGapPhysical

/-! # Physical identification of native regular terminal vectors

One high cutoff works for every positive output, including the own mode.
The actual moving Dirichlet root, deflated root and symmetric gap data fix
the terminal sheet, while the native vector equation supplies every scalar
physical equation through continuous coordinate evaluation.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillNative_regular_terminal_physical_matching (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖ ≤ B →
      ∀ u : Coeff 2, SpectralWeight.one.toCoeff q = Coeff.periodDouble u →
      ∀ k : ℕ+, N ≤ (k : ℕ) → ∀ H : ℂ × Coeff 2 → Coeff 2, ∀ g : ℂ → Coeff 2,
      AnalyticOnNhd ℂ (fun E => H (E,u)) (ball (freeHillEnergy k) (3*(k : ℝ)/4)) →
      (∀ E ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4),
        hillLocalGapPolynomial 0 h0q h0r (k : ℕ) (Coeff.periodDouble u) E • deriv (fun z => H (z,u)) E +
          (E-hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)) • H (E,u) = g E) →
      (∀ n : ℕ+, ∀ E ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4), g E (n : ℤ) =
        -I*hillAbelianSelectedGlobalPsi q hq hr (n : ℕ) n.property E /
          hillDeflatedEnergyCanonicalRoot q hq hr (k : ℕ) E - (if k=n then 1 else 0)) →
      ∀ n : ℕ+, hillNativeRegularTerminal h0q h0r H k u (n : ℤ) =
        hillRegularAbelianCorrection q hq hr (n : ℕ) n.property (k : ℕ) k.property := by
  obtain ⟨Ns,_,hsymmetric⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r B
  obtain ⟨Nl,_,hlocal⟩ := exists_hillFreeGap_bounded_real_midpoint_halfgap_localization
    h0q h0r (1/128) (by norm_num) (by norm_num) B
  obtain ⟨Nm,_,hmumatch⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching
    h0q h0r (1/128) (by norm_num) (by norm_num) B
  obtain ⟨Nc,_,hmuchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/128) (by norm_num) (by norm_num) B
  obtain ⟨Nr,_,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching h0q h0r B
  refine ⟨Ns+Nl+Nm+Nc+Nr+1,by omega,?_⟩
  intro q hq hr hp u hcoeff k hk H g hH heq hphysical n
  have hks : Ns ≤ (k : ℕ) := by omega
  have hkl : Nl ≤ (k : ℕ) := by omega
  have hkm : Nm ≤ (k : ℕ) := by omega
  have hkc : Nc ≤ (k : ℕ) := by omega
  have hkr : Nr ≤ (k : ℕ) := by omega
  obtain ⟨hM,hS⟩ := hsymmetric q hq hr hp (k : ℕ) hks
  obtain ⟨hτ,hδ⟩ := hlocal q hq hr hp (k : ℕ) hkl
  obtain ⟨hc,_,hRhi⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  rw [hc] at hτ
  have hτ' : ‖(hillRealGapCenter q hq hr (k : ℕ) : ℂ)-freeHillEnergy k‖ ≤ (k : ℝ)/16 := by linarith
  have hδ' : ‖(hillRealGapHalfLength q hq hr (k : ℕ) : ℂ)‖ ≤ (k : ℝ)/16 := by linarith
  rw [hcoeff] at hM hS
  let ev : Coeff 2 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)
  let J : ℂ → ℂ := fun E => H (E,u) (n : ℤ)
  have hJ : AnalyticOnNhd ℂ J (ball (freeHillEnergy k) (3*(k : ℝ)/4)) := by
    intro E hE
    exact (ev.analyticAt (H (E,u))).comp (f := fun E : ℂ => H (E,u)) (hH E hE)
  have hODE (E : ℂ) (hE : E ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4)) :
      ((E-(hillRealGapCenter q hq hr (k : ℕ) : ℂ))^2-(hillRealGapHalfLength q hq hr (k : ℕ) : ℂ)^2)*deriv J E +
        (E-(hillRealGapCenter q hq hr (k : ℕ) : ℂ))*J E =
          -I*hillAbelianSelectedGlobalPsi q hq hr (n : ℕ) n.property E /
            hillDeflatedEnergyCanonicalRoot q hq hr (k : ℕ) E - (if (k : ℕ)=(n : ℕ) then 1 else 0) := by
    have hd := ev.hasFDerivAt.comp_hasDerivAt E (hH E hE).differentiableAt.hasDerivAt
    change HasDerivAt J (ev (deriv (fun z => H (z,u)) E)) E at hd
    have hh := congrArg ev (heq E hE)
    simp only [map_add,map_smul,smul_eq_mul] at hh
    rw [← hd.deriv,hillLocalGapPolynomial,hM,hS] at hh
    have hs : (2*(hillRealGapHalfLength q hq hr (k : ℕ) : ℂ))^2/4 =
        (hillRealGapHalfLength q hq hr (k : ℕ) : ℂ)^2 := by ring
    rw [hs] at hh
    change ((E-(hillRealGapCenter q hq hr (k : ℕ) : ℂ))^2-
      (hillRealGapHalfLength q hq hr (k : ℕ) : ℂ)^2)*deriv J E +
      (E-(hillRealGapCenter q hq hr (k : ℕ) : ℂ))*J E = g E (n : ℤ) at hh
    have hm := hphysical n E hE
    simpa only [PNat.coe_inj] using hh.trans hm
  have hphys := hillRegularAbelianCorrection_eq_regular_quadratic_terminal q hq hr
    (n : ℕ) (k : ℕ) n.property k.property (freeHillEnergy k) (k : ℝ) (by positivity)
    J hJ hτ' hδ' hODE
  have hmu := hmumatch q hq hr hp (k : ℕ) hkm
  have hμK := ((hmuchart (k : ℕ) hkc).2 _ hp).1
  have hR : 0 < hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ) :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).1
      (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).2.1
  have hμold : hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (SpectralWeight.one.toCoeff q) ∈
      closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
        (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)) :=
    closedBall_subset_closedBall (by linarith :
      (1/128)*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)) ≤
        hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)) (ball_subset_closedBall hμK)
  rw [hmu] at hμold
  have hU := hroot q hq hr hp (k : ℕ) hkr _ hμold
  have ht : hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u) =
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr (k : ℕ) k.property) /
        hillDeflatedEnergyCanonicalRoot q hq hr (k : ℕ) (hillDirichletEnergy q hq hr (k : ℕ) k.property) := by
    rw [hillScaledComplexDirichletGapTerminal,← hcoeff,hmu,hU]
  conv_lhs at hmu => rw [hcoeff]
  change (I*hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u))*
    H (hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u),u) (n : ℤ) = _
  rw [ht,hmu,hphys]
  dsimp only [J]
  ring

end NLS.KdV
