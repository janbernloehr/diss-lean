import NLS.KdV.HillLocalRegularTerminalData
import NLS.KdV.HillNativeRegularGapNumerator
import NLS.KdV.HillNativeRegularTerminal
import NLS.KdV.HillPhysicalRegularQuadraticTerminal

/-! # Native regular terminals equal the physical correction on local sheets -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillNativeRegularTerminal_eq_of_physical_data
    (k : ℕ+) (q : RealPeriodOneHillPotential) (u : Coeff 2)
    (hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u)
    (hdata : HillRegularTerminalPhysicalData h0q h0r k q)
    (H G : ℂ × Coeff 2 → Coeff 2)
    (hH : AnalyticOnNhd ℂ (fun E => H (E,u)) (ball (freeHillEnergy k) (3*(k : ℝ)/4)))
    (heq : ∀ E ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4),
      hillLocalGapPolynomial 0 h0q h0r (k : ℕ) (Coeff.periodDouble u) E • deriv (fun z => H (z,u)) E +
        (E-hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)) • H (E,u) =
          hillNativeRegularGapNumerator h0q h0r G k (E,u))
    (hG : ∀ n : ℕ+, ∀ E : ℂ, G (E,u) (n : ℤ) =
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E) :
    ∀ n : ℕ+, hillNativeRegularTerminal h0q h0r H k u (n : ℤ) =
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property (k : ℕ) k.property := by
  obtain ⟨r,hr,hrk,hM,hS,hτ,hδ,hmu,hμB,hU⟩ := hdata
  intro n
  have hsub : ball (freeHillEnergy k) (3*r/4) ⊆ ball (freeHillEnergy k) (3*(k : ℝ)/4) :=
    ball_subset_ball (by linarith)
  have hsubr : ball (freeHillEnergy k) (3*r/4) ⊆ ball (freeHillEnergy k) r := ball_subset_ball (by linarith)
  rw [hcoeff] at hM hS
  let ev : Coeff 2 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)
  let J : ℂ → ℂ := fun E => H (E,u) (n : ℤ)
  have hJ : AnalyticOnNhd ℂ J (ball (freeHillEnergy k) (3*r/4)) := by
    intro E hE
    exact (ev.analyticAt (H (E,u))).comp (f := fun E : ℂ => H (E,u)) (hH E (hsub hE))
  have hg (E : ℂ) (hE : E ∈ ball (freeHillEnergy k) (3*r/4)) :
      ev (hillNativeRegularGapNumerator h0q h0r G k (E,u)) =
        -I*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E /
          hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 (k : ℕ) E - (if k=n then 1 else 0) := by
    have hroot := hU E (hsubr hE)
    conv_lhs at hroot => rw [hcoeff]
    change (-I/hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u))*G (E,u) (n : ℤ) -
      (lp.single 2 (k : ℤ) (1 : ℂ) : Coeff 2) (n : ℤ) = _
    rw [hroot,hG n E]
    simp only [lp.single_apply,Pi.single_apply]
    by_cases hkn : k=n
    · subst n
      simp only [ite_true]
      ring
    · have hne : (n : ℤ) ≠ (k : ℤ) := by
        intro he
        apply hkn
        exact_mod_cast he.symm
      rw [if_neg hne,if_neg hkn]
      ring
  have hODE (E : ℂ) (hE : E ∈ ball (freeHillEnergy k) (3*r/4)) :
      ((E-(hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ))^2-
          (hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ) : ℂ)^2)*deriv J E +
        (E-(hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ))*J E =
          -I*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E /
            hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 (k : ℕ) E -
              (if (k : ℕ)=(n : ℕ) then 1 else 0) := by
    have hd := ev.hasFDerivAt.comp_hasDerivAt E (hH E (hsub hE)).differentiableAt.hasDerivAt
    change HasDerivAt J (ev (deriv (fun z => H (z,u)) E)) E at hd
    have hh := congrArg ev (heq E (hsub hE))
    simp only [map_add,map_smul,smul_eq_mul] at hh
    rw [← hd.deriv,hillLocalGapPolynomial,hM,hS] at hh
    have hs : (2*(hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ) : ℂ))^2/4 =
        (hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ) : ℂ)^2 := by ring
    rw [hs] at hh
    change ((E-(hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ))^2-
      (hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ) : ℂ)^2)*deriv J E +
      (E-(hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ))*J E =
        ev (hillNativeRegularGapNumerator h0q h0r G k (E,u)) at hh
    simpa only [PNat.coe_inj] using hh.trans (hg E hE)
  have hphys := hillRegularAbelianCorrection_eq_regular_quadratic_terminal q.val q.property.1 q.property.2
    (n : ℕ) (k : ℕ) n.property k.property (freeHillEnergy k) r hr J hJ hτ hδ hODE
  have ht : hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u) =
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property) /
        hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 (k : ℕ) (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property) := by
    rw [hillScaledComplexDirichletGapTerminal,← hcoeff,hmu,hU _ hμB]
  conv_lhs at hmu => rw [hcoeff]
  change (I*hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u))*
    H (hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u),u) (n : ℤ) = _
  rw [ht,hmu,hphys]
  dsimp only [J]
  ring

end NLS.KdV
