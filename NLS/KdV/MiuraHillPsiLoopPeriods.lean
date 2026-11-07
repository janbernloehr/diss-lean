import NLS.KdV.HillPsiArbitraryShiftGrowth
import NLS.KdV.MiuraHillPsiEnergyCycles
import NLS.ZakharovShabat.SourceEntireNumeratorCircuit

/-! Actual Hill differential periods on arbitrary finite piecewise
smooth comparison loops inside an original cut disk. The normalization
and winding are retained; no circular image hypothesis is imposed. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace MiuraHillPsiFamily

theorem frequency_loop_period (A : MiuraHillPsiFamily) (n m : ℕ+) (u : Coeff 2) (hu : u ∈ A.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u) ((m:ℕ):ℤ))
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment (by norm_num) (by norm_num)
      (hillMiuraDiagonal u) ((m:ℕ):ℤ))) :
    (2*Real.pi:ℂ)⁻¹*Γ.integral (fun z => (2*z*A.numerator n (z^2,u))/
      sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u) z) =
        (if m = n then 1 else 0)*Γ.windingIntegral
          (sourceStandardRootMidpoint (by norm_num) (by norm_num) (hillMiuraDiagonal u) ((m:ℕ):ℤ)) := by
  have hF : AnalyticOnNhd ℂ (fun z : ℂ => 2*z*A.numerator n (z^2,u)) univ := by
    simpa only [add_zero] using A.shifted_numerator_pullback_entire n u 0
  rw [D.entireNumerator_loop_integral _ hF Γ hΓ,← mul_assoc,A.numerator_pullback_period n m u hu D]

theorem energy_loop_period (A : MiuraHillPsiFamily) (n m : ℕ+) (u : Coeff 2) (hu : u ∈ A.source)
    (c : ℂ) (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u) ((m:ℕ):ℤ))
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment (by norm_num) (by norm_num)
      (hillMiuraDiagonal u) ((m:ℕ):ℤ)))
    (hpos : Γ.Inside {z : ℂ | 0 < z.re}) :
    (2*Real.pi:ℂ)⁻¹*(quadraticEnergyLoop Γ c).integral (fun E => A.differential n c (E,u)) =
      (if m = n then 1 else 0)*Γ.windingIntegral
        (sourceStandardRootMidpoint (by norm_num) (by norm_num) (hillMiuraDiagonal u) ((m:ℕ):ℤ)) := by
  have he : (quadraticEnergyLoop Γ c).integral (fun E => A.differential n c (E,u)) =
      Γ.integral (fun z => (2*z*A.numerator n (z^2,u))/
        sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u) z) := by
    apply integral_quadraticEnergyLoop Γ c _ _ _ hpos
    intro z hz
    rw [differential,sub_add_cancel,hillHminusMiuraRoot_at_squared_energy u c z hz]
    ring
  rw [he]
  exact A.frequency_loop_period n m u hu D Γ hΓ

end MiuraHillPsiFamily
end NLS.KdV
