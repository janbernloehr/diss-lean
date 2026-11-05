import NLS.KdV.HillNativeActionGapRatio
import NLS.KdV.HillAllRegularTerminalData
import NLS.KdV.HillActionGapFactor

/-! # Exact all-gap physical identification of the native action ratio -/
noncomputable section
open Set Metric Complex Filter Topology MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillNativeActionGapRatio_eq_physical_of_terminal_data (k : ℕ+)
    (q : RealPeriodOneHillPotential) (u : Coeff 2)
    (hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u)
    (hdata : HillRegularTerminalPhysicalData h0q h0r k q) :
    hillNativeActionGapRatio h0q h0r k u = hillActionGapRatio q.val q.property.1 q.property.2 (k : ℕ) := by
  obtain ⟨r,hr,_,hτ,hS,hτsmall,hδsmall,_,_,hU⟩ := hdata
  let T := hillNativeFilledTraceNumerator h0q h0r k
  let τ := fun v : Coeff 2 => hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble v)
  let δ : ℂ := hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ)
  have htau : τ u = (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ) := by
    simpa only [τ,← hcoeff] using hτ
  have hsq : (sqrt (hillLocalGapSquare 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)/4))^2 = δ^2 := by
    rw [complex_sqrt_sq,← hcoeff,hS]
    change (2*δ)^2/4 = δ^2
    ring
  have hmean : parametricSineSquareCosineMean
      (fun t : ℂ × Coeff 2 => deriv (fun E => T (E,t.2)) t.1) τ
      (sqrt (hillLocalGapSquare 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)/4),u) =
      parametricSineSquareCosineMean
        (fun t : ℂ × Coeff 2 => deriv (fun E => T (E,t.2)) t.1) τ (δ,u) := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with he | he
    · rw [he]
    · rw [he,parametricSineSquareCosineMean_neg]
  change (-2*I/(Real.pi : ℂ))*parametricSineSquareCosineMean
    (fun t : ℂ × Coeff 2 => deriv (fun E => T (E,t.2)) t.1) τ _ = _
  rw [hmean,hillActionGapRatio,parametricSineSquareCosineMean]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  let z : ℂ := (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ)+δ*(Real.cos θ : ℂ)
  have hz : z ∈ ball (freeHillEnergy k) r := by
    rw [mem_ball_iff_norm]
    have hc : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by
      simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg δ)
    have he := norm_add_le ((hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ)-freeHillEnergy k)
      (δ*(Real.cos θ : ℂ))
    rw [show (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ)-freeHillEnergy k+
      δ*(Real.cos θ : ℂ)=z-freeHillEnergy k by dsimp only [z]; ring,norm_mul] at he
    change ‖δ‖ ≤ r/16 at hδsmall
    nlinarith
  have hEq : (fun E => T (E,u)) =ᶠ[𝓝 z] hillDeflatedTraceNumerator q.val q.property.1 q.property.2 (k : ℕ) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with E hE
    dsimp only [T,hillNativeFilledTraceNumerator,hillDeflatedTraceNumerator]
    rw [← hcoeff,hU E hE]
  rw [htau]
  exact congrArg (fun a : ℂ => (Real.sin θ : ℂ)^2*a) hEq.deriv_eq

theorem exists_hillNativeActionGapRatio_all_physical_matching :
    ∃ η : ℝ, 0 < η ∧ ∀ q : RealPeriodOneHillPotential, ∀ u : Coeff 2,
      SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u → ‖u‖ < η → ∀ k : ℕ+,
      hillNativeActionGapRatio h0q h0r k u = hillActionGapRatio q.val q.property.1 q.property.2 (k : ℕ) := by
  obtain ⟨η,hη,_,hphysical⟩ := exists_hillRegularTerminalPhysicalData_all h0q h0r
  refine ⟨η,hη,?_⟩
  intro q u hcoeff hu k
  apply hillNativeActionGapRatio_eq_physical_of_terminal_data h0q h0r k q u hcoeff
  apply hphysical k q
  rwa [hcoeff,Coeff.norm_periodDouble]

end NLS.KdV
