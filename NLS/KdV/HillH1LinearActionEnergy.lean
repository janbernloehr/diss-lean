import NLS.KdV.HillNativeH1Source
import NLS.KdV.HillWeightedActionSequence
import NLS.SequenceSpaces.Multiplier

/-! # The original cubic-weighted linear KdV action energy is continuous on H1 -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

def hillH1LinearActionSymbol (k : ℤ) : ℂ :=
  ((4*Real.pi^2*((Equiv.intEquivNat k+1 : ℕ)/(1+2*(Equiv.intEquivNat k+1 : ℕ)))^2 : ℝ) : ℂ)

theorem norm_hillH1LinearActionSymbol_le (k : ℤ) : ‖hillH1LinearActionSymbol k‖ ≤ 4*Real.pi^2 := by
  let n : ℝ := (Equiv.intEquivNat k+1 : ℕ)
  have hn : 0 ≤ n := by dsimp [n];positivity
  have hd : 0 < 1+2*n := by positivity
  have hratio : 0 ≤ n/(1+2*n) := div_nonneg hn hd.le
  have hratio1 : n/(1+2*n) ≤ 1 := (div_le_one hd).mpr (by linarith)
  change ‖((4*Real.pi^2*(n/(1+2*n))^2 : ℝ) : ℂ)‖ ≤ _
  rw [norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg Real.pi,pow_le_one₀ hratio hratio1 (n := 2)]

def hillH1LinearActionMultiplier : Coeff ⊤ :=
  ⟨hillH1LinearActionSymbol,memℓp_infty ⟨4*Real.pi^2,by
    rintro _ ⟨k,rfl⟩;exact norm_hillH1LinearActionSymbol_le k⟩⟩

def hillH1LinearActionSequence (q : RealHillWeightedPotential hillH1SpectralWeight) : Coeff 1 :=
  Coeff.multiplierCLM hillH1LinearActionMultiplier (hillWeightedActionSequence hillH1SpectralWeight q)

theorem hillH1LinearActionSequence_apply
    (q : RealHillWeightedPotential hillH1SpectralWeight) (k : ℤ) :
    hillH1LinearActionSequence q k =
      ((8*Real.pi^3*(Equiv.intEquivNat k+1 : ℕ)^3*
        hillPeriodOneAction hillH1SpectralWeight q.val q.property (Equiv.intEquivNat k+1) : ℝ) : ℂ) := by
  change hillH1LinearActionSymbol k*(hillWeightedActionTerm hillH1SpectralWeight q (Equiv.intEquivNat k+1) : ℂ) = _
  have hw (n : ℕ) : hillH1SpectralWeight (2*(n : ℤ)) = 1+2*(n : ℝ) := by
    change hillH1SpectralWeight.doubleIndex (n : ℤ) = _
    simpa only [Int.cast_natCast,Nat.abs_cast] using hillH1SpectralWeight_doubleIndex (n : ℤ)
  rw [hillH1LinearActionSymbol,hillWeightedActionTerm,hw]
  rw [←ofReal_mul]
  have hn : (1 : ℝ)+2*(Equiv.intEquivNat k+1 : ℕ) ≠ 0 := by positivity
  apply congrArg Complex.ofReal
  field_simp
  ring

def hillH1LinearActionEnergy (q : RealHillWeightedPotential hillH1SpectralWeight) : ℂ :=
  lp.tsumCLM ℂ ℤ ℂ (hillH1LinearActionSequence q)

theorem continuous_hillH1LinearActionEnergy : Continuous hillH1LinearActionEnergy :=
  (lp.tsumCLM ℂ ℤ ℂ).continuous.comp
    ((Coeff.multiplierCLM hillH1LinearActionMultiplier).continuous.comp
      (continuous_hillWeightedActionSequence hillH1SpectralWeight))

theorem hillH1LinearActionEnergy_eq_tsum
    (q : RealHillWeightedPotential hillH1SpectralWeight) :
    hillH1LinearActionEnergy q = ∑' n : ℕ,
      ((8*Real.pi^3*(n+1 : ℕ)^3*hillPeriodOneAction hillH1SpectralWeight q.val q.property (n+1) : ℝ) : ℂ) := by
  change (∑' k : ℤ, hillH1LinearActionSequence q k) = _
  simp_rw [hillH1LinearActionSequence_apply]
  exact Equiv.intEquivNat.tsum_eq (fun n : ℕ =>
    ((8*Real.pi^3*(n+1 : ℕ)^3*hillPeriodOneAction hillH1SpectralWeight q.val q.property (n+1) : ℝ) : ℂ))

theorem summable_norm_hillH1LinearActionTerms
    (q : RealHillWeightedPotential hillH1SpectralWeight) :
    Summable (fun n : ℕ => ‖((8*Real.pi^3*(n+1 : ℕ)^3*
      hillPeriodOneAction hillH1SpectralWeight q.val q.property (n+1) : ℝ) : ℂ)‖) := by
  have hs := (lp.memℓp (hillH1LinearActionSequence q)).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_one,Real.rpow_one,hillH1LinearActionSequence_apply] at hs
  exact Equiv.intEquivNat.summable_iff.mp hs

end NLS.KdV
