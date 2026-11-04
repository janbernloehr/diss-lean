import NLS.KdV.HillHminusOneComplexNormalizedIdentification
import NLS.KdV.HillHminusOneNormalizedFrequencySeries

/-! # Actual Miura normalized moments and analytic correction series

These moments use the actual Miura numerator on the original frequency
circles. Full complex-source numerator identification transfers exact periods,
all odd cancellations and the convergent second-moment series from the
constructed weighted family on one common rough ball around zero.
Physical Hamiltonian frequency identification remains a separate obligation.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- The literal original-circle moment of the actual Miura numerator. -/
def hillHminusMiuraMoment (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n k : ℕ+) (m : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    (hillHminusFrequencyPrimitive (z,q)+I*(k : ℂ)*Real.pi)^m*
      (hillHminusMiuraEnergyPsi C s (n : ℤ) (z^2,q)/hillHminusContinuedRoot (z^2,q))*(2*z)

/-- The second-moment correction candidate formed from the actual family. -/
def hillHminusMiuraMomentFrequencyCorrection (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  -12*∑' k : ℕ+, (k : ℂ)*hillHminusMiuraMoment C s n k 2 q

theorem hillHminusMiuraMoment_eq_normalized (C Dold : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (q : PeriodOneHminusOne)
    (hmatch : ∀ n : ℕ+, ∀ energy : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) =
      hillHminusNormalizedNumerator Dold N R n (energy,q)) (n k : ℕ+) (m : ℕ) :
    hillHminusMiuraMoment C s n k m q = hillHminusNormalizedMoment Dold N R n k m q := by
  unfold hillHminusMiuraMoment hillHminusNormalizedMoment hillHminusNormalizedMomentIntegrand
  apply circleIntegral.integral_congr (by positivity)
  intro z _
  dsimp only
  rw [hmatch n (z^2)]

/-- Positive moments indexed by the signed lattice, with zero nonpositive terms. -/
def hillHminusMiuraSecondMomentSeriesTerm (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℕ+)
    (q : PeriodOneHminusOne) (j : ℤ) : ℂ :=
  if hj : 0 < j then (j : ℂ)*hillHminusMiuraMoment C s n (positiveIntegerIndex j hj) 2 q else 0

theorem hillHminusMiuraSecondMomentSeriesTerm_eq_normalized (C Dold : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (q : PeriodOneHminusOne)
    (hmatch : ∀ n : ℕ+, ∀ energy : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) =
      hillHminusNormalizedNumerator Dold N R n (energy,q)) (n : ℕ+) (j : ℤ) :
    hillHminusMiuraSecondMomentSeriesTerm C s n q j = hillHminusSecondMomentSeriesTerm Dold N R n q j := by
  unfold hillHminusMiuraSecondMomentSeriesTerm hillHminusSecondMomentSeriesTerm
  split_ifs
  · rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q hmatch]
  · rfl

theorem hillHminusMiuraMomentFrequencyCorrection_eq_normalized (C Dold : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (q : PeriodOneHminusOne)
    (hmatch : ∀ n : ℕ+, ∀ energy : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) =
      hillHminusNormalizedNumerator Dold N R n (energy,q)) (n : ℕ+) :
    hillHminusMiuraMomentFrequencyCorrection C s n q = hillHminusMomentFrequencyCorrection Dold N R n q := by
  unfold hillHminusMiuraMomentFrequencyCorrection hillHminusMomentFrequencyCorrection
  congr 1
  apply tsum_congr
  intro k
  rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q hmatch]

/-- One actual normalized NLS family and one complex rough ball work before
all numerator indices, contour indices and moment orders. The second-moment
series is absolutely convergent and locally uniform, with analytic correction.
This is a local spectral construction, prior to Hamiltonian identification. -/
theorem exists_hillHminus_analytic_miura_frequency_series :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, ∃ W₀ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n)
          (univ ×ˢ ball (0 : PeriodOneHminusOne) δ)) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusMiuraMoment C s n k m)
          (ball (0 : PeriodOneHminusOne) δ)) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ n k : ℕ+,
          (2*(Real.pi : ℂ))⁻¹*hillHminusMiuraMoment C s n k 0 q = (if n = k then 1 else 0)) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ n k : ℕ+, ∀ l : ℕ,
          hillHminusMiuraMoment C s n k (2*l+1) q = 0) ∧
        ∀ n : ℕ+, (∀ q ∈ ball (0 : PeriodOneHminusOne) δ,
          Summable (fun k : ℕ+ => ‖(k : ℂ)*hillHminusMiuraMoment C s n k 2 q‖)) ∧
          AnalyticOnNhd ℂ (hillHminusMiuraMomentFrequencyCorrection C s n) (ball (0 : PeriodOneHminusOne) δ) ∧
          TendstoLocallyUniformlyOn
            (fun (L : ℕ) q => ∑ j ∈ Finset.Icc (1 : ℤ) L, hillHminusMiuraSecondMomentSeriesTerm C s n q j)
            (fun q => ∑' k : ℕ+, (k : ℂ)*hillHminusMiuraMoment C s n k 2 q)
            atTop (ball (0 : PeriodOneHminusOne) δ) := by
  obtain ⟨Dold,N,M,V,U,T,R,S,Q,r,B,hN,hM,hV,h0V,hUV,hU,h0U,D,Hcut,hseries⟩ :=
    exists_hillHminus_analytic_normalized_frequency_series
  obtain ⟨A,Dr⟩ := D.source_data
  obtain ⟨C,δ₀,W₀,W,s,hδ₀,hδV,hδC,H,hW,hpsi,hmatch⟩ :=
    exists_hillHminus_complex_normalized_family_identification Dold Dr T R
      (fun q hq m j => (D.entries q hq m j).1) (fun q hq => (D.inverses q hq).2.1) D.analytic_R
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hU.inter isOpen_ball) 0 ⟨h0U,mem_ball_self hδ₀⟩
  have hsub : ball (0 : PeriodOneHminusOne) δ ⊆ ball 0 δ₀ := fun q hq => (hball hq).2
  refine ⟨C,δ,W₀,W,s,hδ,hsub.trans hδC,H,fun q hq => hW q (hsub hq),
    fun n => (hpsi n).mono (fun t ht => ⟨ht.1,hsub ht.2⟩),?_,?_,?_,?_⟩
  · intro n k m q hq
    have heq : hillHminusMiuraMoment C s n k m =ᶠ[𝓝 q] hillHminusNormalizedMoment Dold N R n k m := by
      filter_upwards [isOpen_ball.mem_nhds hq] with p hp
      exact hillHminusMiuraMoment_eq_normalized C Dold N R s p (hmatch p (hsub hp)) n k m
    exact (D.moment_analytic n k m q (hUV (hball hq).1)).congr heq.symm
  · intro q hq n k
    rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q (hmatch q (hsub hq))]
    exact D.moment_zero q (hUV (hball hq).1) n k
  · intro q hq n k l
    rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q (hmatch q (hsub hq))]
    exact D.moment_odd q (hUV (hball hq).1) n k l
  intro n
  refine ⟨?_,?_,?_⟩
  · intro q hq
    have heq : (fun k : ℕ+ => ‖(k : ℂ)*hillHminusMiuraMoment C s n k 2 q‖) =
        (fun k : ℕ+ => ‖(k : ℂ)*hillHminusNormalizedMoment Dold N R n k 2 q‖) := by
      funext k
      rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q (hmatch q (hsub hq))]
    rw [heq]
    exact (hseries n).1 q (hball hq).1
  · intro q hq
    have heq : hillHminusMiuraMomentFrequencyCorrection C s n =ᶠ[𝓝 q] hillHminusMomentFrequencyCorrection Dold N R n := by
      filter_upwards [isOpen_ball.mem_nhds hq] with p hp
      exact hillHminusMiuraMomentFrequencyCorrection_eq_normalized C Dold N R s p (hmatch p (hsub hp)) n
    exact ((hseries n).2.1 q (hball hq).1).congr heq.symm

  · have hl := ((hseries n).2.2.mono (fun q hq => (hball hq).1)).congr
        (G := fun (L : ℕ) q => ∑ j ∈ Finset.Icc (1 : ℤ) L, hillHminusMiuraSecondMomentSeriesTerm C s n q j)
        (fun L q hq => by
          apply Finset.sum_congr rfl
          intro j _
          exact (hillHminusMiuraSecondMomentSeriesTerm_eq_normalized C Dold N R s q
            (hmatch q (hsub hq)) n j).symm)
    apply hl.congr_right
    intro q hq
    apply tsum_congr
    intro k
    rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q (hmatch q (hsub hq))]

end NLS.KdV
