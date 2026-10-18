import NLS.ZakharovShabat.NLSHamiltonianPhaseReflection
import NLS.ZakharovShabat.SobolevHamiltonianRescaling
import NLS.ZakharovShabat.SobolevHamiltonianPhase

/-! # Hamiltonian reflection on original Sobolev spaces

Smooth density and continuity extend the Hamiltonian parity and phase identities to nonsmooth complex sources on their original domains.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

private theorem hamiltonian_signedSwap_of_smooth
    (s k : ℕ) (F : SobolevSource s → ℂ) (hF : Continuous F)
    (hc : ∀ (ab : SobolevSource s) (a b : ℝ → ℂ),
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) → F ab = classicalNLSHamiltonian a b (k+1))
    (ab : SobolevSource s) : F (-ab.2,-ab.1) = (-1:ℂ)^k*F ab := by
  have he := eq_of_continuous_of_smooth_sobolevSource s
    (fun cd => F (-cd.2,-cd.1)) (fun cd => (-1:ℂ)^k*F cd)
    (hF.comp (continuous_snd.neg.prodMk continuous_fst.neg)) (continuous_const.mul hF) (by
      intro cd a b ha hb hpa hpb hca hcb
      have hca' (j : ℤ) : (-cd.2).val j = periodOneCoefficient (-b) j := by
        simpa only [WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hcb j)
      have hcb' (j : ℤ) : (-cd.1).val j = periodOneCoefficient (-a) j := by
        simpa only [WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hca j)
      rw [hc (-cd.2,-cd.1) (-b) (-a) hb.neg ha.neg
        (fun x => congrArg Neg.neg (hpb x)) (fun x => congrArg Neg.neg (hpa x)) hca' hcb',
        hc cd a b ha hb hpa hpb hca hcb]
      exact classicalNLSHamiltonian_signedSwap a b ha hb hpa hpb k)
  exact congrFun he ab

/-- Every actual Fourier-defined Hamiltonian has the reflection sign on
its full original Sobolev domain, including nonsmooth complex sources. -/
theorem sobolevNLSHamiltonian_signedSwap
    (s k : ℕ) (hk : k+1 ≤ s+1) (ab : SobolevSource s) :
    sobolevNLSHamiltonian s (-ab.2,-ab.1) (k+1) hk =
      (-1:ℂ)^k*sobolevNLSHamiltonian s ab (k+1) hk :=
  hamiltonian_signedSwap_of_smooth s k _ (continuous_sobolevNLSHamiltonian s (k+1) hk)
    (fun cd a b ha hb hpa hpb hca hcb =>
      sobolevNLSHamiltonian_eq_classical s cd a b ha hb hpa hpb hca hcb (k+1) hk) ab

/-- Odd Hamiltonians retain signed-swap invariance at their sharper Hm
regularity, without imposing H(2m). -/
theorem sobolevOddHamiltonian_signedSwap
    (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    sobolevOddHamiltonian m hm (-ab.2,-ab.1) = sobolevOddHamiltonian m hm ab := by
  have h := hamiltonian_signedSwap_of_smooth m (2*m) _ (continuous_sobolevOddHamiltonian m hm)
    (fun cd a b ha hb hpa hpb hca hcb =>
      sobolevOddHamiltonian_eq_classical m hm cd a b ha hb hpa hpb hca hcb) ab
  simpa only [pow_mul,neg_one_sq,one_pow,one_mul] using h

/-- Exact reflected phase cancellation extends to every original complex
Sobolev source at the stated truncation regularity. -/
theorem sobolevHamiltonianPhase_signedSwap
    (s N : ℕ) (hNs : N ≤ s) (ab : SobolevSource s) (z : ℂ) :
    sobolevHamiltonianPhase s N hNs (-ab.2,-ab.1) (-z) =
      -sobolevHamiltonianPhase s N hNs ab z := by
  have he := eq_of_continuous_of_smooth_sobolevSource s
    (fun cd => sobolevHamiltonianPhase s N hNs (-cd.2,-cd.1) (-z))
    (fun cd => -sobolevHamiltonianPhase s N hNs cd z)
    ((continuous_sobolevHamiltonianPhase s N hNs (-z)).comp
      (continuous_snd.neg.prodMk continuous_fst.neg))
    (continuous_sobolevHamiltonianPhase s N hNs z).neg (by
      intro cd a b ha hb hpa hpb hca hcb
      have hca' (j : ℤ) : (-cd.2).val j = periodOneCoefficient (-b) j := by
        simpa only [WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hcb j)
      have hcb' (j : ℤ) : (-cd.1).val j = periodOneCoefficient (-a) j := by
        simpa only [WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hca j)
      rw [sobolevHamiltonianPhase_eq_classical s N hNs (-cd.2,-cd.1) (-b) (-a) hb.neg ha.neg
        (fun x => congrArg Neg.neg (hpb x)) (fun x => congrArg Neg.neg (hpa x)) hca' hcb',
        sobolevHamiltonianPhase_eq_classical s N hNs cd a b ha hb hpa hpb hca hcb]
      exact nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb N z)
  exact congrFun he ab

end NLS.ZakharovShabat
