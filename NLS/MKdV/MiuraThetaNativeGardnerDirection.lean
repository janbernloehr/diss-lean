import NLS.MKdV.MiuraHigherSobolevThetaVector
import NLS.Poisson.L2CotangentGardner

/-! # The actual restricted angle's Gardner direction in the native norm

At an H^(s+1) profile its original NLS angle vector has the same regularity.
The physical spatial difference therefore lies in H^s and represents the
actual spatial derivative of the pulled-back angle cotangent's gradient.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem l2DiagonalCotangentGradient_sourceHamiltonian (L : CoeffPair 2 →L[ℂ] ℂ) (j : ℤ) :
    l2CotangentGradient (L.comp scalarL2Diagonal) j =
      I*((sourceHamiltonianDirection le_rfl L).fst j-(sourceHamiltonianDirection le_rfl L).snd j) := by
  rw [l2CotangentGradient_apply,ContinuousLinearMap.comp_apply]
  change L (CoeffPair.inlCLM (lp.single 2 (-j) 1)+CoeffPair.inrCLM (lp.single 2 (-j) 1)) = _
  rw [map_add,sourceHamiltonianDirection_fst_apply,sourceHamiltonianDirection_snd_apply]
  change L (CoeffPair.inlCLM (lp.single 2 (-j) 1))+L (CoeffPair.inrCLM (lp.single 2 (-j) 1)) =
    I*(-I*L (CoeffPair.inrCLM (lp.single 2 (-j) 1))-I*L (CoeffPair.inlCLM (lp.single 2 (-j) 1)))
  linear_combination (L (CoeffPair.inlCLM (lp.single 2 (-j) 1))+
    L (CoeffPair.inrCLM (lp.single 2 (-j) 1)))*I_sq

def miuraNativeThetaCotangent (m : ℕ) (a : ScalarSobolev m) (n : ℕ) : Coeff 2 →L[ℂ] ℂ :=
  (sourceAngularThetaDifferential (by simp) (by norm_num) n miuraNLSAngleFamily.psi
    (miuraSobolevActionSource m a)).comp scalarL2Diagonal

theorem miuraHigherSobolevThetaVector_gradient (m : ℕ) (a : MiuraRealSobolevSource m) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource m a.val)) (periodOnePotential_mem _) n ≠ 0) (j : ℤ) :
    l2CotangentGradient (miuraNativeThetaCotangent m a.val n) j =
      I*((miuraHigherSobolevThetaVector m a n hn).1.val j-
        (miuraHigherSobolevThetaVector m a n hn).2.val j) := by
  rw [miuraNativeThetaCotangent,l2DiagonalCotangentGradient_sourceHamiltonian]
  change I*((sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n
    miuraNLSAngleFamily.psi (miuraSobolevActionSource m a.val)).fst j-
    (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n
    miuraNLSAngleFamily.psi (miuraSobolevActionSource m a.val)).snd j) = _
  rw [← miuraHigherSobolevThetaVector_inclusion m a n hn,
    higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd]

def miuraThetaNativeGardnerDirection (s : ℕ) (a : MiuraRealSobolevSource (s+1)) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    ScalarSobolev s := miuraEvenCotangentDirection s (miuraHigherSobolevThetaVector (s+1) a n hn)

theorem miuraThetaNativeGardnerDirection_coefficients (s : ℕ) (a : MiuraRealSobolevSource (s+1)) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) (j : ℤ) :
    (miuraThetaNativeGardnerDirection s a n hn).val j =
      2*I*(Real.pi : ℂ)*j*l2CotangentGradient (miuraNativeThetaCotangent (s+1) a.val n) j := by
  rw [miuraHigherSobolevThetaVector_gradient (s+1) a n hn j]
  change (miuraEvenCotangentDirection s _).val j = _
  rw [miuraEvenCotangentDirection_apply]
  ring

theorem miuraThetaNativeGardnerDirection_mean_zero (s : ℕ) (a : MiuraRealSobolevSource (s+1)) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    (miuraThetaNativeGardnerDirection s a n hn).val 0 = 0 := by
  rw [miuraThetaNativeGardnerDirection_coefficients]
  simp

theorem miuraThetaNativeGardnerDirection_memlp (s : ℕ) (a : MiuraRealSobolevSource (s+1)) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    Memℓp (fun j : ℤ => 2*I*(Real.pi : ℂ)*j*
      l2CotangentGradient (miuraNativeThetaCotangent (s+1) a.val n) j) 2 := by
  have h := lp.memℓp (hierarchySobolevJetL2 s 0 (Nat.zero_le s) (miuraThetaNativeGardnerDirection s a n hn))
  convert h using 1
  funext j
  rw [hierarchySobolevJetL2_apply,pow_zero,one_mul,miuraThetaNativeGardnerDirection_coefficients]

theorem miuraThetaNativeGardnerDirection_L2 (s : ℕ) (a : MiuraRealSobolevSource (s+1)) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    hierarchySobolevJetL2 s 0 (Nat.zero_le s) (miuraThetaNativeGardnerDirection s a n hn) =
      l2SpatialDerivative (l2CotangentGradient (miuraNativeThetaCotangent (s+1) a.val n)) := by
  ext j
  rw [l2SpatialDerivative_apply _ (miuraThetaNativeGardnerDirection_memlp s a n hn),
    hierarchySobolevJetL2_apply,pow_zero,one_mul,miuraThetaNativeGardnerDirection_coefficients]

end NLS.MKdV
