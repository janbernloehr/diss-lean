import NLS.ZakharovShabat.SourceHigherSobolevAngleHamiltonian
import NLS.MKdV.MiuraSobolevCartesianRealForm
import NLS.MKdV.MiuraAngleActionBracket
import NLS.MKdV.MiuraSobolevCartesianSequence
import NLS.MKdV.MiuraEvenHamiltonianCotangentTransfer

/-! # Native lifts of the actual original NLS angle vector on the Miura diagonal -/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem existsUnique_miuraHigherSobolevThetaVector (m : ℕ)
    (a : MiuraRealSobolevSource m) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource m a.val)) (periodOnePotential_mem _) n ≠ 0) :
    ∃! v : SobolevSource m, higherSobolevSourceInclusion m v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n miuraNLSAngleFamily.psi
        (miuraSobolevActionSource m a.val) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  have ha : IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion m (a.val,a.val))) := by
    intro j
    change (higherSobolevSourceInclusion m (a.val,a.val)).snd j =
      conj ((higherSobolevSourceInclusion m (a.val,a.val)).fst (-j))
    rw [higherSobolevSourceInclusion_snd,higherSobolevSourceInclusion_fst]
    exact a.property j
  exact D.complex.existsUnique_thetaHamiltonian_higherSobolev miuraNLSAngleFamily.data m
    ⟨(a.val,a.val),ha⟩ n hn

def miuraHigherSobolevThetaVector (m : ℕ) (a : MiuraRealSobolevSource m) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource m a.val)) (periodOnePotential_mem _) n ≠ 0) :
    SobolevSource m := (existsUnique_miuraHigherSobolevThetaVector m a n hn).exists.choose

theorem miuraHigherSobolevThetaVector_inclusion (m : ℕ) (a : MiuraRealSobolevSource m) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource m a.val)) (periodOnePotential_mem _) n ≠ 0) :
    higherSobolevSourceInclusion m (miuraHigherSobolevThetaVector m a n hn) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n miuraNLSAngleFamily.psi
        (miuraSobolevActionSource m a.val) :=
  (existsUnique_miuraHigherSobolevThetaVector m a n hn).exists.choose_spec

/-- The original even NLS frequency on its actual H^m open-angle domain,
computed from the differential of the original S_(2m), independently of
any Hill action normal form. Sharp continuation is a separate statement. -/
def miuraOriginalEvenNLSAngleFrequency (s : ℕ) (a : MiuraRealSobolevSource (s+1)) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) : ℂ :=
  -fderiv ℂ (sobolevEvenHamiltonian (s+1) (by omega)) (a.val,a.val)
    (miuraHigherSobolevThetaVector (s+1) a n hn)

/-- The actual NLS angle-Hamiltonian bracket transfers to the independently
constructed native Hill differential, with its literal spatial direction. -/
theorem miuraOriginalEvenNLSAngleFrequency_eq_native_cotangent (s : ℕ)
    (a : MiuraRealSobolevSource (s+1)) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    miuraOriginalEvenNLSAngleFrequency s a n hn =
      -fderiv ℂ (nativeMiuraHillHamiltonian s)
        (hierarchySobolevInclusion (s+1) s (by omega) a.val)
        (miuraEvenCotangentDirection s (miuraHigherSobolevThetaVector (s+1) a n hn)) :=
  congrArg Neg.neg (fderiv_even_diagonal_eq_nativeHill_cotangent s a.val _)

end NLS.MKdV
