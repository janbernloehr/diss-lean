import NLS.MKdV.MiuraThetaNativeGardnerDirection
import NLS.MKdV.MiuraGlobalNLSActionFactor

/-! # The original restricted angle direction decreases exactly its selected action

All statements use the actual Gardner spatial derivative. Other action
indices may be closed, and the source has arbitrary infinite support.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem scalarInclusion_hierarchySobolevToScalarDomain (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    scalarInclusion (hierarchySobolevToScalarDomain m hm a) = hierarchySobolevJetL2 m 0 (Nat.zero_le m) a := by
  ext j
  rw [scalarInclusion_apply,hierarchySobolevToScalarDomain_apply,hierarchySobolevJetL2_apply,pow_zero,one_mul]

theorem miuraNativeThetaCotangent_eq_original (s : ℕ) (a : MiuraRealSobolevSource (s+1)) (n : ℕ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    miuraNativeThetaCotangent (s+1) a.val n =
      miuraThetaDifferential n (hierarchySobolevJetL2 (s+1) 0 (Nat.zero_le _) a.val) := by
  let b := hierarchySobolevToScalarDomain (s+1) (by omega) a.val
  have hb : ∀ j, b.val j = conj (b.val (-j)) := by
    intro j
    simpa only [b,hierarchySobolevToScalarDomain_apply] using a.property j
  have hscalar := scalarInclusion_hierarchySobolevToScalarDomain (s+1) (by omega) a.val
  have hsource : miuraSobolevActionSource (s+1) a.val = sobolevSourceInclusion (b,b) := by
    rw [miuraSobolevActionSource_eq_L2_diagonal,← hscalar,scalarL2Diagonal_scalarInclusion]
  have hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion (b,b))) (periodOnePotential_mem _) n ≠ 0 := by rwa [hsource] at hn
  rw [miuraNativeThetaCotangent,hsource,← hscalar]
  exact (miuraThetaDifferential_eq_source b hb n hgap).symm

/-- In the native Gardner direction of theta_n, the actual positive
physical action J_k has derivative -delta_nk. Only theta_n's own gap
must be open; the selected J_k is allowed to vanish. -/
theorem miuraThetaNativeGardnerDirection_L2_action (s : ℕ) (a : MiuraRealSobolevSource (s+1))
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    fderiv ℂ (miuraL2Action k) (hierarchySobolevJetL2 (s+1) 0 (Nat.zero_le _) a.val)
      (hierarchySobolevJetL2 s 0 (Nat.zero_le _) (miuraThetaNativeGardnerDirection s a n hgap)) =
        -(if n = k then 1 else 0) := by
  let b := hierarchySobolevToScalarDomain (s+1) (by omega) a.val
  have hb : ∀ j, b.val j = conj (b.val (-j)) := by
    intro j
    simpa only [b,hierarchySobolevToScalarDomain_apply] using a.property j
  have hscalar := scalarInclusion_hierarchySobolevToScalarDomain (s+1) (by omega) a.val
  have hsource : miuraSobolevActionSource (s+1) a.val = sobolevSourceInclusion (b,b) := by
    rw [miuraSobolevActionSource_eq_L2_diagonal,← hscalar,scalarL2Diagonal_scalarInclusion]
  have hgap' : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion (b,b))) (periodOnePotential_mem _) n ≠ 0 := by rwa [hsource] at hgap
  have hm : Memℓp (fun j : ℤ => 2*I*(Real.pi : ℂ)*j*
      l2CotangentGradient (fderiv ℂ (miuraL2Action k)
        (hierarchySobolevJetL2 (s+1) 0 (Nat.zero_le _) a.val)) j) 2 := by
    rw [← hscalar]
    exact miuraActionGardner_memlp b hb k hk
  have hs := l2CotangentGardner_skew (miuraNativeThetaCotangent (s+1) a.val n)
    (fderiv ℂ (miuraL2Action k) (hierarchySobolevJetL2 (s+1) 0 (Nat.zero_le _) a.val))
    (miuraThetaNativeGardnerDirection_memlp s a n hgap) hm
  rw [← miuraThetaNativeGardnerDirection_L2 s a n hgap,
    miuraNativeThetaCotangent_eq_original s a n hgap,← hscalar] at hs
  change miuraThetaGardnerBracket n k (scalarInclusion b) = _ at hs
  rw [miuraThetaGardnerBracket_eq_kronecker b hb n k hn hk hgap'] at hs
  rw [← hscalar]
  linear_combination hs

end NLS.MKdV
