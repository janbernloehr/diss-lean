import NLS.KdV.MiuraL2DirichletAuxiliary
import NLS.KdV.SingularDirichletCharacteristicSufficiency
import NLS.Fourier.UnitDirichletContinuous

/-! A phase-fixed ACTUAL native Dirichlet eigenfunction, constructed from
the full physical L2 Dirac column and normalized to the free sine curve. -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat NLS.MKdV
local instance miuraDirichletSineH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance miuraDirichletSineH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- The scalar Miura position, with phase fixed to the literal free sine. -/
def miuraDirichletSinePosition : (ℂ × ℂ) →L[ℂ] ℂ :=
  (I/2) • (ContinuousLinearMap.fst ℂ ℂ ℂ+I • ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The position map is a contraction in the original product maximum norm. -/
theorem norm_miuraDirichletSinePosition_le (v : ℂ × ℂ) :
    ‖miuraDirichletSinePosition v‖ ≤ ‖v‖ := by
  change ‖(I/2)*(v.1+I*v.2)‖ ≤ ‖v‖
  rw [norm_mul,norm_div,norm_I,norm_ofNat]
  have hb := norm_add_le v.1 (I*v.2)
  rw [norm_mul,norm_I,one_mul] at hb
  have h1 := norm_fst_le v
  have h2 := norm_snd_le v
  linarith

/-- The free position is the LITERAL sine, with no frequency or phase change. -/
theorem miuraDirichletSinePosition_free (z : ℂ) (t : ℝ) :
    miuraDirichletSinePosition (classicalFreeVector z (1,I) t) = sin (z*t) := by
  change (I/2)*(exp (-I*z*t)*1+I*(exp (I*z*t)*I)) = _
  rw [mul_one]
  rw [Complex.sin]
  have h1 : -I*z*(t:ℂ) = -(z*t)*I := by ring
  have h2 : I*z*(t:ℂ) = (z*t)*I := by ring
  rw [h1,h2]
  ring_nf
  simp
  ring

/-- The actual physical Dirac column, with scalar normalization fixed BEFORE
choosing any eigenvalue or native eigenfunction. -/
def hillMiuraDirichletSineCurve (u : Coeff 2) (z : ℂ) : C(Icc (0:ℝ) 1,ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1) miuraDirichletSinePosition
    (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I))

/-- This curve is precisely z times the independent scalar IVP column,
including at zero frequency. -/
theorem hillMiuraDirichletSineCurve_eq_quasiHill (u : Coeff 2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    hillMiuraDirichletSineCurve u z t = z*(quasiHillL2SolutionCurve u (z^2) (0,1) t).1 := by
  have hi : miuraStateMap 0 z (1,I) = (-2*I*z) • ((0,1) : ℂ × ℂ) := by
    apply Prod.ext <;> simp only [miuraStateMap_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals ring_nf
    all_goals simp [I_sq]
    all_goals ring
  have he := congrArg (fun F : Curve (ℂ × ℂ) => (F t).1)
    (quasiHillL2SolutionCurve_eq_transformedDirac u z (1,I))
  rw [hi,quasiHillL2SolutionCurve_smul] at he
  change (-2*I*z)*(quasiHillL2SolutionCurve u (z^2) (0,1) t).1 =
    (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I) t).1+
      I*(l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I) t).2 at he
  change (I/2)*((l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I) t).1+
    I*(l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I) t).2) = _
  rw [← he]
  ring_nf
  simp [I_sq]

/-- Every nonzero actual auxiliary Dirichlet root supplies an ACTUAL native
H1 eigenfunction whose IDENTICAL continuous position is this phase-fixed
sine curve. Neither a native eigenfunction nor a pointwise approximation
is supplied as a hypothesis. -/
theorem exists_native_Miura_eigen_with_sineCurve (u : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (hroot : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u) z = 0) :
    ∃ g : UnitDirichletH1, g ≠ 0 ∧
      singularDirichletOperator (periodOneOriginal (periodOneMiura u)) g =
        z^2 • singularDirichletDomainInclusion g ∧
      unitDirichletContinuousInclusion g = hillMiuraDirichletSineCurve u z := by
  have hd := (auxiliaryDirichlet_eq_zero_iff_quasiHillL2Dirichlet u z hz).mp hroot
  have hw : IsQuasiHillL2DirichletState u (z^2) (quasiHillL2SolutionCurve u (z^2) (0,1)) :=
    (isQuasiHillL2DirichletState_iff_scalar u (z^2) _).mpr ⟨1,by simp,by simpa using hd⟩
  obtain ⟨f,hf,hpos⟩ := exists_native_Miura_eigen_of_quasiHill_state u (z^2) _ hw
  have hf0 : f ≠ 0 := by
    intro he
    have hwzero : quasiHillL2SolutionCurve u (z^2) (0,1) = 0 :=
      quasiHillL2Solution_eq_zero_of_fst_eq_zero u (z^2) _ hw.1 (by
        intro t
        rw [hpos t,he]
        change periodOneSobolevSynthesis (0 : ScalarDomain 2) (t.val : AddCircle (2:ℝ)) = 0
        rw [map_zero]
        rfl)
    have hzero := congrArg (fun F : Curve (ℂ × ℂ) =>
      (F ⟨0,by constructor <;> norm_num⟩).2) hwzero
    rw [quasiHillL2SolutionCurve_zero] at hzero
    norm_num at hzero
  refine ⟨z • f,smul_ne_zero hz hf0,?_,?_⟩
  · rw [map_smul,map_smul,hf,smul_smul,smul_smul,mul_comm z]
  · rw [map_smul]
    apply ContinuousMap.ext
    intro t
    rw [hillMiuraDirichletSineCurve_eq_quasiHill]
    change z*unitDirichletRepresentative f t.val = _
    rw [← hpos t]

end NLS.KdV
