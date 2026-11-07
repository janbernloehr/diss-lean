import NLS.SequenceSpaces.PositiveInsertion
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.Truncation

/-! An algebraic embedding of literal positive Hill energy factors
into the verified single-root product. These auxiliary linear roots
are not asserted to be the physical Dirac spectrum. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

def positiveReciprocalCoefficients : Coeff 2 :=
  LpSequence.positiveInsert (LpSequence.positiveRestrictionCLM (Coeff.puncturedLattice 2 (by norm_num)))

theorem positiveReciprocalCoefficients_apply (m : ℕ+) :
    positiveReciprocalCoefficients (m:ℕ) = ((m:ℕ):ℂ)⁻¹ := by
  rw [positiveReciprocalCoefficients,LpSequence.positiveInsert_apply]
  change Coeff.puncturedLattice 2 (by norm_num) ((m:ℕ):ℤ) = _
  rw [Coeff.puncturedLattice_apply,if_neg (by exact_mod_cast m.ne_zero)]
  simp only [Int.cast_natCast]

def hillEnergyRawProductEmbedding (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 :=
  (Real.pi:ℂ)⁻¹ • LpSequence.positiveInsert t.2-(t.1/(Real.pi:ℂ)) • positiveReciprocalCoefficients

theorem hillEnergyRawProductEmbedding_positive (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    hillEnergyRawProductEmbedding t (m:ℕ) = t.2 m/(Real.pi:ℂ)-t.1/((Real.pi:ℂ)*(m:ℕ)) := by
  simp only [hillEnergyRawProductEmbedding,lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,LpSequence.positiveInsert_apply,positiveReciprocalCoefficients_apply]
  ring

theorem hillEnergyRawProductEmbedding_nonpos (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2)
    (k : ℤ) (hk : k ≤ 0) : hillEnergyRawProductEmbedding t k = 0 := by
  simp only [hillEnergyRawProductEmbedding,positiveReciprocalCoefficients,lp.coeFn_sub,Pi.sub_apply,
    lp.coeFn_smul,Pi.smul_apply,LpSequence.positiveInsert_apply_nonpos _ k hk,smul_zero,sub_self]

theorem analyticAt_hillEnergyRawProductEmbedding (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    AnalyticAt ℂ hillEnergyRawProductEmbedding t := by
  have hI := (LpSequence.positiveInsertIsometry.toContinuousLinearMap.analyticAt t.2).comp analyticAt_snd
  exact (hI.const_smul (c := (Real.pi:ℂ)⁻¹)).sub
    ((analyticAt_fst.div_const).smul analyticAt_const)

def hillEnergyProductEmbedding (n : ℕ+) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 :=
  hillEnergyRawProductEmbedding t-Coeff.truncate {((n:ℕ):ℤ)} (hillEnergyRawProductEmbedding t)

theorem hillEnergyProductEmbedding_positive (n m : ℕ+) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyProductEmbedding n t (m:ℕ) =
      if m = n then 0 else t.2 m/(Real.pi:ℂ)-t.1/((Real.pi:ℂ)*(m:ℕ)) := by
  have he : ((m:ℕ):ℤ) = ((n:ℕ):ℤ) ↔ m = n := by
    constructor
    · exact fun h => Subtype.ext (Int.ofNat.inj h)
    · exact fun h => congrArg (fun k : ℕ+ => ((k:ℕ):ℤ)) h
  simp only [hillEnergyProductEmbedding,lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,
    Finset.mem_singleton,he,hillEnergyRawProductEmbedding_positive]
  split_ifs <;> simp only [sub_self,sub_zero]

theorem hillEnergyProductEmbedding_nonpos (n : ℕ+) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2)
    (k : ℤ) (hk : k ≤ 0) : hillEnergyProductEmbedding n t k = 0 := by
  simp only [hillEnergyProductEmbedding,lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,
    hillEnergyRawProductEmbedding_nonpos t k hk,ite_self,sub_self]

theorem analyticAt_hillEnergyProductEmbedding (n : ℕ+) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    AnalyticAt ℂ (hillEnergyProductEmbedding n) t :=
  (analyticAt_hillEnergyRawProductEmbedding t).sub
    (((Coeff.truncateCLM (p := 2) {((n:ℕ):ℤ)}).analyticAt _).comp
      (analyticAt_hillEnergyRawProductEmbedding t))

end NLS.KdV
