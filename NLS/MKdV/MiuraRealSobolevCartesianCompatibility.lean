import NLS.MKdV.MiuraRealSobolevCartesianLocalInverse
import NLS.MKdV.MiuraRealCartesianSmallData

/-! # The real Sobolev Cartesian maps are compatible with the original L² map -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCartesianWeight_ge_half (s : ℕ) (n : ℤ) : Weight.sobolev (1/2) n ≤ miuraCartesianWeight s n := by
  rw [miuraCartesianWeight_factor]
  have hw : 1 ≤ Weight.sobolev (s : ℝ) n := Real.one_le_rpow (by simp [abs_nonneg]) (Nat.cast_nonneg s)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hw ((Weight.sobolev (1/2)).positive n).le

def miuraPositiveSobolevL2HalfInclusion (s : ℕ) : MiuraPositiveSobolevHalf s →L[ℂ] MiuraPositiveHalf :=
  ((WeightedCoeff.inclusionCLM (miuraCartesianWeight s) (Weight.sobolev (1/2)) (miuraCartesianWeight_ge_half s)).comp
    (MiuraPositiveSobolevHalf s).subtypeL).codRestrict MiuraPositiveHalf (by
      intro a n hn
      rw [ContinuousLinearMap.comp_apply,WeightedCoeff.inclusionCLM_apply]
      exact a.property n hn)

@[simp] theorem miuraPositiveSobolevL2HalfInclusion_apply (s : ℕ) (a : MiuraPositiveSobolevHalf s) (n : ℤ) :
    (miuraPositiveSobolevL2HalfInclusion s a).val.val n = a.val.val n :=
  WeightedCoeff.inclusionCLM_apply _ _ (miuraCartesianWeight_ge_half s) a.val n

def miuraPositiveSobolevL2CartesianInclusion (s : ℕ) : MiuraPositiveSobolevTarget s →L[ℂ] MiuraPositiveCartesianTarget :=
  ((miuraPositiveSobolevL2HalfInclusion s).prodMap (miuraPositiveSobolevL2HalfInclusion s)).prodMap (ContinuousLinearMap.id ℂ ℂ)

theorem miuraPositiveSobolevL2CartesianInclusion_eval (s : ℕ) (z : MiuraPositiveSobolevTarget s) (n : ℤ) :
    miuraPositiveCartesianEval n (miuraPositiveSobolevL2CartesianInclusion s z) = miuraSobolevPositiveEval s n z := by
  change ((miuraPositiveSobolevL2HalfInclusion s z.1.1).val.val n,
    (miuraPositiveSobolevL2HalfInclusion s z.1.2).val.val n) = _
  rw [miuraPositiveSobolevL2HalfInclusion_apply,miuraPositiveSobolevL2HalfInclusion_apply]
  rfl

def miuraPhysicalSobolevL2SourceInclusion (s : ℕ) : MiuraRealSobolevSource s →L[ℝ] Coeff.physicalRealSubmodule 2 :=
  (((hierarchySobolevJetL2 s 0 (Nat.zero_le s)).restrictScalars ℝ).comp (MiuraRealSobolevSource s).subtypeL).codRestrict
    (Coeff.physicalRealSubmodule 2) (by
      intro a n
      change hierarchySobolevJetL2 s 0 (Nat.zero_le s) a.val n =
        conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a.val (-n))
      simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using! a.property n)

@[simp] theorem miuraPhysicalSobolevL2SourceInclusion_apply (s : ℕ) (a : MiuraRealSobolevSource s) (n : ℤ) :
    (miuraPhysicalSobolevL2SourceInclusion s a).val n = a.val.val n := by
  change hierarchySobolevJetL2 s 0 (Nat.zero_le s) a.val n = _
  simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul]

theorem miuraPhysicalSobolevL2SourceInclusion_injective (s : ℕ) :
    Function.Injective (miuraPhysicalSobolevL2SourceInclusion s) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  funext n
  simpa only [miuraPhysicalSobolevL2SourceInclusion_apply] using
    congrArg (fun c : Coeff.physicalRealSubmodule 2 => c.val n) hab

theorem miuraPositiveSobolevL2CartesianInclusion_mean (s : ℕ) (z : MiuraPositiveSobolevTarget s) :
    (miuraPositiveSobolevL2CartesianInclusion s z).2 = z.2 :=
  NLS.FunctionalAnalysis.prodMap_id_snd
    ((miuraPositiveSobolevL2HalfInclusion s).prodMap (miuraPositiveSobolevL2HalfInclusion s)) z

theorem miuraPositiveSobolevL2CartesianInclusion_real (s : ℕ) (z : MiuraRealSobolevCartesianTarget s) :
    miuraPositiveSobolevL2CartesianInclusion s z.val ∈ miuraCartesianRealSubmodule := by
  obtain ⟨hz,hmean⟩ := (mem_miuraSobolevCartesianRealSubmodule_iff s z.val).mp z.property
  constructor
  · intro n
    have he := miuraPositiveSobolevL2CartesianInclusion_eval s z.val n
    exact ⟨(congrArg (fun c : ℂ × ℂ => c.1.im) he).trans (hz n).1,
      (congrArg (fun c : ℂ × ℂ => c.2.im) he).trans (hz n).2⟩
  · rw [miuraPositiveSobolevL2CartesianInclusion_mean]
    exact hmean

def miuraPhysicalSobolevL2CartesianInclusion (s : ℕ) :
    MiuraRealSobolevCartesianTarget s →L[ℝ] MiuraRealCartesianTarget :=
  (((miuraPositiveSobolevL2CartesianInclusion s).restrictScalars ℝ).comp
    (miuraSobolevCartesianRealSubmodule s).subtypeL).codRestrict miuraCartesianRealSubmodule
      (miuraPositiveSobolevL2CartesianInclusion_real s)

/-- The bounded native inclusions retain the same actual Cartesian
coefficients and literal signed mean on every physical Sobolev profile. -/
theorem miuraPhysicalSobolevCartesianMap_L2 (s : ℕ) (a : MiuraRealSobolevSource s) :
    miuraPhysicalSobolevL2CartesianInclusion s (miuraPhysicalSobolevCartesianMap s a) =
      miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s a) := by
  apply Subtype.ext
  change miuraPositiveSobolevL2CartesianInclusion s (miuraPhysicalSobolevCartesianMap s a).val =
    (miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s a)).val
  rw [miuraPhysicalSobolevCartesianMap_inclusion,miuraPhysicalCartesianMap_inclusion]
  apply WeightedCoeff.positivePairMean_ext
  · intro n hn
    have he := miuraPositiveSobolevL2CartesianInclusion_eval s (miuraSobolevPositiveCartesianMap s a.val) n
    have hseq := miuraSobolevCartesianSequence_L2_coefficients s a.val a.property n
    change _ = ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a.val).1).val.val n,
      (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a.val).2).val.val n) at he
    rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,if_pos hn,if_pos hn] at he
    change _ = ((WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2
      (miuraL2CartesianSequence (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a.val)).1).val.val n,
      (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2
      (miuraL2CartesianSequence (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a.val)).2).val.val n)
    rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,if_pos hn,if_pos hn]
    exact he.trans hseq
  · rw [miuraPositiveSobolevL2CartesianInclusion_mean]
    change a.val.val 0 = hierarchySobolevJetL2 s 0 (Nat.zero_le s) a.val 0
    simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul]

end NLS.MKdV
