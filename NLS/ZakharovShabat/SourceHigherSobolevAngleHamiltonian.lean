import NLS.ZakharovShabat.SourceWeightedAngleHamiltonian
import NLS.ZakharovShabat.SourceWeightedRealMembership
import NLS.ZakharovShabat.SourceSection14WeightedMembership
import NLS.ZakharovShabat.SourceHigherSobolevEmbedding
import NLS.ZakharovShabat.SourceHigherSobolevRealGerm

/-! # Original angle vectors in every integer Sobolev source space

All raw Fourier coefficients are preserved. The only angle-domain
restriction is the selected open gap, with no finite-gap or support bound.
-/
noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

theorem thetaHamiltonian_sobolev_mem
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (t : ℝ) (ht : 0 ≤ t) (φ : realTypeSourceSubmodule 2)
    (hφ : Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*φ.val.fst n) 2 ∧
      Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*φ.val.snd n) 2)
    (k : ℤ) (hk : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) k ≠ 0) :
    let X := sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl k u φ.val
    Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*X.fst n) 2 ∧
      Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*X.snd n) 2 := by
  let w := sourceSobolevSpectralWeight t ht
  obtain ⟨a,ha⟩ := (exists_originalWeightedRealSource_iff w φ).mpr
    (by simpa only [w,sourceSobolevSpectralWeight_even] using hφ)
  obtain ⟨v,hv,_⟩ := D.existsUnique_thetaHamiltonian_weighted E w a k (by rwa [ha])
  rw [ha] at hv
  dsimp only
  rw [← hv]
  simp only [originalWeightedSourceCLM_fst,originalWeightedSourceCLM_snd]
  rw [← sourceFrequencyWeight_sobolev t ht]
  exact ⟨v.fst.property,v.snd.property⟩

/-- The actual original angle vector lifts uniquely to the full original
H^m source. This is proved at all real profiles with its own gap open. -/
theorem existsUnique_thetaHamiltonian_higherSobolev
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (m : ℕ) (a : realTypeHigherSobolevSourceLocus m) (k : ℤ)
    (hk : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion m a.val)) (periodOnePotential_mem _) k ≠ 0) :
    ∃! v : SobolevSource m, higherSobolevSourceInclusion m v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl k u
        (higherSobolevSourceInclusion m a.val) := by
  let φ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  have hmem := D.thetaHamiltonian_sobolev_mem E m (Nat.cast_nonneg m) φ
    (by simpa only [φ,higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd] using
      (show Memℓp (fun n => (Weight.sobolev (m : ℝ) n : ℂ)*a.val.1.val n) 2 ∧
        Memℓp (fun n => (Weight.sobolev (m : ℝ) n : ℂ)*a.val.2.val n) 2 from
          ⟨a.val.1.property,a.val.2.property⟩)) k hk
  let X := sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl k u φ.val
  let v : SobolevSource m := (⟨X.fst,hmem.1⟩,⟨X.snd,hmem.2⟩)
  have hv : higherSobolevSourceInclusion m v = X := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext n
    · exact higherSobolevSourceInclusion_fst m v n
    · exact higherSobolevSourceInclusion_snd m v n
  refine ⟨v,hv,?_⟩
  intro v' hv'
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact (higherSobolevSourceInclusion_fst m v' n).symm.trans
      ((congrArg (fun z : CoeffPair 2 => z.fst n) (hv'.trans hv.symm)).trans
        (higherSobolevSourceInclusion_fst m v n))
  · exact (higherSobolevSourceInclusion_snd m v' n).symm.trans
      ((congrArg (fun z : CoeffPair 2 => z.snd n) (hv'.trans hv.symm)).trans
        (higherSobolevSourceInclusion_snd m v n))

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
