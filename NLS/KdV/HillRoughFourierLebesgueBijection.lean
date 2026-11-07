import NLS.KdV.HillRoughGlobalFourierLebesgueRegularity
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughRealInverse
import NLS.SequenceSpaces.FiniteFourierLebesgueWeakInclusion
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedExponent

/-! # The fixed physical Birkhoff bijection in original Fourier-Lebesgue norms

The source and target retain their original real mean-zero weighted lp
norms and raw coefficients. Exact nonlinear regularity restricts the
already-fixed global rough bijection onto the ENTIRE stronger target.
This module proves a bijection, not yet native analytic diffeomorphism.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def fourierLebesgueSourceInclusion (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] PeriodOneHminusOne :=
  WeightedCoeff.finiteFourierLebesgueWeakInclusion s (-1) p hp h2p (by
    have hδ : 0≤1/(2*p.toReal) := by positivity
    linarith)

@[simp] theorem fourierLebesgueSourceInclusion_apply (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (fourierLebesgueSourceInclusion s hs p hp h2p a).val n=a.val n :=
  WeightedCoeff.finiteFourierLebesgueWeakInclusion_apply _ _ _ _ _ _ _ _

def fourierLebesgueTargetInclusion (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    WeightedCoeff (Weight.sobolev (s+1/2)) p →L[ℂ]
      WeightedCoeff (Weight.sobolev (-1/2)) 2 :=
  WeightedCoeff.finiteFourierLebesgueWeakInclusion (s+1/2) (-1/2) p hp h2p (by
    have hδ : 0≤1/(2*p.toReal) := by positivity
    linarith)

@[simp] theorem fourierLebesgueTargetInclusion_apply (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (a : WeightedCoeff (Weight.sobolev (s+1/2)) p) (n : ℤ) :
    (fourierLebesgueTargetInclusion s hs p hp h2p a).val n=a.val n :=
  WeightedCoeff.finiteFourierLebesgueWeakInclusion_apply _ _ _ _ _ _ _ _

theorem fourierLebesgueSourceInclusion_real (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    IsRealPeriodOneHminusOne (fourierLebesgueSourceInclusion s hs p hp h2p a.val) := by
  intro n
  simpa only [fourierLebesgueSourceInclusion_apply] using a.property.1 n

/-- Restriction of the SAME actual global signed physical map. -/
def fourierLebesgueForward (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p →
      physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p := fun a =>
  let q := fourierLebesgueSourceInclusion s hs p hp h2p a.val
  have hr := fourierLebesgueSourceInclusion_real s hs p hp h2p a
  have hmem : Memℓp (fun n => (Weight.sobolev (s+1/2) n : ℂ)*(D.signed q).val n) p :=
    (D.fourierLebesgue_iff_signed_mem q hr s hs p hp h2p).mp (by
      simpa only [q,fourierLebesgueSourceInclusion_apply] using
        (show Memℓp (fun n => (Weight.sobolev s n : ℂ)*a.val.val n) p from a.val.property))
  ⟨⟨(D.signed q).val,hmem⟩,D.signed_real q hr,D.signed_zero q (D.real_mem_domain q hr)⟩

@[simp] theorem fourierLebesgueForward_apply (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (n : ℤ) :
    (D.fourierLebesgueForward s hs p hp h2p a).val.val n=
      (D.signed (fourierLebesgueSourceInclusion s hs p hp h2p a.val)).val n := rfl

theorem fourierLebesgueForward_signed (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    D.signed (fourierLebesgueSourceInclusion s hs p hp h2p a.val)=
      fourierLebesgueTargetInclusion s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p a).val := by
  apply Subtype.ext
  funext n
  simp only [fourierLebesgueTargetInclusion_apply,fourierLebesgueForward_apply]

/-- Onto the ENTIRE original stronger target, including infinite support
and closed coordinates; initial stronger inverse membership is not assumed. -/
theorem fourierLebesgueForward_bijective (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Function.Bijective (D.fourierLebesgueForward s hs p hp h2p) := by
  constructor
  · intro a b hab
    have hrA := fourierLebesgueSourceInclusion_real s hs p hp h2p a
    have hrB := fourierLebesgueSourceInclusion_real s hs p hp h2p b
    have hsig : D.signed (fourierLebesgueSourceInclusion s hs p hp h2p a.val)=
        D.signed (fourierLebesgueSourceInclusion s hs p hp h2p b.val) := by
      rw [D.fourierLebesgueForward_signed,D.fourierLebesgueForward_signed,hab]
    have he := D.signed_injective_real_meanZero _ _ hrA hrB
      (by simpa only [fourierLebesgueSourceInclusion_apply] using a.property.2)
      (by simpa only [fourierLebesgueSourceInclusion_apply] using b.property.2) hsig
    apply Subtype.ext
    apply Subtype.ext
    funext n
    simpa only [fourierLebesgueSourceInclusion_apply] using congrArg (fun q => q.val n) he
  · intro z
    let b := fourierLebesgueTargetInclusion s hs p hp h2p z.val
    have hbr (n : ℤ) : b.val (-n)=conj (b.val n) := by
      simpa only [b,fourierLebesgueTargetInclusion_apply] using z.property.1 n
    have hbm : b.val 0=0 := by
      simpa only [b,fourierLebesgueTargetInclusion_apply] using z.property.2
    obtain ⟨q,hqr,hqm,hqz⟩ := D.exists_real_meanZero_signed_preimage b hbr hbm
    have hmem : Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) p :=
      (D.fourierLebesgue_iff_signed_mem q hqr s hs p hp h2p).mpr (by
        rw [hqz]
        simpa only [b,fourierLebesgueTargetInclusion_apply] using
          (show Memℓp (fun n => (Weight.sobolev (s+1/2) n : ℂ)*z.val.val n) p from z.val.property))
    let a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p := ⟨⟨q.val,hmem⟩,hqr,hqm⟩
    have hsource : fourierLebesgueSourceInclusion s hs p hp h2p a.val=q := by
      apply Subtype.ext
      funext n
      exact fourierLebesgueSourceInclusion_apply _ _ _ _ _ _ _
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext n
    rw [D.fourierLebesgueForward_apply,hsource,hqz]
    exact fourierLebesgueTargetInclusion_apply _ _ _ _ _ _ _

/-- Bijection in the ORIGINAL native real mean-zero Fourier-Lebesgue
spaces. Analyticity in those norms is a separate remaining obligation. -/
def fourierLebesgueEquiv (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p ≃
      physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p :=
  Equiv.ofBijective (D.fourierLebesgueForward s hs p hp h2p)
    (D.fourierLebesgueForward_bijective s hs p hp h2p)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
