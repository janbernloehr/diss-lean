import NLS.Articles.KdVKdV2Frequencies.ActualAllNativeStrongRInverse
import NLS.SequenceSpaces.DeletedRealConjugation

/-! # Native analytic germs of the SAME R at EVERY eligible REAL target -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- ONE common rough inverse-source ball before ALL native orders gives
actual native complex analytic germs of the SAME R at EVERY real target
whose actual inverse lies in that ball. All inclusions and zero slots are exact. -/
def HasAllRealTargetStrongRInverseGerms (η : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (W : Set (DeletedCoeff 2 0)) (R : DeletedCoeff 2 0 → PeriodOneHminusOne) : Prop :=
  ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∀ t : ℝ, ∀ ht : 0≤t, ∀ b : DeletedCoeff 2 0,
    WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b∈W →
    deletedL2Conjugation (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b)=
      WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b →
    R (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b)∈ball (0 : PeriodOneHminusOne) ρ →
    ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ b∈T ∧
      ∃ G : DeletedCoeff 2 0 → WeightedCoeff (Weight.sobolev (t-1)) 2,
        AnalyticOnNhd ℂ G T ∧ ∀ c∈T,
          WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) c∈W ∧
          periodOneSobolevImageInclusion t ht (G c)=
            R (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) c) ∧
          (G c).val 0=0 ∧ Z (periodOneSobolevImageInclusion t ht (G c))=
            WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
              (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) c)

/-- Existing actual real Sobolev membership and the matched source-based
inverse germs give genuine complex native analyticity of the SAME R at
EVERY eligible real target. Membership alone is not used to infer analyticity. -/
theorem HasAllNativeStrongRInverseGerms.real_target_germs
    {η : ℝ} {Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2}
    {W : Set (DeletedCoeff 2 0)} {R : DeletedCoeff 2 0 → PeriodOneHminusOne}
    (h : HasAllNativeStrongRInverseGerms η Z W R)
    (hRdata : ∀ b∈W, (R b).val 0=0 ∧ Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b)
    (hRreal : ∀ b∈W, deletedL2Conjugation b=b → IsRealPeriodOneHminusOne (R b))
    (hSob : ∀ b∈W, deletedL2Conjugation b=b → ∀ s : ℝ, -1≤s →
      (Memℓp (fun j => (Weight.sobolev s j : ℂ)*(R b).val j) 2 ↔
        Memℓp (fun j => (Weight.sobolev (s+1/2) j : ℂ)*
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2)) :
    HasAllRealTargetStrongRInverseGerms η Z W R := by
  obtain ⟨ρ,hρ,hρη,hstrong⟩ := h
  refine ⟨ρ,hρ,hρη,?_⟩
  intro t ht b hbW hbr hbρ
  let I := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let Q := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (t-1))
  let J := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1)
  have htarget : Memℓp (fun j => (Weight.sobolev (t-1+1/2) j : ℂ)*
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) (I b)).val j) 2 := by
    have hmem := (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) b).property
    change Memℓp (fun j => (Weight.sobolev (t-1/2) j : ℂ)*
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) b).val j) 2 at hmem
    simpa only [I,WeightedCoeff.meanZeroSobolevInclusion_lift,WeightedCoeff.sobolevInclusion_apply,
      show t-1+1/2=t-1/2 by ring] using hmem
  have hsource := (hSob (I b) hbW hbr (t-1) (by linarith)).mpr htarget
  let q : WeightedCoeff (Weight.sobolev (t-1)) 2 := ⟨(R (I b)).val,hsource⟩
  let a := Q q
  have hLa : L a=q := WeightedCoeff.meanZeroWeightedLift_projection _ _ (hRdata (I b) hbW).1
  have hraw : periodOneSobolevImageInclusion t ht (L a)=R (I b) := by
    rw [hLa]
    apply Subtype.ext
    funext n
    exact periodOneSobolevImageInclusion_apply t ht q n
  have hreal : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht (L a)) := by
    rw [hraw]
    exact hRreal (I b) hbW hbr
  have haρ : periodOneSobolevImageInclusion t ht (L a)∈ball (0 : PeriodOneHminusOne) ρ := by
    rw [hraw]
    exact hbρ
  obtain ⟨V,_hV,haV,g,_hga,hcomm,T,hT,himageT,G,hGa,_hGbase,hGd⟩ := hstrong t ht a hreal haρ
  have hweaksource : WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (J a)=
      periodOneSobolevImageInclusion t ht (L a) := WeightedCoeff.meanZeroSobolevInclusion_lift _ a
  have hcenter : nativeMeanZeroAbelianMap t g a=b := by
    apply WeightedCoeff.meanZeroSobolevInclusion_injective (by linarith : (-1/2 : ℝ)≤t-1/2)
    calc
      _ = weakMeanZeroAbelianMap Z (J a) := nativeMeanZeroAbelianMap_commuting t ht Z g a (hcomm _ haV).2
      _ = I b := by
        change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
          (Z (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (J a)))=I b
        rw [hweaksource,hraw,(hRdata (I b) hbW).2]
        exact WeightedCoeff.meanZeroWeightedProjection_lift _ (I b)
  refine ⟨T,hT,?_,G,hGa,?_⟩
  · rw [←hcenter]
    exact himageT
  · intro c hc
    obtain ⟨hcW,_hcV,hmean,hmatch,_hforward⟩ := hGd c hc
    refine ⟨hcW,hmatch,hmean,?_⟩
    rw [hmatch,(hRdata _ hcW).2,WeightedCoeff.meanZeroSobolevInclusion_lift]

end NLS.Articles.KdVKdV2Frequencies
