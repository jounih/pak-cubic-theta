module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The real kernel of the cubic jump after removing the inverse square-root.
At scaled action z, the mth moment below probes the kernel at u/z. -/
public section
namespace CubicTheta
open Real Filter MeasureTheory Set
open scoped Topology
noncomputable section

def jumpKernel (v : ℝ) := cosh (arcosh (1+v)/3) / √(2+v)

theorem jumpKernel_bound {v : ℝ} (hv : 0 ≤ v) :
    0 < jumpKernel v ∧ jumpKernel v ≤ 1/√2 := by
  let t := arcosh (1+v)
  have ht : 0 ≤ t := arcosh_nonneg (by linarith)
  have hcmp : cosh (t/3) ≤ cosh (t/2) := cosh_le_cosh.mpr (by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]; linarith)
  have heq := cosh_two_mul (t/2)
  rw [show 2*(t/2) = t by ring] at heq
  have hct : cosh t = 1+v := cosh_arcosh (by linarith)
  have hval : (cosh (t/2) * √2)^2 = (√(2+v))^2 := by
    rw [mul_pow, sq_sqrt (by norm_num), sq_sqrt (by linarith)]
    nlinarith [cosh_sq_sub_sinh_sq (t/2)]
  have hupper : cosh (t/2) * √2 ≤ √(2+v) := by
    nlinarith [sqrt_nonneg (2+v), mul_nonneg (cosh_pos (t/2)).le (sqrt_nonneg 2)]
  constructor
  · exact div_pos (cosh_pos _) (sqrt_pos.mpr (by linarith))
  · apply (div_le_div_iff₀ (sqrt_pos.mpr (by linarith : 0 < 2+v)) (sqrt_pos.mpr (by norm_num : (0:ℝ)<2))).mpr
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hcmp (sqrt_nonneg 2)).trans hupper

private theorem jumpKernel_cont : ContinuousOn jumpKernel (Ici 0) := by
  have ha : ContinuousOn (fun v : ℝ ↦ arcosh (1+v)) (Ici 0) :=
    continuousOn_arcosh.comp (continuous_const.add continuous_id).continuousOn (fun v hv ↦ by
      change 0 ≤ v at hv; change 1 ≤ 1+v; linarith)
  exact (continuous_cosh.comp_continuousOn (ha.div_const 3)).div
    ((continuous_const.add continuous_id).sqrt.continuousOn) (fun v hv ↦ sqrt_ne_zero'.mpr (by
      change 0 ≤ v at hv; linarith))

/-- Any Gamma weight with shape h>0 is allowed, including all h=j+1/2 arising
when differentiating the cut integral. -/
theorem jump_moment_limit (h : ℝ) (hh : 0 < h) :
    Tendsto (fun z : ℝ ↦ ∫ u in Ioi (0:ℝ), exp (-u) * u^(h-1) * jumpKernel (u/z))
      atTop (𝓝 (Gamma h * (1/√2))) := by
  let weight (u : ℝ) := exp (-u) * u^(h-1)
  have hc : ContinuousOn weight (Ioi 0) := continuous_id.neg.rexp.continuousOn.mul
    (continuousOn_id.rpow_const (by intro u hu; exact Or.inl (ne_of_gt hu)))
  have hi : IntegrableOn weight (Ioi 0) := GammaIntegral_convergent hh
  have hm : ∀ᶠ z : ℝ in atTop, AEStronglyMeasurable
      (fun u ↦ weight u * jumpKernel (u/z)) (volume.restrict (Ioi 0)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with z hz
    exact (hc.mul (jumpKernel_cont.comp (continuous_id.div_const z).continuousOn
      (fun _ hu ↦ (div_pos hu hz).le))).aestronglyMeasurable measurableSet_Ioi
  have hdom : ∀ᶠ z : ℝ in atTop, ∀ᵐ u ∂volume.restrict (Ioi (0:ℝ)),
      ‖weight u * jumpKernel (u/z)‖ ≤ weight u * (1/√2) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with z hz
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    have hw : 0 ≤ weight u := mul_nonneg (exp_pos _).le (rpow_pos_of_pos hu _).le
    obtain ⟨hl,hr⟩ := jumpKernel_bound (div_pos hu hz).le
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw hl.le)]
    exact mul_le_mul_of_nonneg_left hr hw
  have hpoint (u : ℝ) (hu : 0 < u) :
      Tendsto (fun z : ℝ ↦ weight u * jumpKernel (u/z)) atTop (𝓝 (weight u * (1/√2))) := by
    have hz : Tendsto (fun z : ℝ ↦ u/z) atTop (𝓝[≥] 0) := tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_const_nhds.div_atTop tendsto_id, (eventually_gt_atTop (0:ℝ)).mono (fun z hz ↦ (div_pos hu hz).le)⟩
    have h0 := (jumpKernel_cont 0 (by simp)).tendsto.comp hz
    simpa [Function.comp_def, jumpKernel] using h0.const_mul (weight u)
  have hl := tendsto_integral_filter_of_dominated_convergence _ hm hdom
    (hi.mul_const (1/√2)) ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono hpoint)
  simpa only [integral_mul_const, weight, ← Gamma_eq_integral hh] using hl
end
end CubicTheta
