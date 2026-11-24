module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Absolute control before contour deformation. The Borel kernel obeys
(4-27z)K³=3K+1. The angles and constant scale are absorbed into its ray. -/
public section
namespace CubicTheta
open Real Filter Set MeasureTheory
open scoped Topology
noncomputable section

theorem cubic_branch_bound {z k : ℂ} {d : ℝ} (hd : 0 < d) (gap : d ≤ ‖4-27*z‖)
    (alg : (4-27*z)*k^3 = 3*k+1) : ‖k‖ ≤ max 1 (4/d) := by
  by_cases hk : ‖k‖ ≤ 1
  · exact hk.trans (le_max_left ..)
  have hp : 1 < ‖k‖ := lt_of_not_ge hk
  have h : ‖4-27*z‖ * ‖k‖^3 ≤ 3*‖k‖+1 := by
    calc _ = ‖(4-27*z)*k^3‖ := by rw [norm_mul,norm_pow]
         _ ≤ _ := by rw [alg]; simpa using norm_add_le (3*k) (1:ℂ)
  have sq : ‖k‖^2 ≤ ‖k‖^3 := by nlinarith [mul_nonneg (sq_nonneg ‖k‖) (sub_nonneg.mpr hp.le)]
  have h' : d * ‖k‖^2 ≤ 4*‖k‖ := (mul_le_mul gap sq (sq_nonneg _) (norm_nonneg _)).trans
    (h.trans (by linarith))
  apply le_trans _ (le_max_right ..)
  apply (le_div_iff₀ hd).mpr
  apply (mul_le_mul_iff_left₀ (by linarith : 0 < ‖k‖)).mp
  nlinarith

/-- Parametrize the cut by s=sinh(t), h=cosh(t), S=sinh(3t).
For J=±i√3 the two displayed numerators give genuine roots at
27z=4(1+S²). Branch assignment by analytic continuation is separate. -/
theorem cut_root {s h J : ℂ} (hc : h^2-s^2=1) (hJ : J^2 = -3)
    (hn : 4*s^3+3*s ≠ 0) :
    let S := 4*s^3+3*s
    let k := (s+J*h)/(2*S)
    (-4*S^2)*k^3 = 3*k+1 := by
  dsimp only
  have poly : (s+J*h)^3 + 3*(s+J*h) + 2*(4*s^3+3*s) = 0 := by
    linear_combination (3*s*h^2+J*h^3)*hJ - (9*s+3*J*h)*hc
  have cube : (s+J*h)^3 = -(3*(s+J*h)+2*(4*s^3+3*s)) := by
    linear_combination poly
  rw [div_pow, cube]
  generalize hS : 4*s^3+3*s = S at *
  field_simp [hn]
  ring

theorem cut_root_difference (s h J S : ℂ) (hn : S ≠ 0) :
    (s+J*h)/(2*S) - (s-J*h)/(2*S) = J*h/S := by
  field_simp
  ring

/-- The distance to the branch value is uniformly positive on every nonreal
straight ray. Multiplication by the conjugate of the ray direction exhibits
a constant imaginary part. -/
theorem nonreal_ray_gap {c : ℂ} (hc : c.im ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ r : ℝ, d ≤ ‖4-27*(c*r)‖ := by
  have hc0 : c ≠ 0 := fun h ↦ hc (h ▸ rfl)
  refine ⟨|4*c.im|/‖c‖, div_pos (abs_pos.mpr (mul_ne_zero (by norm_num) hc)) (norm_pos_iff.mpr hc0), ?_⟩
  intro r
  apply (div_le_iff₀ (norm_pos_iff.mpr hc0)).mpr
  have h := Complex.abs_im_le_norm ((4-27*(c*r))*star c)
  have him : ((4-27*(c*r))*star c).im = -(4*c.im) := by
    simp [Complex.mul_im, Complex.mul_re]; ring
  simpa only [him,abs_neg,norm_mul,norm_star] using h

/-- K(0)=1 gives a linear estimate for K(z)-1 near zero from its own cubic,
and the branch bound extends it to the entire noncritical ray. -/
theorem cubic_ray_linear (K : ℝ → ℂ) (c : ℂ) {d : ℝ} (hd : 0 < d)
    (gap : ∀ (r : ℝ), 0 < r → d ≤ ‖4-27*(c*r)‖)
    (alg : ∀ (r : ℝ), 0 < r → (4-27*(c*r))*K r^3 = 3*K r+1)
    (h0 : Tendsto K (𝓝[>] 0) (𝓝 1)) :
    ∃ C : ℝ, ∀ r > 0, ‖K r-1‖ ≤ C*r := by
  let M := max 1 (4/d)
  have hm r (hr : 0 < r) : ‖K r‖ ≤ M := cubic_branch_bound hd (gap r hr) (alg r hr)
  have hz : Tendsto (fun r ↦ ‖2*K r+1‖) (𝓝[>] 0) (𝓝 ‖(2:ℂ)*1+1‖) :=
    ((tendsto_const_nhds.mul h0).add tendsto_const_nhds).norm
  have hn := hz.eventually (lt_mem_nhds (by norm_num : (1:ℝ) < ‖(2:ℂ)*1+1‖))
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hn)
  refine ⟨max (27*‖c‖*M^3) ((M+1)/δ),fun r hr ↦ ?_⟩
  by_cases hrδ : r < δ
  · have hden := hnear (y := r) (by simpa [Real.dist_eq, abs_of_pos hr] using hrδ) hr
    have he : (K r-1)*(2*K r+1)^2 = 27*(c*r)*K r^3 := by
      linear_combination alg r hr
    have hnorm := congrArg norm he
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] at hnorm
    norm_num at hnorm
    calc ‖K r-1‖ ≤ ‖K r-1‖ * ‖2*K r+1‖^2 :=
           le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hden.le)
         _ = _ := hnorm
         _ ≤ 27*(‖c‖*r)*M^3 := by gcongr; exact hm r hr
         _ ≤ _ := by
           calc _ = (27*‖c‖*M^3)*r := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) hr.le
  · have hnear' : ‖K r-1‖ ≤ M+1 := (norm_sub_le ..).trans (by simpa using add_le_add_right (hm r hr) 1)
    apply hnear'.trans
    have hM : 0 ≤ M := le_trans zero_le_one (le_max_left ..)
    calc M+1 = ((M+1)/δ)*δ := by field_simp
         _ ≤ ((M+1)/δ)*r := mul_le_mul_of_nonneg_left (le_of_not_gt hrδ) (by positivity)
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) hr.le

/-- On one lateral ray the difference of the two normalized branches is O(r).
The cubic rescaling r=u²/n³ and prefactor 1/n produce the summable n⁻⁴ bound.
A complex weight can contain a rotating phase as well as exponential damping. -/
theorem cubic_lateral_interchange (K weight : ℝ → ℂ) (C : ℝ)
    (hK : ContinuousOn K (Ioi 0)) (hw : Continuous weight)
    (hlin : ∀ r > 0, ‖K r‖ ≤ C*r) (hdamp : ∀ u > 0, ‖weight u‖ ≤ exp (-u)) :
    let t := fun (n : ℕ) (u : ℝ) ↦ weight u * (((n+1 : ℕ) : ℝ)⁻¹ • K (u^2 / ((n+1 : ℕ) : ℝ)^3))
    HasSum (fun n ↦ ∫ u in Ioi (0:ℝ), t n u) (∫ u in Ioi (0:ℝ), ∑' n, t n u) := by
  intro t
  let b (n : ℕ) := (((n+1:ℕ):ℝ)^4)⁻¹
  let M (u : ℝ) := C*(exp (-u)*u^2)
  have hb : Summable b := (summable_nat_add_iff 1).2 (summable_nat_pow_inv.mpr (by decide : 1 < 4))
  have hi : IntegrableOn M (Ioi 0) := by
    simpa only [M, IntegrableOn, show (3:ℝ)-1=2 by norm_num, rpow_two] using!
      (GammaIntegral_convergent (s := 3) (by norm_num)).const_mul C
  have hm (n : ℕ) : AEStronglyMeasurable (t n) (volume.restrict (Ioi 0)) := by
    let k : ℝ := (n+1:ℕ)
    have hk : 0 < k := by dsimp [k]; positivity
    have hc : ContinuousOn (fun u : ℝ ↦ K (u^2/k^3)) (Ioi 0) :=
      hK.comp ((continuous_id.pow 2).div_const (k^3)).continuousOn
        (fun _ hu ↦ div_pos (pow_pos hu 2) (pow_pos hk 3))
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact hw.continuousOn.mul (hc.const_smul k⁻¹)
  have hbound (n : ℕ) (u : ℝ) (hu : 0 < u) : ‖t n u‖ ≤ b n * M u := by
    let k : ℝ := (n+1 : ℕ)
    have hk : 0 < k := by dsimp [k]; positivity
    change ‖weight u * (k⁻¹ • K (u^2/k^3))‖ ≤ (k^4)⁻¹ * (C*(exp (-u)*u^2))
    rw [norm_mul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk)]
    calc _ ≤ exp (-u) * (k⁻¹ * (C*(u^2/k^3))) := mul_le_mul (hdamp u hu)
           (mul_le_mul_of_nonneg_left (hlin _ (div_pos (pow_pos hu 2) (pow_pos hk 3))) (inv_pos.mpr hk).le)
           (mul_nonneg (inv_pos.mpr hk).le (norm_nonneg _)) (exp_pos _).le
         _ = _ := by field_simp
  have hInt n := ((hi.const_mul (b n)).mono' (hm n)
    ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono (hbound n)))
  apply hasSum_integral_of_summable_integral_norm hInt
  apply Summable.of_nonneg_of_le (fun n ↦ integral_nonneg (fun _ ↦ norm_nonneg _)) _ (hb.mul_right (∫ u in Ioi (0:ℝ), M u))
  intro n
  rw [← integral_const_mul]
  exact integral_mono_ae (hInt n).norm (hi.const_mul (b n))
    ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono (hbound n))

/-- Termwise lateral integration for the actual cubic algebraic equation.
The remaining inputs here describe branch continuations on a single nonreal
ray and its opposite. A contour-jump identity is a separate assertion. -/
theorem normalized_branches_interchange (P Q weight : ℝ → ℂ) (c : ℂ) (hc : c.im ≠ 0)
    (hP : ContinuousOn P (Ioi 0)) (hQ : ContinuousOn Q (Ioi 0))
    (p0 : Tendsto P (𝓝[>] 0) (𝓝 1)) (q0 : Tendsto Q (𝓝[>] 0) (𝓝 1))
    (ap : ∀ (r : ℝ), 0 < r → (4-27*(c*r))*P r^3 = 3*P r+1)
    (aq : ∀ (r : ℝ), 0 < r → (4-27*(-c*r))*Q r^3 = 3*Q r+1)
    (hw : Continuous weight) (hdamp : ∀ u > 0, ‖weight u‖ ≤ exp (-u)) :
    let t := fun (n : ℕ) (u : ℝ) ↦ weight u * (((n+1 : ℕ) : ℝ)⁻¹ •
      (P (u^2 / ((n+1 : ℕ) : ℝ)^3) - Q (u^2 / ((n+1 : ℕ) : ℝ)^3)))
    HasSum (fun n ↦ ∫ u in Ioi (0:ℝ), t n u) (∫ u in Ioi (0:ℝ), ∑' n, t n u) := by
  obtain ⟨d,hd,hgap⟩ := nonreal_ray_gap hc
  obtain ⟨e,he,hegap⟩ := nonreal_ray_gap (c := -c) (by simpa using hc)
  obtain ⟨A,hA⟩ := cubic_ray_linear P c hd (fun r _ ↦ hgap r) ap p0
  obtain ⟨B,hB⟩ := cubic_ray_linear Q (-c) he (fun r _ ↦ hegap r) aq q0
  apply cubic_lateral_interchange (fun r ↦ P r-Q r) weight (A+B) (hP.sub hQ) hw _ hdamp
  intro r hr
  calc ‖P r-Q r‖ = ‖(P r-1)-(Q r-1)‖ := by rw [sub_sub_sub_cancel_right]
       _ ≤ ‖P r-1‖ + ‖Q r-1‖ := norm_sub_le ..
       _ ≤ _ := by rw [add_mul]; exact add_le_add (hA r hr) (hB r hr)

end
end CubicTheta
