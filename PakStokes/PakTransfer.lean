module

public import PakStokes.NomeChart
public import PakStokes.OrdinaryPoint
import all PakStokes.NomeChart
import all PakStokes.CubeNome
import all PakStokes.PolynomialFlow

/-! Transfer an equation in the literal formal cube power series, with
polynomial coefficients in the nome, to the autonomous physical theorem. -/
public section
namespace CubicTheta.Nome
open Filter Set Flow MvPolynomial
open scoped Topology
noncomputable section

private theorem transfer_at_ordinary {n : ℕ} (Q : MvPolynomial (Fin (n+1)) ℂ)
    (x : ℝ) (hx : 0<x)
    (ordinary : eval (fun i : Fin (n+1) ↦ source i.val x) (pderiv (Fin.last n) Q) ≠ 0)
    (ident : ∀ p > 0, eval (fun i : Fin (n+1) ↦ source i.val p) Q=0) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ p : ℝ in atTop, eval (fun j : Fin J ↦ iteratedDeriv j.val Physical.regularCube p) P=0 := by
  classical
  let v (i : Fin (n+1)) := source i.val
  let g (i : Fin (n+1)) (p : ℝ) := eval (fun j ↦ v j p) (pderiv i Q)
  let top := Fin.last n
  let S := g top
  have hd {p : ℝ} (hp : 0<p) (i : Fin (n+1)) : DifferentiableAt ℝ (v i) p :=
    (source_analytic hp i.val).differentiableAt
  have chain (A : MvPolynomial (Fin (n+1)) ℂ) {p : ℝ} (hp : 0<p) :=
    polynomial_chain A v (fun i ↦ deriv (v i)) p (fun i ↦ (hd hp i).hasDerivAt)
  have vanish {p : ℝ} (hp : 0<p) : ∑ i, g i p * deriv (v i) p = 0 := by
    have near : (fun z ↦ eval (fun i ↦ v i z) Q) =ᶠ[𝓝 p] (fun _ ↦ 0) :=
      (lt_mem_nhds hp).mono fun z hz ↦ ident z hz
    exact (chain Q hp).deriv.symm.trans (near.deriv_eq.trans (deriv_const ..))
  have hn : n ≠ 0 := by
    rintro rfl; have he := vanish hx
    change ∑ i : Fin 1, g i x * deriv (v i) x = 0 at he
    rw [Fin.sum_univ_one] at he
    have ds : deriv (v 0) x = speed x := (qRay_deriv hx).deriv
    rw [ds] at he
    have hs : speed x ≠ 0 := by unfold speed recip qRay; norm_cast; positivity
    exact (mul_ne_zero ordinary hs) he
  -- Localize the state at the separant on the solution curve.
  let invS (p : ℝ) := (S p)⁻¹
  let u : Fin (n+1) ⊕ Fin 3 → ℝ → ℂ := Sum.elim v ![recip,pole,invS]
  let G := Generated u x
  have gv (i : Fin (n+1)) : G (v i) := Generated.coord (u := u) (.inl i)
  have gr : G recip := Generated.coord (u := u) (.inr 0)
  have gp : G pole := Generated.coord (u := u) (.inr 1)
  have gw : G invS := Generated.coord (u := u) (.inr 2)
  have gc (c : ℂ) : G (fun _ ↦ c) := Generated.const _
  have gs : G speed := ((gc 2).mul (gr.pow 3)).mul (gv 0)
  have gg (i : Fin (n+1)) : G (g i) := Generated.evalPoly v gv _
  have pos : ∀ᶠ p in 𝓝 x, 0<p := lt_mem_nhds hx
  have Snz : ∀ᶠ p in 𝓝 x, S p ≠ 0 := (chain (pderiv top Q) hx).continuousAt.eventually_ne ordinary
  have low (i : Fin (n+1)) (hi : i ≠ top) : G (deriv (v i)) := by
    obtain ⟨k,hk⟩ := i
    cases k with
    | zero => exact gs.congr (pos.mono fun p hp ↦ (qRay_deriv hp).deriv.symm)
    | succ k =>
      have lt : k+2 < n+1 := by
        have h : k+1≠n := fun eqn ↦ hi (Fin.ext eqn); omega
      apply (gs.mul (gv ⟨k+2,lt⟩)).congr
      exact pos.mono fun p hp ↦ (source_deriv hp k).deriv.symm
  -- Solve the differentiated scalar equation for its highest coordinate.
  let lowSum := ∑ i ∈ Finset.univ.erase top, g i * deriv (v i)
  have gl : G lowSum := Generated.finsetSum _ _ (fun i hi ↦ (gg i).mul (low i (Finset.mem_erase.mp hi).1))
  have dv (i : Fin (n+1)) : G (deriv (v i)) := by
    by_cases hi : i=top
    · subst i
      apply (((gc (-1)).mul gl).mul gw).congr
      filter_upwards [pos,Snz] with p hp nz
      have he := vanish hp
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at he
      change (-1)*lowSum p*(S p)⁻¹ = deriv (v top) p
      have hh : S p*deriv (v top) p+lowSum p=0 := by simpa [S,lowSum,Finset.sum_apply] using he
      field_simp [nz]; linear_combination -hh
    · exact low i hi
  have dS : G (deriv S) := by
    let D (i : Fin (n+1)) (p : ℝ) := eval (fun k ↦ v k p) (pderiv i (pderiv top Q))
    have gen (i) : G (D i) := Generated.evalPoly v gv _
    apply (Generated.finsetSum Finset.univ _ (fun i _ ↦ (gen i).mul (dv i))).congr
    filter_upwards [pos] with p hp
    simpa [D,Finset.sum_apply] using (chain (pderiv top Q) hp).deriv.symm
  have smooth : ∀ᶠ p in 𝓝 x, ∀ i, DifferentiableAt ℝ (u i) p := by
    filter_upwards [pos,Snz] with p hp nz i
    rcases i with i|i
    · exact hd hp i
    · fin_cases i
      · exact (recip_deriv hp).differentiableAt
      · exact (pole_deriv hp).differentiableAt
      · exact (chain (pderiv top Q) hp).differentiableAt.inv nz
  have closed (i) : G (deriv (u i)) := by
    rcases i with i|i
    · exact dv i
    · fin_cases i
      · change G (deriv recip)
        exact ((gc (-1)).mul (gr.pow 2)).congr (pos.mono fun p hp ↦ by simpa using (recip_deriv hp).deriv.symm)
      · exact (((gc (2/3)).mul gr).mul gp).congr (pos.mono fun p hp ↦ (pole_deriv hp).deriv.symm)
      · apply (((gc (-1)).mul dS).mul (gw.pow 2)).congr
        filter_upwards [pos,Snz] with p hp nz
        have hi := ((chain (pderiv top Q) hp).differentiableAt.hasDerivAt.inv nz).deriv
        change (-1)*deriv S p*((S p)⁻¹)^2 = deriv invS p
        change deriv invS p = -deriv S p / (S p)^2 at hi
        rw [hi]; simp [inv_pow,div_eq_mul_inv]
  -- The elementary terms removed in the physical theorem are state polynomials.
  have readout : G Physical.regularCube := by
    apply ((gv ⟨1,by omega⟩).sub ((gc (1/2)).add ((gc (Real.Gamma (4/3))).mul gp))).congr
    exact pos.mono fun p hp ↦ (regular_at hp).symm
  obtain ⟨P,hp,hz⟩ := autonomous_readout u x _ readout smooth closed
  exact ⟨_,P,hp,local_to_tail P hx hz⟩

theorem pak_formal_transfer (Q : MvPolynomial ℕ ℂ) (hQ : Q ≠ 0)
    (zero : MvPolynomial.aeval coordinates Q=0) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ p : ℝ in atTop, eval (fun j : Fin J ↦ iteratedDeriv j.val Physical.regularCube p) P=0 := by
  have relation (p : ℝ) (hp : 0<p) : eval (fun i ↦ source i p) Q=0 :=
    formal_identity_on_disk Q zero (qRay_disk hp)
  obtain ⟨n,A,x,hx,ordinary,ident⟩ := ordinary_relation (Ioi (0:ℝ)) ⟨1,zero_lt_one⟩ source ⟨Q,hQ,relation⟩
  exact transfer_at_ordinary A x hx ordinary ident
end
end CubicTheta.Nome
