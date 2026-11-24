module

public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Vandermonde

/-! Algebraic tests of the highest-degree mixed coefficients of a jet relation. -/
public section
namespace CubicTheta
open Matrix
noncomputable section

/-- Each slot can use its own Vandermonde basis of wave jets. If the slots
are assigned disjoint labels, only coefficients of distinct waves are tested. -/
theorem mixed_jet_grid {K : Type*} [Field K] {slots : Type*} [Finite slots] {n : ℕ}
    (nodes : slots → Fin n → K) (distinct : ∀ i, Function.Injective (nodes i))
    (L : MultilinearMap (RingHom.id K) (fun _ : slots ↦ Fin n → K) K)
    (zero : ∀ choice : slots → Fin n,
      L (fun i j ↦ nodes i (choice i) ^ j.val) = 0) : L = 0 := by
  classical
  have independent (i : slots) : LinearIndependent K (vandermonde (nodes i)).row :=
    Matrix.linearIndependent_rows_of_det_ne_zero (det_vandermonde_ne_zero_iff.mpr (distinct i))
  let basis (i : slots) := basisOfLinearIndependentOfCardEqFinrank' _ (independent i)
    (Module.finrank_fintype_fun_eq_card K).symm
  have row (i : slots) (k : Fin n) : basis i k = fun j : Fin n ↦ nodes i k ^ j.val :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ (independent i)
      (Module.finrank_fintype_fun_eq_card K).symm) k
  apply Module.Basis.ext_multilinear basis
  intro choice
  change (L fun i ↦ basis i (choice i)) = 0
  simp_rw [row]
  exact zero choice

/-- The polynomial with roots at the unused nodes gives a diagonal test on
equicardinal subsets. At the intended subset its product of values is nonzero. -/
theorem mixed_subset_diagonal {K ι : Type*} [Field K] [DecidableEq ι] (z : ι → K)
    (hz : Function.Injective z) (pool s t : Finset ι) (ht : t ⊆ pool)
    (card : s.card = t.card) :
    (∏ i ∈ t, ∏ j ∈ pool \ s, (z i - z j)) ≠ 0 ↔ t = s := by
  classical
  simp only [Finset.prod_ne_zero_iff,sub_ne_zero,hz.ne_iff]
  constructor
  · intro h
    apply Finset.eq_of_subset_of_card_le _ card.le
    intro i hi
    by_contra hn
    exact h i hi i (Finset.mem_sdiff.mpr ⟨ht hi,hn⟩) rfl
  · rintro rfl i hi j hj rfl
    exact (Finset.mem_sdiff.mp hj).2 hi

end
end CubicTheta
