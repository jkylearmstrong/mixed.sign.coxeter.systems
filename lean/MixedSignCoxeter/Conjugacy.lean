/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.ReflectionSystem

/-!
# Conjugate Reflection Systems and Reflection Diagrams (Section 2.3)

Formalization of Section 2.3 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main definitions
* `SignedPerm n`: Elements of `𝒪`, the subgroup of the orthogonal group permuting
  `{±e₁, ..., ±eₙ}` (Definition 2.8).
* `GraphIso B₁ B₂`: An isomorphism of reflection diagrams `Γ(B₁) ≅ Γ(B₂)` (Definition 2.33).

## Main results
* `SignedPerm.toMatrix_transpose_mul_self`: `Pᵀ * P = 1` (Remark 2.30).
* `conjugate_reflections_of_form` (Lemma 2.32): If `B₂ = ± Pᵀ * B₁ * P` with `P ∈ 𝒪`, then
  `Pᵀ * s_{P.perm j}(B₁) * P = s_j(B₂)`.
* `graphIso_conjugates_forms` (Lemma 2.37): An isomorphism `Γ(B₁) ≅ Γ(B₂)` induces
  `P ∈ 𝒪` with `Pᵀ * B₁ * P = B₂`.
-/

open Matrix BigOperators

namespace ReflectionSystem

variable {n : ℕ}

/-- An element `P ∈ 𝒪` (Definition 2.8): a signed permutation matrix sending
`e_j ↦ (±1) e_{perm j}`. -/
structure SignedPerm (n : ℕ) where
  perm : Equiv.Perm (Fin n)
  neg : Fin n → Bool

namespace SignedPerm

def signReal (P : SignedPerm n) (j : Fin n) : ℝ :=
  if P.neg j then -1 else 1

@[simp]
lemma signReal_mul_self (P : SignedPerm n) (j : Fin n) :
    P.signReal j * P.signReal j = 1 := by
  cases h : P.neg j <;> simp [signReal, h]

/-- Matrix representation of `P ∈ 𝒪` in the standard basis. -/
def toMatrix (P : SignedPerm n) : Matrix (Fin n) (Fin n) ℝ :=
  of fun r c => if r = P.perm c then P.signReal c else 0

@[simp]
lemma toMatrix_apply (P : SignedPerm n) (r c : Fin n) :
    P.toMatrix r c = if r = P.perm c then P.signReal c else 0 := rfl

/-- **Remark 2.30**: Every `P ∈ 𝒪` is orthogonal (`Pᵀ * P = 1`). -/
theorem toMatrix_transpose_mul_self (P : SignedPerm n) :
    P.toMatrixᵀ * P.toMatrix = 1 := by
  ext r c
  simp only [mul_apply, transpose_apply, toMatrix_apply, one_apply]
  have hterm : ∀ k : Fin n,
      (if k = P.perm r then P.signReal r else 0) *
        (if k = P.perm c then P.signReal c else 0) =
      if k = P.perm r then (if P.perm r = P.perm c then P.signReal r * P.signReal c else 0) else 0 := by
    intro k
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hrc : r = c
  · subst hrc
    simp
  · have hp : P.perm r ≠ P.perm c := fun h => hrc (P.perm.injective h)
    simp [hrc, hp]

/-- Entrywise formula for `Pᵀ * M * P`. -/
lemma toMatrix_conj_apply (P : SignedPerm n) (M : Matrix (Fin n) (Fin n) ℝ) (r c : Fin n) :
    (P.toMatrixᵀ * M * P.toMatrix) r c =
      P.signReal r * P.signReal c * M (P.perm r) (P.perm c) := by
  have hleft : ∀ k : Fin n,
      (P.toMatrixᵀ * M) r k = P.signReal r * M (P.perm r) k := by
    intro k
    simp only [mul_apply, transpose_apply, toMatrix_apply]
    have ht : ∀ m : Fin n,
        (if m = P.perm r then P.signReal r else 0) * M m k =
        if m = P.perm r then P.signReal r * M m k else 0 := by
      intro m; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun m _ => ht m)]
    simp
  rw [mul_apply]
  simp_rw [hleft, toMatrix_apply]
  have ht2 : ∀ k : Fin n,
      P.signReal r * M (P.perm r) k * (if k = P.perm c then P.signReal c else 0) =
      if k = P.perm c then P.signReal r * P.signReal c * M (P.perm r) k else 0 := by
    intro k; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ => ht2 k)]
  simp

end SignedPerm

/-- **Lemma 2.32** (positive sign): If `B₂ = Pᵀ * B₁ * P` with `P ∈ 𝒪`, then
conjugating `s_{P.perm j}(B₁)` by `P` yields `s_j(B₂)`. -/
theorem conjugate_reflections_of_form (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) (P : SignedPerm n)
    (hB : B₂ = P.toMatrixᵀ * B₁ * P.toMatrix) (j : Fin n) :
    P.toMatrixᵀ * reflectionMatrix B₁ (P.perm j) * P.toMatrix = reflectionMatrix B₂ j := by
  ext r c
  rw [P.toMatrix_conj_apply]
  simp only [reflectionMatrix_apply, hB, P.toMatrix_conj_apply]
  have h1 : P.signReal j * P.signReal j = 1 := P.signReal_mul_self j
  by_cases hrc : r = c
  · subst hrc
    have hp : P.perm r = P.perm r := rfl
    by_cases hrj : r = j
    · subst hrj
      simp [P.signReal_mul_self r]
    · have hpj : P.perm r ≠ P.perm j := fun h => hrj (P.perm.injective h)
      simp [hrj, hpj, P.signReal_mul_self r]
  · have hprc : P.perm r ≠ P.perm c := fun h => hrc (P.perm.injective h)
    by_cases hrj : r = j
    · subst hrj
      simp only [hrc, ↓reduceIte, hprc, P.signReal_mul_self r, one_mul]
      ring
    · have hpj : P.perm r ≠ P.perm j := fun h => hrj (P.perm.injective h)
      simp [hrc, hprc, hrj, hpj]

/-- **Lemma 2.32** (negative sign): If `B₂ = -(Pᵀ * B₁ * P)` with `P ∈ 𝒪`,
conjugating `s_{P.perm j}(B₁)` by `P` still yields `s_j(B₂)` (by Lemma 2.31). -/
theorem conjugate_reflections_of_neg_form (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) (P : SignedPerm n)
    (hB : B₂ = -(P.toMatrixᵀ * B₁ * P.toMatrix)) (j : Fin n) :
    P.toMatrixᵀ * reflectionMatrix B₁ (P.perm j) * P.toMatrix = reflectionMatrix B₂ j := by
  rw [hB, reflectionMatrix_neg]
  exact conjugate_reflections_of_form B₁ (P.toMatrixᵀ * B₁ * P.toMatrix) P rfl j

/-- **Definition 2.33**: An isomorphism of reflection diagrams `Γ(B₁) ≅ Γ(B₂)` is a
bijection `φ` on nodes preserving node weights and edge weights. -/
def IsGraphIso (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) (φ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, B₂ i j = B₁ (φ i) (φ j)

/-- **Lemma 2.37**: If `Γ(B₁) ≅ Γ(B₂)` via `φ`, then `B₂ = Pᵀ * B₁ * P` for `P ∈ 𝒪`. -/
theorem graphIso_conjugates_forms {B₁ B₂ : Matrix (Fin n) (Fin n) ℝ}
    {φ : Equiv.Perm (Fin n)} (hφ : IsGraphIso B₁ B₂ φ) :
    let P : SignedPerm n := ⟨φ, fun _ => false⟩
    P.toMatrixᵀ * B₁ * P.toMatrix = B₂ := by
  intro P
  ext r c
  rw [P.toMatrix_conj_apply]
  simp only [P, SignedPerm.signReal, Bool.false_eq_true, ↓reduceIte, one_mul]
  exact (hφ r c).symm

/-- **Corollary 2.38 (permutation conjugacy)**: Two reflection diagrams `Γ(B₁)` and
`Γ(B₂)` are isomorphic if and only if `B₂ = Pᵀ * B₁ * P` for a permutation matrix
`P ∈ 𝒪` (`P.neg = fun _ => false`). -/
theorem graphIso_iff_perm_conjugate (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) :
    (∃ φ : Equiv.Perm (Fin n), IsGraphIso B₁ B₂ φ) ↔
      ∃ P : SignedPerm n, (∀ i, P.neg i = false) ∧
        B₂ = P.toMatrixᵀ * B₁ * P.toMatrix := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨⟨φ, fun _ => false⟩, fun _ => rfl, (graphIso_conjugates_forms hφ).symm⟩
  · rintro ⟨P, hneg, hB⟩
    refine ⟨P.perm, fun i j => ?_⟩
    rw [hB, P.toMatrix_conj_apply]
    have hsi : P.signReal i = 1 := by simp [SignedPerm.signReal, hneg i]
    have hsj : P.signReal j = 1 := by simp [SignedPerm.signReal, hneg j]
    rw [hsi, hsj, one_mul, one_mul]

/-- **Corollary 2.38 (general `𝒪`-conjugacy)**: Any `𝒪`-conjugacy `B₂ = Pᵀ * B₁ * P`
with `P : SignedPerm n` preserves diagonal weights and absolute values of edge weights. -/
theorem O_conjugate_preserves_diag_and_abs {B₁ B₂ : Matrix (Fin n) (Fin n) ℝ}
    (P : SignedPerm n) (hB : B₂ = P.toMatrixᵀ * B₁ * P.toMatrix) (i j : Fin n) :
    B₂ i i = B₁ (P.perm i) (P.perm i) ∧ |B₂ i j| = |B₁ (P.perm i) (P.perm j)| := by
  rw [hB, P.toMatrix_conj_apply, P.toMatrix_conj_apply]
  have h1 : P.signReal i * P.signReal i = 1 := P.signReal_mul_self i
  have habs : ∀ k, |P.signReal k| = 1 := by
    intro k; unfold SignedPerm.signReal; cases P.neg k <;> norm_num
  refine ⟨by rw [h1, one_mul], ?_⟩
  rw [abs_mul, abs_mul, habs i, habs j, one_mul, one_mul]

/-- **Corollary 2.46**: Conjugate reflection systems (`B₂ = Pᵀ * B₁ * P` with `P ∈ 𝒪`)
have identical quadratic-form values under `v ↦ P.toMatrix.mulVec v`, and therefore
the same signature classification. -/
theorem O_conjugate_quadForm {B₁ B₂ : Matrix (Fin n) (Fin n) ℝ} (P : SignedPerm n)
    (hB : B₂ = P.toMatrixᵀ * B₁ * P.toMatrix) (v : Fin n → ℝ) :
    quadForm B₂ v = quadForm B₁ (P.toMatrix.mulVec v) := by
  simp only [quadForm, hB, P.toMatrix_conj_apply]
  have hmul : ∀ i : Fin n, P.toMatrix.mulVec v (P.perm i) = P.signReal i * v i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, SignedPerm.toMatrix_apply]
    have ht : ∀ k : Fin n,
        (if P.perm i = P.perm k then P.signReal k else 0) * v k =
        if k = i then P.signReal i * v i else 0 := by
      intro k
      by_cases hki : k = i
      · subst hki; simp
      · have hp : P.perm i ≠ P.perm k := fun h => hki (P.perm.injective h).symm
        simp [hki, hp]
    rw [Finset.sum_congr rfl fun k _ => ht k]
    simp
  have hsum_perm : ∀ f : Fin n → ℝ, (∑ i : Fin n, f (P.perm i)) = ∑ i : Fin n, f i :=
    fun f => Equiv.sum_comp P.perm f
  calc (∑ i : Fin n, ∑ j : Fin n,
        v i * (P.signReal i * P.signReal j * B₁ (P.perm i) (P.perm j)) * v j)
      = ∑ i : Fin n, ∑ j : Fin n,
          (P.signReal i * v i) * B₁ (P.perm i) (P.perm j) * (P.signReal j * v j) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i : Fin n, ∑ j : Fin n,
          P.toMatrix.mulVec v (P.perm i) * B₁ (P.perm i) (P.perm j) * P.toMatrix.mulVec v (P.perm j) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
              rw [hmul i, hmul j]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          P.toMatrix.mulVec v i * B₁ i j * P.toMatrix.mulVec v j := by
            rw [hsum_perm (fun i => ∑ j : Fin n,
              P.toMatrix.mulVec v i * B₁ i (P.perm j) * P.toMatrix.mulVec v (P.perm j))]
            refine Finset.sum_congr rfl fun i _ => hsum_perm (fun j =>
              P.toMatrix.mulVec v i * B₁ i j * P.toMatrix.mulVec v j)

theorem O_conjugate_isPosDef_iff (S₁ S₂ : ReflectionSystem n) (P : SignedPerm n)
    (hB : S₂.B = P.toMatrixᵀ * S₁.B * P.toMatrix) :
    S₁.IsPosDef ↔ S₂.IsPosDef := by
  have hinj : ∀ v : Fin n → ℝ, P.toMatrix.mulVec v = 0 ↔ v = 0 := by
    intro v
    constructor
    · intro h0
      have h1 : P.toMatrixᵀ.mulVec (P.toMatrix.mulVec v) = 0 := by rw [h0, Matrix.mulVec_zero]
      rw [Matrix.mulVec_mulVec, P.toMatrix_transpose_mul_self, Matrix.one_mulVec] at h1
      exact h1
    · intro h0; subst h0; simp
  have hsurj : ∀ u : Fin n → ℝ, ∃ v : Fin n → ℝ, P.toMatrix.mulVec v = u := by
    intro u
    refine ⟨P.toMatrixᵀ.mulVec u, ?_⟩
    rw [Matrix.mulVec_mulVec]
    have hPP : P.toMatrix * P.toMatrixᵀ = 1 := by
      ext r c
      simp only [Matrix.mul_apply, Matrix.transpose_apply, SignedPerm.toMatrix_apply, Matrix.one_apply]
      have hterm : ∀ k : Fin n,
          (if r = P.perm k then P.signReal k else 0) *
            (if c = P.perm k then P.signReal k else 0) =
          if k = P.perm.symm r then (if r = c then 1 else 0) else 0 := by
        intro k
        by_cases hk : k = P.perm.symm r
        · subst hk
          have hpk : P.perm (P.perm.symm r) = r := P.perm.apply_symm_apply r
          by_cases hrc : r = c
          · subst hrc; simp [hpk, P.signReal_mul_self]
          · simp [hpk, hrc, Ne.symm hrc]
        · have hne : r ≠ P.perm k := fun h => hk (P.perm.eq_symm_apply.mpr h.symm)
          simp [hk, hne]
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      simp
    rw [hPP, Matrix.one_mulVec]
  constructor
  · intro h1 v hv
    rw [O_conjugate_quadForm P hB v]
    exact h1 _ ((hinj v).not.mpr hv)
  · intro h2 u hu
    obtain ⟨v, rfl⟩ := hsurj u
    rw [← O_conjugate_quadForm P hB v]
    exact h2 v (fun hv => hu ((hinj v).mpr hv))

/-- **Example 2.36**: Swapping the two nodes of an asymmetric rank-2 bilinear form
gives an `𝒪`-conjugate bilinear form via `Equiv.swap 0 1`. -/
theorem example_2_36_form_conjugate (a b c : ℝ) :
    let B₁ : Matrix (Fin 2) (Fin 2) ℝ := !![a, c; c, b]
    let B₂ : Matrix (Fin 2) (Fin 2) ℝ := !![b, c; c, a]
    let P : SignedPerm 2 := ⟨Equiv.swap 0 1, fun _ => true⟩
    B₂ = P.toMatrixᵀ * B₁ * P.toMatrix := by
  intro B₁ B₂ P
  ext i j
  rw [P.toMatrix_conj_apply]
  fin_cases i <;> fin_cases j <;>
    simp [B₁, B₂, P, SignedPerm.signReal]

/-! ### Remark 2.35: Diagram Isomorphism Induces Reflection Group Isomorphism -/

private lemma signedPerm_toMatrix_mul_transpose (P : SignedPerm n) :
    P.toMatrix * P.toMatrixᵀ = 1 := by
  ext r c
  simp only [Matrix.mul_apply, Matrix.transpose_apply, SignedPerm.toMatrix_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n,
      (if r = P.perm k then P.signReal k else 0) *
        (if c = P.perm k then P.signReal k else 0) =
      if k = P.perm.symm r then (if r = c then 1 else 0) else 0 := by
    intro k
    by_cases hk : k = P.perm.symm r
    · subst hk
      have hpk : P.perm (P.perm.symm r) = r := P.perm.apply_symm_apply r
      by_cases hrc : r = c
      · subst hrc; simp [hpk, P.signReal_mul_self]
      · simp [hpk, hrc, Ne.symm hrc]
    · have hne : r ≠ P.perm k := fun h => hk (P.perm.eq_symm_apply.mpr h.symm)
      simp [hk, hne]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  simp

/-- Conjugating a generating reflection of `S₁` by a diagram isomorphism `φ : Γ(B₁) ≅ Γ(B₂)`
yields the corresponding generating reflection of `S₂`. -/
theorem reflectionMatrix_conj_by_graphIso (S₁ S₂ : ReflectionSystem n)
    {φ : Equiv.Perm (Fin n)} (hφ : IsGraphIso S₁.B S₂.B φ) (i : Fin n) :
    let P : SignedPerm n := ⟨φ, fun _ => false⟩
    P.toMatrixᵀ * reflectionMatrix S₁.B (φ i) * P.toMatrix = reflectionMatrix S₂.B i := by
  intro P
  ext r c
  rw [P.toMatrix_conj_apply]
  have hsr : P.signReal r = 1 := rfl
  have hsc : P.signReal c = 1 := rfl
  rw [hsr, hsc, one_mul, one_mul]
  rw [reflectionMatrix_apply, reflectionMatrix_apply]
  have hrc : (φ r = φ c) ↔ (r = c) := φ.injective.eq_iff
  have hri : (φ r = φ i) ↔ (r = i) := φ.injective.eq_iff
  simp only [P]
  rw [hφ i c, hφ i i]
  by_cases h1 : r = c <;> by_cases h2 : r = i <;>
    simp [hrc, hri, h1, h2]

/-- **Remark 2.35 (forward direction)**: An isomorphism of reflection diagrams `Γ(B₁) ≅ Γ(B₂)`
induces an isomorphism of reflection groups `W(B₁) ≃* W(B₂)` via matrix conjugation. -/
noncomputable def graphIso_mulEquiv (S₁ S₂ : ReflectionSystem n)
    {φ : Equiv.Perm (Fin n)} (hφ : IsGraphIso S₁.B S₂.B φ) :
    W_group S₁ ≃* W_group S₂ := by
  let P : SignedPerm n := ⟨φ, fun _ => false⟩
  have hPtP : P.toMatrixᵀ * P.toMatrix = 1 := P.toMatrix_transpose_mul_self
  have hPPt : P.toMatrix * P.toMatrixᵀ = 1 := signedPerm_toMatrix_mul_transpose P
  have hmem_fwd : ∀ M ∈ W_group S₁, P.toMatrixᵀ * M * P.toMatrix ∈ W_group S₂ := by
    intro M hM
    induction hM using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨j, rfl⟩
      have hconj := reflectionMatrix_conj_by_graphIso S₁ S₂ hφ (φ.symm j)
      simp only [Equiv.apply_symm_apply] at hconj
      change P.toMatrixᵀ * reflectionMatrix S₁.B j * P.toMatrix ∈ W_group S₂
      rw [hconj]
      exact Submonoid.subset_closure ⟨φ.symm j, rfl⟩
    | one =>
      simp only [Matrix.mul_one, hPtP]
      exact (W_group S₂).one_mem
    | mul x y _ _ ihx ihy =>
      have hmul : P.toMatrixᵀ * (x * y) * P.toMatrix =
          (P.toMatrixᵀ * x * P.toMatrix) * (P.toMatrixᵀ * y * P.toMatrix) := by
        calc
          P.toMatrixᵀ * (x * y) * P.toMatrix
            = P.toMatrixᵀ * x * (1 * y) * P.toMatrix := by simp [Matrix.mul_assoc]
          _ = P.toMatrixᵀ * x * ((P.toMatrix * P.toMatrixᵀ) * y) * P.toMatrix := by rw [hPPt]
          _ = (P.toMatrixᵀ * x * P.toMatrix) * (P.toMatrixᵀ * y * P.toMatrix) := by
                simp [Matrix.mul_assoc]
      rw [hmul]
      exact (W_group S₂).mul_mem ihx ihy
  have hmem_bwd : ∀ N ∈ W_group S₂, P.toMatrix * N * P.toMatrixᵀ ∈ W_group S₁ := by
    intro N hN
    induction hN using Submonoid.closure_induction with
    | mem y hy =>
      rcases hy with ⟨i, rfl⟩
      have hconj := reflectionMatrix_conj_by_graphIso S₁ S₂ hφ i
      have hinv : P.toMatrix * reflectionMatrix S₂.B i * P.toMatrixᵀ =
          reflectionMatrix S₁.B (φ i) := by
        rw [← hconj]
        calc
          P.toMatrix * (P.toMatrixᵀ * reflectionMatrix S₁.B (φ i) * P.toMatrix) * P.toMatrixᵀ
            = (P.toMatrix * P.toMatrixᵀ) * reflectionMatrix S₁.B (φ i) *
                (P.toMatrix * P.toMatrixᵀ) := by simp [Matrix.mul_assoc]
          _ = reflectionMatrix S₁.B (φ i) := by rw [hPPt, Matrix.one_mul, Matrix.mul_one]
      rw [hinv]
      exact Submonoid.subset_closure ⟨φ i, rfl⟩
    | one =>
      simp only [Matrix.mul_one, hPPt]
      exact (W_group S₁).one_mem
    | mul x y _ _ ihx ihy =>
      have hmul : P.toMatrix * (x * y) * P.toMatrixᵀ =
          (P.toMatrix * x * P.toMatrixᵀ) * (P.toMatrix * y * P.toMatrixᵀ) := by
        calc
          P.toMatrix * (x * y) * P.toMatrixᵀ
            = P.toMatrix * x * (1 * y) * P.toMatrixᵀ := by simp [Matrix.mul_assoc]
          _ = P.toMatrix * x * ((P.toMatrixᵀ * P.toMatrix) * y) * P.toMatrixᵀ := by rw [hPtP]
          _ = (P.toMatrix * x * P.toMatrixᵀ) * (P.toMatrix * y * P.toMatrixᵀ) := by
                simp [Matrix.mul_assoc]
      rw [hmul]
      exact (W_group S₁).mul_mem ihx ihy
  exact
    { toFun := fun M => ⟨P.toMatrixᵀ * M.1 * P.toMatrix, hmem_fwd M.1 M.2⟩
      invFun := fun N => ⟨P.toMatrix * N.1 * P.toMatrixᵀ, hmem_bwd N.1 N.2⟩
      left_inv := fun M => by
        ext1
        show P.toMatrix * (P.toMatrixᵀ * M.1 * P.toMatrix) * P.toMatrixᵀ = M.1
        calc
          P.toMatrix * (P.toMatrixᵀ * M.1 * P.toMatrix) * P.toMatrixᵀ
            = (P.toMatrix * P.toMatrixᵀ) * M.1 * (P.toMatrix * P.toMatrixᵀ) := by
                simp [Matrix.mul_assoc]
          _ = M.1 := by rw [hPPt, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun N => by
        ext1
        show P.toMatrixᵀ * (P.toMatrix * N.1 * P.toMatrixᵀ) * P.toMatrix = N.1
        calc
          P.toMatrixᵀ * (P.toMatrix * N.1 * P.toMatrixᵀ) * P.toMatrix
            = (P.toMatrixᵀ * P.toMatrix) * N.1 * (P.toMatrixᵀ * P.toMatrix) := by
                simp [Matrix.mul_assoc]
          _ = N.1 := by rw [hPtP, Matrix.one_mul, Matrix.mul_one]
      map_mul' := fun M₁ M₂ => by
        ext1
        show P.toMatrixᵀ * (M₁.1 * M₂.1) * P.toMatrix =
          (P.toMatrixᵀ * M₁.1 * P.toMatrix) * (P.toMatrixᵀ * M₂.1 * P.toMatrix)
        calc
          P.toMatrixᵀ * (M₁.1 * M₂.1) * P.toMatrix
            = P.toMatrixᵀ * M₁.1 * (1 * M₂.1) * P.toMatrix := by simp [Matrix.mul_assoc]
          _ = P.toMatrixᵀ * M₁.1 * ((P.toMatrix * P.toMatrixᵀ) * M₂.1) * P.toMatrix := by
                rw [hPPt]
          _ = (P.toMatrixᵀ * M₁.1 * P.toMatrix) * (P.toMatrixᵀ * M₂.1 * P.toMatrix) := by
                simp [Matrix.mul_assoc] }

end ReflectionSystem
