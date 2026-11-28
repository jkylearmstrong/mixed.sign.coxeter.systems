/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.ClassicalDeletion

/-!
# Relations of a nondegenerate subdiagram persist in every larger diagram (Theorem 1.2)

Formalization of the proof of Theorem 1.2 (Section 3.3) of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

The dissertation builds the family `Γ₃ := ~A_{-2}`, `Γ₄ := ~A_{-2} ∗_{r₃} {r₄}`,
`Γₙ := Γₙ₋₁ ∗_{rₙ₋₁} {rₙ}` (a tail of nodes hanging off `~A_{-2}`) and observes that
*any* graph containing `~A_{-2}` contains the bad word of Lemma 3.21. This file makes that
observation a theorem.

Let `f : Fin m → Fin n` pick out a set `T` of nodes, and let `B_T = B.submatrix f f` be the
form of the induced subdiagram. For a word `w` in the letters of `T`:

* `wordProd_map_eq_one_add`: `W(Γ) ∋ s_{f w₁} ⋯ s_{f w_k} = 1 + E C R` and
  `W(Γ_T) ∋ s_{w₁} ⋯ s_{w_k} = 1 + C B_T` for one and the same coefficient matrix `C`,
  where `E` is the embedding `ℝ^T → ℝⁿ` and `R` is the block of rows of `B` indexed by `T`.
* `wordProd_map_eq_of_sub` (needs `det B_T ≠ 0`): every relation of `W(Γ_T)` holds in `W(Γ)`.
* `wordProd_sub_eq_of_map` (no hypothesis): every relation among the `s_{f a}` in `W(Γ)`
  holds in `W(Γ_T)`; equivalently non-relations of `W(Γ_T)` persist.

Since `det B(~A_{-2}) = -4 ≠ 0`, we get:

* `not_deletion_of_contains_tildeAminus2` (**Theorem 1.2, general form**): every reflection
  system whose diagram contains `~A_{-2}` as an induced subdiagram (with arbitrary further
  nodes, signs and edges) fails the Deletion Property.
* `tildeAminus2Tail k` and `theorem_1_2_tail_family`: the dissertation's family `Γ_{3+k}`
  (`~A_{-2}` with a tail of `k` nodes attached to `r₃`) fails the Deletion Property for
  every `k`.
-/

open Matrix

namespace ReflectionSystem

variable {n m : ℕ}

/-- The embedding `ℝ^m → ℝⁿ`, `e_a ↦ e_{f a}`. -/
def embedMat (f : Fin m → Fin n) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun r a => if r = f a then 1 else 0

/-- The rank-one coefficient of the `a`-th reflection: `2 / B(e_{f a}, e_{f a})` at `(a, a)`. -/
noncomputable def reflCoeff (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin m → Fin n) (a : Fin m) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun x y => if x = a ∧ y = a then 2 / B (f a) (f a) else 0

lemma rows_mul_embedMat (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin m → Fin n) :
    B.submatrix f id * embedMat f = B.submatrix f f := by
  ext b a
  simp only [mul_apply, submatrix_apply, id_eq, embedMat, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

lemma embedMat_transpose_mul (f : Fin m → Fin n) (hf : Function.Injective f) :
    (embedMat f)ᵀ * embedMat f = 1 := by
  ext a b
  simp only [mul_apply, transpose_apply, embedMat, of_apply, one_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  by_cases hab : a = b
  · simp [hab]
  · have : f b ≠ f a := fun h => hab (hf h).symm
    simp [hab, this]

lemma reflectionMatrix_comp_eq (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin m → Fin n) (a : Fin m) :
    reflectionMatrix B (f a) = 1 - embedMat f * reflCoeff B f a * B.submatrix f id := by
  ext r c
  simp only [reflectionMatrix_apply, Matrix.sub_apply, one_apply, mul_apply, embedMat, reflCoeff,
    of_apply, submatrix_apply, id_eq]
  congr 1
  have hinner : ∀ y : Fin m,
      (∑ x : Fin m, (if r = f x then (1 : ℝ) else 0) *
          (if x = a ∧ y = a then 2 / B (f a) (f a) else 0)) =
        if y = a then (if r = f a then 2 / B (f a) (f a) else 0) else 0 := by
    intro y
    rw [Finset.sum_eq_single a]
    · by_cases hy : y = a <;> by_cases hr : r = f a <;> simp [hy, hr]
    · intro x _ hx; simp [hx]
    · simp
  simp_rw [hinner]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hr : r = f a
  · simp [hr]; ring
  · simp [hr]

lemma reflectionMatrix_sub_eq (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin m → Fin n) (a : Fin m) :
    reflectionMatrix (B.submatrix f f) a = 1 - reflCoeff B f a * B.submatrix f f := by
  ext x c
  simp only [reflectionMatrix_apply, Matrix.sub_apply, one_apply, mul_apply, reflCoeff, of_apply,
    submatrix_apply]
  congr 1
  have hterm : ∀ y : Fin m,
      (if x = a ∧ y = a then 2 / B (f a) (f a) else 0) * B (f y) (f c) =
        if y = a then (if x = a then 2 / B (f a) (f a) * B (f a) (f c) else 0) else 0 := by
    intro y
    by_cases hy : y = a <;> by_cases hx : x = a <;> simp [hy, hx]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hx : x = a
  · simp [hx]; ring
  · simp [hx]

/-- **Structure of parabolic words**: a word in the letters `f a` has the form `1 + E C R`
in `W(Γ)`, and the same word read in `W(Γ_T)` is `1 + C B_T`, with the same `C`. -/
theorem wordProd_map_eq_one_add (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin m → Fin n)
    (w : List (Fin m)) :
    ∃ C : Matrix (Fin m) (Fin m) ℝ,
      ((w.map f).map (reflectionMatrix B)).prod = 1 + embedMat f * C * B.submatrix f id ∧
      (w.map (reflectionMatrix (B.submatrix f f))).prod = 1 + C * B.submatrix f f := by
  induction w with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons a t ih =>
    obtain ⟨C, h₁, h₂⟩ := ih
    set E := embedMat f
    set R := B.submatrix f id
    set D := reflCoeff B f a
    refine ⟨C - D - D * B.submatrix f f * C, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, h₁, reflectionMatrix_comp_eq B f a]
      rw [← rows_mul_embedMat B f]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    · simp only [List.map_cons, List.prod_cons, h₂, reflectionMatrix_sub_eq B f a]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel

/-- If the induced subdiagram on `T` is nondegenerate (`det B_T ≠ 0`), every relation of
`W(Γ_T)` holds among the corresponding generators of `W(Γ)`. -/
theorem wordProd_map_eq_of_sub (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin m → Fin n)
    (hdet : (B.submatrix f f).det ≠ 0) (w w' : List (Fin m))
    (h : (w.map (reflectionMatrix (B.submatrix f f))).prod =
      (w'.map (reflectionMatrix (B.submatrix f f))).prod) :
    ((w.map f).map (reflectionMatrix B)).prod = ((w'.map f).map (reflectionMatrix B)).prod := by
  obtain ⟨C, h₁, h₂⟩ := wordProd_map_eq_one_add B f w
  obtain ⟨C', h₁', h₂'⟩ := wordProd_map_eq_one_add B f w'
  rw [h₂, h₂'] at h
  have hCB : C * B.submatrix f f = C' * B.submatrix f f := add_left_cancel h
  have hunit : IsUnit (B.submatrix f f).det := isUnit_iff_ne_zero.mpr hdet
  have hCC : C = C' := by
    have := congr_arg (· * (B.submatrix f f)⁻¹) hCB
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit] using this
  rw [h₁, h₁', hCC]

/-- Conversely (with no hypothesis on `B_T`), a relation among the generators `s_{f a}` of
`W(Γ)` already holds in `W(Γ_T)`. -/
theorem wordProd_sub_eq_of_map (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin m → Fin n)
    (hf : Function.Injective f) (w w' : List (Fin m))
    (h : ((w.map f).map (reflectionMatrix B)).prod = ((w'.map f).map (reflectionMatrix B)).prod) :
    (w.map (reflectionMatrix (B.submatrix f f))).prod =
      (w'.map (reflectionMatrix (B.submatrix f f))).prod := by
  obtain ⟨C, h₁, h₂⟩ := wordProd_map_eq_one_add B f w
  obtain ⟨C', h₁', h₂'⟩ := wordProd_map_eq_one_add B f w'
  rw [h₁, h₁'] at h
  have hECR : embedMat f * C * B.submatrix f id = embedMat f * C' * B.submatrix f id :=
    add_left_cancel h
  have hE := embedMat_transpose_mul f hf
  have hCR : C * B.submatrix f id = C' * B.submatrix f id := by
    have := congr_arg ((embedMat f)ᵀ * ·) hECR
    simpa [← Matrix.mul_assoc, hE] using this
  have hCB : C * B.submatrix f f = C' * B.submatrix f f := by
    rw [← rows_mul_embedMat B f, ← Matrix.mul_assoc, hCR, Matrix.mul_assoc]
  rw [h₂, h₂', hCB]

end ReflectionSystem

namespace MixedSignCoxeter

open ReflectionSystem

private lemma deleteTwo_map' {α β : Type*} (g : α → β) (w : List α) (i j : ℕ) :
    deleteTwo (w.map g) i j = (deleteTwo w i j).map g := by
  simp [deleteTwo, List.zipIdx_map, List.filter_map, Function.comp_def]

/-- `det B(~A_{-2}) = -4`: the `~A_{-2}` form is nondegenerate. -/
theorem det_tildeAminus2 : (tildeAminus2Graph.toBilinearForm).det = -4 := by
  rw [Matrix.det_fin_three]
  simp [tildeAminus2Graph, MixedSignCoxeterGraph.toBilinearForm, Sign.toReal, edgeEntry,
    Real.cos_pi_div_three]
  norm_num

/-- **Theorem 1.2 (general form)**: Let `S` be any reflection system and `f : Fin 3 → Fin n`
an injective choice of three nodes spanning an induced copy of `~A_{-2}`
(`B(e_{f a}, e_{f b}) = B(~A_{-2})_{a b}`). Then the word `s_{f 0} s_{f 1} s_{f 0} s_{f 2} s_{f 0}`
equals the shorter word `s_{f 2} s_{f 0} s_{f 1}`, no deletion of two letters gives back the
same element, and hence `S` fails the Deletion Property. No assumption is made on the other
nodes, their signs, or the edges among them. -/
theorem not_deletion_of_contains_tildeAminus2 (S : ReflectionSystem n) (f : Fin 3 → Fin n)
    (hf : Function.Injective f)
    (hsub : S.B.submatrix f f = tildeAminus2Graph.toBilinearForm) :
    let w : List (Fin n) := [0, 1, 0, 2, 0].map f
    S.wordProd w = S.wordProd ([2, 0, 1].map f) ∧
    (∀ i j : Fin 5, i < j → S.wordProd (deleteTwo w i.val j.val) ≠ S.wordProd w) ∧
    ¬ SatisfiesDeletionProperty S := by
  intro w
  obtain ⟨hbase_eq, hbase_no⟩ := tildeAminus2_fails_deletion
  have hdet : (S.B.submatrix f f).det ≠ 0 := by rw [hsub, det_tildeAminus2]; norm_num
  have heq : S.wordProd w = S.wordProd ([2, 0, 1].map f) := by
    have := wordProd_map_eq_of_sub S.B f hdet [0, 1, 0, 2, 0] [2, 0, 1] (by
      rw [hsub]; exact hbase_eq)
    simpa [wordProd, w] using this
  have hno : ∀ i j : Fin 5, i < j → S.wordProd (deleteTwo w i.val j.val) ≠ S.wordProd w := by
    intro i j hij hEq
    apply hbase_no i j hij
    have hdel : deleteTwo w i.val j.val = (deleteTwo [0, 1, 0, 2, 0] i.val j.val).map f :=
      deleteTwo_map' f _ _ _
    rw [hdel] at hEq
    have := wordProd_sub_eq_of_map S.B f hf _ _ hEq
    rw [hsub] at this
    simpa [wordProd, MixedSignCoxeterGraph.toReflectionSystem] using this
  refine ⟨heq, hno, ?_⟩
  intro hdel
  have hu : ([2, 0, 1].map f).length < w.length := by simp [w]
  obtain ⟨i, j, hij, hj, hdel_eq⟩ := hdel w ⟨_, hu, heq⟩
  have hlen : w.length = 5 := by simp [w]
  rw [hlen] at hj
  exact hno ⟨i, lt_trans hij hj⟩ ⟨j, hj⟩ hij hdel_eq

/-- The dissertation's family for Theorem 1.2 (Section 3.3): `Γ₃ := ~A_{-2}` on nodes
`0, 1, 2`, and `Γ_{3+k}` obtained by attaching a tail `2 — 3 — 4 — ⋯ — (2+k)` of positive
nodes with edge weight `3` (`Γ₄ := ~A_{-2} ∗_{r₃} {r₄}`, `Γₙ := Γₙ₋₁ ∗_{rₙ₋₁} {rₙ}`). -/
def tildeAminus2Tail (k : ℕ) : MixedSignCoxeterGraph (3 + k) where
  sign i := if i.val < 3 then Sign.neg else Sign.pos
  weight i j :=
    if i.val < 3 ∧ j.val < 3 then some 3
    else if 2 ≤ i.val ∧ 2 ≤ j.val ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) then some 3
    else some 2
  weight_symm i j := by
    by_cases h1 : i.val < 3 ∧ j.val < 3
    · have h1' : j.val < 3 ∧ i.val < 3 := ⟨h1.2, h1.1⟩
      simp [h1, h1']
    · have h1' : ¬(j.val < 3 ∧ i.val < 3) := fun h => h1 ⟨h.2, h.1⟩
      simp only [h1, h1', ↓reduceIte]
      by_cases h2 : 2 ≤ i.val ∧ 2 ≤ j.val ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
      · have h2' : 2 ≤ j.val ∧ 2 ≤ i.val ∧ (j.val + 1 = i.val ∨ i.val + 1 = j.val) :=
          ⟨h2.2.1, h2.1, h2.2.2.symm⟩
        simp [h2, h2']
      · have h2' : ¬(2 ≤ j.val ∧ 2 ≤ i.val ∧ (j.val + 1 = i.val ∨ i.val + 1 = j.val)) :=
          fun h => h2 ⟨h.2.1, h.1, h.2.2.symm⟩
        simp [h2, h2']
  weight_ge_two i j m h := by
    split_ifs at h <;> cases h <;> omega

/-- **Theorem 1.2 (the dissertation's tail family)**: for every `k : ℕ`, the mixed-sign Coxeter
system `Γ_{3+k}` (`~A_{-2}` with a tail of `k` nodes) fails the Deletion Property. -/
theorem theorem_1_2_tail_family (k : ℕ) :
    let S := (tildeAminus2Tail k).toReflectionSystem
    let w : List (Fin (3 + k)) := [0, 1, 0, 2, 0].map (Fin.castAdd k)
    S.wordProd w = S.wordProd ([2, 0, 1].map (Fin.castAdd k)) ∧
    (∀ i j : Fin 5, i < j → S.wordProd (deleteTwo w i.val j.val) ≠ S.wordProd w) ∧
    ¬ SatisfiesDeletionProperty S := by
  apply not_deletion_of_contains_tildeAminus2 _ (Fin.castAdd k) (Fin.castAdd_injective 3 k)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [tildeAminus2Tail, tildeAminus2Graph, MixedSignCoxeterGraph.toBilinearForm,
      MixedSignCoxeterGraph.toReflectionSystem]

/-- The earlier family `tildeAminus2Extended k` (`~A_{-2}` plus `k` isolated nodes) is also an
instance of the general theorem. -/
theorem theorem_1_2_extended_family (k : ℕ) :
    ¬ SatisfiesDeletionProperty (tildeAminus2Extended k).toReflectionSystem := by
  refine (not_deletion_of_contains_tildeAminus2 _ (Fin.castAdd k)
    (Fin.castAdd_injective 3 k) ?_).2.2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [tildeAminus2Extended, tildeAminus2Graph, MixedSignCoxeterGraph.toBilinearForm,
      MixedSignCoxeterGraph.toReflectionSystem]

end MixedSignCoxeter

namespace ReflectionSystem

variable {n : ℕ}

/-! ### Definition 2.56: Node Deletion `Γ / (r_i)` -/

section NodeDeletion

/-- **Definition 2.56**: The reflection system `Γ / (r_i)` obtained by deleting node `i`
and all incident edges from `S : ReflectionSystem (n + 1)`. -/
def deleteNode (S : ReflectionSystem (n + 1)) (i : Fin (n + 1)) : ReflectionSystem n where
  B := S.B.submatrix i.succAbove i.succAbove
  B_symm := by
    ext j k
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    exact congr_fun (congr_fun S.B_symm (i.succAbove j)) (i.succAbove k)
  B_diag_ne_zero j := S.B_diag_ne_zero (i.succAbove j)

@[simp]
lemma deleteNode_B (S : ReflectionSystem (n + 1)) (i : Fin (n + 1)) (j k : Fin n) :
    (S.deleteNode i).B j k = S.B (i.succAbove j) (i.succAbove k) := rfl

/-- Any relation among the remaining generators in `Γ` already holds in `Γ / (r_i)`. -/
theorem deleteNode_wordProd_sub_of_map (S : ReflectionSystem (n + 1)) (i : Fin (n + 1))
    (w₁ w₂ : List (Fin n))
    (h : wordProd S (w₁.map i.succAbove) = wordProd S (w₂.map i.succAbove)) :
    wordProd (S.deleteNode i) w₁ = wordProd (S.deleteNode i) w₂ :=
  wordProd_sub_eq_of_map S.B i.succAbove Fin.succAbove_right_injective w₁ w₂ h

/-- When `B(Γ / (r_i))` is nonsingular, relations in `Γ` on the remaining generators coincide
with relations in `Γ / (r_i)`. -/
theorem deleteNode_wordProd_eq_iff (S : ReflectionSystem (n + 1)) (i : Fin (n + 1))
    (hdet : (S.deleteNode i).B.det ≠ 0) (w₁ w₂ : List (Fin n)) :
    wordProd S (w₁.map i.succAbove) = wordProd S (w₂.map i.succAbove) ↔
      wordProd (S.deleteNode i) w₁ = wordProd (S.deleteNode i) w₂ :=
  ⟨deleteNode_wordProd_sub_of_map S i w₁ w₂,
   wordProd_map_eq_of_sub S.B i.succAbove hdet w₁ w₂⟩

end NodeDeletion

end ReflectionSystem
