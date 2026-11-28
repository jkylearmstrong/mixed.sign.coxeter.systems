/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Basic
import MixedSignCoxeter.SpectralRadius

/-!
# Spectral classification and interlacing for bipartite Coxeter elements
(Theorems 3.27 and 3.28)

Formalization of Theorems 3.27 and 3.28 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012),
which the dissertation quotes from [A'C76], [MS05], [McM02].

## Setting

Order the nodes of a bipartite classical Coxeter graph as `N₁ = Fin p` followed by
`N₂ = Fin q`. With the normalisation `B(e_i, e_i) = 2` of Chapter 3 the bilinear form is
`B = [[2, -A], [-Aᵀ, 2]]` (`bipForm A`), where `A : Matrix (Fin p) (Fin q) ℝ` holds the edge
entries `2 cos(π / m_{ij})` (the results below hold for every real `A`). The product of the
pairwise-commuting reflections in `N₁` is `s₊ = [[-1, A], [0, 1]]`, the product of those in
`N₂` is `s₋ = [[1, 0], [Aᵀ, -1]]`, and the bipartite Coxeter element is `w = s₊ s₋`
(`bipCoxeter A`). By Theorem 2.58 (`TreeConjugacy.lean`) every Coxeter element of a tree is
conjugate to `w`, so for trees the results apply to every Coxeter element.

## Main results
* `eigen_analysis`: every complex eigenvalue `λ ≠ -1` of `w` satisfies
  `λ² - (ν - 2) λ + 1 = 0` for some real eigenvalue `ν ≥ 0` of `A Aᵀ`.
* `theorem_3_27_classification` (**Theorem 3.27**):
  - `B` is positive definite (spherical) iff every eigenvalue of `w` has modulus `1` and `1`
    is not an eigenvalue;
  - `B` is positive semidefinite and degenerate (affine) iff every eigenvalue of `w` has
    modulus `1` and `1` is an eigenvalue;
  - `B` is indefinite (hyperbolic) iff `w` has a real eigenvalue `λ > 1`.
* `theorem_3_28_interlacing` (**Theorem 3.28**): if `Γ' ⊂ Γ` is an induced subgraph
  (`A' = A.submatrix f g` for injective `f`, `g`; deleting a single node `rᵢ` gives
  `Γ' = Γ/(rᵢ)`), then for every eigenvalue `λ'` of `w(Γ')` there is an eigenvalue `λ` of
  `w(Γ)` with `‖λ'‖ ≤ ‖λ‖`, i.e. `ρ(w(Γ')) ≤ ρ(w(Γ))`.
* `theorem_3_28_strict`: the inequality is strict, `‖λ'‖ < ‖λ‖`, when `Γ` is hyperbolic and
  `Γ'` is not. (The dissertation writes `λ(w₁) > λ(w₂)` with no hypothesis; strictness fails for
  spherical graphs, e.g. `A₂ ⊂ A₃`, whose Coxeter elements both have spectral radius `1`.)
-/

open Matrix

namespace MixedSignCoxeter

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form `v ↦ vᵀ B v`. -/
def qf (B : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (B *ᵥ v)

/-- Spherical (positive definite), Definition 2.47. -/
def FormSpherical (B : Matrix ι ι ℝ) : Prop := ∀ v : ι → ℝ, v ≠ 0 → 0 < qf B v

/-- Affine (positive semidefinite and degenerate), Definition 2.48. -/
def FormAffine (B : Matrix ι ι ℝ) : Prop :=
  (∀ v : ι → ℝ, 0 ≤ qf B v) ∧ ∃ v : ι → ℝ, v ≠ 0 ∧ qf B v = 0

/-- Hyperbolic or higher rank (indefinite), Definitions 2.50–2.51. -/
def FormIndefinite (B : Matrix ι ι ℝ) : Prop :=
  (∃ u : ι → ℝ, 0 < qf B u) ∧ ∃ v : ι → ℝ, qf B v < 0

/-- `M` has the complex eigenvalue `λ`, acting on `ℂ^ι`. -/
def HasEigenC (M : Matrix ι ι ℝ) (lam : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧ (M.map (↑) : Matrix ι ι ℂ) *ᵥ v = lam • v

lemma dot_self_nonneg (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma dot_self_pos {v : ι → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))

lemma mulVec_map_ofReal (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    (M.map (↑) : Matrix ι ι ℂ) *ᵥ (fun i => (v i : ℂ)) = fun i => ((M *ᵥ v) i : ℂ) := by
  funext i
  simp [mulVec, dotProduct]

lemma mulVec_map_ofReal' {κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (v : κ → ℝ) :
    (M.map (↑) : Matrix ι κ ℂ) *ᵥ (fun i => (v i : ℂ)) = fun i => ((M *ᵥ v) i : ℂ) := by
  funext i
  simp [mulVec, dotProduct]

lemma hasEigenC_of_real {M : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ} (hv : v ≠ 0)
    (h : M *ᵥ v = lam • v) : HasEigenC M lam := by
  refine ⟨fun i => (v i : ℂ), fun h0 => hv (funext fun i => by
    simpa using congr_fun h0 i), ?_⟩
  rw [mulVec_map_ofReal, h]
  funext i
  simp

lemma re_mulVec_map (M : Matrix ι ι ℝ) (x : ι → ℂ) (i : ι) :
    (((M.map (↑) : Matrix ι ι ℂ) *ᵥ x) i).re = (M *ᵥ fun j => (x j).re) i := by
  simp [mulVec, dotProduct, Complex.re_sum]

lemma im_mulVec_map (M : Matrix ι ι ℝ) (x : ι → ℂ) (i : ι) :
    (((M.map (↑) : Matrix ι ι ℂ) *ᵥ x) i).im = (M *ᵥ fun j => (x j).im) i := by
  simp [mulVec, dotProduct, Complex.im_sum]

/-- Real form of a complex eigen-equation `M x = ν x`. -/
lemma real_parts_of_eigen (M : Matrix ι ι ℝ) (x : ι → ℂ) (ν : ℂ)
    (h : (M.map (↑) : Matrix ι ι ℂ) *ᵥ x = ν • x) :
    M *ᵥ (fun j => (x j).re) = ν.re • (fun j => (x j).re) - ν.im • (fun j => (x j).im) ∧
    M *ᵥ (fun j => (x j).im) = ν.im • (fun j => (x j).re) + ν.re • (fun j => (x j).im) := by
  constructor
  · funext i
    rw [← re_mulVec_map, h]
    simp
  · funext i
    rw [← im_mulVec_map, h]
    simp [add_comm]

/-- A real symmetric matrix with a complex eigenvector has a real eigenvalue there: the
eigenvalue is real and the real or imaginary part is a real eigenvector. -/
lemma real_eigen_of_complex (M : Matrix ι ι ℝ) (hM : Mᵀ = M) (x : ι → ℂ) (hx : x ≠ 0)
    (ν : ℂ) (h : (M.map (↑) : Matrix ι ι ℂ) *ᵥ x = ν • x) :
    ν.im = 0 ∧ ∃ a : ι → ℝ, a ≠ 0 ∧ M *ᵥ a = ν.re • a := by
  obtain ⟨h1, h2⟩ := real_parts_of_eigen M x ν h
  set a : ι → ℝ := fun j => (x j).re
  set b : ι → ℝ := fun j => (x j).im
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hx
    funext j
    apply Complex.ext
    · simpa [a] using congr_fun hc.1 j
    · simpa [b] using congr_fun hc.2 j
  have hsym : a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (M *ᵥ a) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  rw [h1, h2] at hsym
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hsym
  have hpos : 0 < a ⬝ᵥ a + b ⬝ᵥ b := by
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (dot_self_pos ha) (dot_self_nonneg b)
    · exact add_pos_of_nonneg_of_pos (dot_self_nonneg a) (dot_self_pos hb)
  have hcomm : a ⬝ᵥ b = b ⬝ᵥ a := dotProduct_comm a b
  rw [hcomm] at hsym
  have him : ν.im * (a ⬝ᵥ a + b ⬝ᵥ b) = 0 := by linarith
  have him0 : ν.im = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · linarith
  refine ⟨him0, ?_⟩
  rw [him0, zero_smul, sub_zero] at h1
  rw [him0, zero_smul, zero_add] at h2
  rcases hab with ha | hb
  · exact ⟨a, ha, h1⟩
  · exact ⟨b, hb, h2⟩

/-- If `‖λ‖` solves `λ² - b λ + 1 = 0` with `b` real and `b² ≤ 4`, then `‖λ‖ = 1`. -/
lemma norm_eq_one_of_quadratic (lam : ℂ) (b : ℝ) (hb : b ^ 2 ≤ 4)
    (h : lam ^ 2 - b * lam + 1 = 0) : ‖lam‖ = 1 := by
  have hre := congr_arg Complex.re h
  have him := congr_arg Complex.im h
  simp [pow_two] at hre him
  have hsq : lam.re ^ 2 + lam.im ^ 2 = 1 := by
    by_cases hc : lam.im = 0
    · rw [hc] at hre
      have : (2 * lam.re - b) ^ 2 = b ^ 2 - 4 := by nlinarith
      have h1 : (2 * lam.re - b) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * lam.re - b)]
      have h2 : 2 * lam.re = b := by nlinarith [sq_nonneg (2 * lam.re - b)]
      rw [hc]; nlinarith
    · have h2 : 2 * lam.re = b := by
        have : lam.im * (2 * lam.re - b) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hc
        · linarith
      linear_combination -hre + lam.re * h2
  have hn : ‖lam‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith
  have hn0 : 0 ≤ ‖lam‖ := norm_nonneg _
  nlinarith

/-- For a Hermitian (real symmetric) `N`, if `N` is not positive definite then `N` has a
real eigenvector with eigenvalue `≤ 0`. -/
lemma exists_eigen_nonpos_of_not_posDef (N : Matrix ι ι ℝ) (hN : N.IsHermitian)
    (h : ¬ N.PosDef) : ∃ θ : ℝ, θ ≤ 0 ∧ ∃ u : ι → ℝ, u ≠ 0 ∧ N *ᵥ u = θ • u := by
  rw [hN.posDef_iff_eigenvalues_pos] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine ⟨hN.eigenvalues i, hi, ⇑(hN.eigenvectorBasis i), ?_, hN.mulVec_eigenvectorBasis i⟩
  intro h0
  have hne := (hN.eigenvectorBasis).orthonormal.ne_zero i
  apply hne
  ext j
  simpa using congr_fun h0 j

/-- For a Hermitian `N`, if `N` is not positive semidefinite then `N` has a real eigenvector
with eigenvalue `< 0`. -/
lemma exists_eigen_neg_of_not_posSemidef (N : Matrix ι ι ℝ) (hN : N.IsHermitian)
    (h : ¬ N.PosSemidef) : ∃ θ : ℝ, θ < 0 ∧ ∃ u : ι → ℝ, u ≠ 0 ∧ N *ᵥ u = θ • u := by
  rw [hN.posSemidef_iff_eigenvalues_nonneg] at h
  simp only [Pi.le_def, Pi.zero_apply, not_forall, not_le] at h
  obtain ⟨i, hi⟩ := h
  refine ⟨hN.eigenvalues i, hi, ⇑(hN.eigenvectorBasis i), ?_, hN.mulVec_eigenvectorBasis i⟩
  intro h0
  have hne := (hN.eigenvectorBasis).orthonormal.ne_zero i
  apply hne
  ext j
  simpa using congr_fun h0 j

lemma isHermitian_of_transpose_eq {N : Matrix ι ι ℝ} (h : Nᵀ = N) : N.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, h]

end General

/-! ### The bipartite Coxeter element -/

variable {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)

/-- `B = [[2, -A], [-Aᵀ, 2]]`: the bilinear form of a bipartite graph, nodes of `N₁` first. -/
def bipForm : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  fromBlocks (2 • (1 : Matrix (Fin p) (Fin p) ℝ)) (-A) (-Aᵀ) (2 • (1 : Matrix (Fin q) (Fin q) ℝ))

/-- `s₊`, the product of the reflections of the nodes in `N₁`. -/
def sPlusBip : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ := fromBlocks (-1) A 0 1

/-- `s₋`, the product of the reflections of the nodes in `N₂`. -/
def sMinusBip : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ := fromBlocks 1 0 Aᵀ (-1)

/-- The bipartite Coxeter element `w = s₊ s₋`. -/
def bipCoxeter : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ := sPlusBip A * sMinusBip A

lemma bipCoxeter_eq : bipCoxeter A = fromBlocks (A * Aᵀ - 1) (-A) Aᵀ (-1) := by
  simp only [bipCoxeter, sPlusBip, sMinusBip, fromBlocks_multiply]
  congr 1 <;> simp [sub_eq_add_neg, add_comm]

lemma AAt_transpose : (A * Aᵀ)ᵀ = A * Aᵀ := by
  rw [transpose_mul, transpose_transpose]

lemma dot_AAt (a : Fin p → ℝ) : a ⬝ᵥ ((A * Aᵀ) *ᵥ a) = (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

lemma qf_bipForm (x : Fin p → ℝ) (y : Fin q → ℝ) :
    qf (bipForm A) (Sum.elim x y) =
      2 * (x ⬝ᵥ x) - 2 * ((Aᵀ *ᵥ x) ⬝ᵥ y) + 2 * (y ⬝ᵥ y) := by
  simp only [qf, bipForm, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, smul_mulVec, one_mulVec, neg_mulVec, dotProduct_add,
    dotProduct_neg, dotProduct_smul, smul_eq_mul]
  have h1 : x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y := by
    rw [dotProduct_mulVec, mulVec_transpose]
  have h2 : y ⬝ᵥ (Aᵀ *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ y := dotProduct_comm _ _
  rw [h1, h2]
  ring

lemma qf_bipForm' (v : Fin p ⊕ Fin q → ℝ) :
    qf (bipForm A) v = 2 * ((v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl)) -
      2 * ((Aᵀ *ᵥ (v ∘ Sum.inl)) ⬝ᵥ (v ∘ Sum.inr)) + 2 * ((v ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)) := by
  conv_lhs => rw [← Sum.elim_comp_inl_inr v]
  exact qf_bipForm A _ _

lemma bipForm_transpose : (bipForm A)ᵀ = bipForm A := by
  simp [bipForm, fromBlocks_transpose]

/-- If `‖Aᵀ a‖² ≤ 4 ‖a‖²` for every `a`, then `B` is positive semidefinite. -/
lemma qf_nonneg_of_bound (hb : ∀ a : Fin p → ℝ, (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) ≤ 4 * (a ⬝ᵥ a))
    (v : Fin p ⊕ Fin q → ℝ) : 0 ≤ qf (bipForm A) v := by
  rw [qf_bipForm']
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have h0 := dot_self_nonneg (Aᵀ *ᵥ x - (2 : ℝ) • y)
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at h0
  have hc : y ⬝ᵥ (Aᵀ *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ y := dotProduct_comm _ _
  have := hb x
  nlinarith

/-- The test vector of an eigenvector `a` of `A Aᵀ` with eigenvalue `ν = t²`, `t > 0`:
`qf B (a, Aᵀ a / t) = 2 ‖a‖² (2 - t)`. -/
lemma qf_test_vector (a : Fin p → ℝ) (t : ℝ) (ht : 0 < t)
    (ha : (A * Aᵀ) *ᵥ a = (t ^ 2) • a) :
    qf (bipForm A) (Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a))) = 2 * (a ⬝ᵥ a) * (2 - t) := by
  rw [qf_bipForm]
  have hAA : (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) = t ^ 2 * (a ⬝ᵥ a) := by
    rw [← dot_AAt, ha, dotProduct_smul, smul_eq_mul]
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hAA]
  field_simp
  ring

/-- The eigenvalues of `A Aᵀ` are nonnegative. -/
lemma eigen_AAt_nonneg {a : Fin p → ℝ} (ha0 : a ≠ 0) {ν : ℝ}
    (ha : (A * Aᵀ) *ᵥ a = ν • a) : 0 ≤ ν := by
  have h := dot_AAt A a
  rw [ha, dotProduct_smul, smul_eq_mul] at h
  have h1 := dot_self_pos ha0
  have h2 := dot_self_nonneg (Aᵀ *ᵥ a)
  by_contra hν
  push Not at hν
  nlinarith

/-- Spherical forms force `ν < 4`, positive semidefinite forms force `ν ≤ 4`, for every
eigenvalue `ν` of `A Aᵀ`. -/
lemma eigen_AAt_le_four (hpsd : ∀ v, 0 ≤ qf (bipForm A) v) {a : Fin p → ℝ} (ha0 : a ≠ 0)
    {ν : ℝ} (ha : (A * Aᵀ) *ᵥ a = ν • a) : ν ≤ 4 := by
  have hν0 := eigen_AAt_nonneg A ha0 ha
  rcases eq_or_lt_of_le hν0 with h | hpos
  · rw [← h]; norm_num
  set t := Real.sqrt ν
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have ht2 : t ^ 2 = ν := Real.sq_sqrt hν0
  have hq := qf_test_vector A a t ht (by rw [ht2]; exact ha)
  have := hpsd (Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)))
  rw [hq] at this
  have h1 := dot_self_pos ha0
  have ht' : t ≤ 2 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

lemma eigen_AAt_lt_four (hsph : FormSpherical (bipForm A)) {a : Fin p → ℝ} (ha0 : a ≠ 0)
    {ν : ℝ} (ha : (A * Aᵀ) *ᵥ a = ν • a) : ν < 4 := by
  have hν0 := eigen_AAt_nonneg A ha0 ha
  rcases eq_or_lt_of_le hν0 with h | hpos
  · rw [← h]; norm_num
  set t := Real.sqrt ν
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have ht2 : t ^ 2 = ν := Real.sq_sqrt hν0
  have hq := qf_test_vector A a t ht (by rw [ht2]; exact ha)
  have hne : Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)) ≠ 0 := by
    intro h0; apply ha0; funext i; simpa using congr_fun h0 (Sum.inl i)
  have := hsph _ hne
  rw [hq] at this
  have h1 := dot_self_pos ha0
  have ht' : t < 2 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

/-- The complexification of `w`. -/
lemma bipCoxeter_map :
    ((bipCoxeter A).map (↑) : Matrix _ _ ℂ) =
      fromBlocks ((A.map (↑)) * (A.map (↑))ᵀ - 1) (-(A.map (↑))) (A.map (↑))ᵀ (-1) := by
  rw [bipCoxeter_eq]
  ext (i | i) (j | j) <;>
    simp [fromBlocks, Matrix.mul_apply, Matrix.one_apply] <;>
    split_ifs <;> simp

/-- **Eigenvalue analysis.** Every complex eigenvalue `λ ≠ -1` of `w = s₊ s₋` satisfies
`λ² - (ν - 2) λ + 1 = 0` for a real eigenvalue `ν ≥ 0` of `A Aᵀ`. -/
theorem eigen_analysis {lam : ℂ} (h : HasEigenC (bipCoxeter A) lam) (hlam : lam ≠ -1) :
    ∃ ν : ℝ, 0 ≤ ν ∧ (∃ a : Fin p → ℝ, a ≠ 0 ∧ (A * Aᵀ) *ᵥ a = ν • a) ∧
      lam ^ 2 - ((ν : ℂ) - 2) * lam + 1 = 0 := by
  obtain ⟨v, hv0, hv⟩ := h
  rw [bipCoxeter_map, fromBlocks_mulVec] at hv
  set Ac : Matrix (Fin p) (Fin q) ℂ := A.map (↑)
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have E1 : (Ac * Acᵀ - 1) *ᵥ x + (-Ac) *ᵥ y = lam • x := by
    funext i; simpa [x, y] using congr_fun hv (Sum.inl i)
  have E2 : Acᵀ *ᵥ x + (-1 : Matrix (Fin q) (Fin q) ℂ) *ᵥ y = lam • y := by
    funext i; simpa [x, y] using congr_fun hv (Sum.inr i)
  have hl1 : lam + 1 ≠ 0 := fun h => hlam (by linear_combination h)
  have E2' : Acᵀ *ᵥ x = (lam + 1) • y := by
    rw [neg_mulVec, one_mulVec] at E2
    rw [add_smul, one_smul, ← E2]; abel
  have hx0 : x ≠ 0 := by
    intro hx
    apply hv0
    have hy : y = 0 := by
      rw [hx, mulVec_zero] at E2'
      funext j
      have := congr_fun E2' j
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hl1
    funext k
    cases k with
    | inl i => exact congr_fun hx i
    | inr j => exact congr_fun hy j
  -- `λ (A Aᵀ) x = (λ + 1)² x`
  have E3 : lam • ((Ac * Acᵀ) *ᵥ x) = ((lam + 1) ^ 2) • x := by
    have := congr_arg ((lam + 1) • ·) E1
    simp only [sub_mulVec, one_mulVec, neg_mulVec, smul_add, smul_sub, smul_neg] at this
    have hAc : (lam + 1) • (Ac *ᵥ y) = Ac *ᵥ (Acᵀ *ᵥ x) := by
      rw [← mulVec_smul, ← E2']
    rw [hAc, mulVec_mulVec] at this
    funext i
    have hi := congr_fun this i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  have hl0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at E3
    apply hx0
    funext i
    have := congr_fun E3 i
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, h0, zero_add, one_pow,
      one_mul] at this
    exact this.symm
  set ν : ℂ := (lam + 1) ^ 2 / lam
  have E4 : (Ac * Acᵀ) *ᵥ x = ν • x := by
    funext i
    have := congr_fun E3 i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    simp only [ν]
    field_simp
    linear_combination this
  have hmap : ((A * Aᵀ).map (↑) : Matrix (Fin p) (Fin p) ℂ) = Ac * Acᵀ := by
    ext i j; simp [Ac, Matrix.mul_apply]
  rw [← hmap] at E4
  obtain ⟨him, a, ha0, ha⟩ := real_eigen_of_complex (A * Aᵀ) (AAt_transpose A) x hx0 ν E4
  refine ⟨ν.re, eigen_AAt_nonneg A ha0 ha, ⟨a, ha0, ha⟩, ?_⟩
  have hνc : (ν.re : ℂ) = ν := Complex.ext (by simp) (by simp [him])
  rw [hνc]
  simp only [ν]
  field_simp
  ring

/-! ### Theorem 3.27 -/

lemma exhaustive : FormSpherical (bipForm A) ∨ FormAffine (bipForm A) ∨
    FormIndefinite (bipForm A) := by
  by_cases hpsd : ∀ v, 0 ≤ qf (bipForm A) v
  · by_cases hsph : FormSpherical (bipForm A)
    · exact Or.inl hsph
    · right; left
      refine ⟨hpsd, ?_⟩
      simp only [FormSpherical, not_forall, not_lt] at hsph
      obtain ⟨v, hv, hle⟩ := hsph
      exact ⟨v, hv, le_antisymm hle (hpsd v)⟩
  · right; right
    push Not at hpsd
    obtain ⟨v, hv⟩ := hpsd
    refine ⟨?_, v, hv⟩
    have hne : v ≠ 0 := by
      intro h0; rw [h0] at hv; simp [qf] at hv
    obtain ⟨k, _⟩ := Function.ne_iff.mp hne
    refine ⟨Pi.single k 1, ?_⟩
    have h2p : ∀ i : Fin p, (2 : Matrix (Fin p) (Fin p) ℝ) i i = 2 := fun i => by
      rw [← one_add_one_eq_two]; simp; norm_num
    have h2q : ∀ j : Fin q, (2 : Matrix (Fin q) (Fin q) ℝ) j j = 2 := fun j => by
      rw [← one_add_one_eq_two]; simp; norm_num
    simp only [qf, mulVec_single, single_dotProduct, one_mul]
    cases k <;> simp [bipForm, h2p, h2q]

lemma forall_norm_eq_one (hpsd : ∀ v, 0 ≤ qf (bipForm A) v) (lam : ℂ)
    (h : HasEigenC (bipCoxeter A) lam) : ‖lam‖ = 1 := by
  by_cases hl : lam = -1
  · rw [hl]; simp
  obtain ⟨ν, hν0, ⟨a, ha0, ha⟩, hq⟩ := eigen_analysis A h hl
  have hν4 := eigen_AAt_le_four A hpsd ha0 ha
  refine norm_eq_one_of_quadratic lam (ν - 2) (by nlinarith) ?_
  push_cast
  exact hq

lemma not_eigen_one_of_spherical (hsph : FormSpherical (bipForm A)) :
    ¬ HasEigenC (bipCoxeter A) 1 := by
  intro h
  obtain ⟨ν, _, ⟨a, ha0, ha⟩, hq⟩ := eigen_analysis A h (by norm_num)
  have hν : (ν : ℂ) = 4 := by linear_combination -hq
  have hν' : ν = 4 := by exact_mod_cast hν
  have := eigen_AAt_lt_four A hsph ha0 ha
  linarith

lemma eigen_one_of_affine (haff : FormAffine (bipForm A)) : HasEigenC (bipCoxeter A) 1 := by
  obtain ⟨hpsd, v, hv0, hv⟩ := haff
  have hBv : bipForm A *ᵥ v = 0 := by
    set w := bipForm A *ᵥ v
    by_contra hw0
    have ha : 0 < w ⬝ᵥ w := dot_self_pos hw0
    set b := qf (bipForm A) w
    have hb : 0 ≤ b := hpsd w
    set t : ℝ := -(w ⬝ᵥ w) / (b + 1)
    have hnonneg : 0 ≤ qf (bipForm A) (v + t • w) := hpsd (v + t • w)
    have hexp : qf (bipForm A) (v + t • w) =
        qf (bipForm A) v + 2 * t * (w ⬝ᵥ w) + t ^ 2 * b := by
      simp only [qf, b, w, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      have hsym : v ⬝ᵥ (bipForm A *ᵥ w) = w ⬝ᵥ (bipForm A *ᵥ v) := by
        rw [dotProduct_mulVec, ← mulVec_transpose, bipForm_transpose, dotProduct_comm]
      rw [hsym]
      ring
    rw [hv, zero_add] at hexp
    have hneg : 2 * t * (w ⬝ᵥ w) + t ^ 2 * b < 0 := by
      have hden : 0 < b + 1 := by linarith
      have hnum : -(w ⬝ᵥ w) ^ 2 * (b + 2) < 0 := by nlinarith
      have heq : 2 * t * (w ⬝ᵥ w) + t ^ 2 * b = -(w ⬝ᵥ w) ^ 2 * (b + 2) / (b + 1) ^ 2 := by
        simp only [t]; field_simp; ring
      rw [heq]
      exact div_neg_of_neg_of_pos hnum (sq_pos_of_pos hden)
    linarith
  rw [← Sum.elim_comp_inl_inr v] at hBv
  rw [bipForm, fromBlocks_mulVec] at hBv
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have e1 : (2 : ℝ) • x = A *ᵥ y := by
    funext i
    have := congr_fun hBv (Sum.inl i)
    rw [two_smul, add_mulVec, one_mulVec] at this
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Pi.add_apply, Pi.zero_apply,
      neg_mulVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  have e2 : Aᵀ *ᵥ x = (2 : ℝ) • y := by
    funext j
    have := congr_fun hBv (Sum.inr j)
    have h2 : ((2 • (1 : Matrix (Fin q) (Fin q) ℝ)) *ᵥ y) j = 2 * y j := by
      rw [two_smul, add_mulVec, one_mulVec]; simp; ring
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Pi.add_apply, Pi.zero_apply,
      neg_mulVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [h2] at this
    linarith
  have hw : bipCoxeter A *ᵥ v = (1 : ℝ) • v := by
    rw [one_smul, bipCoxeter_eq]
    conv_lhs => rw [← Sum.elim_comp_inl_inr v]
    rw [fromBlocks_mulVec]
    conv_rhs => rw [← Sum.elim_comp_inl_inr v]
    congr 1
    · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      rw [sub_mulVec, ← mulVec_mulVec, e2, mulVec_smul, ← e1, neg_mulVec, ← e1, one_mulVec]
      funext i; simp [x]; ring
    · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      rw [e2, neg_mulVec, one_mulVec]
      funext j; simp [y]; ring
  have := hasEigenC_of_real hv0 hw
  simpa using this

/-- `w` has a real eigenvalue `> 1` when `B` is indefinite. -/
lemma real_eigen_gt_one_of_indefinite (hind : FormIndefinite (bipForm A)) :
    ∃ lam : ℝ, 1 < lam ∧ HasEigenC (bipCoxeter A) lam := by
  obtain ⟨_, v, hv⟩ := hind
  -- `4 - A Aᵀ` is not positive semidefinite
  set N : Matrix (Fin p) (Fin p) ℝ := (4 : ℝ) • 1 - A * Aᵀ
  have hNt : Nᵀ = N := by simp [N, transpose_sub, AAt_transpose]
  have hN := isHermitian_of_transpose_eq hNt
  have hnot : ¬ N.PosSemidef := by
    intro hpsd
    have hb : ∀ a : Fin p → ℝ, (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) ≤ 4 * (a ⬝ᵥ a) := by
      intro a
      have := hpsd.dotProduct_mulVec_nonneg a
      simp only [star_trivial, N, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, dot_AAt] at this
      linarith
    exact absurd (qf_nonneg_of_bound A hb v) (not_le.mpr hv)
  obtain ⟨θ, hθ, u, hu0, hu⟩ := exists_eigen_neg_of_not_posSemidef N hN hnot
  set ν : ℝ := 4 - θ
  have huν : (A * Aᵀ) *ᵥ u = ν • u := by
    have : (A * Aᵀ) *ᵥ u = (4 : ℝ) • u - N *ᵥ u := by
      simp [N, sub_mulVec, smul_mulVec]
    rw [this, hu, ← sub_smul]
  have hν4 : 4 < ν := by simp only [ν]; linarith
  set μ := Real.sqrt ν
  have hμ : μ ^ 2 = ν := Real.sq_sqrt (by linarith)
  set lam : ℝ := ((ν - 2) + Real.sqrt ((ν - 2) ^ 2 - 4)) / 2
  have hdisc : 0 ≤ (ν - 2) ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hdisc
  have hlam : lam ^ 2 - (μ ^ 2 - 2) * lam + 1 = 0 := by
    rw [hμ]; simp only [lam]; nlinarith
  have hgt : 1 < lam := by
    have := Real.sqrt_nonneg ((ν - 2) ^ 2 - 4)
    simp only [lam]; linarith
  have heig := theorem_3_27_bipartite_coxeter_eigenvalue A u μ lam (by rw [hμ]; exact huν) hlam
  refine ⟨lam, hgt, hasEigenC_of_real (v := Sum.elim ((lam + 1) • u) (Aᵀ *ᵥ u)) ?_ ?_⟩
  · intro h0
    apply hu0
    funext i
    have := congr_fun h0 (Sum.inl i)
    simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have hl1 : lam + 1 ≠ 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hl1
  · exact heig

/-- **Theorem 3.27** (A'Campo) for the bipartite Coxeter element `w = s₊ s₋` of a bipartite
Coxeter graph with form `B = [[2, -A], [-Aᵀ, 2]]`:
* `B` is spherical (positive definite) iff all eigenvalues of `w` have modulus `1` and `1` is
  not an eigenvalue;
* `B` is affine (positive semidefinite, degenerate) iff all eigenvalues of `w` have modulus `1`
  and `1` is an eigenvalue;
* `B` is hyperbolic or higher rank (indefinite) iff `w` has a real eigenvalue `λ > 1`. -/
theorem theorem_3_27_classification :
    (FormSpherical (bipForm A) ↔
      (∀ lam, HasEigenC (bipCoxeter A) lam → ‖lam‖ = 1) ∧ ¬ HasEigenC (bipCoxeter A) 1) ∧
    (FormAffine (bipForm A) ↔
      (∀ lam, HasEigenC (bipCoxeter A) lam → ‖lam‖ = 1) ∧ HasEigenC (bipCoxeter A) 1) ∧
    (FormIndefinite (bipForm A) ↔
      ∃ lam : ℝ, 1 < lam ∧ HasEigenC (bipCoxeter A) lam) := by
  have sph_psd : FormSpherical (bipForm A) → ∀ v, 0 ≤ qf (bipForm A) v := by
    intro h v
    by_cases hv : v = 0
    · rw [hv]; simp [qf]
    · exact (h v hv).le
  have real_gt_one_contra : ∀ lam : ℝ, 1 < lam → HasEigenC (bipCoxeter A) lam →
      (∀ v, 0 ≤ qf (bipForm A) v) → False := by
    intro lam hl he hpsd
    have := forall_norm_eq_one A hpsd _ he
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    linarith
  refine ⟨⟨fun h => ⟨forall_norm_eq_one A (sph_psd h), not_eigen_one_of_spherical A h⟩,
    fun ⟨hn, h1⟩ => ?_⟩, ⟨fun h => ⟨forall_norm_eq_one A h.1, eigen_one_of_affine A h⟩,
    fun ⟨hn, h1⟩ => ?_⟩, ⟨real_eigen_gt_one_of_indefinite A, fun ⟨lam, hl, he⟩ => ?_⟩⟩
  · rcases exhaustive A with h | h | h
    · exact h
    · exact absurd (eigen_one_of_affine A h) h1
    · obtain ⟨lam, hl, he⟩ := real_eigen_gt_one_of_indefinite A h
      have := hn _ he
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
      linarith
  · rcases exhaustive A with h | h | h
    · exact absurd h1 (not_eigen_one_of_spherical A h)
    · exact h
    · obtain ⟨lam, hl, he⟩ := real_eigen_gt_one_of_indefinite A h
      have := hn _ he
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
      linarith
  · rcases exhaustive A with h | h | h
    · exact (real_gt_one_contra lam hl he (sph_psd h)).elim
    · exact (real_gt_one_contra lam hl he h.1).elim
    · exact h

/-! ### Theorem 3.28 -/

lemma rplus_mono {x y : ℝ} (hx : 4 ≤ x) (hxy : x ≤ y) :
    ((x - 2) + Real.sqrt ((x - 2) ^ 2 - 4)) / 2 ≤ ((y - 2) + Real.sqrt ((y - 2) ^ 2 - 4)) / 2 := by
  have : Real.sqrt ((x - 2) ^ 2 - 4) ≤ Real.sqrt ((y - 2) ^ 2 - 4) :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- For `ν > 4` and an eigenvector `u` of `A Aᵀ`, `w` has the real eigenvalue
`r₊(ν) = ((ν - 2) + √((ν - 2)² - 4)) / 2 > 1`. -/
lemma real_eigen_of_AAt_gt_four {u : Fin p → ℝ} (hu0 : u ≠ 0) {ν : ℝ}
    (hu : (A * Aᵀ) *ᵥ u = ν • u) (hν : 4 < ν) :
    1 < ((ν - 2) + Real.sqrt ((ν - 2) ^ 2 - 4)) / 2 ∧
      HasEigenC (bipCoxeter A) (((ν - 2) + Real.sqrt ((ν - 2) ^ 2 - 4)) / 2 : ℝ) := by
  set μ := Real.sqrt ν
  have hμ : μ ^ 2 = ν := Real.sq_sqrt (by linarith)
  set lam : ℝ := ((ν - 2) + Real.sqrt ((ν - 2) ^ 2 - 4)) / 2
  have hdisc : 0 ≤ (ν - 2) ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hdisc
  have hlam : lam ^ 2 - (μ ^ 2 - 2) * lam + 1 = 0 := by
    rw [hμ]; simp only [lam]; nlinarith
  have hgt : 1 < lam := by
    have := Real.sqrt_nonneg ((ν - 2) ^ 2 - 4)
    simp only [lam]; linarith
  have heig := theorem_3_27_bipartite_coxeter_eigenvalue A u μ lam (by rw [hμ]; exact hu) hlam
  refine ⟨hgt, hasEigenC_of_real (v := Sum.elim ((lam + 1) • u) (Aᵀ *ᵥ u)) ?_ ?_⟩
  · intro h0
    apply hu0
    funext i
    have := congr_fun h0 (Sum.inl i)
    simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have hl1 : lam + 1 ≠ 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hl1
  · exact heig

/-- Complex eigenvectors of `w` from real eigenvectors of `A Aᵀ`: if `A Aᵀ u = ν u` and
`λ² - (ν - 2) λ + 1 = 0`, then `w ((λ + 1) u, Aᵀ u) = λ ((λ + 1) u, Aᵀ u)`. -/
lemma complex_eigen_of_AAt (u : Fin p → ℝ) (ν : ℝ) (hu : (A * Aᵀ) *ᵥ u = ν • u) (lam : ℂ)
    (hlam : lam ^ 2 - ((ν : ℂ) - 2) * lam + 1 = 0) :
    ((bipCoxeter A).map (↑) : Matrix _ _ ℂ) *ᵥ
        Sum.elim (fun i => (lam + 1) * (u i : ℂ)) (fun j => ((Aᵀ *ᵥ u) j : ℂ)) =
      lam • Sum.elim (fun i => (lam + 1) * (u i : ℂ)) (fun j => ((Aᵀ *ᵥ u) j : ℂ)) := by
  rw [bipCoxeter_map, fromBlocks_mulVec]
  have hmap : ((A * Aᵀ).map (↑) : Matrix (Fin p) (Fin p) ℂ) = A.map (↑) * (A.map (↑))ᵀ := by
    ext i j; simp [Matrix.mul_apply]
  have hAA : ∀ i, ((A.map (↑) * (A.map (↑))ᵀ : Matrix (Fin p) (Fin p) ℂ) *ᵥ
      (fun i => (u i : ℂ))) i = (ν : ℂ) * u i := by
    intro i
    rw [← hmap, mulVec_map_ofReal, hu]
    simp
  have hA : ∀ i, ((A.map (↑) : Matrix (Fin p) (Fin q) ℂ) *ᵥ
      (fun j => ((Aᵀ *ᵥ u) j : ℂ))) i = (ν : ℂ) * u i := by
    intro i
    rw [mulVec_map_ofReal', mulVec_mulVec, hu]
    simp
  have hAt : ((A.map (↑) : Matrix (Fin p) (Fin q) ℂ)ᵀ *ᵥ (fun i => (lam + 1) * (u i : ℂ))) =
      fun j => (lam + 1) * ((Aᵀ *ᵥ u) j : ℂ) := by
    have : (fun i => (lam + 1) * (u i : ℂ)) = (lam + 1) • (fun i => (u i : ℂ)) := by
      funext i; simp
    rw [this, mulVec_smul, ← transpose_map, mulVec_map_ofReal']
    funext j; simp
  funext k
  cases k with
  | inl i =>
    have hx : (fun i => (lam + 1) * (u i : ℂ)) = (lam + 1) • (fun i => (u i : ℂ)) := by
      funext i; simp
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, sub_mulVec, one_mulVec, neg_mulVec, Pi.sub_apply, Pi.neg_apply]
    rw [hx, mulVec_smul, Pi.smul_apply, hAA, hA]
    simp only [smul_eq_mul]
    linear_combination -(u i : ℂ) * hlam
  | inr j =>
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, neg_mulVec, one_mulVec, Pi.neg_apply, hAt]
    ring

/-- `w` always has an eigenvalue of modulus at least `1` (on a nonempty node set). -/
lemma exists_eigen_norm_ge_one (hne : Nonempty (Fin p ⊕ Fin q)) :
    ∃ lam : ℂ, HasEigenC (bipCoxeter A) lam ∧ 1 ≤ ‖lam‖ := by
  by_cases hp : Nonempty (Fin p)
  · obtain ⟨i₀⟩ := hp
    set M := A * Aᵀ
    have hM := isHermitian_of_transpose_eq (AAt_transpose A)
    set u : Fin p → ℝ := ⇑(hM.eigenvectorBasis i₀)
    set ν := hM.eigenvalues i₀
    have hu : M *ᵥ u = ν • u := hM.mulVec_eigenvectorBasis i₀
    have hu0 : u ≠ 0 := by
      intro h0
      apply (hM.eigenvectorBasis).orthonormal.ne_zero i₀
      ext j
      simpa using congr_fun h0 j
    have hν0 : 0 ≤ ν := eigen_AAt_nonneg A hu0 hu
    by_cases hν4 : 4 < ν
    · obtain ⟨hgt, he⟩ := real_eigen_of_AAt_gt_four A hu0 hu hν4
      refine ⟨_, he, ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact hgt.le
    · push Not at hν4
      by_cases hAu : Aᵀ *ᵥ u = 0
      · -- eigenvalue `-1` with eigenvector `(u, 0)`
        refine ⟨((-1 : ℝ) : ℂ), hasEigenC_of_real (v := Sum.elim u 0) ?_ ?_, by simp⟩
        · intro h0; apply hu0; funext i; simpa using congr_fun h0 (Sum.inl i)
        · rw [bipCoxeter_eq, fromBlocks_mulVec]
          funext k
          cases k with
          | inl i =>
            have : (A * Aᵀ) *ᵥ u = 0 := by rw [← mulVec_mulVec, hAu, mulVec_zero]
            simp [sub_mulVec, this]
          | inr j => simp [hAu]
      · set b : ℝ := ν - 2
        have hb : b ^ 2 ≤ 4 := by simp only [b]; nlinarith
        set lam : ℂ := ⟨b / 2, Real.sqrt (4 - b ^ 2) / 2⟩
        have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 - b ^ 2)
        have hlam : lam ^ 2 - ((ν : ℂ) - 2) * lam + 1 = 0 := by
          rw [show ((ν : ℂ) - 2) = (b : ℂ) by simp [b]]
          apply Complex.ext
          · simp only [lam, pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.zero_re]
            rw [show √(4 - b * b) / 2 * (√(4 - b * b) / 2) = √(4 - b ^ 2) ^ 2 / 4 by
              rw [show b * b = b ^ 2 by ring]; ring, hs]
            ring
          · simp [lam, pow_two, b]; ring
        refine ⟨lam, ⟨_, ?_, complex_eigen_of_AAt A u ν hu lam hlam⟩, ?_⟩
        · intro h0
          apply hAu
          funext j
          have := congr_fun h0 (Sum.inr j)
          simpa using this
        · rw [norm_eq_one_of_quadratic lam b hb (by
            have : ((ν : ℂ) - 2) = (b : ℂ) := by simp [b]
            rw [← this]; exact hlam)]
  · -- `N₁ = ∅`: `w = -1` on `ℝ^{N₂}`
    have hq : Nonempty (Fin q) := by
      obtain ⟨k⟩ := hne
      cases k with
      | inl i => exact absurd ⟨i⟩ hp
      | inr j => exact ⟨j⟩
    obtain ⟨j₀⟩ := hq
    refine ⟨((-1 : ℝ) : ℂ), hasEigenC_of_real (v := Sum.elim 0 (Pi.single j₀ 1)) ?_ ?_, by simp⟩
    · intro h0
      have := congr_fun h0 (Sum.inr j₀)
      simp at this
    · rw [bipCoxeter_eq, fromBlocks_mulVec]
      funext k
      cases k with
      | inl i => exact absurd ⟨i⟩ hp
      | inr j =>
        have h0 : (Pi.single (Sum.inr j₀) (1 : ℝ) : Fin p ⊕ Fin q → ℝ) ∘ Sum.inl = 0 := by
          funext i; simp
        simp [h0, neg_mulVec, one_mulVec]

/-- Restriction of a vector to the rows kept by `f`, and its extension by zero. -/
lemma sum_mul_extend {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (a' : Fin m → ℝ) (h : Fin n → ℝ) :
    ∑ r, h r * Function.extend f a' 0 r = ∑ r', h (f r') * a' r' := by
  classical
  have hsub : Finset.univ.map ⟨f, hf⟩ ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ r ∈ (Finset.univ : Finset (Fin n)), r ∉ Finset.univ.map ⟨f, hf⟩ →
      h r * Function.extend f a' 0 r = 0 := by
    intro r _ hr
    have hnr : ¬ ∃ r', f r' = r := by simpa using hr
    simp [Function.extend_apply' _ _ _ hnr]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_map]
  simp [hf.extend_apply]

/-- **Theorem 3.28 (interlacing)**: let `Γ' ⊂ Γ` be the induced subgraph on the nodes picked by
injective maps `f : N₁' → N₁` and `g : N₂' → N₂` (so `A' = A.submatrix f g`; deleting the
single node `rᵢ` gives `Γ' = Γ/(rᵢ)`). Then every eigenvalue `λ'` of the Coxeter element
`w(Γ')` is dominated in modulus by an eigenvalue `λ` of `w(Γ)`: `ρ(w(Γ')) ≤ ρ(w(Γ))`. -/
theorem theorem_3_28_interlacing {p' q' : ℕ} (f : Fin p' → Fin p) (g : Fin q' → Fin q)
    (hf : Function.Injective f) (hg : Function.Injective g) (lam' : ℂ)
    (h' : HasEigenC (bipCoxeter (A.submatrix f g)) lam') :
    ∃ lam : ℂ, HasEigenC (bipCoxeter A) lam ∧ ‖lam'‖ ≤ ‖lam‖ := by
  set A' := A.submatrix f g
  have hne : Nonempty (Fin p ⊕ Fin q) := by
    obtain ⟨v, hv0, _⟩ := h'
    obtain ⟨k, _⟩ := Function.ne_iff.mp hv0
    cases k with
    | inl i => exact ⟨Sum.inl (f i)⟩
    | inr j => exact ⟨Sum.inr (g j)⟩
  by_cases hsmall : ‖lam'‖ ≤ 1
  · obtain ⟨lam, he, hn⟩ := exists_eigen_norm_ge_one A hne
    exact ⟨lam, he, hsmall.trans hn⟩
  push Not at hsmall
  have hl1 : lam' ≠ -1 := by intro h; rw [h] at hsmall; simp at hsmall
  obtain ⟨ν', hν'0, ⟨a', ha'0, ha'⟩, hq⟩ := eigen_analysis A' h' hl1
  -- `ν' > 4`, otherwise `‖λ'‖ = 1`
  have hν'4 : 4 < ν' := by
    by_contra hc
    push Not at hc
    have := norm_eq_one_of_quadratic lam' (ν' - 2) (by nlinarith) (by push_cast; exact hq)
    linarith
  -- `λ'` is one of the two real roots, so `‖λ'‖ ≤ r₊(ν')`
  set d := Real.sqrt ((ν' - 2) ^ 2 - 4)
  have hd2 : d ^ 2 = (ν' - 2) ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  set rp : ℝ := ((ν' - 2) + d) / 2
  set rm : ℝ := ((ν' - 2) - d) / 2
  have hfac : (lam' - rp) * (lam' - rm) = 0 := by
    have e1 : (rp : ℂ) + rm = ν' - 2 := by simp only [rp, rm]; push_cast; ring
    have e2 : (rp : ℂ) * rm = 1 := by
      have : rp * rm = 1 := by simp only [rp, rm]; nlinarith
      exact_mod_cast this
    linear_combination hq - lam' * e1 + e2
  have hrm_le : rm ≤ rp := by simp only [rm, rp]; linarith
  have hrm_pos : 0 < rm := by
    simp only [rm]
    have : d < ν' - 2 := by
      rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ ν' - 2)]
      exact Real.sqrt_lt_sqrt (by nlinarith) (by linarith)
    linarith
  have hnorm' : ‖lam'‖ ≤ rp := by
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    · rw [sub_eq_zero.mp h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrm_pos]
      exact hrm_le
  -- extend `a'` by zero to `N₁`
  set a : Fin p → ℝ := Function.extend f a' 0
  have ha0 : a ≠ 0 := by
    intro h0
    apply ha'0
    funext i
    have := congr_fun h0 (f i)
    simpa [a, hf.extend_apply] using this
  have hAa : ∀ c', (Aᵀ *ᵥ a) (g c') = (A'ᵀ *ᵥ a') c' := by
    intro c'
    simp only [mulVec, dotProduct, transpose_apply, A', submatrix_apply]
    rw [show (∑ x, A x (g c') * a x) = ∑ r', A (f r') (g c') * a' r' from
      sum_mul_extend f hf a' (fun r => A r (g c'))]
  have haa : a ⬝ᵥ a = a' ⬝ᵥ a' := by
    simp only [dotProduct]
    have := sum_mul_extend f hf a' a
    simp only [a, hf.extend_apply] at this ⊢
    exact this
  have hle : (A'ᵀ *ᵥ a') ⬝ᵥ (A'ᵀ *ᵥ a') ≤ (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) := by
    classical
    simp only [dotProduct]
    rw [show (∑ c', (A'ᵀ *ᵥ a') c' * (A'ᵀ *ᵥ a') c') =
        ∑ c ∈ Finset.univ.map ⟨g, hg⟩, (Aᵀ *ᵥ a) c * (Aᵀ *ᵥ a) c by
      rw [Finset.sum_map]; simp [hAa]]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun c _ _ => mul_self_nonneg _)
  have hray : ν' * (a ⬝ᵥ a) ≤ a ⬝ᵥ ((A * Aᵀ) *ᵥ a) := by
    rw [dot_AAt, haa]
    have := dot_AAt A' a'
    rw [ha', dotProduct_smul, smul_eq_mul] at this
    linarith
  -- an eigenvalue `ν ≥ ν'` of `A Aᵀ`
  set N : Matrix (Fin p) (Fin p) ℝ := ν' • 1 - A * Aᵀ
  have hNt : Nᵀ = N := by simp [N, transpose_sub, AAt_transpose]
  have hN := isHermitian_of_transpose_eq hNt
  have hnot : ¬ N.PosDef := by
    intro hpd
    have := (posDef_iff_dotProduct_mulVec.mp hpd).2 ha0
    simp only [star_trivial, N, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at this
    linarith
  obtain ⟨θ, hθ, u, hu0, hu⟩ := exists_eigen_nonpos_of_not_posDef N hN hnot
  have huν : (A * Aᵀ) *ᵥ u = (ν' - θ) • u := by
    have : (A * Aᵀ) *ᵥ u = ν' • u - N *ᵥ u := by
      simp [N, sub_mulVec, smul_mulVec]
    rw [this, hu, ← sub_smul]
  obtain ⟨_, he⟩ := real_eigen_of_AAt_gt_four A hu0 huν (by linarith)
  refine ⟨_, he, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine hnorm'.trans (le_trans (rplus_mono (by linarith) (by linarith : ν' ≤ ν' - θ))
    (le_abs_self _))

/-- **Theorem 3.28 (strict form)**: if `Γ` is hyperbolic and its induced subgraph `Γ'` is not,
every eigenvalue of `w(Γ')` is strictly smaller in modulus than some eigenvalue of `w(Γ)`. -/
theorem theorem_3_28_strict {p' q' : ℕ} (f : Fin p' → Fin p) (g : Fin q' → Fin q)
    (hΓ : FormIndefinite (bipForm A)) (hΓ' : ¬ FormIndefinite (bipForm (A.submatrix f g)))
    (lam' : ℂ) (h' : HasEigenC (bipCoxeter (A.submatrix f g)) lam') :
    ∃ lam : ℂ, HasEigenC (bipCoxeter A) lam ∧ ‖lam'‖ < ‖lam‖ := by
  have hpsd : ∀ v, 0 ≤ qf (bipForm (A.submatrix f g)) v := by
    rcases exhaustive (A.submatrix f g) with h | h | h
    · intro v
      by_cases hv : v = 0
      · rw [hv]; simp [qf]
      · exact (h v hv).le
    · exact h.1
    · exact absurd h hΓ'
  have h1 := forall_norm_eq_one _ hpsd lam' h'
  obtain ⟨lam, hl, he⟩ := real_eigen_gt_one_of_indefinite A hΓ
  refine ⟨lam, he, ?_⟩
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact hl

end MixedSignCoxeter

namespace ReflectionSystem

open Matrix BigOperators

variable {n : ℕ}

/-! ### Definitions 2.47 & 2.51: Eigenvalue Signature Triple and 4-Way Classification -/

section Signature

/-- Every `ReflectionSystem` has a real Hermitian (symmetric) bilinear form matrix `S.B`. -/
lemma B_isHermitian (S : ReflectionSystem n) : S.B.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, S.B_symm]

/-- Number of strictly positive eigenvalues of `S.B` (counted with multiplicity). -/
noncomputable def posEigenCount (S : ReflectionSystem n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => 0 < S.B_isHermitian.eigenvalues i).card

/-- Number of strictly negative eigenvalues of `S.B` (counted with multiplicity). -/
noncomputable def negEigenCount (S : ReflectionSystem n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i < 0).card

/-- Number of zero eigenvalues of `S.B` (nullity). -/
noncomputable def zeroEigenCount (S : ReflectionSystem n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i = 0).card

/-- **Definition 2.47**: The signature `sig(B) = (p, q, l)` of the bilinear form `B`, where
`p`, `q`, `l` are the counts of positive, negative, and zero eigenvalues of `B`. -/
noncomputable def signature (S : ReflectionSystem n) : ℕ × ℕ × ℕ :=
  (S.posEigenCount, S.negEigenCount, S.zeroEigenCount)

/-- The eigenvalue counts satisfy `p + q + l = n`. -/
theorem signature_sum (S : ReflectionSystem n) :
    S.posEigenCount + S.negEigenCount + S.zeroEigenCount = n := by
  unfold posEigenCount negEigenCount zeroEigenCount
  have hd12 : Disjoint
      (Finset.univ.filter fun i : Fin n => 0 < S.B_isHermitian.eigenvalues i)
      (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i < 0) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2; linarith
  have hd12_3 : Disjoint
      ((Finset.univ.filter fun i : Fin n => 0 < S.B_isHermitian.eigenvalues i) ∪
        (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i < 0))
      (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i = 0) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    rcases hi1 with h | h <;> linarith
  rw [← Finset.card_union_of_disjoint hd12, ← Finset.card_union_of_disjoint hd12_3]
  have hunion :
      ((Finset.univ.filter fun i : Fin n => 0 < S.B_isHermitian.eigenvalues i) ∪
        (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i < 0)) ∪
      (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i = 0) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases lt_trichotomy (S.B_isHermitian.eigenvalues i) 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  rw [hunion, Finset.card_univ, Fintype.card_fin]

lemma isPosDef_iff_posDef (S : ReflectionSystem n) :
    S.IsPosDef ↔ S.B.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨S.B_isHermitian, fun v hv => ?_⟩
    simpa [quadForm_eq_dotProduct] using h v hv
  · intro h v hv
    simpa [quadForm_eq_dotProduct] using h.2 hv

/-- `S` is positive definite iff `sig(B) = (n, 0, 0)`. -/
theorem isPosDef_iff_signature (S : ReflectionSystem n) :
    S.IsPosDef ↔ S.signature = (n, 0, 0) := by
  rw [isPosDef_iff_posDef, S.B_isHermitian.posDef_iff_eigenvalues_pos]
  constructor
  · intro hpos
    have hp : S.posEigenCount = n := by
      unfold posEigenCount
      rw [Finset.filter_true_of_mem fun i _ => hpos i, Finset.card_univ, Fintype.card_fin]
    have hsum := S.signature_sum
    have hq : S.negEigenCount = 0 := by omega
    have hl : S.zeroEigenCount = 0 := by omega
    simp [signature, hp, hq, hl]
  · intro hsig i
    have hp : S.posEigenCount = n := congr_arg Prod.fst hsig
    unfold posEigenCount at hp
    have hall : (Finset.univ.filter fun j : Fin n => 0 < S.B_isHermitian.eigenvalues j) =
        Finset.univ := Finset.eq_univ_of_card _ (by simpa using hp)
    have hi : i ∈ Finset.univ.filter fun j : Fin n => 0 < S.B_isHermitian.eigenvalues j := by
      rw [hall]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2

/-- `S` is negative definite iff `sig(B) = (0, n, 0)`. -/
theorem isNegDef_iff_signature (S : ReflectionSystem n) :
    S.IsNegDef ↔ S.signature = (0, n, 0) := by
  have hneg : S.IsNegDef ↔ (-S.B).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · intro h
      have hH : (-S.B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_neg,
          Matrix.conjTranspose_eq_transpose_of_trivial, S.B_symm]
      refine ⟨hH, fun v hv => ?_⟩
      have h1 := h v hv
      rw [quadForm_eq_dotProduct] at h1
      simpa [Matrix.neg_mulVec, dotProduct_neg] using h1
    · intro h v hv
      have h1 := h.2 hv
      rw [quadForm_eq_dotProduct]
      simpa [Matrix.neg_mulVec, dotProduct_neg] using h1
  have hall_neg : (-S.B).PosDef ↔ ∀ i : Fin n, S.B_isHermitian.eigenvalues i < 0 := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · intro hpos i
      have hv_ne : (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ) ≠ 0 := by
        intro h0
        apply S.B_isHermitian.eigenvectorBasis.orthonormal.ne_zero i
        ext j; simpa using congr_fun h0 j
      have h1 := hpos.2 hv_ne
      have heig := S.B_isHermitian.mulVec_eigenvectorBasis i
      rw [star_trivial, Matrix.neg_mulVec, heig, dotProduct_neg, dotProduct_smul,
        smul_eq_mul] at h1
      have hnorm : 0 < dotProduct (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ)
          (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ) := by
        have hnn : 0 ≤ dotProduct (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ)
            (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ) :=
          Finset.sum_nonneg fun j _ => mul_self_nonneg _
        rcases lt_or_eq_of_le hnn with hlt | heq
        · exact hlt
        · exfalso
          apply hv_ne
          ext j
          have hj0 : (S.B_isHermitian.eigenvectorBasis i j) *
              (S.B_isHermitian.eigenvectorBasis i j) = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg
              (S.B_isHermitian.eigenvectorBasis i k))).mp heq.symm j (Finset.mem_univ j)
          exact mul_self_eq_zero.mp hj0
      nlinarith
    · intro hall
      have hH : (-S.B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_neg,
          Matrix.conjTranspose_eq_transpose_of_trivial, S.B_symm]
      refine ⟨hH, fun v hv => ?_⟩
      let U : Matrix (Fin n) (Fin n) ℝ := S.B_isHermitian.eigenvectorUnitary.1
      have hU : S.B = U * Matrix.diagonal S.B_isHermitian.eigenvalues * star U :=
        S.B_isHermitian.spectral_theorem
      have hUU : U * star U = 1 := by
        exact Unitary.coe_mul_star_self S.B_isHermitian.eigenvectorUnitary
      have hv' : (star U) *ᵥ v ≠ 0 := by
        intro h0
        apply hv
        have hmul := congr_arg (fun w => U *ᵥ w) h0
        rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec, Matrix.mulVec_zero] at hmul
        exact hmul
      set y := (star U) *ᵥ v
      have hquad : dotProduct v (S.B *ᵥ v) = ∑ i : Fin n, S.B_isHermitian.eigenvalues i * (y i) ^ 2 := by
        conv_lhs => rw [hU]
        rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec]
        have hvec : v ᵥ* U = y := by
          ext j
          simp only [y, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply,
            star_trivial]
          exact Finset.sum_congr rfl fun x _ => mul_comm _ _
        rw [hvec]
        simp only [dotProduct, Matrix.mulVec_diagonal]
        refine Finset.sum_congr rfl fun i _ => by ring
      have hneg_sum : dotProduct v (S.B *ᵥ v) < 0 := by
        rw [hquad]
        have hex : ∃ i : Fin n, y i ≠ 0 := by
          by_contra h
          push Not at h
          exact hv' (funext h)
        rcases hex with ⟨i₀, hi₀⟩
        have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
            S.B_isHermitian.eigenvalues i * (y i) ^ 2 ≤ (0 : ℝ) := fun i _ =>
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt (hall i)) (sq_nonneg _)
        have hlt : S.B_isHermitian.eigenvalues i₀ * (y i₀) ^ 2 < (0 : ℝ) :=
          mul_neg_of_neg_of_pos (hall i₀) (sq_pos_of_ne_zero hi₀)
        have hsum := Finset.sum_lt_sum hle ⟨i₀, Finset.mem_univ i₀, hlt⟩
        simpa using hsum
      simpa [Matrix.neg_mulVec, dotProduct_neg] using hneg_sum
  rw [hneg, hall_neg]
  constructor
  · intro hneg_eigs
    have hq : S.negEigenCount = n := by
      unfold negEigenCount
      rw [Finset.filter_true_of_mem fun i _ => hneg_eigs i, Finset.card_univ, Fintype.card_fin]
    have hsum := S.signature_sum
    have hp : S.posEigenCount = 0 := by omega
    have hl : S.zeroEigenCount = 0 := by omega
    simp [signature, hp, hq, hl]
  · intro hsig i
    have hq : S.negEigenCount = n := congr_arg (fun t => t.2.1) hsig
    unfold negEigenCount at hq
    have hall : (Finset.univ.filter fun j : Fin n => S.B_isHermitian.eigenvalues j < 0) =
        Finset.univ := Finset.eq_univ_of_card _ (by simpa using hq)
    have hi : i ∈ Finset.univ.filter fun j : Fin n => S.B_isHermitian.eigenvalues j < 0 := by
      rw [hall]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2

/-- **Definition 2.51**: The four signature classes of a reflection system:
`spherical`, `affine`, `hyperbolic`, and `higherRank`. -/
inductive SignatureType
  | spherical
  | affine
  | hyperbolic
  | higherRank
  deriving DecidableEq, Repr

/-- **Definition 2.51**: Classification of a rank-`n` reflection system by its signature
`sig(B) = (p, q, l)`:
1. `spherical` if `sig = (n, 0, 0)` or `(0, n, 0)`;
2. `affine` if `sig = (n - 1, 0, 1)` or `(0, n - 1, 1)`;
3. `hyperbolic` if `2 ≤ n` and `sig = (n - 1, 1, 0)` or `(1, n - 1, 0)`;
4. `higherRank` otherwise. -/
noncomputable def signatureType (S : ReflectionSystem n) : SignatureType :=
  if S.signature = (n, 0, 0) ∨ S.signature = (0, n, 0) then .spherical
  else if 1 ≤ n ∧ (S.signature = (n - 1, 0, 1) ∨ S.signature = (0, n - 1, 1)) then .affine
  else if 2 ≤ n ∧ (S.signature = (n - 1, 1, 0) ∨ S.signature = (1, n - 1, 0)) then .hyperbolic
  else .higherRank

/-- A reflection system is spherical iff it is positive or negative definite. -/
theorem signatureType_eq_spherical_iff (S : ReflectionSystem n) :
    S.signatureType = .spherical ↔ S.IsPosDef ∨ S.IsNegDef := by
  unfold signatureType
  rw [isPosDef_iff_signature, isNegDef_iff_signature]
  split_ifs <;> simp_all

/-- A reflection system is hyperbolic iff `2 ≤ n` and `sig(B) = (n - 1, 1, 0)` or `(1, n - 1, 0)`. -/
theorem signatureType_eq_hyperbolic_iff (S : ReflectionSystem n) :
    S.signatureType = .hyperbolic ↔
      2 ≤ n ∧ (S.signature = (n - 1, 1, 0) ∨ S.signature = (1, n - 1, 0)) := by
  unfold signatureType
  constructor
  · intro h
    split_ifs at h with h1 h2 h3
    exact h3
  · rintro ⟨hn, hsig⟩
    have hnot1 : ¬ (S.signature = (n, 0, 0) ∨ S.signature = (0, n, 0)) := by
      rcases hsig with h | h <;> rw [h] <;> simp <;> omega
    have hnot2 : ¬ (1 ≤ n ∧ (S.signature = (n - 1, 0, 1) ∨ S.signature = (0, n - 1, 1))) := by
      rintro ⟨_, h2⟩
      rcases hsig with h | h <;> rw [h] at h2 <;> simp at h2
    simp only [hnot1, hnot2, hn, hsig, and_self, ↓reduceIte]

/-- Any reflection system with at least 2 positive and at least 2 negative eigenvalues is
`higherRank` (explicitly separating higher-rank from hyperbolic indefinite systems). -/
theorem signatureType_eq_higherRank_of_two_pos_two_neg (S : ReflectionSystem n)
    (hp : 2 ≤ S.posEigenCount) (hq : 2 ≤ S.negEigenCount) :
    S.signatureType = .higherRank := by
  unfold signatureType
  have h1 : ¬ (S.signature = (n, 0, 0) ∨ S.signature = (0, n, 0)) := by
    simp only [signature, Prod.mk.injEq]; omega
  have h2 : ¬ (1 ≤ n ∧ (S.signature = (n - 1, 0, 1) ∨ S.signature = (0, n - 1, 1))) := by
    rintro ⟨_, h⟩; simp only [signature, Prod.mk.injEq] at h; omega
  have h3 : ¬ (2 ≤ n ∧ (S.signature = (n - 1, 1, 0) ∨ S.signature = (1, n - 1, 0))) := by
    rintro ⟨_, h⟩; simp only [signature, Prod.mk.injEq] at h; omega
  simp only [h1, h2, h3, ↓reduceIte]

end Signature

/-! ### Definition 2.61: Spectral Radius `λ(w)` -/

section SpectralRadius

/-- **Definition 2.61**: The spectral radius `λ(M) = sup {‖μ‖ | μ is a complex eigenvalue of M}`
of a real `n × n` matrix `M` (in particular, of a principal element `w ∈ W`). -/
noncomputable def spectralRadius (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup { r : ℝ | ∃ μ : ℂ, MixedSignCoxeter.HasEigenC M μ ∧ r = ‖μ‖ }

/-- Every complex eigenvalue `μ` of `M` is bounded in modulus by `∑ i, ∑ j, ‖M i j‖`. -/
lemma norm_le_l1_of_hasEigenC (M : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ}
    (hμ : MixedSignCoxeter.HasEigenC M μ) :
    ‖μ‖ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ := by
  rcases hμ with ⟨v, hv, heig⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hv
    ext i
    exact absurd (Finset.mem_univ i) (by rw [hemp]; simp)
  obtain ⟨i₀, _, hi₀max⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖) hne
  have hvi₀ : 0 < ‖v i₀‖ := by
    by_contra hle
    push Not at hle
    apply hv
    ext j
    have hj : ‖v j‖ ≤ 0 := le_trans (hi₀max j (Finset.mem_univ j)) hle
    exact norm_eq_zero.mp (le_antisymm hj (norm_nonneg _))
  have hrow := congr_fun heig i₀
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hrow
  have hbound : ‖μ‖ * ‖v i₀‖ ≤ (∑ j : Fin n, ‖M i₀ j‖) * ‖v i₀‖ := by
    rw [← norm_mul, ← hrow]
    calc
      ‖∑ j : Fin n, (M i₀ j : ℂ) * v j‖
        ≤ ∑ j : Fin n, ‖(M i₀ j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖M i₀ j‖ * ‖v j‖ := by
          refine Finset.sum_congr rfl fun j _ => by rw [norm_mul, Complex.norm_real]
      _ ≤ ∑ j : Fin n, ‖M i₀ j‖ * ‖v i₀‖ :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hi₀max j (Finset.mem_univ j)) (norm_nonneg _)
      _ = (∑ j : Fin n, ‖M i₀ j‖) * ‖v i₀‖ := (Finset.sum_mul _ _ _).symm
  have hrow_le : ‖μ‖ ≤ ∑ j : Fin n, ‖M i₀ j‖ := le_of_mul_le_mul_right hbound hvi₀
  have hsum_le : ∑ j : Fin n, ‖M i₀ j‖ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ :=
    Finset.single_le_sum (f := fun i => ∑ j : Fin n, ‖M i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i₀)
  exact le_trans hrow_le hsum_le

lemma hasEigenC_norms_bddAbove (M : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove { r : ℝ | ∃ μ : ℂ, MixedSignCoxeter.HasEigenC M μ ∧ r = ‖μ‖ } := by
  refine ⟨∑ i : Fin n, ∑ j : Fin n, ‖M i j‖, ?_⟩
  rintro r ⟨μ, hμ, rfl⟩
  exact norm_le_l1_of_hasEigenC M hμ

/-- Every complex eigenvalue `μ` of `M` satisfies `‖μ‖ ≤ spectralRadius M`. -/
theorem norm_le_spectralRadius (M : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ}
    (hμ : MixedSignCoxeter.HasEigenC M μ) :
    ‖μ‖ ≤ spectralRadius M :=
  le_csSup (hasEigenC_norms_bddAbove M) ⟨μ, hμ, rfl⟩

/-- If every complex eigenvalue of `M` has modulus `≤ C` (with `0 ≤ C`), then
`spectralRadius M ≤ C`. -/
theorem spectralRadius_le_of_forall (M : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ μ : ℂ, MixedSignCoxeter.HasEigenC M μ → ‖μ‖ ≤ C) :
    spectralRadius M ≤ C := by
  apply Real.sSup_le
  · rintro r ⟨μ, hμ, rfl⟩
    exact h μ hμ
  · exact hC

/-- The spectral radius of any real matrix is nonnegative. -/
theorem spectralRadius_nonneg (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ spectralRadius M := by
  apply Real.sSup_nonneg
  rintro r ⟨μ, _, rfl⟩
  exact norm_nonneg μ

/-- If `M` has a complex eigenvalue `μ` with `c < ‖μ‖`, then `c < spectralRadius M`. -/
theorem lt_spectralRadius_of_eigen (M : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ} {c : ℝ}
    (hμ : MixedSignCoxeter.HasEigenC M μ) (hc : c < ‖μ‖) :
    c < spectralRadius M :=
  lt_of_lt_of_le hc (norm_le_spectralRadius M hμ)

/-! ### Definition 2.62: Minimal Principal Spectral Radius `Λ(Γ)` -/

/-- **Definition 2.62**: The minimal spectral radius `Λ(Γ) = min { λ(w) | w principal in W(Γ) }`
over all `n!` principal elements of a reflection system `S`. -/
noncomputable def minPrincipalSpectralRadius (S : ReflectionSystem n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun σ : Equiv.Perm (Fin n) => spectralRadius (principalElementOfPerm S σ))

/-- `Λ(Γ) ≤ λ(w_σ)` for every principal element `w_σ`. -/
theorem minPrincipalSpectralRadius_le (S : ReflectionSystem n) (σ : Equiv.Perm (Fin n)) :
    minPrincipalSpectralRadius S ≤ spectralRadius (principalElementOfPerm S σ) :=
  Finset.inf'_le _ (Finset.mem_univ σ)

/-- The minimum `Λ(Γ)` is attained by some principal element `w_σ`. -/
theorem exists_principal_eq_minPrincipalSpectralRadius (S : ReflectionSystem n) :
    ∃ σ : Equiv.Perm (Fin n),
      spectralRadius (principalElementOfPerm S σ) = minPrincipalSpectralRadius S := by
  obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun σ : Equiv.Perm (Fin n) => spectralRadius (principalElementOfPerm S σ))
  exact ⟨σ, hσ.symm⟩

/-- `0 ≤ Λ(Γ)` for every reflection system `S`. -/
theorem minPrincipalSpectralRadius_nonneg (S : ReflectionSystem n) :
    0 ≤ minPrincipalSpectralRadius S := by
  obtain ⟨σ, hσ⟩ := exists_principal_eq_minPrincipalSpectralRadius S
  rw [← hσ]
  exact spectralRadius_nonneg _

/-! ### Definition 2.65: Mahler Measure `M(f)` -/

/-- **Definition 2.65**: The Mahler measure
`M(f) = |a_d| · ∏ max(1, |λ_i|)` of a complex polynomial `f`, where the product runs over
the multiset of complex roots of `f` (counted with multiplicity). -/
noncomputable def mahlerMeasure (p : Polynomial ℂ) : ℝ :=
  ‖p.leadingCoeff‖ * (p.roots.map fun z : ℂ => max (1 : ℝ) ‖z‖).prod

/-- The Mahler measure of any polynomial is nonnegative. -/
theorem mahlerMeasure_nonneg (p : Polynomial ℂ) : 0 ≤ mahlerMeasure p := by
  unfold mahlerMeasure
  refine mul_nonneg (norm_nonneg _) ?_
  exact Multiset.prod_nonneg fun r hr => by
    rcases Multiset.mem_map.mp hr with ⟨z, _, rfl⟩
    exact le_trans zero_le_one (le_max_left 1 ‖z‖)

/-- Every monic polynomial has Mahler measure `≥ 1`. -/
theorem one_le_mahlerMeasure_of_monic {p : Polynomial ℂ} (hp : p.Monic) :
    1 ≤ mahlerMeasure p := by
  unfold mahlerMeasure
  rw [hp.leadingCoeff, norm_one, one_mul]
  have hprod : ∀ s : Multiset ℝ, (∀ r ∈ s, (1 : ℝ) ≤ r) → (1 : ℝ) ≤ s.prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro h
      rw [Multiset.prod_cons]
      have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
      have hs : 1 ≤ s.prod := ih fun r hr => h r (Multiset.mem_cons_of_mem hr)
      nlinarith
  exact hprod _ fun r hr => by
    rcases Multiset.mem_map.mp hr with ⟨z, _, rfl⟩
    exact le_max_left 1 ‖z‖

end SpectralRadius

end ReflectionSystem
