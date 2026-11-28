import Towers.BSD.BSD_NormBridge
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# BSD_FormIdeal — Form-to-ideal map for the BSD class-number bridge

Maps each reduced BQF `Q = ax² + bxy + cy²` of discriminant -143 to a fractional
ideal `𝔞_Q ⊆ 𝓞 K` and proves that `Ideal.absNorm 𝔞_Q = a`.

## Mathematical content

For `K = ℚ(√-143)`, `𝓞_K = ℤ ⊕ ℤ·ω` (`ω = (1+√-143)/2`), and a primitive
positive-definite BQF `Q = ax² + bxy + cy²` with `b² − 4ac = -143`:

  `𝔞_Q := Ideal.span {(a : 𝓞_K),  (b+√-143)/2}  =  Ideal.span {a,  (b-1)/2 + ω}`

Since all valid `b` for disc -143 are **odd** (`b² ≡ 1 mod 4` forces this), the
element `(b-1)/2 + ω` lands in `𝓞_K`. ✓

### Proof that `Ideal.absNorm 𝔞_Q = a` (§4)

The key tool is the **coordinate map**
  `coordMap a b : 𝓞_K →+ ZMod a.natAbs`,
  `coordMap a b x = (m − ((b−1)/2)·n) mod a`
where `x = m·1 + n·ω` (unique ℤ-basis coordinates via `BSD_intBasis`).

**Claim:** `𝓞_K / 𝔞_Q  ≅  ZMod a.natAbs` as additive groups, giving
  `Ideal.absNorm 𝔞_Q = Nat.card (𝓞_K / 𝔞_Q) = a`.

Proof:
- `coordMap` kills both generators: `a ↦ (a mod a) = 0` and `gen2 ↦ 0` (sub_self).
- Surjectivity: `coordMap a b 1 = 1 mod a.natAbs`.  For `0 < a.natAbs` this generates
  `ZMod a.natAbs`.
- Kernel = `𝔞_Q`: (→) any ideal element `r·(a : 𝓞_K)` sends to `a·(...)·mod a = 0`,
  and `r·gen2` uses the `ω²-equation` + disc = -143 to get `n·ac mod a = 0`.
  (←) divisibility `a | m - (b-1)/2·n` → element is a ℤ-combination of generators.

## Proved (0 sorry, classical trio)

| Theorem | Content |
|---------|---------|
| `gen2_of_form_coe` | K-value of the second generator |
| `BSD_intBasis_zero_eq_one` | `BSD_intBasis 0 = (1 : 𝓞 K)` |
| `BSD_intBasis_one_eq_nω_OK` | `BSD_intBasis 1 = nω_OK` |
| `repr_intCast` | Basis repr of `(a : 𝓞 K)` |
| `repr_gen2` | Basis repr of `gen2_of_form b` |
| `coordMap` | Additive hom `𝓞 K →+ ZMod a.natAbs` |
| `coordMap_kills_gen1` | `coordMap a b (a : 𝓞 K) = 0` |
| `coordMap_kills_gen2` | `coordMap a b (gen2_of_form b) = 0` |
| `idealOfForm_one_eq_top` | `idealOfForm 1 b = ⊤` |
| `idealOfForm_absNorm_one` | `Ideal.absNorm (idealOfForm 1 b) = 1` |
| `coordMap_kills_ideal` | Surface 1 CLOSED |
| `coordMap_ker_eq_ideal` | Surface 2 CLOSED |
| `idealOfForm_absNorm` | Surface 3 CLOSED |
| `idealOfForm_classGroup_bridge_proof` | Surface 4 CLOSED |

## Named OPEN surfaces (replaced by proofs below)

All four original OPEN surfaces are now CLOSED. Definitions retained for compatibility.

SORRY: 0. Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
BSD class number lower bound: depends on ClassGroup API (separate surface).
-/

namespace Towers.BSD

open NumberField Polynomial

noncomputable section

/-! ## §1. Definitions -/

/-- Second generator of the form ideal `𝔞_Q` for a BQF `(a, b, c)`:
    `(b + √-143)/2 = (b-1)/2 + ω`.

    When `b` is odd (guaranteed by disc = -143), `(b-1)/2 : ℤ` is exact
    and `(b-1)/2 + ω` lies in `𝓞 K`. -/
def gen2_of_form (b : ℤ) : 𝓞 K := ((b - 1) / 2 : ℤ) + nω_OK

/-- The form ideal `𝔞_Q = ⟨a, (b+√-143)/2⟩ ⊆ 𝓞 K`. -/
def idealOfForm (a b : ℤ) : Ideal (𝓞 K) :=
  Ideal.span {(a : 𝓞 K), gen2_of_form b}

/-- K-value of `gen2_of_form b` is `(b-1)/2 + ω`. -/
lemma gen2_of_form_coe (b : ℤ) :
    (gen2_of_form b : K) = ((b - 1) / 2 : ℤ) + ω := by
  simp only [gen2_of_form, map_add, nω_OK_coe, map_intCast]

/-! ## §2. Basis identification lemmas -/

/-- `BSD_intBasis 0 = (1 : 𝓞 K)` as elements of `𝓞 K`. -/
lemma BSD_intBasis_zero_eq_one : BSD_intBasis 0 = (1 : 𝓞 K) := by
  apply_fun ((↑) : 𝓞 K → K) using Subtype.coe_injective
  simp [BSD_intBasis_zero_coe]

/-- `BSD_intBasis 1 = nω_OK` as elements of `𝓞 K`. -/
lemma BSD_intBasis_one_eq_nω_OK : BSD_intBasis 1 = nω_OK := by
  apply_fun ((↑) : 𝓞 K → K) using Subtype.coe_injective
  rw [BSD_intBasis_one_coe, nω_OK_coe]

/-! ## §3. Basis representation lemmas -/

/-- The `BSD_intBasis` representation of `(a : 𝓞 K)` is `Finsupp.single 0 a`. -/
lemma repr_intCast (a : ℤ) :
    BSD_intBasis.repr ((a : 𝓞 K)) = Finsupp.single 0 a := by
  have ha : ((a : ℤ) : 𝓞 K) = a • BSD_intBasis 0 := by
    rw [BSD_intBasis_zero_eq_one]; simp
  rw [ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The `BSD_intBasis` representation of `gen2_of_form b` is
    `Finsupp.single 0 ((b-1)/2) + Finsupp.single 1 1`. -/
lemma repr_gen2 (b : ℤ) :
    BSD_intBasis.repr (gen2_of_form b) =
    Finsupp.single 0 ((b - 1) / 2) + Finsupp.single 1 1 := by
  simp only [gen2_of_form, map_add, repr_intCast,
    show nω_OK = BSD_intBasis 1 from BSD_intBasis_one_eq_nω_OK.symm,
    Basis.repr_self]

/-! ## §4. The coordinate map -/

/-- The **coordinate map** `coordMap a b : 𝓞 K →+ ZMod a.natAbs`:
    sends `x = m·1 + n·ω` to `(m - (b-1)/2 · n) mod a`.

    This is the key additive group hom whose kernel is `idealOfForm a b`
    (proved in §7). -/
def coordMap (a b : ℤ) : 𝓞 K →+ ZMod a.natAbs where
  toFun x := ((BSD_intBasis.repr x 0 -
               (b - 1) / 2 * BSD_intBasis.repr x 1 : ℤ) : ZMod a.natAbs)
  map_zero' := by simp [map_zero]
  map_add' x y := by
    simp only [map_add, Finsupp.add_apply]
    push_cast; ring

/-- `coordMap a b` kills the first generator `(a : 𝓞 K)`. -/
theorem coordMap_kills_gen1 (a b : ℤ) :
    coordMap a b ((a : 𝓞 K)) = 0 := by
  simp only [coordMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, repr_intCast]
  have h0 : (Finsupp.single (0 : Fin 2) a) (0 : Fin 2) = a := Finsupp.single_eq_same
  have h1 : (Finsupp.single (0 : Fin 2) a) (1 : Fin 2) = 0 :=
    Finsupp.single_eq_of_ne (by decide)
  rw [h0, h1, mul_zero, sub_zero]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natAbs_dvd.mpr (dvd_refl a)

/-- `coordMap a b` kills the second generator `gen2_of_form b`. -/
theorem coordMap_kills_gen2 (a b : ℤ) :
    coordMap a b (gen2_of_form b) = 0 := by
  simp only [coordMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, repr_gen2, Finsupp.add_apply]
  have h00 : (Finsupp.single (0 : Fin 2) ((b - 1) / 2)) (0 : Fin 2) = (b - 1) / 2 :=
    Finsupp.single_eq_same
  have h01 : (Finsupp.single (0 : Fin 2) ((b - 1) / 2)) (1 : Fin 2) = 0 :=
    Finsupp.single_eq_of_ne (by decide)
  have h10 : (Finsupp.single (1 : Fin 2) (1 : ℤ)) (0 : Fin 2) = 0 :=
    Finsupp.single_eq_of_ne (by decide)
  have h11 : (Finsupp.single (1 : Fin 2) (1 : ℤ)) (1 : Fin 2) = 1 :=
    Finsupp.single_eq_same
  rw [h00, h01, h10, h11]
  push_cast; ring

/-! ## §5. The a = 1 case (trivial form) -/

/-- For `a = 1`, the form ideal `idealOfForm 1 b` equals `⊤ = 𝓞 K`. -/
theorem idealOfForm_one_eq_top (b : ℤ) : idealOfForm 1 b = ⊤ := by
  rw [Ideal.eq_top_iff_one, idealOfForm]
  apply Ideal.subset_span
  simp

/-- For `a = 1`, the absolute norm of `idealOfForm 1 b` is 1. -/
theorem idealOfForm_absNorm_one (b : ℤ) :
    Ideal.absNorm (idealOfForm 1 b) = 1 := by
  rw [idealOfForm_one_eq_top, Ideal.absNorm_top]

/-! ## §6. Surjectivity of coordMap (for 0 < a.natAbs) -/

/-- `coordMap a b 1 = (1 : ZMod a.natAbs)`. -/
lemma coordMap_one_eq_one (a b : ℤ) :
    coordMap a b (1 : 𝓞 K) = (1 : ZMod a.natAbs) := by
  simp only [coordMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have h_repr : BSD_intBasis.repr (1 : 𝓞 K) = Finsupp.single 0 1 := by
    have hcast : (1 : 𝓞 K) = ((1 : ℤ) : 𝓞 K) := by norm_cast
    rw [hcast, repr_intCast]
  rw [h_repr]
  have h0 : (Finsupp.single (0 : Fin 2) (1 : ℤ)) (0 : Fin 2) = 1 := Finsupp.single_eq_same
  have h1 : (Finsupp.single (0 : Fin 2) (1 : ℤ)) (1 : Fin 2) = 0 :=
    Finsupp.single_eq_of_ne (by decide)
  rw [h0, h1, mul_zero, sub_zero]
  norm_cast

/-! ## §7. Named OPEN surfaces — definitions (retained for compatibility) -/

/-- **CLOSED**: `coordMap a b` kills every element of `idealOfForm a b`. -/
def coordMap_kills_ideal_OPEN (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) : Prop :=
  ∀ x ∈ idealOfForm a b, coordMap a b x = 0

/-- **CLOSED**: The kernel of `coordMap a b` equals `idealOfForm a b`. -/
def coordMap_ker_eq_ideal_OPEN (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) : Prop :=
  ∀ x : 𝓞 K, coordMap a b x = 0 ↔ x ∈ idealOfForm a b

/-- **CLOSED**: `Ideal.absNorm (idealOfForm a b) = a.natAbs`. -/
def idealOfForm_absNorm_OPEN (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) : Prop :=
  Ideal.absNorm (idealOfForm a b) = a.natAbs

/-- **CLOSED**: absNorm bridge for all 10 reduced forms of disc -143. -/
def idealOfForm_classGroup_bridge_OPEN : Prop :=
  ∀ abc : ℤ × ℤ × ℤ,
    abc ∈ ([(1, 1, 36), (2, 1, 18), (2, -1, 18),
            (3, 1, 12), (3, -1, 12), (4, 1, 9), (4, -1, 9),
            (6, 1, 6), (6, 5, 7), (6, -5, 7)] : List (ℤ × ℤ × ℤ)) →
    Ideal.absNorm (idealOfForm abc.1 abc.2.1) = abc.1.natAbs

/-! ## §7b. Auxiliary lemmas for closing the surfaces -/

/-- When `b² - 4ac = -143`, `b` is odd.
    If `b = 2k` then `4k² - 4ac = -143`, so `4 ∣ -143`, contradiction. -/
lemma b_odd_of_disc {a b c : ℤ} (h_disc : b ^ 2 - 4 * a * c = -143) :
    ∃ k : ℤ, b = 2 * k + 1 := by
  rcases Int.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    have hb2 : b ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
    have h4 : (4 : ℤ) ∣ -143 := ⟨k ^ 2 - a * c, by linarith⟩
    norm_num at h4
  · exact ⟨k, hk⟩

/-- Basis decomposition: `s = (r₀ : 𝓞 K) + (r₁ : 𝓞 K) * nω_OK`
    where `rᵢ = BSD_intBasis.repr s i`. -/
lemma ok_basis_decomp (s : 𝓞 K) :
    s = (BSD_intBasis.repr s 0 : 𝓞 K) + (BSD_intBasis.repr s 1 : 𝓞 K) * nω_OK := by
  have h := BSD_intBasis.sum_repr s
  simp only [Fin.sum_univ_two, BSD_intBasis_zero_eq_one, BSD_intBasis_one_eq_nω_OK,
             Algebra.smul_def, mul_one] at h
  push_cast at h
  exact h.symm

/-- `repr ((c : 𝓞 K) * nω_OK) = Finsupp.single 1 c` for any `c : ℤ`. -/
lemma repr_intCast_mul_nω_OK (c : ℤ) :
    BSD_intBasis.repr ((c : 𝓞 K) * nω_OK) = Finsupp.single 1 c := by
  rw [show (c : 𝓞 K) * nω_OK = c • nω_OK from (Algebra.smul_def c nω_OK).symm,
      show nω_OK = BSD_intBasis 1 from BSD_intBasis_one_eq_nω_OK.symm,
      map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §7c. Closing surface 1 -/

/-- Helper: `coordMap a b` kills `r * (a : 𝓞 K)` for any `r : 𝓞 K`.
    Proof: `r * a = a • r`, and `a ≡ 0 mod a.natAbs`. -/
theorem coordMap_mul_gen1_aux (a b : ℤ) (r : 𝓞 K) :
    coordMap a b (r * (a : 𝓞 K)) = 0 := by
  have hmul : r * (a : 𝓞 K) = (a : ℤ) • r := by
    rw [mul_comm]; exact (Algebra.smul_def a r).symm
  rw [hmul, map_zsmul, zsmul_eq_mul]
  have ha : (a : ZMod a.natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl a)
  simp [ha]

/-- Helper: `coordMap a b` kills `s * gen2_of_form b`, given disc = -143.
    Key steps: basis-decompose `s`, use `nω_OK² = nω_OK - 36`, apply disc arithmetic. -/
theorem coordMap_mul_gen2_aux (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143)
    (s : 𝓞 K) : coordMap a b (s * gen2_of_form b) = 0 := by
  set r0 := BSD_intBasis.repr s 0 with hr0_def
  set r1 := BSD_intBasis.repr s 1 with hr1_def
  -- Compute s * gen2 in 𝓞 K using nω_OK² = nω_OK - 36
  have hprod : s * gen2_of_form b =
      ((r0 * ((b - 1) / 2) - 36 * r1 : ℤ) : 𝓞 K) +
      ((r0 + r1 * ((b - 1) / 2 + 1) : ℤ) : 𝓞 K) * nω_OK := by
    rw [ok_basis_decomp s, gen2_of_form]
    push_cast
    ring_nf
    linear_combination (r1 : 𝓞 K) * nω_OK_sq
  -- Read off repr coordinates from hprod
  have hprod_repr : BSD_intBasis.repr (s * gen2_of_form b) =
      Finsupp.single 0 (r0 * ((b - 1) / 2) - 36 * r1) +
      Finsupp.single 1 (r0 + r1 * ((b - 1) / 2 + 1)) := by
    conv_lhs => rw [hprod]
    rw [map_add, repr_intCast, repr_intCast_mul_nω_OK]
  have hrepr0 : BSD_intBasis.repr (s * gen2_of_form b) 0 =
      r0 * ((b - 1) / 2) - 36 * r1 := by
    rw [hprod_repr, Finsupp.add_apply,
        Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        add_zero]
  have hrepr1 : BSD_intBasis.repr (s * gen2_of_form b) 1 =
      r0 + r1 * ((b - 1) / 2 + 1) := by
    rw [hprod_repr, Finsupp.add_apply,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        Finsupp.single_eq_same,
        zero_add]
  -- Evaluate coordMap
  simp only [coordMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hrepr0, hrepr1]
  -- b = 2k+1 (odd), so (b-1)/2 = k exactly
  obtain ⟨k, hb⟩ := b_odd_of_disc h_disc
  have hbhalf : (b - 1) / 2 = k := by omega
  rw [hbhalf]
  -- Disc condition gives 36 + k² + k = a*c
  have h_ac : 36 + k ^ 2 + k = a * c := by
    have hbsq : b ^ 2 = (2 * k + 1) ^ 2 := by rw [hb]
    linarith [show (2 * k + 1) ^ 2 = 4 * k ^ 2 + 4 * k + 1 from by ring]
  -- The expression = -(r1 * a * c) ≡ 0 mod a
  have h_expr : r0 * k - 36 * r1 - k * (r0 + r1 * (k + 1)) = -(r1 * (a * c)) := by
    linear_combination -r1 * h_ac
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, h_expr, dvd_neg,
      show r1 * (a * c) = a * c * r1 from by ring]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natAbs_dvd.mpr (dvd_refl a)) c) r1

/-- **CLOSED — Surface 1**: `coordMap a b` kills every element of `idealOfForm a b`.
    For any `x = r * a + s * gen2 ∈ 𝔞_Q`, both summands map to 0 and add to 0. -/
theorem coordMap_kills_ideal (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) :
    coordMap_kills_ideal_OPEN a b c h_disc := by
  intro x hx
  simp only [idealOfForm, Ideal.mem_span_pair] at hx
  obtain ⟨r, s, hrs⟩ := hx
  rw [← hrs, map_add,
      coordMap_mul_gen1_aux a b r,
      coordMap_mul_gen2_aux a b c h_disc s,
      add_zero]

/-! ## §7d. Closing surface 2 -/

/-- **CLOSED — Surface 2**: Kernel of `coordMap a b` equals `idealOfForm a b`.

    Forward: `coordMap x = 0` gives divisibility `a ∣ m − (b-1)/2·n`,
    yielding `x = k·(a:𝓞K) + n·gen2 ∈ 𝔞_Q`.
    Backward: Surface 1. -/
theorem coordMap_ker_eq_ideal (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) :
    coordMap_ker_eq_ideal_OPEN a b c h_disc := by
  obtain ⟨kb, hbk⟩ := b_odd_of_disc h_disc
  have hbhalf : (b - 1) / 2 = kb := by omega
  intro x
  constructor
  · intro hzero
    simp only [coordMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hbhalf] at hzero
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd] at hzero
    obtain ⟨k, hk⟩ := hzero
    rw [idealOfForm, Ideal.mem_span_pair]
    refine ⟨(k : 𝓞 K), (BSD_intBasis.repr x 1 : 𝓞 K), ?_⟩
    apply_fun ((↑) : 𝓞 K → K) using Subtype.coe_injective
    simp only [map_add, map_mul, map_intCast, gen2_of_form_coe, nω_OK_coe]
    rw [show ((b - 1) / 2 : ℤ) = kb from hbhalf]
    have hx_K : (x : K) = (BSD_intBasis.repr x 0 : K) +
                           (BSD_intBasis.repr x 1 : K) * ω := by
      have h := ok_basis_decomp x
      apply_fun ((↑) : 𝓞 K → K) at h
      simp only [map_add, map_mul, map_intCast, nω_OK_coe] at h
      exact h
    rw [hx_K]
    have h_int : BSD_intBasis.repr x 0 = a * k + kb * BSD_intBasis.repr x 1 := by linarith
    have h_m : (a : K) * k + (kb : K) * BSD_intBasis.repr x 1 = BSD_intBasis.repr x 0 := by
      exact_mod_cast h_int.symm
    linear_combination h_m
  · exact coordMap_kills_ideal a b c h_disc x

/-! ## §7e. Closing surface 3 -/

/-- **CLOSED — Surface 3**: `Ideal.absNorm (idealOfForm a b) = a.natAbs`.

    Proof: `coordMap a b` is surjective with kernel = `idealOfForm a b` (surface 2).
    First isomorphism theorem gives `𝓞 K / 𝔞_Q ≃+ ZMod a.natAbs`.
    Then `absNorm = cardQuot = Nat.card = a.natAbs`. -/
theorem idealOfForm_absNorm (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) :
    idealOfForm_absNorm_OPEN a b c h_disc := by
  have ha_pos : 0 < a * c := by nlinarith [sq_nonneg b]
  have ha_ne : a ≠ 0 := left_ne_zero_of_mul ha_pos.ne'
  haveI : NeZero a.natAbs := ⟨Int.natAbs_ne_zero.mpr ha_ne⟩
  have h_ker := coordMap_ker_eq_ideal a b c h_disc
  unfold idealOfForm_absNorm_OPEN
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h_surj : Function.Surjective (coordMap a b) := fun z =>
    ⟨(z.val : ℕ) • (1 : 𝓞 K), by
      rw [map_nsmul, coordMap_one_eq_one, nsmul_eq_mul, mul_one]
      exact_mod_cast ZMod.natCast_zmod_val z⟩
  have h_ker_eq : (coordMap a b).ker = (idealOfForm a b).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
    exact h_ker x
  have hequiv : 𝓞 K ⧸ (idealOfForm a b).toAddSubgroup ≃+ ZMod a.natAbs := by
    rw [← h_ker_eq]
    exact QuotientAddGroup.quotientKerEquivOfSurjective _ h_surj
  have hcard : Nat.card (𝓞 K ⧸ idealOfForm a b) = Nat.card (ZMod a.natAbs) := by
    have htype : (𝓞 K ⧸ idealOfForm a b) = (𝓞 K ⧸ (idealOfForm a b).toAddSubgroup) := rfl
    rw [htype]
    exact Nat.card_congr hequiv.toEquiv
  rw [hcard, Nat.card_zmod]

/-! ## §7f. Closing surface 4 -/

/-- **CLOSED — Surface 4**: All 10 reduced BQF ideals of disc -143 have the correct norm.
    Applies surface 3 to each of the 10 forms; disc = -143 verified by norm_num. -/
theorem idealOfForm_classGroup_bridge_proof : idealOfForm_classGroup_bridge_OPEN := by
  intro abc hmem
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.fst, Prod.snd]
  · exact idealOfForm_absNorm 1 1 36 (by norm_num)
  · exact idealOfForm_absNorm 2 1 18 (by norm_num)
  · exact idealOfForm_absNorm 2 (-1) 18 (by norm_num)
  · exact idealOfForm_absNorm 3 1 12 (by norm_num)
  · exact idealOfForm_absNorm 3 (-1) 12 (by norm_num)
  · exact idealOfForm_absNorm 4 1 9 (by norm_num)
  · exact idealOfForm_absNorm 4 (-1) 9 (by norm_num)
  · exact idealOfForm_absNorm 6 1 6 (by norm_num)
  · exact idealOfForm_absNorm 6 5 7 (by norm_num)
  · exact idealOfForm_absNorm 6 (-5) 7 (by norm_num)

/-! ## §8. Bridge combinators and ledger -/

/-- Surface ledger for BSD_FormIdeal:

    PROVED (0 sorry, classical trio):
    • gen2_of_form_coe
    • BSD_intBasis_zero_eq_one, BSD_intBasis_one_eq_nω_OK
    • repr_intCast, repr_gen2
    • coordMap (def), coordMap_kills_gen1, coordMap_kills_gen2
    • coordMap_one_eq_one (surjectivity source)
    • idealOfForm_one_eq_top, idealOfForm_absNorm_one

    CLOSED (0 sorry, classical trio):
    • coordMap_kills_ideal  (surface 1)
    • coordMap_ker_eq_ideal (surface 2)
    • idealOfForm_absNorm   (surface 3)
    • idealOfForm_classGroup_bridge_proof (surface 4) -/
theorem BSD_FormIdeal_ledger :
    ∀ b : ℤ, idealOfForm 1 b = ⊤ ∧ Ideal.absNorm (idealOfForm 1 b) = 1 :=
  fun b => ⟨idealOfForm_one_eq_top b, idealOfForm_absNorm_one b⟩

end
end Towers.BSD
