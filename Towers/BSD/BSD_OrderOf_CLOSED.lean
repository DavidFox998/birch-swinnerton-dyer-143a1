/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_OrderOf_CLOSED.lean — extracted 4 closed declarations. -/

theorem EvenK_NonPrincipal_Bridge_CLOSED : EvenK_NonPrincipal_Bridge_p2_OK :=
  EvenK_NonPrincipal_Bridge_proof

/-- **CLOSED — orderOf [𝔭₂] ≥ 10** (Milestone 5.6):
    `∃ p2 : ClassGroup (𝓞 K), 10 ≤ orderOf p2`.

    Explicit witness: `g := ClassGroup.mk0 ⟨p₂_OK, _⟩`.
    For any k ∈ {1,...,9}: `g^k = 1` ↔ `p₂^k` principal ↔ FALSE
    (by `master_not_principal_1_to_9` for odd k and EvenK bridge for even k).
    Therefore `orderOf g ≥ 10`.

    This is the explicit extraction of steps 1-4 of `BSD_classNumber_lower_bound`. -/

theorem BSD_orderOf_p2_CLOSED : BSD_orderOf_p2_OPEN := by
  have hp2_ne : (p2_OK : Ideal (𝓞 K)) ≠ 0 := by
    intro h
    have h2 := absNorm_p2_eq_2
    rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at h2
    norm_num at h2
  have hp₂_mem : p2_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
    mem_nonZeroDivisors_of_ne_zero hp2_ne
  let I₂ : nonZeroDivisors (Ideal (𝓞 K)) := ⟨p2_OK, hp₂_mem⟩
  let g : ClassGroup (𝓞 K) := ClassGroup.mk0 I₂
  refine ⟨g, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hlt9 : orderOf g ≤ 9 := Nat.lt_succ_iff.mp hlt
  have hpos : 0 < orderOf g := orderOf_pos g
  have hpow_ne : ∀ k : ℕ, 1 ≤ k → k ≤ 9 → g ^ k ≠ 1 := by
    intro k hk1 hk9 hgk
    have hmap : g ^ k = ClassGroup.mk0 (I₂ ^ k) :=
      (map_pow (ClassGroup.mk0 (R := 𝓞 K)) I₂ k).symm
    have hcoe : (↑(I₂ ^ k) : Ideal (𝓞 K)) = p2_OK ^ k := by
      simp only [SubmonoidClass.coe_pow, I₂]
    have hprinc : (↑(I₂ ^ k) : Ideal (𝓞 K)).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (I₂ ^ k).prop).mp (hmap ▸ hgk)
    exact master_not_principal_1_to_9 k hk1 hk9 (hcoe ▸ hprinc)
  exact hpow_ne (orderOf g) hpos hlt9 (pow_orderOf_eq_one g)

/-- **CLOSED — ClassGroup OrderOf bridge** (Milestone 5.6):
    `ClassGroup_OrderOf_Bridge_p2_OK :=
      EvenK_NonPrincipal_Bridge_p2_OK → ∃ p2 : ClassGroup (𝓞 K), 10 ≤ orderOf p2`.

    Proof: the consequent holds unconditionally (`BSD_orderOf_p2_CLOSED`), so
    the implication is trivially true regardless of the antecedent. -/

theorem ClassGroup_OrderOf_Bridge_CLOSED : ClassGroup_OrderOf_Bridge_p2_OK :=
  fun _ => BSD_orderOf_p2_CLOSED

/-- **Milestone 5.6 OrderOf surface ledger**: all 3 ClassGroup order surfaces closed.
    No sorry, classical trio only. -/

theorem BSD_OrderOf_all_CLOSED :
    EvenK_NonPrincipal_Bridge_p2_OK ∧
    BSD_orderOf_p2_OPEN ∧
    ClassGroup_OrderOf_Bridge_p2_OK :=
  ⟨EvenK_NonPrincipal_Bridge_proof, BSD_orderOf_p2_CLOSED, ClassGroup_OrderOf_Bridge_CLOSED⟩

/-- Open surface count for OrderOf module: 0 (all 3 closed at Milestone 5.6). -/
def BSD_OrderOf_open_count : ℕ := 0

end Towers.BSD

