/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_FormIdeal_CLOSED.lean — extracted 5 closed declarations. -/

theorem coordMap_kills_ideal_CLOSED (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) :
    coordMap_kills_ideal_OPEN a b c h_disc :=
  coordMap_kills_ideal a b c h_disc

/-- **CLOSED — FormIdeal Surface 2** (Milestone 5.5):
    `ker(coordMap a b) = idealOfForm a b`.

    Proof: `coordMap_ker_eq_ideal a b c h_disc` (BSD_FormIdeal.lean §7d).
    Forward: `coordMap x = 0` → `a ∣ repr(x,0) − kb·repr(x,1)` → `x ∈ 𝔞_Q`.
    Backward: Surface 1. -/

theorem coordMap_ker_eq_ideal_CLOSED (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) :
    coordMap_ker_eq_ideal_OPEN a b c h_disc :=
  coordMap_ker_eq_ideal a b c h_disc

/-- **CLOSED — FormIdeal Surface 3** (Milestone 5.5):
    `Ideal.absNorm (idealOfForm a b) = a.natAbs`.

    Proof: `idealOfForm_absNorm a b c h_disc` (BSD_FormIdeal.lean §7e).
    Method: `coordMap a b` surjective (ZMod.natCast_zmod_val), kernel = `idealOfForm` (Surface 2),
    first isomorphism theorem → `𝓞 K / 𝔞_Q ≃+ ZMod a.natAbs` → `absNorm = Nat.card = a.natAbs`. -/

theorem idealOfForm_absNorm_CLOSED (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) :
    idealOfForm_absNorm_OPEN a b c h_disc :=
  idealOfForm_absNorm a b c h_disc

/-- **CLOSED — FormIdeal Surface 4** (Milestone 5.5):
    All 10 reduced BQFs of disc -143 have `absNorm(𝔞_Q) = a`.

    Proof: `idealOfForm_classGroup_bridge_proof` (BSD_FormIdeal.lean §7f).
    Applies Surface 3 to each of the 10 forms; disc = -143 verified by `norm_num`. -/

theorem idealOfForm_classGroup_bridge_CLOSED : idealOfForm_classGroup_bridge_OPEN :=
  idealOfForm_classGroup_bridge_proof

/-- **Milestone 5.5 FormIdeal surface ledger**: all 4 FormIdeal surfaces closed.
    No sorry, classical trio only. -/

theorem BSD_FormIdeal_all_CLOSED :
    (∀ a b c : ℤ, ∀ h : b ^ 2 - 4 * a * c = -143, coordMap_kills_ideal_OPEN a b c h) ∧
    (∀ a b c : ℤ, ∀ h : b ^ 2 - 4 * a * c = -143, coordMap_ker_eq_ideal_OPEN a b c h) ∧
    (∀ a b c : ℤ, ∀ h : b ^ 2 - 4 * a * c = -143, idealOfForm_absNorm_OPEN a b c h) ∧
    idealOfForm_classGroup_bridge_OPEN :=
  ⟨coordMap_kills_ideal, coordMap_ker_eq_ideal, idealOfForm_absNorm,
   idealOfForm_classGroup_bridge_proof⟩

/-- Open surface count for FormIdeal module: 0 (all 4 closed at Milestone 5.5). -/
def BSD_FormIdeal_open_count : ℕ := 0

end Towers.BSD

