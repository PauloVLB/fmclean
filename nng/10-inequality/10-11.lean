theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin
intro ab,
intro t,
cases ab with c hc,
rw hc,
rw add_assoc,
rw add_comm c t,
rw ← add_assoc,
use c,
refl,

end