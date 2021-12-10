lemma one_mul (m : mynat) : 1 * m = m :=
begin
induction m with h hd,
rw mul_zero,
refl,
rw mul_succ,
rw hd,
rw one_eq_succ_zero,
rw add_succ,
rw add_zero,
refl,
end