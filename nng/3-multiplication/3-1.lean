lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin
induction m with h hd,
rw mul_zero,
refl,
rw mul_succ,
rw hd,
rw add_zero,
refl,
end