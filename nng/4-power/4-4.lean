lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=
begin
induction m with h hd,
rw pow_zero,
refl,
rw pow_succ,
rw hd,
rw mul_one,
refl,
end