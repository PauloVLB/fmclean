theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=
begin
symmetry,
rw succ_eq_add_one,
refl,
end