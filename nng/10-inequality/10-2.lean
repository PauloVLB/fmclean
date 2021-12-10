lemma le_refl (x : mynat) : x ≤ x :=
begin
use 0,
rw add_zero,
refl,

end