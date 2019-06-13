require import Ring List FSet Int.
require (*--*) FinType.

pragma -oldip. pragma +implicits.

(**************************************************************************)
clone include Ring.ZModule.

op enum: t list.
axiom enumS x: count (pred1 x) enum = 1.

clone include FinType with
  type  t         <- t,
  op    enum      <- enum
proof enum_spec by exact/enumS.

(**************************************************************************)
op is_subgroup (s : t fset) =
  zeror \in s /\
  forall x y, x \in s => y \in s => (x - y) \in s.

lemma subgroup_opp (s : t fset) x:
  is_subgroup s => x \in s => -x \in s.
proof.
rewrite /is_subgroup=> -[+ mems_sub] - /mems_sub h /h {h}.
by rewrite sub0r.
qed.

lemma subgroup_add (s : t fset) x y:
  is_subgroup s => x \in s => y \in s => x + y \in s.
proof.
move=> ^ /(subgroup_opp _ y) opp_y.
rewrite /is_subgroup=> -[_ mems_sub] /mems_sub + /opp_y - h /h.
by rewrite opprK.
qed.

(**************************************************************************)
op coset1 g H = oflist (map (fun x=> g + x) (elems H))
axiomatized by coset1E.

lemma coset1P g H x:
  (x \in coset1 g H <=> x - g \in H).
proof.
rewrite coset1E mem_oflist mapP; split=> [[h] [] /= + ->>|xg_in_H].
+ by rewrite -memE addrAC subrr add0r.
by exists (x - g)=> /=; rewrite -memE xg_in_H /= addrCA subrr addr0.
qed.

lemma cosets_bij a b H:
  exists f,
    bijective f /\
    coset1 b H = image f (coset1 a H).
proof.
exists (fun h=> b - a + h); split.
+ exists (fun h=> a - b + h); rewrite /cancel /=; split=> x.
  + by rewrite addrA addrCA addrA addrCA subrr addr0 subrr add0r.
  by rewrite addrA addrCA addrA addrCA subrr addr0 subrr add0r.
apply/fsetP=> h; rewrite imageP coset1P; split=> [hb_in_H|].
+ exists (a + h - b); rewrite coset1P /=.
  rewrite -!addrA (@addrA (-a)) (@addrC (-a)) subrr add0r.
  rewrite (@addrC h (-b)) (@addrA b (-b) h) subrr add0r //=.
  by rewrite addrC -!addrA (@addrC (-a) a) subrr addr0.
move=> [ah] [] /= + <<-; rewrite coset1P (@addrC b) -addrA (@addrC _ (-b)).
by rewrite -addrA (@addrA b (-b)) subrr add0r addrC.
qed.

(**************************************************************************)
op cosets H = oflist (map (fun g=> coset1 g H) enum)
axiomatized by cosetsE.

(**************************************************************************)
op gen x = oflist (filter (fun y=> exists n, y = intmul x n) enum)
axiomatized by genE.

lemma mem_gen y x:
  y \in gen x <=> exists n, y = intmul x n.
proof. by rewrite genE mem_oflist mem_filter enumP /=. qed.

lemma mem0_gen x: zeror \in gen x.
proof. by rewrite -(@mulr0z x) mem_gen; exists 0. qed.

lemma mem1_gen x: x \in gen x.
proof. by rewrite -{2}(@mulr1z x) mem_gen; exists 1. qed.

lemma is_subgroup_gen x: is_subgroup (gen x).
proof.
split=> [|y z]; first by exact/mem0_gen.
rewrite !mem_gen=> - [log_y ->>] [log_z ->>].
by exists (log_y - log_z); rewrite -mulrNz mulrzz_add.
qed.

(**************************************************************************)
op order x = card (gen x).
